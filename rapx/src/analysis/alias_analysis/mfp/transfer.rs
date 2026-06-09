/// Transfer functions for alias analysis
use rustc_middle::mir::{Operand, Place, ProjectionElem};

use super::intraproc::{AliasDomain, PlaceId, PlaceInfo};

/// Convert a MIR Place to a PlaceId
pub fn mir_place_to_place_id<'tcx>(place: Place<'tcx>) -> PlaceId {
    let mut place_id = PlaceId::Local(place.local.as_usize());

    // Process projections
    for proj in place.projection {
        match proj {
            ProjectionElem::Field(field, _) => {
                place_id = place_id.project_field(field.as_usize());
            }
            ProjectionElem::Deref => {
                // For deref, we keep the current place (pointer itself)
                // The actual memory is not tracked as a separate place
            }
            _ => {
                // Other projections (index, downcast, etc.) are not tracked
            }
        }
    }

    place_id
}

/// Extract place from operand if it's Copy or Move
pub fn operand_to_place_id<'tcx>(operand: &Operand<'tcx>) -> Option<PlaceId> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(mir_place_to_place_id(*place)),
        Operand::Constant(_) => None,
    }
}

/// Transfer function for assignment: lv = rv
pub fn transfer_assign<'tcx>(
    state: &mut AliasDomain,
    lv: Place<'tcx>,
    rv: &Operand<'tcx>,
    place_info: &PlaceInfo<'tcx>,
) {
    let lv_id = mir_place_to_place_id(lv);

    // Get index for lv
    let lv_idx = match place_info.get_index(&lv_id) {
        Some(idx) => idx,
        None => return, // Place not tracked
    };

    // Check if lv may drop
    if !place_info.may_drop(lv_idx) {
        return;
    }

    // Kill: remove old aliases for lv and all its fields (e.g., lv.0, lv.1.2, etc.)
    state.remove_aliases_with_prefix(&lv_id, place_info);

    // Gen: add alias lv ≈ rv if rv is a place
    if let Some(rv_id) = operand_to_place_id(rv) {
        if let Some(rv_idx) = place_info.get_index(&rv_id) {
            if place_info.may_drop(rv_idx) {
                state.union(lv_idx, rv_idx);

                // Sync fields if both have fields
                sync_fields(state, &lv_id, &rv_id, place_info);
            }
        }
    }
}

/// Transfer function for reference: lv = &rv
pub fn transfer_ref<'tcx>(
    state: &mut AliasDomain,
    lv: Place<'tcx>,
    rv: Place<'tcx>,
    place_info: &PlaceInfo<'tcx>,
) {
    // Reference creation is similar to assignment
    let lv_id = mir_place_to_place_id(lv);
    let rv_id = mir_place_to_place_id(rv);

    let lv_idx = match place_info.get_index(&lv_id) {
        Some(idx) => idx,
        None => return,
    };

    let rv_idx = match place_info.get_index(&rv_id) {
        Some(idx) => idx,
        None => return,
    };

    if !place_info.may_drop(lv_idx) || !place_info.may_drop(rv_idx) {
        return;
    }

    // Kill: remove old aliases for lv and all its fields
    state.remove_aliases_with_prefix(&lv_id, place_info);

    // Gen: add alias lv ≈ rv
    state.union(lv_idx, rv_idx);

    // Sync fields
    sync_fields(state, &lv_id, &rv_id, place_info);
}

/// Transfer function for field assignment: lv = rv.field
pub fn transfer_field_assign<'tcx>(
    state: &mut AliasDomain,
    lv: Place<'tcx>,
    rv_base: Place<'tcx>,
    field_idx: usize,
    place_info: &PlaceInfo<'tcx>,
) {
    let lv_id = mir_place_to_place_id(lv);
    let rv_base_id = mir_place_to_place_id(rv_base);
    let rv_field_id = rv_base_id.project_field(field_idx);

    let lv_idx = match place_info.get_index(&lv_id) {
        Some(idx) => idx,
        None => return,
    };

    let rv_field_idx = match place_info.get_index(&rv_field_id) {
        Some(idx) => idx,
        None => return,
    };

    if !place_info.may_drop(lv_idx) || !place_info.may_drop(rv_field_idx) {
        return;
    }

    // Kill: remove old aliases for lv and all its fields
    state.remove_aliases_with_prefix(&lv_id, place_info);

    // Gen: add alias lv ≈ rv.field
    state.union(lv_idx, rv_field_idx);

    // Sync fields
    sync_fields(state, &lv_id, &rv_field_id, place_info);
}

/// Transfer function for aggregate: lv = (operands...)
pub fn transfer_aggregate<'tcx>(
    state: &mut AliasDomain,
    lv: Place<'tcx>,
    operands: &[Operand<'tcx>],
    place_info: &PlaceInfo<'tcx>,
) {
    let lv_id = mir_place_to_place_id(lv);

    // Kill: remove old aliases for lv and all its fields
    state.remove_aliases_with_prefix(&lv_id, place_info);

    // Gen: for each field, add alias lv.i ≈ operand[i]
    for (field_idx, operand) in operands.iter().enumerate() {
        if let Some(rv_id) = operand_to_place_id(operand) {
            let lv_field_id = lv_id.project_field(field_idx);

            if let Some(lv_field_idx) = place_info.get_index(&lv_field_id) {
                if let Some(rv_idx) = place_info.get_index(&rv_id) {
                    if place_info.may_drop(lv_field_idx) && place_info.may_drop(rv_idx) {
                        state.union(lv_field_idx, rv_idx);

                        // Sync nested fields
                        sync_fields(state, &lv_field_id, &rv_id, place_info);
                    }
                }
            }
        }
    }
}

/// Transfer function for function call
pub fn transfer_call<'tcx>(
    state: &mut AliasDomain,
    ret: Place<'tcx>,
    _args: &[Operand<'tcx>],
    place_info: &PlaceInfo<'tcx>,
) {
    let ret_id = mir_place_to_place_id(ret);

    // Kill: remove old aliases for return value and all its fields
    state.remove_aliases_with_prefix(&ret_id, place_info);

    // Note: Function summary application will be handled separately
    // in the Analysis implementation. This is just the basic kill effect.
    // The gen effect (applying function summaries) happens in apply_call_return_effect
}

/// Synchronize field aliases
/// If lv and rv are aliased, ensure all their corresponding fields are also aliased
pub fn sync_fields<'tcx>(
    state: &mut AliasDomain,
    lv: &PlaceId,
    rv: &PlaceId,
    place_info: &PlaceInfo<'tcx>,
) {
    // Recursively sync fields up to a reasonable depth
    const MAX_SYNC_DEPTH: usize = 3;
    sync_fields_recursive(state, lv, rv, place_info, 0, MAX_SYNC_DEPTH);
}

/// Recursive helper for field synchronization
fn sync_fields_recursive<'tcx>(
    state: &mut AliasDomain,
    lv: &PlaceId,
    rv: &PlaceId,
    place_info: &PlaceInfo<'tcx>,
    depth: usize,
    max_depth: usize,
) {
    if depth >= max_depth {
        return;
    }

    // Try to sync common fields (0..N)
    // We'll try up to 16 fields as a reasonable upper bound
    for field_idx in 0..16 {
        let lv_field = lv.project_field(field_idx);
        let rv_field = rv.project_field(field_idx);

        // Check if both field places exist
        if let (Some(lv_field_idx), Some(rv_field_idx)) = (
            place_info.get_index(&lv_field),
            place_info.get_index(&rv_field),
        ) {
            // Both fields exist and may drop, union them
            if place_info.may_drop(lv_field_idx) && place_info.may_drop(rv_field_idx) {
                if state.union(lv_field_idx, rv_field_idx) {
                    // If union succeeded (they weren't already aliased), recurse
                    sync_fields_recursive(
                        state,
                        &lv_field,
                        &rv_field,
                        place_info,
                        depth + 1,
                        max_depth,
                    );
                }
            }
        } else {
            // If either field doesn't exist, no more fields to sync
            break;
        }
    }
}
