---
name: rapx-scan
description: Run RAPx scan to inventory a Rust crate before deeper analysis — reports crate name, crate type, and four counts (total/generic/unsafe APIs, unsafe blocks). Applies to crate-level inventory only, not vulnerability detection, verification verdicts, or optimization advice.
---

# RAPx scan

## 使用情景

- 开始分析一个 crate 时，调用此命令以获取它的对外 API 规模和 unsafe 分布，再进行其他分析。
- 改动前后对同一个 crate 做粗略对比：同一命令、同一 crate 根目录，比较四个数字。

## 使用方法

在待分析 crate 的根目录运行：

```shell
cargo rapx analyze scan 2>&1
```

结果只写到 stderr，stdout 是空的。需要重定向 stderr 。输出带终端颜色控制字符，
解析前需要先进行清洗。

取值时按四个标签获取对应数据：`# total api`、`# generic api`、`# unsafe api`、
`# unsafe block`。

日志使用默认级别。要旁证命令行参数时可开 `RAPX_LOG=TRACE`；不要用 `RAPX_LOG=DEBUG`，
它会让整次分析 panic 中断。目前没有可安全开启的逐函数日志。

## 结果

输出具有固定格式：

```
======== crate info ========
name: <crate name>
type: <crate type>
============================

======== API info ========
# total api    = N
# generic api  = N
# unsafe api   = N
# unsafe block = N
============================
```

四项各自的含义：

- `total api`：对外公开的 api 数量，含 `pub use` 重新导出的；带函数体的各类函数都计入，
  只有签名没有函数体的 trait 方法不计入。
- `generic api`：其中泛型函数的数量，包含在 `total api` 之内。
- `unsafe api`：其中声明为 `unsafe fn` 的公开函数数量；私有的 unsafe 函数不计入。
- `unsafe block`：整个 crate 中 `unsafe {}` 块的数量，跨模块统计，不按可见性过滤。

解读这些数字时的注意点：

- `total api` 至少为 2：每次运行会多计两个 RAPx 辅助函数。实际结果为调用结果减 2。
- `type:` 只报告 crate 的第一个类型。声明了多种类型（如 `lib` 加 `cdylib`）的 crate
  只能看到其中一种。
- `unsafe api` 为 0 不代表 crate 里没有 unsafe 代码：私有的 unsafe 函数不计入该数字，
  但它们的 `unsafe {}` 块计入 `unsafe block`。

调用后记录 crate 名称、类型及四项数据，以备后续分析，注意 total_api 的实际结果偏差问题。