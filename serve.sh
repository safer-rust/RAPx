#!/usr/bin/env bash
usage() {
    cat <<EOF
用法: $0 (-d <项目目录> | -k) [-p 端口]

参数:
  -d <dir>   Rust 项目根目录（执行构建并启动服务）
  -k         清理指定端口上的服务进程并退出
  -p <port>  HTTP 服务端口（可选，默认: 8080）

行为说明:
  - 使用 -d 时:
      * 自动清理指定端口上的已有服务
      * 在项目目录中构建 UPG 与 Rust 文档
      * 启动本地 HTTP 服务用于浏览文档与 UPG

  - 使用 -k 时:
      * 仅清理指定端口上的服务进程
EOF
    exit 1
}

set -e

PORT=8080
DIR=""
KILL=0

while getopts "d:p:k" opt; do
    case $opt in
        d) DIR="$OPTARG" ;;
        p) PORT="$OPTARG" ;;
        k) KILL=1 ;;
        *) usage ;;
    esac
done

# 至少有 -d 或 -k
[ -z "$DIR" ] && [ "$KILL" -eq 0 ] && usage

# 只要 -d 或 -k，就清理端口
if [ "$KILL" -eq 1 ] || [ -n "$DIR" ]; then
    lsof -ti :"$PORT" | xargs -r kill -9
    echo "端口 $PORT 已清理"
fi

# 仅 -k 时结束
[ -z "$DIR" ] && exit 0
[ ! -d "$DIR" ] && { echo "错误: 目录不存在"; exit 1; }

cd "$DIR"

MOD=$(basename "$PWD")
BASE_URL="http://127.0.0.1:$PORT"
SRC_URL="$BASE_URL/target/doc/src/$MOD/"

echo "生成 UPG..."
cargo rapx -upg

echo "构建文档..."
cargo clean
cargo doc --no-deps --document-private-items

[ -d UPG ] && sed -i "s|{{BASE_URL}}|$SRC_URL|g" UPG/*.html

echo "文档: $BASE_URL/target/doc/$MOD/"
echo "UPG : $BASE_URL/UPG"

python -m http.server "$PORT" >/dev/null 2>&1 &
echo "Server PID: $!"
