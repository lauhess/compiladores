#hyperfine --warmup 5 --runs 10 \
#    "tests/bench/run_simple_eval.sh"
#
#sleep 5

hyperfine --warmup 5 --runs 25 \
    --prepare "tests/bench/prepare_cc.sh" \
    "tests/bench/ack_3_8.out" 

sleep 5

hyperfine --warmup 5 --runs 25 \
    --prepare "tests/bench/prepare_bytecode32.sh" \
    "vm/macc tests/bench/ack_3_8.bc32" 

sleep 5

hyperfine --warmup 5 --runs 25 \
    --prepare "tests/bench/prepare_bytecode8.sh" \
    "vm/macc8 tests/bench/ack_3_8.bc8" 

sleep 5

hyperfine --warmup 5 --runs 25 \
    --prepare "gcc -o tests/bench/ackermann_native -Os tests/bench/ackermann.c" \
    "tests/bench/ackermann_native"

sleep 5

hyperfine --warmup 5 --runs 25 \
    --prepare "ghc -o tests/bench/ackermann_haskell tests/bench/ack.hs" \
    "tests/bench/ackermann_haskell"
