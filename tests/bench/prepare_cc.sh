cabal run compiladores2023.cabal -- -c tests/bench/ack_3_8.fd4
gcc -o tests/bench/ack_3_8.out runtime.c tests/bench/ack_3_8.c -Os -lgc
