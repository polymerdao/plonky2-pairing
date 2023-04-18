# plonky2-pairing

```shell
$ cargo test --package plonky2-pairing --lib gadgets::pairing::tests::test_pairing -r
```

```shell
running 1 test
[INFO  plonky2::plonk::circuit_builder] Degree before blinding & padding: 5546084
[INFO  plonky2::plonk::circuit_builder] Degree after blinding & padding: 8388608
test gadgets::pairing::tests::test_pairing has been running for over 60 seconds
[INFO  plonky2::util::timing] 915.2555s to build
[INFO  plonky2::util::timing] 520.5687s to prove
[INFO  plonky2::util::timing] 0.0545s to verify
test gadgets::pairing::tests::test_pairing ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 84 filtered out; finished in 1516.65s
```