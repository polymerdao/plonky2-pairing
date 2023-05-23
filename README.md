# plonky2-pairing

```shell
$ cargo test --package plonky2-pairing --lib gadgets::pairing::tests::test_pairing -r
```

Test on Macbook pro M1

```shell
running 1 test
[INFO  plonky2::plonk::circuit_builder] Degree before blinding & padding: 218847
[INFO  plonky2::plonk::circuit_builder] Degree after blinding & padding: 262144
[INFO  plonky2::util::timing] 11.9844s to build
test gadgets::pairing::tests::test_pairing has been running for over 60 seconds
[INFO  plonky2::util::timing] 52.7091s to prove
[INFO  plonky2::util::timing] 0.0073s to verify
test gadgets::pairing::tests::test_pairing ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 94 filtered out; finished in 67.49s
```