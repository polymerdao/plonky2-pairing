# plonky2-pairing

Bn254 curve. Reference implementation is [here](https://github.com/zcash-hackworks/bn/blob/master/src/groups/mod.rs).

```shell
$ cargo test --package plonky2-pairing --lib gadgets::pairing::tests::test_pairing -r
```

Test result on Macbook pro M1

```shell
[INFO  plonky2::plonk::circuit_builder] Degree before blinding & padding: 193636
[INFO  plonky2::plonk::circuit_builder] Degree after blinding & padding: 262144
[INFO  plonky2::util::timing] 11.6787s to build
test gadgets::pairing::tests::test_pairing has been running for over 60 seconds
[INFO  plonky2::util::timing] 49.1468s to prove
[INFO  plonky2::util::timing] 0.0079s to verify
test gadgets::pairing::tests::test_pairing ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 93 filtered out; finished in 62.58s
```