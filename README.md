# encoding_rs

[![Build Status](https://travis-ci.org/hsivonen/safe_encoding_rs_mem.svg?branch=master)](https://travis-ci.org/hsivonen/safe_encoding_rs_mem)
[![Apache 2 / MIT dual-licensed](https://img.shields.io/badge/license-Apache%202%20%2F%20MIT-blue.svg)](https://github.com/hsivonen/safe_encoding_rs_mem/blob/master/COPYRIGHT)

`safe_encoding_rs_mem` is a second implementation of the `encoding_rs::mem`
API using only safe code and the standard library in an obviously correct
way. The purpose of this crate is to serve as a fuzzing and benchmarking
reference for `encoding_rs::mem`, which uses `unsafe` in the hope of
outperforming the standard library.

## Licensing

Please see the file named
[COPYRIGHT](https://github.com/hsivonen/encoding_rs/blob/master/COPYRIGHT).
