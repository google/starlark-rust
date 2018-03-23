mod testutil;
use testutil::do_conformance_test;

include!(concat!(env!("OUT_DIR"), "/tests/go-testcases.rs"));
