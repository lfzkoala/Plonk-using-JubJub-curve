#[macro_use]
extern crate lazy_static;

use dusk_bls12_381::Scalar;
use dusk_plonk::constraint_system::{StandardComposer, Variable};
use hades252::strategies::*;
use hades252::WIDTH;

pub mod jubjub;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
