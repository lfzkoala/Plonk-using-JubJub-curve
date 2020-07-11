use dusk_bls12_381::Scalar;
use dusk_plonk::{
    commitment_scheme::kzg10::PublicParameters,
    constraint_system::{StandardComposer, Variable},
    fft::EvaluationDomain,
};
use jubjub_plonk::jubjub::*;
use jubjub_plonk::pedersen::*;
use merlin::Transcript;
use rand;
use std::time::Instant;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

fn merkel_path_gadget(
    composer: &mut StandardComposer,
    leaf: &[(ValuedVar, ValuedVar)],
    point_vars: &[(ValuedVar, ValuedVar)],
    pedersen_bases: &[CurvePoint],
) -> (ValuedVar, ValuedVar) {
    let leafhash = pedersen_hash_gadget(composer, leaf, pedersen_bases);
    let mut hash = leafhash;
    for i in 0..point_vars.len() {
        let input = [hash, point_vars[i]];
        hash = pedersen_hash_gadget(composer, &input, pedersen_bases);
    }
    return hash;
}

fn main() {
    const CAPACITY: usize = 1 << 16;
    const USED_CAPACITY: usize = 1 << 16;
    // Setup OG params.
    let public_parameters = PublicParameters::setup(CAPACITY * 8, &mut rand::thread_rng()).unwrap();
    let (ck, vk) = public_parameters.trim(USED_CAPACITY * 8).unwrap();
    let domain = EvaluationDomain::new(USED_CAPACITY * 8).unwrap();

    let mut composer = StandardComposer::new();

    let bases = pedersen_bases(40000);
    let points = random_point_vars(&mut composer, 40);
    let leaf = random_point_vars(&mut composer, 2);

    let hash = merkel_path_gadget(&mut composer, &leaf, &points, &bases);
    composer.add_dummy_constraints();
    composer.check_circuit_satisfied();

    let mut transcript = Transcript::new(b"testing");
    // Preprocess circuit
    let circuit = composer.preprocess(&ck, &mut transcript, &domain);

    // Prove
    println!("Starting the construction of proof");
    let now = Instant::now();
    let proof = composer.prove(&ck, &circuit, &mut transcript.clone());
    let elapsed = now.elapsed();
    // Verify
    let result = proof.verify(
        &circuit,
        &mut transcript.clone(),
        &vk,
        &composer.public_inputs(),
    );
    assert!(result);
    println!(
        "Verification result: {}, proof time: {} milliseconds",
        result,
        elapsed.as_millis()
    );
}
