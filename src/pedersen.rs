use crate::jubjub::*;
use dusk_bls12_381::Scalar;
use dusk_plonk::constraint_system::{StandardComposer, Variable};
use rand;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

lazy_static! {
    static ref SCALAR_POWERS_OF_TWO: [Scalar; 256] = {
        let mut scalar_powers = [Scalar::one(); 256];
        let mut sp = Scalar::one();
        for i in 0..256 {
            scalar_powers[i] = sp;
            sp = sp + sp;
        }
        scalar_powers
    };
}
pub fn choose_curve_point_based_on_boolean(
    composer: &mut StandardComposer,
    b: ValuedVar,
    x0: Scalar,
    y0: Scalar,
    x1: Scalar,
    y1: Scalar,
) -> (ValuedVar, ValuedVar) {
    let bnot = composer.add_input(Scalar::one() - b.1);
    let xout = composer.add((x0, bnot), (x1, b.0), Scalar::zero(), Scalar::zero());
    let yout = composer.add((y0, bnot), (y1, b.0), Scalar::zero(), Scalar::zero());
    let xd = if b.1 == Scalar::zero() { x0 } else { x1 };
    let yd = if b.1 == Scalar::zero() { y0 } else { y1 };

    ((xout, xd), (yout, yd))
}

pub fn construct_scalar_from_bits_gadget(
    composer: &mut StandardComposer,
    bits: &[ValuedVar],
    base_power: usize,
) -> ValuedVar {
    if bits.len() == 1 {
        return bits[0];
    } else if bits.len() == 2 {
        let sum = composer.add(
            (SCALAR_POWERS_OF_TWO[base_power] * bits[0].1, bits[0].0),
            (SCALAR_POWERS_OF_TWO[base_power + 1] * bits[1].1, bits[1].0),
            Scalar::zero(),
            Scalar::zero(),
        );
        return (
            sum,
            SCALAR_POWERS_OF_TWO[base_power] * bits[0].1
                + SCALAR_POWERS_OF_TWO[base_power + 1] * bits[1].1,
        );
    } else if bits.len() == 3 {
        let sum = composer.big_add(
            (SCALAR_POWERS_OF_TWO[base_power] * bits[0].1, bits[0].0),
            (SCALAR_POWERS_OF_TWO[base_power + 1] * bits[1].1, bits[1].0),
            (SCALAR_POWERS_OF_TWO[base_power + 2] * bits[2].1, bits[2].0),
            Scalar::zero(),
            Scalar::zero(),
        );
        return (
            sum,
            SCALAR_POWERS_OF_TWO[base_power] * bits[0].1
                + SCALAR_POWERS_OF_TWO[base_power + 1] * bits[1].1
                + SCALAR_POWERS_OF_TWO[base_power + 2] * bits[2].1,
        );
    } else {
        let chunk_size = bits.len() / 3 + if bits.len() % 3 == 0 { 0 } else { 1 };
        let mut sums = Vec::new();
        for i in 0..3 {
            let bp = i * chunk_size;
            let num_bits = if bits.len() - i * chunk_size >= chunk_size {
                chunk_size
            } else {
                bits.len() - chunk_size * i
            };
            println!("bits.len()={:?}", bits.len());
            if num_bits > 0 {
                let sum = construct_scalar_from_bits_gadget(
                    composer,
                    &bits[bp..bp + num_bits],
                    bp + base_power,
                );
                sums.push(sum);
            }
        }

        if sums.len() == 3 {
            let sum_var = composer.big_add(
                (Scalar::one(), sums[0].0),
                (Scalar::one(), sums[1].0),
                (Scalar::one(), sums[2].0),
                Scalar::zero(),
                Scalar::zero(),
            );
            let sum_val = sums[0].1 + sums[1].1 + sums[2].1;
            return (sum_var, sum_val);
        } else if sums.len() == 2 {
            let sum_var = composer.add(
                (Scalar::one(), sums[0].0),
                (Scalar::one(), sums[1].0),
                Scalar::zero(),
                Scalar::zero(),
            );
            let sum_val = sums[0].1 + sums[1].1;
            return (sum_var, sum_val);
        } else {
            return sums[0];
        }
    }
}
pub fn compute_scalar_from_bits(bits: &[ValuedVar]) -> Scalar {
    let mut s = Scalar::zero();
    for i in 0..bits.len() {
        s = s + SCALAR_POWERS_OF_TWO[i] * bits[i].1;
    }
    s
}
pub fn split_scalar_into_bits_gadget(
    composer: &mut StandardComposer,
    s: ValuedVar,
) -> [ValuedVar; 256] {
    let bytes = s.1.to_bytes();
    let mut bit_wires = [s; 256];
    for i in 0..bytes.len() {
        for j in 0..8 {
            let bit_i = i * 8 + j;
            let byte = bytes[i];
            let bit = byte & (1 << j); //anyway we check against zero, so no need to right shift.
            let sbit = if bit == 0 {
                Scalar::zero()
            } else {
                Scalar::one()
            };
            let w = composer.add_input(sbit);
            bit_wires[bit_i] = (w, sbit);
            composer.bool_gate(w);
        }
    }
    // let sss = compute_scalar_from_bits(&bit_wires);
    // assert_eq!(s.1, sss);
    //Need to add the sum check
    let computed_sum_gadget = construct_scalar_from_bits_gadget(composer, &bit_wires, 0);
    //assert_eq!(s.1, computed_sum_gadget.1);
    let check = composer.add(
        (Scalar::one(), s.0),
        (-Scalar::one(), computed_sum_gadget.0),
        Scalar::zero(),
        Scalar::zero(),
    );
    composer.constrain_to_constant(check, Scalar::zero(), Scalar::zero());
    return bit_wires;
}

fn fill_slice_into_vec<E: Copy>(v: &mut Vec<E>, s: &[E]) {
    for i in 0..s.len() {
        v.push(s[i]);
    }
}
///Computes Pedersen hash of a slice of curve points.
pub fn pedersen_hash_gadget(
    composer: &mut StandardComposer,
    s: &[(ValuedVar, ValuedVar)],
    bases: &[CurvePoint],
) -> (ValuedVar, ValuedVar) {
    let mut bits = Vec::new();
    for i in 0..s.len() {
        let sbits0 = split_scalar_into_bits_gadget(composer, s[i].0);
        let point = CurvePoint {
            x: (s[i].0).1,
            y: (s[i].1).1,
        };
        let sbits1 = if point.sign() {
            ((composer.add_input(Scalar::one())), Scalar::one())
        } else {
            ((composer.add_input(Scalar::zero())), Scalar::zero())
        };
        fill_slice_into_vec(&mut bits, &sbits0);
        bits.push(sbits1);
    }
    let zero_point = CurvePoint::zero_point();
    let mut nodes = Vec::with_capacity(bits.len());
    for i in 0..bits.len() {
        let point = choose_curve_point_based_on_boolean(
            composer,
            bits[i],
            zero_point.x,
            zero_point.y,
            bases[i].x,
            bases[i].y,
        );
        nodes.push(point);
    }
    return curve_point_multi_add_gadget(composer, &nodes);
}

pub fn pedersen_bases(n: usize) -> Vec<CurvePoint> {
    let mut bases = Vec::new();
    for i in 0..n {
        bases.push(CurvePoint::random_point());
    }
    bases
}
pub fn random_point_vars(composer: &mut StandardComposer, n: usize) -> Vec<(ValuedVar, ValuedVar)> {
    let mut bases = Vec::new();
    for i in 0..n {
        let point = CurvePoint::random_point();
        let xvar = composer.add_input(point.x);
        let yvar = composer.add_input(point.y);
        bases.push(((xvar, point.x), (yvar, point.y)));
    }

    bases
}

mod test {
    use super::*;
    use dusk_plonk::{commitment_scheme::kzg10::PublicParameters, fft::EvaluationDomain};
    use merlin::Transcript;
    use std::time::Instant;

    #[test]
    fn test_pedersen_hash() {
        const CAPACITY: usize = 1 << 12;
        const USED_CAPACITY: usize = 1 << 11;
        // Setup OG params.
        let public_parameters =
            PublicParameters::setup(CAPACITY * 8, &mut rand::thread_rng()).unwrap();
        let (ck, vk) = public_parameters.trim(USED_CAPACITY * 8).unwrap();
        let domain = EvaluationDomain::new(USED_CAPACITY * 8).unwrap();

        let mut composer = StandardComposer::new();

        let bases = pedersen_bases(1024);
        let points = random_point_vars(&mut composer, 2);

        let hash = pedersen_hash_gadget(&mut composer, &points, &bases);
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

    #[test]
    fn test_scalar_split_gadget() {
        const CAPACITY: usize = 1 << 6;
        const USED_CAPACITY: usize = 1 << 3;
        // Setup OG params.
        let public_parameters =
            PublicParameters::setup(CAPACITY * 8, &mut rand::thread_rng()).unwrap();
        let (ck, vk) = public_parameters.trim(USED_CAPACITY * 8).unwrap();
        let domain = EvaluationDomain::new(USED_CAPACITY * 8).unwrap();

        let mut composer = StandardComposer::new();

        let s = Scalar::random(&mut rand::thread_rng());
        let s_var = composer.add_input(s);
        let bits = split_scalar_into_bits_gadget(&mut composer, (s_var, s));
        composer.add_dummy_constraints();
        composer.check_circuit_satisfied();
    }
}
