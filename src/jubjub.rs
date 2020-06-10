use dusk_bls12_381::Scalar;
use dusk_plonk::constraint_system::{StandardComposer, Variable};
use rand;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Debug)]
pub struct CurvePoint {
    pub x: Scalar,
    pub y: Scalar,
}

impl CurvePoint {
    //The curve has an order q such that (q-1)/2
    //is even. So either both the square roots are odd,
    //or both are even. So the choise between the two y values
    //would be made based on whether y or (q-y) is bigger.
    pub fn from_x(x: Scalar, y_choose: bool) -> CtOption<Self> {
        let x_squared = x * x;
        let y_squared =
            (Scalar::one() + x_squared) * ((Scalar::one() - *d * x_squared).invert().unwrap());
        let y_opt = y_squared.sqrt();
        y_opt.map(|y| {
            if (!y_choose && y < -y) || (y_choose && y > -y) {
                CurvePoint { x, y }
            } else {
                CurvePoint { x, y: -y }
            }
        })
    }

    pub fn random_point() -> CurvePoint {
        loop {
            let x = Scalar::random(&mut rand::thread_rng());
            let y_choose: bool = rand::random();
            let opt_point = CurvePoint::from_x(x, y_choose);
            if opt_point.is_some().unwrap_u8() != 0 {
                return opt_point.unwrap();
            }
        }
    }
}

impl From<&str> for CurvePoint {
    fn from(_: &str) -> Self {
        todo!()
    }
}

lazy_static! {
    static ref d: Scalar = {
        let num = Scalar::from(10240u64);
        let dnum = Scalar::from(10241u64);
        (-num) * dnum.invert().unwrap()
    };
}
type ValuedVar = (Variable, Scalar);
pub fn curve_point_addition_gadget(
    composer: &mut StandardComposer,
    x1: ValuedVar,
    y1: ValuedVar,
    x2: ValuedVar,
    y2: ValuedVar,
) -> (ValuedVar, ValuedVar) {
    let beta = composer.mul(Scalar::one(), x1.0, y2.0, Scalar::zero(), Scalar::zero());
    let gamma = composer.mul(Scalar::one(), y1.0, x2.0, Scalar::zero(), Scalar::zero());
    let delta = composer.mul(Scalar::one(), y1.0, y2.0, Scalar::zero(), Scalar::zero());
    let epsilon = composer.mul(Scalar::one(), x1.0, x2.0, Scalar::zero(), Scalar::zero());
    let tao = composer.mul(
        Scalar::one(),
        delta,
        epsilon,
        Scalar::zero(),
        Scalar::zero(),
    );

    let x1d = x1.1;
    let y1d = y1.1;
    let x2d = x2.1;
    let y2d = y2.1;

    let x3d = (x1d * y2d + y1d * x2d)
        * ((Scalar::one() + (*d) * x1d * x2d * y1d * y2d)
            .invert()
            .unwrap());
    let y3d = (y1d * y2d + x1d * x2d)
        * ((Scalar::one() - (*d) * x1d * x2d * y1d * y2d)
            .invert()
            .unwrap());

    let x3 = composer.add_input(x3d);
    let y3 = composer.add_input(y3d);

    let beta_plus_gamma = composer.add(
        (Scalar::one(), beta),
        (Scalar::one(), gamma),
        Scalar::zero(),
        Scalar::zero(),
    );
    let delta_plus_epsilon = composer.add(
        (Scalar::one(), delta),
        (Scalar::one(), epsilon),
        Scalar::zero(),
        Scalar::zero(),
    );

    composer.poly_gate(
        tao,
        x3,
        beta_plus_gamma,
        *d,
        Scalar::zero(),
        Scalar::one(),
        -Scalar::one(),
        Scalar::zero(),
        Scalar::zero(),
    );
    composer.poly_gate(
        tao,
        y3,
        delta_plus_epsilon,
        -(*d),
        Scalar::zero(),
        Scalar::one(),
        -Scalar::one(),
        Scalar::zero(),
        Scalar::zero(),
    );
    return ((x3, x3d), (y3, y3d));
}

mod test {
    use super::*;
    use dusk_plonk::{commitment_scheme::kzg10::PublicParameters, fft::EvaluationDomain};
    use merlin::Transcript;
    use std::time::Instant;

    #[test]
    fn test_addition_associative() {
        const CAPACITY: usize = 1 << 12;
        // Setup OG params.
        let public_parameters =
            PublicParameters::setup(CAPACITY * 8, &mut rand::thread_rng()).unwrap();
        let (ck, vk) = public_parameters.trim(CAPACITY * 8).unwrap();
        let domain = EvaluationDomain::new(CAPACITY * 8).unwrap();

        let point_a = CurvePoint::random_point();
        let point_b = CurvePoint::random_point();
        let point_c = CurvePoint::random_point();

        println!("a={:?}", point_a);
        println!("b={:?}", point_b);
        println!("c={:?}", point_c);

        let mut composer = StandardComposer::new();
        let a_var_x = composer.add_input(point_a.x);
        let a_var_y = composer.add_input(point_a.y);
        let b_var_x = composer.add_input(point_b.x);
        let b_var_y = composer.add_input(point_b.y);
        let c_var_x = composer.add_input(point_c.x);
        let c_var_y = composer.add_input(point_c.y);

        let a_plus_b = curve_point_addition_gadget(
            &mut composer,
            (a_var_x, point_a.x),
            (a_var_y, point_a.y),
            (b_var_x, point_b.x),
            (b_var_y, point_b.y),
        );
        let b_plus_c = curve_point_addition_gadget(
            &mut composer,
            (b_var_x, point_b.x),
            (b_var_y, point_b.y),
            (c_var_x, point_c.x),
            (c_var_y, point_c.y),
        );
        //
        let a_plus_b__plus_c = curve_point_addition_gadget(
            &mut composer,
            a_plus_b.0,
            a_plus_b.1,
            (c_var_x, point_c.x),
            (c_var_y, point_c.y),
        );
        let a_plus__b_plus_c = curve_point_addition_gadget(
            &mut composer,
            (a_var_x, point_a.x),
            (a_var_y, point_a.y),
            b_plus_c.0,
            b_plus_c.1,
        );
        //
        // //check both x values are same
        composer.add_gate(
            (a_plus_b__plus_c.0).0,
            (a_plus__b_plus_c.0).0,
            composer.zero_var,
            Scalar::one(),
            -Scalar::one(),
            Scalar::zero(),
            Scalar::zero(),
            Scalar::zero(),
        );
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
}
