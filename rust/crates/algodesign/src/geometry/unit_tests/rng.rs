use super::*;

#[test]
fn the_stream_is_fixed_by_the_seed() {
    // SplitMix64's first output for seed 0 (Vigna's reference implementation).
    assert_eq!(SplitMix64::new(0).next_u64(), 0xE220_A839_7B1D_CDAF);
    let (mut a, mut b) = (SplitMix64::new(7), SplitMix64::new(7));
    assert!((0..100).all(|_| a.next_u64() == b.next_u64()));
}

#[test]
fn normals_have_mean_zero_and_variance_one() {
    let mut r = SplitMix64::new(42);
    let xs: Vec<f64> = (0..100_000).map(|_| r.standard_normal()).collect();
    let mean = xs.iter().sum::<f64>() / xs.len() as f64;
    let var = xs.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / xs.len() as f64;
    // Standard error of the mean is 1/sqrt(1e5) ≈ 0.003; 0.02 is over six of them.
    assert!(
        (mean.abs() < 0.02) && ((var - 1.0).abs() < 0.02),
        "mean {mean}, var {var}"
    );
}

#[cfg(feature = "unchecked")]
#[test]
fn draws_are_three_fresh_streams() {
    let (u, f, g) = draws(0, 3);
    assert_eq!(u[0], 0xE220_A839_7B1D_CDAF);
    let (mut b, mut c) = (SplitMix64::new(0), SplitMix64::new(0));
    assert_eq!(f, (0..3).map(|_| b.next_f64()).collect::<Vec<_>>());
    assert_eq!(g, (0..3).map(|_| c.standard_normal()).collect::<Vec<_>>());
    assert_eq!(u.len(), 3);
}
