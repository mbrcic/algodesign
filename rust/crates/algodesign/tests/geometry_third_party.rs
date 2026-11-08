//! Differentials for `algodesign::geometry` against independent crates. Each test says what it
//! checks and what it does not. None of these crates is a dependency of the library.
use proptest::prelude::*;

/// A double `m · 2^e` with `|m| < 2^20` and `|e| ≤ 60`.
fn coord() -> impl Strategy<Value = f64> {
    (-(1i64 << 20)..(1i64 << 20), -60i32..60).prop_map(|(m, e)| m as f64 * 2f64.powi(e))
}

proptest! {
    /// `robust` is another port of Shewchuk's predicates: the same algorithm in independent code,
    /// so this checks our transcription, not the method (the exact-rational oracle in the unit
    /// tests checks the method). Its `orient2d` is positive for counterclockwise, as ours is.
    /// Coordinates are `m · 2^e` with `|m| < 2^20`, `|e| ≤ 60`, so no product overflows or
    /// underflows (Shewchuk's error bounds assume neither), and every fourth point is pulled onto
    /// the line through the other two, the case where the adaptive stages run.
    #[test]
    fn orient2d_sign_agrees_with_robust(p in [[coord(), coord()], [coord(), coord()], [coord(), coord()]], t in -4i32..4, collinear in any::<bool>()) {
        let mut p = p;
        if collinear {
            let t = f64::from(t);
            p[2] = [p[0][0] + t * (p[1][0] - p[0][0]), p[0][1] + t * (p[1][1] - p[0][1])];
        }
        let ours = algodesign::geometry::orientation::orient2d(p[0], p[1], p[2]);
        let c = |q: [f64; 2]| robust::Coord { x: q[0], y: q[1] };
        let theirs = robust::orient2d(c(p[0]), c(p[1]), c(p[2]));
        prop_assert_eq!(ours.partial_cmp(&0.0), theirs.partial_cmp(&0.0));
    }
}

proptest! {
    /// `kiddo` is an independent k-d tree. Exact NN: the **distances** must agree. Indices may
    /// differ on ties, because kiddo's tie rule is not ours; ours is checked against the scan in
    /// the unit tests.
    #[test]
    fn kdtree_nearest_distance_agrees_with_kiddo(
        rows in prop::collection::vec([-1e3f64..1e3, -1e3f64..1e3], 1..300),
        q in [-1e3f64..1e3, -1e3f64..1e3],
    ) {
        let p = algodesign::geometry::point::Points::from_rows(2, &rows).unwrap();
        let ours = algodesign::geometry::kdtree::KdTree::new(p).k_nearest(&q, 1)[0].sq_dist;
        let theirs: kiddo::ImmutableKdTree<f64, 2> = kiddo::ImmutableKdTree::new_from_slice(&rows).unwrap();
        let nn = theirs.query(&q).nearest_one::<kiddo::SquaredEuclidean<f64>>().execute();
        prop_assert_eq!(ours, nn.distance);
    }

    /// `rstar` (an R-tree) as the second opinion for the box query: the **sets** must be equal.
    #[test]
    fn kdtree_range_agrees_with_rstar(
        rows in prop::collection::vec([-50i32..50, -50i32..50], 0..300),
        a in [-60i32..60, -60i32..60], b in [-60i32..60, -60i32..60],
    ) {
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = algodesign::geometry::point::Points::from_rows(2, &rows).unwrap();
        let lo = [f64::from(a[0].min(b[0])), f64::from(a[1].min(b[1]))];
        let hi = [f64::from(a[0].max(b[0])), f64::from(a[1].max(b[1]))];
        let mut ours = algodesign::geometry::kdtree::KdTree::new(p).range(&lo, &hi);
        ours.sort_unstable();
        let tree = rstar::RTree::bulk_load(
            rows.iter().copied().enumerate().map(|(i, r)| rstar::primitives::GeomWithData::new(r, i)).collect(),
        );
        let mut theirs: Vec<usize> = tree.locate_in_envelope(rstar::AABB::from_corners(lo, hi)).map(|g| g.data).collect();
        theirs.sort_unstable();
        prop_assert_eq!(ours, theirs);
    }
}

/// `instant-distance` needs a point type.
#[derive(Clone)]
struct V(Vec<f32>);

impl instant_distance::Point for V {
    fn distance(&self, other: &Self) -> f32 {
        self.0
            .iter()
            .zip(&other.0)
            .map(|(a, b)| (a - b) * (a - b))
            .sum()
    }
}

/// Recall@10 of our HNSW against two independent ones, on 2 000 random unit vectors in d = 16
/// with 100 queries, at `ef_construction = 200` and `ef = 100`, against our scan.
///
/// **What it checks:** ours is within 0.03 of the better of the two. **What it does not:** equal
/// graphs or equal results, because the randomness differs; matched parameters only where the
/// crates allow it: `hnsw_rs` takes `M = 16` but draws its levels from OS randomness, so its
/// recall moves a little between runs; `instant-distance` fixes `M = 32` as a constant.
#[test]
fn hnsw_recall_matches_hnsw_rs_and_instant_distance() {
    use algodesign::geometry::{
        hnsw::{Hnsw, HnswParams},
        point::Points,
        scan,
    };
    let unit = |n: usize, seed: u64| -> Points {
        // SplitMix64-free on purpose: this file sees only the public API. A fixed LCG is enough.
        let mut s = seed;
        let mut next = || {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((s >> 11) as f64 / (1u64 << 53) as f64) * 2.0 - 1.0
        };
        Points::new(16, (0..n * 16).map(|_| next()).collect())
            .unwrap()
            .normalized()
            .unwrap()
    };
    let (p, qs) = (unit(2000, 1), unit(100, 2));
    let truth: Vec<Vec<usize>> = qs
        .iter()
        .map(|q| scan::k_nearest(&p, q, 10).iter().map(|n| n.id).collect())
        .collect();
    let recall = |found: &dyn Fn(&[f64]) -> Vec<usize>| -> f64 {
        let hit: usize = qs
            .iter()
            .zip(&truth)
            .map(|(q, t)| found(q).iter().filter(|i| t.contains(i)).count())
            .sum();
        hit as f64 / 1000.0
    };

    let ours = Hnsw::build(p.clone(), HnswParams::new(16));
    let r_ours = recall(&|q| ours.search(q, 10, 100).iter().map(|n| n.id).collect());

    let f32s: Vec<Vec<f32>> = p
        .iter()
        .map(|v| v.iter().map(|&x| x as f32).collect())
        .collect();
    let theirs = hnsw_rs::hnsw::Hnsw::<f32, hnsw_rs::prelude::DistL2>::new(
        16,
        2000,
        16,
        200,
        hnsw_rs::prelude::DistL2 {},
    );
    for (i, v) in f32s.iter().enumerate() {
        theirs.insert((v.as_slice(), i));
    }
    let r_hnsw_rs = recall(&|q| {
        let q: Vec<f32> = q.iter().map(|&x| x as f32).collect();
        theirs.search(&q, 10, 100).iter().map(|n| n.d_id).collect()
    });

    let map = instant_distance::Builder::default()
        .ef_construction(200)
        .ef_search(100)
        .seed(3)
        .build(
            f32s.iter().cloned().map(V).collect(),
            (0..2000usize).collect(),
        );
    let r_instant = recall(&|q| {
        let q = V(q.iter().map(|&x| x as f32).collect());
        let mut search = instant_distance::Search::default();
        map.search(&q, &mut search)
            .take(10)
            .map(|item| *item.value)
            .collect()
    });

    eprintln!("recall@10: ours {r_ours}, hnsw_rs {r_hnsw_rs}, instant-distance {r_instant}");
    let best = r_hnsw_rs.max(r_instant);
    assert!(
        r_ours + 0.03 >= best,
        "ours {r_ours}, hnsw_rs {r_hnsw_rs}, instant-distance {r_instant}"
    );
}
