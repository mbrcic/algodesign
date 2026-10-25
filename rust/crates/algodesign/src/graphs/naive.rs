// SPDX-License-Identifier: Apache-2.0
//! Slow references that are correct by inspection, for the tests to compare the real structures
//! against. Built only for the tests and behind the `unchecked` feature, so they are not part
//! of the library's interface.

/// The group of every item after the unions in `pairs`: each item is labelled with the smallest
/// item it is joined to, found by a depth-first search over the pairs as undirected links.
/// `O(n + pairs)`.
///
/// # Panics
///
/// If a pair names an item `>= n`.
#[must_use]
pub fn groups(n: usize, pairs: &[(usize, usize)]) -> Vec<usize> {
    let mut links = vec![Vec::new(); n];
    for &(x, y) in pairs {
        links[x].push(y);
        links[y].push(x);
    }
    let mut label = vec![usize::MAX; n];
    for start in 0..n {
        if label[start] != usize::MAX {
            continue;
        }
        label[start] = start;
        let mut stack = vec![start];
        while let Some(i) = stack.pop() {
            for &j in &links[i] {
                if label[j] == usize::MAX {
                    label[j] = start;
                    stack.push(j);
                }
            }
        }
    }
    label
}

/// Whether some vertex in `keep` reaches another vertex in `keep` and back by arrows between
/// vertices in `keep`: for each arrow `(a, b)` inside `keep`, a plain search from `b` looks for
/// `a`. A loop is a cycle on its own. `O(arrows · (n + arrows))`.
///
/// # Panics
///
/// If an arrow names a vertex `>= keep.len()`.
#[must_use]
pub fn has_cycle_within(keep: &[bool], arrows: &[(u32, u32)]) -> bool {
    let inside = |&(a, b): &(u32, u32)| keep[a as usize] && keep[b as usize];
    arrows.iter().filter(|e| inside(e)).any(|&(a, b)| {
        let mut seen = vec![false; keep.len()];
        let mut stack = vec![b];
        seen[b as usize] = true;
        while let Some(v) = stack.pop() {
            if v == a {
                return true;
            }
            for &(x, y) in arrows {
                if x == v && inside(&(x, y)) && !seen[y as usize] {
                    seen[y as usize] = true;
                    stack.push(y);
                }
            }
        }
        false
    })
}

/// Whether the arrows on the vertices `0..n` form a cycle anywhere.
///
/// # Panics
///
/// If an arrow names a vertex `>= n`.
#[must_use]
pub fn has_cycle(n: usize, arrows: &[(u32, u32)]) -> bool {
    has_cycle_within(&vec![true; n], arrows)
}

/// Whether `order` is a topological order of the arrows on `0..n`: each vertex exactly once, and
/// every arrow from an earlier vertex to a later one (so no loop).
#[must_use]
pub fn is_topological_order(n: usize, arrows: &[(u32, u32)], order: &[u32]) -> bool {
    let mut position = vec![usize::MAX; n];
    for (i, &v) in order.iter().enumerate() {
        match position.get_mut(v as usize) {
            Some(p) if *p == usize::MAX => *p = i,
            _ => return false,
        }
    }
    order.len() == n
        && arrows
            .iter()
            .all(|&(a, b)| position[a as usize] < position[b as usize])
}

/// Whether `vertices` is exactly the set Kahn's method leaves unplaced on the arrows on `0..n`:
/// nonempty and increasing; every member has an arrow into it from a member (so it waits for
/// ever); no arrow leaves the set (so every vertex outside it waits only on vertices outside); and
/// the vertices outside have no cycle among themselves (so they are all placed).
///
/// # Panics
///
/// If an arrow names a vertex `>= n`.
#[must_use]
pub fn is_stuck(n: usize, arrows: &[(u32, u32)], vertices: &[u32]) -> bool {
    if vertices.is_empty()
        || !vertices.windows(2).all(|p| p[0] < p[1])
        || vertices.iter().any(|&v| v as usize >= n)
    {
        return false;
    }
    let mut member = vec![false; n];
    for &v in vertices {
        member[v as usize] = true;
    }
    let waits_on_member = |v: u32| arrows.iter().any(|&(a, b)| b == v && member[a as usize]);
    let outside: Vec<bool> = member.iter().map(|&m| !m).collect();
    vertices.iter().all(|&v| waits_on_member(v))
        && arrows
            .iter()
            .all(|&(a, b)| !member[a as usize] || member[b as usize])
        && !has_cycle_within(&outside, arrows)
}

/// Whether `vertices` is a cycle w, …, v, w of the arrows on `0..n`: at least two entries, the last
/// equal to the first, the ones before it distinct, and an arrow from each entry to the next.
#[must_use]
pub fn is_cycle(n: usize, arrows: &[(u32, u32)], vertices: &[u32]) -> bool {
    let Some((&last, path)) = vertices.split_last() else {
        return false;
    };
    let mut seen = vec![false; n];
    !path.is_empty()
        && path[0] == last
        && path
            .iter()
            .all(|&v| (v as usize) < n && !std::mem::replace(&mut seen[v as usize], true))
        && vertices.windows(2).all(|p| arrows.contains(&(p[0], p[1])))
}

/// Every vertex reachable from `v` by zero or more arrows, `v` included, by a plain search over
/// the arrow list. `O(n · arrows)`.
fn reach_from(n: usize, arrows: &[(u32, u32)], v: u32) -> Vec<bool> {
    let mut seen = vec![false; n];
    seen[v as usize] = true;
    let mut stack = vec![v];
    while let Some(x) = stack.pop() {
        for &(a, b) in arrows {
            if a == x && !seen[b as usize] {
                seen[b as usize] = true;
                stack.push(b);
            }
        }
    }
    seen
}

/// Each vertex labelled with the smallest vertex it reaches and is reached from (a vertex reaches
/// itself by no arrows): the strong components as a labelling. `O(n² · arrows)`.
///
/// # Panics
///
/// If an arrow names a vertex `>= n`.
#[must_use]
pub fn mutual_groups(n: usize, arrows: &[(u32, u32)]) -> Vec<u32> {
    let reach: Vec<Vec<bool>> = (0..n as u32).map(|v| reach_from(n, arrows, v)).collect();
    (0..n)
        .map(|v| {
            (0..n)
                .find(|&w| reach[v][w] && reach[w][v])
                .expect("a vertex reaches itself") as u32
        })
        .collect()
}

/// Whether the labellings `a` and `b` put the same vertices together, whatever the labels are.
#[must_use]
pub fn same_partition(a: &[u32], b: &[u32]) -> bool {
    use std::collections::HashMap;
    if a.len() != b.len() {
        return false;
    }
    let (mut ab, mut ba) = (HashMap::new(), HashMap::new());
    a.iter()
        .zip(b)
        .all(|(&x, &y)| *ab.entry(x).or_insert(y) == y && *ba.entry(y).or_insert(x) == x)
}

/// The vertices in the order a depth-first walk finishes them: roots from 0 upward, the arrows
/// leaving each vertex taken in (target, id) order, a vertex marked when it is entered. Frames on
/// an explicit stack, each a vertex and how many of its targets it has tried.
///
/// # Panics
///
/// If an arrow names a vertex `>= n`.
#[must_use]
pub fn postorder(n: usize, arrows: &[(u32, u32)]) -> Vec<u32> {
    let mut rows = vec![Vec::new(); n];
    for &(a, b) in arrows {
        rows[a as usize].push(b);
    }
    for row in &mut rows {
        row.sort_unstable();
    }
    let mut entered = vec![false; n];
    let mut finished = Vec::with_capacity(n);
    for root in 0..n {
        if entered[root] {
            continue;
        }
        entered[root] = true;
        let mut frames = vec![(root, 0usize)];
        while let Some(&(v, tried)) = frames.last() {
            match rows[v].get(tried) {
                None => {
                    frames.pop();
                    finished.push(v as u32);
                }
                Some(&w) => {
                    frames.last_mut().expect("a frame").1 += 1;
                    if !entered[w as usize] {
                        entered[w as usize] = true;
                        frames.push((w as usize, 0));
                    }
                }
            }
        }
    }
    finished
}

/// Whether every clause `(a, b)` holds under `values`, literal `2i` being xᵢ and `2i + 1` ¬xᵢ.
///
/// # Panics
///
/// If a literal names a variable past `values`.
#[must_use]
pub fn satisfies(values: &[bool], clauses: &[(u32, u32)]) -> bool {
    let holds = |lit: u32| values[lit as usize / 2] != (lit % 2 == 1);
    clauses.iter().all(|&(a, b)| holds(a) || holds(b))
}

/// The first assignment, counting in binary with x₀ the most significant, that satisfies every
/// clause, or `None`. `O(2^n_vars · clauses)`.
///
/// # Panics
///
/// If a literal names a variable `>= n_vars`, or `n_vars >= 32`.
#[must_use]
pub fn two_sat(n_vars: usize, clauses: &[(u32, u32)]) -> Option<Vec<bool>> {
    (0..1u32 << n_vars)
        .map(|bits| {
            (0..n_vars)
                .map(|i| bits >> (n_vars - 1 - i) & 1 == 1)
                .collect::<Vec<bool>>()
        })
        .find(|values| satisfies(values, clauses))
}

/// Each vertex labelled with the smallest vertex it reaches by links, by a plain search over the
/// link list, leaving out the vertex `skip_vertex` (labelled `u32::MAX`) and the link with id
/// `skip_link`. A loop reaches nothing new. `O(n · links)`.
fn labels(
    n: usize,
    links: &[(u32, u32)],
    skip_vertex: Option<u32>,
    skip_link: Option<usize>,
) -> Vec<u32> {
    let mut label = vec![u32::MAX; n];
    for start in 0..n as u32 {
        if label[start as usize] != u32::MAX || skip_vertex == Some(start) {
            continue;
        }
        label[start as usize] = start;
        let mut stack = vec![start];
        while let Some(v) = stack.pop() {
            for (id, &(a, b)) in links.iter().enumerate() {
                if Some(id) == skip_link {
                    continue;
                }
                for (x, y) in [(a, b), (b, a)] {
                    if x == v && Some(y) != skip_vertex && label[y as usize] == u32::MAX {
                        label[y as usize] = start;
                        stack.push(y);
                    }
                }
            }
        }
    }
    label
}

/// The number of pieces of the links on `0..n`, leaving out `skip_vertex` and the link `skip_link`.
fn pieces_without(
    n: usize,
    links: &[(u32, u32)],
    skip_vertex: Option<u32>,
    skip_link: Option<usize>,
) -> usize {
    let label = labels(n, links, skip_vertex, skip_link);
    (0..n as u32).filter(|&v| label[v as usize] == v).count()
}

/// The number of pieces of the links on `0..n`; a vertex with no link is a piece of its own.
///
/// # Panics
///
/// If a link names a vertex `>= n`.
#[must_use]
pub fn pieces(n: usize, links: &[(u32, u32)]) -> usize {
    pieces_without(n, links, None, None)
}

/// The bridges, by id, increasing: each link whose deletion, by id, leaves more pieces.
/// `O(links² · n)`.
///
/// # Panics
///
/// If a link names a vertex `>= n`.
#[must_use]
pub fn bridges(n: usize, links: &[(u32, u32)]) -> Vec<u32> {
    let before = pieces(n, links);
    (0..links.len())
        .filter(|&e| pieces_without(n, links, None, Some(e)) > before)
        .map(|e| e as u32)
        .collect()
}

/// The cut vertices, increasing: each vertex whose deletion, with its links, leaves more pieces
/// among the other vertices. `O(n² · links)`.
///
/// # Panics
///
/// If a link names a vertex `>= n`.
#[must_use]
pub fn cut_vertices(n: usize, links: &[(u32, u32)]) -> Vec<u32> {
    let before = pieces(n, links);
    (0..n as u32)
        .filter(|&v| pieces_without(n, links, Some(v), None) > before)
        .collect()
}

/// The book's block relation on the links: `together[e][f]` when `e` and `f` are not loops and are
/// the same link or lie on one cycle whose vertices are all different (a doubled link is such a
/// cycle of two). Every cycle is found from its smallest vertex `s` as a path of distinct vertices
/// above `s` closed by a link back to `s` that the path has not used. Exponential: small graphs
/// only.
///
/// # Panics
///
/// If a link names a vertex `>= n`.
#[must_use]
pub fn same_block(n: usize, links: &[(u32, u32)]) -> Vec<Vec<bool>> {
    let m = links.len();
    let mut together = vec![vec![false; m]; m];
    let mut rows: Vec<Vec<(u32, u32)>> = vec![Vec::new(); n];
    for (id, &(a, b)) in links.iter().enumerate() {
        if a != b {
            together[id][id] = true;
            rows[a as usize].push((b, id as u32));
            rows[b as usize].push((a, id as u32));
        }
    }
    for s in 0..n as u32 {
        let mut on_path = vec![false; n];
        on_path[s as usize] = true;
        let mut path: Vec<u32> = Vec::new(); // the links of the path from s
        let mut frames = vec![(s, 0usize)];
        while let Some(&mut (v, ref mut next)) = frames.last_mut() {
            let Some(&(w, e)) = rows[v as usize].get(*next) else {
                frames.pop();
                on_path[v as usize] = false;
                path.pop();
                continue;
            };
            *next += 1;
            if path.contains(&e) {
                continue;
            }
            if w == s && !path.is_empty() {
                for &x in path.iter().chain([&e]) {
                    for &y in path.iter().chain([&e]) {
                        together[x as usize][y as usize] = true;
                    }
                }
            } else if w > s && !on_path[w as usize] {
                on_path[w as usize] = true;
                path.push(e);
                frames.push((w, 0));
            }
        }
    }
    together
}

/// The vertices whose deletion alone separates `u` from `v`, increasing; `None` when `u` and `v`
/// are in different pieces. Neither `u` nor `v` is a separator; `u == v` has none. `O(n² · links)`.
///
/// # Panics
///
/// If a link names a vertex `>= n`, or `u` or `v` is not below `n`.
#[must_use]
pub fn separators(n: usize, links: &[(u32, u32)], u: u32, v: u32) -> Option<Vec<u32>> {
    let label = labels(n, links, None, None);
    if label[u as usize] != label[v as usize] {
        return None;
    }
    Some(
        (0..n as u32)
            .filter(|&w| w != u && w != v)
            .filter(|&w| {
                let label = labels(n, links, Some(w), None);
                label[u as usize] != label[v as usize]
            })
            .collect(),
    )
}
