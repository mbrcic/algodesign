use super::*;

#[test]
fn the_path_follows_the_previous_vertices_back_to_the_start() {
    let d = Distances {
        cost: vec![Some(3), Some(0), Some(5), None],
        previous: vec![Some(1), None, Some(0), None],
    };
    assert_eq!(d.path_to(2), Some(vec![1, 0, 2]));
    assert_eq!(d.path_to(1), Some(vec![1]));
    assert_eq!(d.path_to(3), None);
}

#[test]
fn records_that_go_round_in_a_circle_give_no_path() {
    let d = Distances {
        cost: vec![Some(1), Some(1)],
        previous: vec![Some(1), Some(0)],
    };
    assert_eq!(d.path_to(0), None);
}

#[test]
#[should_panic(expected = "vertex 2 out of range 0..2")]
fn a_vertex_out_of_range_is_a_broken_contract() {
    let d = Distances {
        cost: vec![Some(0), None],
        previous: vec![None, None],
    };
    let _ = d.path_to(2);
}
