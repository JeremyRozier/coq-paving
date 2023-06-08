from dp import iterative_has_periodic, recursive_has_periodic

def test_iterative_has_periodic():
    assert iterative_has_periodic([(1, 1)])
    assert iterative_has_periodic([(1, 2), (1, 1)])
    assert iterative_has_periodic([(1, 2), (2, 1)])
    assert iterative_has_periodic([(0, 1), (1, 2), (2, 3), (2, 4), (4, 5), (4, 6), (6, 7), (7, 0)])
    assert not iterative_has_periodic([(1, 2)])
    assert not iterative_has_periodic([(1, 2), (2, 3), (3, 4), (4, 5), (4, 6), (1, 7), (7, 8), (8, 9)])

def test_recursive_has_periodic():
    assert recursive_has_periodic([(1, 1)])
    assert recursive_has_periodic([(1, 2), (1, 1)])
    assert recursive_has_periodic([(1, 2), (2, 1)])
    assert recursive_has_periodic([(0, 1), (1, 2), (2, 3), (2, 4), (4, 5), (4, 6), (6, 7), (7, 0)])
    assert not recursive_has_periodic([(1, 2)])
    assert not recursive_has_periodic([(1, 2), (2, 3), (3, 4), (4, 5), (4, 6), (1, 7), (7, 8), (8, 9)])
