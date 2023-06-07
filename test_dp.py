from dp import has_periodic

def test_has_periodic():
    assert has_periodic([(1, 1)])
    assert has_periodic([(1, 2), (1, 1)])
    assert has_periodic([(1, 2), (2, 1)])
    assert has_periodic([(0, 1), (1, 2), (2, 3), (2, 4), (4, 5), (4, 6), (6, 7), (7, 0)])
    assert not has_periodic([(1, 2)])
    assert not has_periodic([(1, 2), (2, 3), (3, 4), (4, 5), (4, 6), (1, 7), (7, 8), (8, 9)])
    