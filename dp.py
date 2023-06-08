def iterative_has_periodic(tau):
    """Iterative function which determines if from
    a gather of tiles we can produce a periodic
    sequence of tiles ie tau solves DP."""

    for tile in tau:
        way = [tile]
        tau_copy = tau[:]
        while len(way) <= len(tau) and len(way) != 0:
            associated_tiles = [tile for tile in tau_copy if way[-1][1] == tile[0]]

            if len(associated_tiles) == 0:
                tau_copy.remove(way[-1])
                way.pop(-1)
                continue

            for tile2 in associated_tiles:
                way.append(tile2)
                if way[-1][1] == tile[0]:
                    return True
                associated_tiles = [tile for tile in tau_copy if way[-1][1] == tile[0]]
    return False


def recursive_has_periodic(tau, way=None, visited=None):
    """Recursive function which determines if from
    a gather of tiles we can produce a periodic
    sequence of tiles ie tau solves DP."""

    if way is None and visited is None:
        way = [tau[0]]
        visited = []

    if len(way) > len(tau):
        return False

    list_bool = []
    if len(visited) < len(tau):
        unvisited_tiles = [tile for tile in tau if tile not in visited]
        for unvisited_tile in unvisited_tiles:
            visited.append(way[-1])
            list_bool.append(recursive_has_periodic(tau, [unvisited_tile], visited))

    associated_tiles = [tile for tile in tau if way[-1][1] == tile[0]]
    for tile in associated_tiles:
        if tile in way:
            return True
        list_bool.append(recursive_has_periodic(tau, way + [tile], visited))

    return any(list_bool)
