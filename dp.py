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


def recursive_has_periodic2(tau, way=None, unvisited=None):
    """Recursive function (more adapted to coq) which determines if from
    a gather of tiles we can produce a periodic
    sequence of tiles ie tau solves DP."""

    def get_associated_tiles(tau, tile, list_associated_tiles=None):

        if list_associated_tiles is None:
            list_associated_tiles = []

        if len(tau) == 0:
            return list_associated_tiles

        if tile[1] == tau[-1][0]:
            to_add = [tau[-1]]
        else:
            to_add = []

        return get_associated_tiles(tau[:-1], tile, list_associated_tiles + to_add)

    def run_associated_tiles(list_associated_tiles, list_bool=None):

        if list_bool is None:
            list_bool = []

        if len(list_associated_tiles) == 0:
            if len(unvisited) == 0:
                list_bool.append(False)
                return list_bool
            tile = unvisited.pop(-1)
            list_bool.append(recursive_has_periodic2(tau, [tile], unvisited))
            list_bool.append(False)
            return list_bool

        if list_associated_tiles[-1] in way:
            list_bool.append(True)
            return list_bool

        list_bool.append(
            recursive_has_periodic2(tau, way + [list_associated_tiles[-1]], unvisited)
        )

        list_bool.extend(run_associated_tiles(list_associated_tiles[:-1]))

        return list_bool

    if unvisited is None and way is None:
        unvisited = tau[:]
        way = [unvisited.pop(-1)]

    if len(way) > len(tau):
        return False

    list_bool = []
    tile = way[-1]
    list_associated_tiles = get_associated_tiles(tau, tile)
    list_bool.extend(run_associated_tiles(list_associated_tiles))
    return any(list_bool)
