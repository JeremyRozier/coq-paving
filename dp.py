def has_periodic(tau):
    """Function which determines if from
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


                
                