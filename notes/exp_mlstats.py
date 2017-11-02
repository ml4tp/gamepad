def _nbf(x):
    return x[0]


def _nbod(x):
    return x[1]


def _naf(x):
    return x[2]


def _cnt(x):
    return x[3]


def myfilter(pred, ls):
    sat_ls = []
    unsat_ls = []
    for x in ls:
        if pred(x):
            sat_ls += [x]
        else:
            unsat_ls += [x]
    return sat_ls, unsat_ls


def stats_unique_mltac(d_mlstats):
    # Compute unique
    acc = []
    for name, info in d_mlstats.items():
        if len(info) == 1:
            x = info[0]
            acc += [(name, _nbf(x), _naf(x))]
    print("--------------------------------")
    print("UNIQUE ({}/{})".format(len(acc), len(d_mlstats.items())))
    eq_ls, neq_ls = myfilter(lambda x: x[0] == x[1], acc)
    eq_ls = sorted(eq_ls, key=lambda k: (k[0], k[2]))
    neq_ls = sorted(neq_ls, key=lambda k: (k[0], k[2]))
    for name, nbf, naf in eq_ls:
        print("naf = nbf,  ({} = {}),  {}".format(nbf, naf, name))
    for name, nbf, naf in neq_ls:
        print("naf != nbf, ({} != {}), {}".format(nbf, naf, name))
    print("\n")
    return [x[0] for x in acc], acc


def stats_allbf1_mltac(d_mlstats):
    # Compute all before = 1
    acc = []
    for name, info in d_mlstats.items():
        if all(nbf == 1 for (nbf, nbody, naf, cnt) in info):
            y = [(_naf(x), _nbod(x), _cnt(x)) for x in info]
            acc += [(name, y)]
    print("--------------------------------")
    print("ALL before = 1 ({}/{})".format(len(acc), len(d_mlstats.items())))
    acc = sorted(acc, key=lambda k: (k[0], len(k[1])))
    for name, x in acc:
        print("{}, {}".format(name, x))
    comp = set([x[0] for x in d_mlstats.items()]).difference(set([x[0] for x in acc]))
    print("Complement", comp)
    print("\n")
    return [x[0] for x in acc], acc


def stats_allaf1_mltac(d_mlstats):
    # Compute all after = 1
    acc = []
    for name, info in d_mlstats.items():
        if all(naf == 1 for (nbf, nbody, naf, cnt) in info):
            y = [(_nbf(x), _nbod(x), _cnt(x)) for x in info]
            acc += [(name, y)]
    print("--------------------------------")
    print("ALL after = 1 ({}/{})".format(len(acc), len(d_mlstats.items())))
    acc = sorted(acc, key=lambda k: (k[0], len(k[1])))
    for name, x in acc:
        print("{}, {}".format(name, x))
    print("\n")
    return [x[0] for x in acc], acc


def stats_body0_mltac(d_mlstats):
    # Compute all body = 0
    acc = []
    for name, info in d_mlstats.items():
        if all(nbody == 0 for (nbf, nbody, naf, cnt) in info):
            y = [(_naf(x), _nbf(x), _cnt(x)) for x in info]
            acc += [(name, y)]
    print("--------------------------------")
    print("ALL body = 0 ({}/{})".format(len(acc), len(d_mlstats.items())))
    acc = sorted(acc, key=lambda k: (k[0], len(k[1])))
    for name, x in acc:
        print("{}, {}".format(name, x))
    print("\n")
    return [x[0] for x in acc], acc


if __name__ == "__main__":
    mlcnt = []
    mlstats = []
    d_mlstats = {}
    with open("mltac.stats.raw", 'r') as f:
        f_stats = False
        for line in f:
            line = line.strip()
            if line == "MLCNT":
                pass
            elif line == "MLSTATS":
                f_stats = True
            elif f_stats:
                toks = line.split(",")
                name = toks[0].strip()
                nbf = int(toks[1].strip())
                nbody = int(toks[2].strip())
                naf = int(toks[3].strip())
                cnt = int(toks[4].strip())
                mlstats += [(name, nbf, nbody, naf, cnt)]
                if name in d_mlstats:
                    d_mlstats[name] += [(nbf, nbody, naf, cnt)]
                else:
                    d_mlstats[name] = [(nbf, nbody, naf, cnt)]
            else:
                toks = line.split(",")
                name = toks[0].strip()
                cnt = int(toks[1].strip())
                mlcnt += [(name, cnt)]

    mlcnt = sorted(mlcnt, key=lambda k: (k[1], k[0]), reverse=True)
    mltacs = [v[0] for v in mlcnt]
    NUM_MLTACS = len(mltacs)
    mlstats = sorted(mlstats, key=lambda k: (k[0], k[1], k[3], k[2], k[4]), reverse=True)

    print("--------------------------------")
    print("MLCNT")
    for (name, cnt) in mlcnt:
        print("{}, {}".format(name, cnt))
    print("\n")

    print("--------------------------------")
    print("MLSTATS")
    for (name, nbf, nbody, naf, cnt) in mlstats:
        print("{}, {}, {}, {}, {}".format(name, nbf, nbody, naf, cnt))
    print("\n")

    ids1, stats1 = stats_unique_mltac(d_mlstats)
    
    ids2, stats2 = stats_allbf1_mltac(d_mlstats)
    
    ids3, stats3 = stats_allaf1_mltac(d_mlstats)

    ids4, stats4 = stats_body0_mltac(d_mlstats)
    
    print("--------------------------------")
    print("Unique intersect allbf=1\n", set(ids1).intersection(set(ids2)))
    print("\n")

    print("--------------------------------")
    print("Unique intersect allaf=1\n", set(ids1).intersection(set(ids3)))
    print("\n")

    print("--------------------------------")
    print("Body=0 intersect allbf=1\n", set(ids2).intersection(set(ids4)))
    print("Complement\n", set(ids2).difference(set(ids4)))
    print("\n")

    print("--------------------------------")
    print("Body=0 intersect allaf=1\n", set(ids3).intersection(set(ids4)))
    print("\n")
