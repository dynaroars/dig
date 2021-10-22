

e1 = [('vtrace0', 4, 3),
      ('vtrace1', 3, 3),
      ('vtrace2', 2, 3),
      ('vtrace2', 1, 0),
      ('vtrace4', 0, 4),
      ('vtrace5', 0, 1),
      ('vtrace6', 0, -1)]

e2 = [('vtrace0', 2, 1),
      ('vtrace1', 3, 1),
      ('vtrace3', 2, 1),
      ('vtrace3', 1, 0),
      ('vtrace9', 1, 1)]


def infer(traces):
    data = {}
    for i, execution in enumerate(traces):
        for j, state in enumerate(execution):
            for k, value in enumerate(state):
                if k not in data:
                    data[k] = {}

                if i not in data[k]:
                    data[k][i] = []
                data[k][i].append(value)

    for v in data:
        traces = list(data[v].values())
        minv, maxv = intersect(map(set, traces))
        print(v, minv, maxv)


def intersect(traces):
    iset = set.intersection(*traces)
    return min(iset), max(iset)


def find_occur_first(pos, v, traces):
    before = set()
    for trace in traces:
        for i, val in enumerate(trace):
            if i != pos:
                continue
            if val == v:
                break
            before.add(v)

    for trace in traces:
        for i, val in enuerate(trace):
            if i != pos:
                continue


infer([e1, e2])
