class MyHist(object):
    def __init__(self, binids):
        self.binids = binids

        self.ids = [i for i, _ in enumerate(binids)]
        self.bin2id = dict([(binid, i) for i, binid in enumerate(binids)])
        self.id2bin = dict([(i, binid) for i, binid in enumerate(binids)])

    def empty(self):
        return [0 for _ in self.binids]

    def delta(self, key):
        hist = self.empty()
        return self.insert(hist, key, 1)

    def insert(self, hist, key, value):
        hist[self.bin2id[key]] = value
        return hist

    def merge(self, hist1, hist2):
        return [i + j for i, j in zip(hist1, hist2)]

    def merges(self, hists):
        acc = self.empty()
        for i in self.ids:
            for hist in hists:
                acc[i] += hist[i]
        return acc

    def view(self, hist, f_sort=True):
        ls = [(binid, cnt) for binid, cnt in zip(self.binids, hist)]
        if f_sort:
            return sorted(ls, key=lambda k: (k[1], k[0]), reverse=True)
        else:
            return ls