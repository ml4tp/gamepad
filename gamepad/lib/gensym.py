class GenSym(object):
    """Symbol generation
    """
    def __init__(self, prefix=None):
        self.cnt = 0
        self.prefix = prefix

    def gensym(self):
        idx = self.cnt
        self.cnt += 1
        if self.prefix:
            return "{}{}".format(self.prefix, idx)
        else:
            return idx
