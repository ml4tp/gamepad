class MyIter(object):
    """
    Iterator wrapper.
    """
    def __init__(self, data):
        self.data = data
        self.idx = 0

    def __iter__(self):
        return self

    def __next__(self):
        if self.idx < len(self.data):
            elem = self.data[self.idx]
            self.idx += 1
            return elem
        else:
            raise StopIteration

    def has_next(self):
        return self.idx < len(self.data)

    def peek(self):
        return self.data[self.idx]

    def lookahead(self, n):
        return self.data[self.idx + n]
