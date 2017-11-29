from coq.ast import Name


class NotFound(Exception):
    def __init__(self, msg):
        self.msg = msg


class MyEnv(object):
    def __init__(self, env={}, order=[]):
        self.env = env
        self.order = order

    def extend(self, ident, value):
        assert isinstance(ident, Name)
        env_p = {}
        for k, v in self.env.items():
            env_p[k] = v
        env_p[ident] = value
        return MyEnv(env_p, self.order + [value])

    def lookup_id(self, ident):
        if ident in self.env:
            return self.env[ident]
        else:
            raise NotFound("Lookup failure of {} in env [{}]".format(
                           ident, self.dump()))

    def lookup_rel(self, idx):
        if idx < len(self.order):
            return self.order[idx]
        else:
            raise NotFound("Lookup failure of {} in env [{}]".format(
                           idx, self.dump()))

    def dump(self):
        # TODO(deh): something wrong with dumping code when printing v
        xs = (["{}".format(k) for k, v in self.env.items()])
        return ", ".join(xs)
