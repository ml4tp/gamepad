from coq.constr import Name
from lib.myutil import NotFound


class MyEnv(object):
    def __init__(self, env, order):
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
            return self.order[-1-idx]
        else:
            raise NotFound("Lookup failure of {} in env [{}]".format(
                           idx, self.dump()))

    def dump(self):
        # TODO(deh): something wrong with dumping code when printing v
        xs = (["{}".format(k) for k, v in self.env.items()])
        return ", ".join(xs)


class FastEnv(object):
    def __init__(self, ctx_env, local_env, ctx_order, local_order):
        self.ctx_env = ctx_env
        self.local_env = local_env
        self.ctx_order = ctx_order
        self.local_order = local_order

    def ctx_extend(self, ident, value):
        assert isinstance(ident, Name)
        self.ctx_env[ident] = value
        self.ctx_order.append(value)
        return FastEnv(self.ctx_env, self.local_env, self.ctx_order, self.local_order)

    def local_extend(self, ident, value):
        assert isinstance(ident, Name)
        local_env_p = {}
        for k, v in self.local_env.items():
            local_env_p[k] = v
        local_env_p[ident] = value
        return FastEnv(self.ctx_env, local_env_p, self.ctx_order, self.local_order + [value])

    def lookup_id(self, ident):
        if ident in self.local_env:
            return self.local_env[ident]
        elif ident in self.ctx_env:
            return self.ctx_env[ident]
        else:
            raise NotFound("Lookup failure of {} in env [{}]".format(
                           ident, self.dump()))

    def lookup_rel(self, idx):
        if idx < len(self.local_order):
            return self.local_order[-1-idx]
        else:
            raise NotFound("Lookup failure of {} in env [{}]".format(
                           idx, self.dump()))

    def dump(self):
        # TODO(deh): something wrong with dumping code when printing v
        xs = ["ctx:"] + ["{}".format(k) for k, v in self.ctx_env.items()] + ["\nlocal:"] + ["{}".format(k) for k, v in self.local_env.items()]

        return ", ".join(xs)