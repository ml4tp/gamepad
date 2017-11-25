class MyEnv(object):
    def __init__(self, env={}, order=[]):
        self.env = env
        self.order = order

    def extend(self, ident, value):
        env_p = {}
        for k, v in env.items():
            env_p[k] = v
        env_p[key] = value
        return MyEnv(env_p, self.order + [value])

    def lookup_id(self, ident):
        return self.env[ident]

    def lookup_rel(self, idx):
        return self.order[idx]
