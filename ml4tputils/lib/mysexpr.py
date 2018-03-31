import sexpdata


def sexpr_strify(sexpr):
    ty = type(sexpr)
    if ty is sexpdata.Symbol:
        return sexpr._val
    elif ty is float:
        # NOTE(deh): wtf, inF -> inf as a floating point ...
        return str(sexpr)
    elif ty is bool:
        return str(sexpr)
    else:
        raise NameError("Cannot strify {}::{}".format(sexpr, type(sexpr)))


def sexpr_unpack(sexpr):
    try:
        tag = sexpr[0]
        body = sexpr[1:]
        return tag._val, body
    except:
        return sexpr._val, None
