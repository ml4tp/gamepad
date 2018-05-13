from apted import APTED
from apted.helpers import Tree


def kern2tr(tactr, kdx):
    return Tree("FOO").from_text(tactr.decoder.decode_exp_by_key(kdx).apted_tree())


def kern_tree_edit_dist(tactr, kdx1, kdx2):
    return APTED(kern2tr(tactr, kdx1), kern2tr(tactr, kdx2)).compute_edit_distance()


def mid2tr(tactr, mdx):
    return Tree("FOO").from_text(tactr.mid_decoder.decode_exp_by_key(mdx).apted_tree())


def mid_tree_edit_dist(tactr, kdx1, kdx2):
    return APTED(mid2tr(tactr, kdx1), mid2tr(tactr, kdx2)).compute_edit_distance()


def tree_edit_dist(tr1, tr2):
    return APTED(tr1, tr2).compute_edit_distance()
