"""
[Note]

Utility functions.
"""

def pp_tab(tab, str):
    return tab * " " + str


def dict_ls_app(dict_, k, v):
	if k in dict_:
		dict_[k] += [v]
	else:
		dict_[k] = [v]