from setuptools import setup, find_packages
setup(
    name="gamepad",
    version="0.1",
    packages=find_packages(), install_requires=['sexpdata', 'plotly', 'matplotlib', 'networkx', 'numpy', 'scipy',
                                                'torch', 'pandas', 'psutil', 'apted', 'editdistance']
)
