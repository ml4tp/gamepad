from setuptools import setup, find_packages
setup(
    name="gamepad",
    version="0.1",
    packages=find_packages(),
    install_requires=['apted',
                      'editdistance'
                      'matplotlib',
                      'networkx',
                      'numpy',
                      'pandas',
                      'plotly',
                      'psutil',
                      'scipy',
                      'torch'
                      ]
)
