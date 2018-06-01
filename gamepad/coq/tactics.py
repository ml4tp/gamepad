# Copyright 2018 The GamePad Authors. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

from enum import Enum

from lib.myhist import MyHist


"""
[Note]

Contains information on tactics.

str s.mltac_plugin ++ str "::" ++ str s.mltac_tactic ++ str "@" ++ int i
"""


class Type(Enum):
    ATOM = 0
    COQ_ML = 1
    SSR_ML = 2
    SSR_AUX = 3


class TacKind(Enum):
    NAME = 1
    ATOMIC = 2
    NOTATION = 3
    ML = 4


TACTIC_INFO = [("<coretactics::intro@0>", Type.COQ_ML),
               ("<coretactics::assumption@0>", Type.COQ_ML),
               ("<coretactics::clear@0>", Type.COQ_ML),
               ("<coretactics::clearbody@0>", Type.COQ_ML),
               ("<coretactics::constructor@0>", Type.COQ_ML),
               ("<coretactics::constructor@1>", Type.COQ_ML),
               ("<coretactics::exact@0>", Type.COQ_ML),
               ("<coretactics::exists@1>", Type.COQ_ML),
               ("<coretactics::left@0>", Type.COQ_ML),
               ("<coretactics::reflexivity@0>", Type.COQ_ML),
               ("<coretactics::right@0>", Type.COQ_ML),
               ("<coretactics::right_with@0>", Type.COQ_ML),
               ("<coretactics::split@0>", Type.COQ_ML),
               ("<coretactics::symmetry@0>", Type.COQ_ML),
               ("<coretactics::transitivity@0>", Type.COQ_ML),
               ("<extratactics::contradiction@0>", Type.COQ_ML),
               ("<extratactics::discriminate@0>", Type.COQ_ML),
               ("<g_auto::auto@0>", Type.COQ_ML),
               ("<g_auto::eauto@0>", Type.COQ_ML),
               ("<g_auto::trivial@0>", Type.COQ_ML),
               ("apply", Type.ATOM),
               ("case", Type.ATOM),
               ("compute", Type.ATOM),
               ("intros", Type.ATOM),
               ("red", Type.ATOM),
               ("split", Type.ATOM),
               ("simpl", Type.ATOM),
               ("<ssreflect_plugin::ssrapply@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrapply@1>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrcase@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrcase@1>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrclear@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrcongr@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrelim@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrexact@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrexact@1>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrhave@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrmove@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrmove@1>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrmove@2>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrpose@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrpose@2>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrrewrite@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrset@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrsuff@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrsuffices@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrtclby@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrtcldo@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrtclintros@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrtclseq@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrwithoutloss@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrwithoutlossss@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrwlog@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrwlogs@0>", Type.SSR_ML),
               ("<ssreflect_plugin::ssrwlogss@0>", Type.SSR_ML),
               ("ml4tp.MYDONE", Type.SSR_AUX),   # ssr done
               ("ml4tp.SI", Type.SSR_AUX),       # ssr internal intros inside tclintros
               ("ml4tp.SIO", Type.SSR_AUX),      # ssr internal intros inside tclintros
               ("ml4tp.SC", Type.SSR_AUX),       # ssr internal clear inside tclintros
               ("ml4tp.SPS", Type.SSR_AUX),      # ssr internal simpl pattern
               ("ml4tp.SPC2", Type.SSR_AUX),     # ssr internal case pattern
               ("ml4tp.DOEND", Type.SSR_AUX)     # end of a ssrdo
               ]


TACTICS = [info[0] for info in TACTIC_INFO]


TACTIC_HIST = MyHist(TACTICS)


def is_tclintros_intern(tac):
    """
    ml4tp.SI      ssr internal intros inside tclintros
    ml4tp.SC      ssr internal clear inside tclintros
    ml4tp.SPS     ssr internal simpl pattern
    ml4tp.SPC2    ssr internal intros on case pattern
    """
    return (tac.name == "ml4tp.SI" or    # intro part of tclintros
            tac.name == "ml4tp.SC" or    # clear part of tclintros
            tac.name == "ml4tp.SPS" or   # simpl pattern
            tac.name == "ml4tp.SPC2")    # case pattern


def is_tclintros_all(tac):
    return (tac.name == "ml4tp.SIO" or  # original tactic wrapped by tclintros
            is_tclintros_intern(tac))


def parse_full_tac(tac_str):
    return tac_str


TACTICS_INFO_EQUIV = [("intro", [("<coretactics::intro@0>", Type.COQ_ML), ("intros", Type.ATOM), ("<ssreflect_plugin::ssrtclintros@0>", Type.SSR_ML), ("ml4tp.SI", Type.SSR_AUX), ("ml4tp.SPC2", Type.SSR_AUX)]),
                      ("done", [("ml4tp.MYDONE", Type.SSR_AUX), ("<coretactics::assumption@0>", Type.COQ_ML), ("<g_auto::trivial@0>", Type.COQ_ML), ("<coretactics::reflexivity@0>", Type.COQ_ML), ("<extratactics::discriminate@0>", Type.COQ_ML), ("<extratactics::contradiction@0>", Type.COQ_ML)]),
                      ("clear", [("<coretactics::clear@0>", Type.COQ_ML), ("<ssreflect_plugin::ssrclear@0>", Type.SSR_ML), ("<coretactics::clearbody@0>", Type.COQ_ML), ("ml4tp.SC", Type.SSR_AUX), ("ml4tp.DOEND", Type.SSR_AUX)]),
                      ("exact", [("<coretactics::exact@0>", Type.COQ_ML), ("<ssreflect_plugin::ssrexact@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrexact@1>", Type.SSR_ML)]),
                      ("constructor", [("<coretactics::constructor@0>", Type.COQ_ML), ("<coretactics::constructor@1>", Type.COQ_ML)]),
                      ("left", [("<coretactics::left@0>", Type.COQ_ML), ("<coretactics::left_with@0>", Type.COQ_ML)]),
                      ("right", [("<coretactics::right@0>", Type.COQ_ML), ("<coretactics::right_with@0>", Type.COQ_ML)]),
                      ("split", [("<coretactics::split@0>", Type.COQ_ML), ("split", Type.ATOM)]),
                      ("symmetry", [("<coretactics::symmetry@0>", Type.COQ_ML)]),
                      ("transitivity", [("<coretactics::transitivity@0>", Type.COQ_ML)]),
                      ("auto", [("<g_auto::auto@0>", Type.COQ_ML), ("<g_auto::eauto@0>", Type.COQ_ML)]),
                      ("apply", [("apply", Type.ATOM), ("<ssreflect_plugin::ssrapply@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrapply@1>", Type.SSR_ML)]),
                      ("case", [("case", Type.ATOM), ("<ssreflect_plugin::ssrcase@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrcase@1>", Type.SSR_ML)]),
                      ("compute", [("compute", Type.ATOM), ("red", Type.ATOM), ("simpl", Type.ATOM), ("ml4tp.SPS", Type.SSR_AUX)]),
                      ("congr", [("<ssreflect_plugin::ssrcongr@0>", Type.SSR_ML)]),
                      ("elim", [("<ssreflect_plugin::ssrelim@0>", Type.SSR_ML)]),
                      ("have", [("<ssreflect_plugin::ssrhave@0>", Type.SSR_ML), ("<coretactics::exists@0>", Type.COQ_ML), ("<coretactics::exists@1>", Type.COQ_ML)]),
                      ("move", [("<ssreflect_plugin::ssrmove@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrmove@1>", Type.SSR_ML), ("<ssreflect_plugin::ssrmove@2>", Type.SSR_ML), ("<ssreflect_plugin::ssrmove@3>", Type.SSR_ML)]),
                      ("pose", [("<ssreflect_plugin::ssrpose@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrpose@1>", Type.SSR_ML), ("<ssreflect_plugin::ssrpose@2>", Type.SSR_ML)]),
                      ("rewrite", [("<ssreflect_plugin::ssrrewrite@0>", Type.SSR_ML), ("rewrite", Type.ATOM)]),
                      ("set", [("<ssreflect_plugin::ssrset@0>", Type.SSR_ML)]),
                      ("suff", [("<ssreflect_plugin::ssrsuff@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrsuffices@0>", Type.SSR_ML)]),
                      ("dostart", [("<ssreflect_plugin::ssrtcldo@0>", Type.SSR_ML)]),  # Note(deh): do beginning part
                      ("wlog", [("<ssreflect_plugin::ssrwithoutloss@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwithoutlossss@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwlog@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwlogs@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwlogss@0>", Type.SSR_ML)]),
                      ]

TACTICS_EQUIV = [[tac[0] for tac in tacs] for pp_name, tacs in TACTICS_INFO_EQUIV]


# TACTICS_EQUIV_HIST = MyHist(TACTICS_EQUIV)