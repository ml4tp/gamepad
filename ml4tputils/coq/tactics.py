from enum import Enum

from lib.myhist import MyHist


"""
[Note]

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
               ("ml4tp.SC", Type.SSR_AUX),       # ssr internal clear inside tclintros
               ("ml4tp.SPS", Type.SSR_AUX),      # ssr internal simpl pattern
               ("ml4tp.SPC2", Type.SSR_AUX)      # ssr internal case pattern
               ]


TACTICS = [info[0] for info in TACTIC_INFO]


TACTIC_HIST = MyHist(TACTICS)


TACTICS_INFO_EQUIV = [[("<coretactics::intro@0>", Type.COQ_ML)],
                      [("<coretactics::assumption@0>", Type.COQ_ML)],
                      [("<coretactics::clear@0>", Type.COQ_ML), ("<ssreflect_plugin::ssrclear@0>", Type.SSR_ML)],
                      [("<coretactics::clearbody@0>", Type.COQ_ML)],
                      [("<coretactics::constructor@0>", Type.COQ_ML), ("<coretactics::constructor@1>", Type.COQ_ML)],
                      [("<coretactics::exact@0>", Type.COQ_ML), ("<ssreflect_plugin::ssrexact@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrexact@1>", Type.SSR_ML)],
                      [("<coretactics::exists@1>", Type.COQ_ML)],
                      [("<coretactics::left@0>", Type.COQ_ML), ("<coretactics::left_with@0>", Type.COQ_ML)],
                      [("<coretactics::reflexivity@0>", Type.COQ_ML)],
                      [("<coretactics::right@0>", Type.COQ_ML), ("<coretactics::right_with@0>", Type.COQ_ML)],
                      [("<coretactics::split@0>", Type.COQ_ML)],
                      [("<coretactics::symmetry@0>", Type.COQ_ML)],
                      [("<coretactics::transitivity@0>", Type.COQ_ML)],
                      [("<extratactics::contradiction@0>", Type.COQ_ML)],
                      [("<extratactics::discriminate@0>", Type.COQ_ML)],
                      [("<g_auto::auto@0>", Type.COQ_ML)],
                      [("<g_auto::eauto@0>", Type.COQ_ML)],
                      [("<g_auto::trivial@0>", Type.COQ_ML)],
                      [("apply", Type.ATOM), ("<ssreflect_plugin::ssrapply@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrapply@1>", Type.SSR_ML)],
                      [("case", Type.ATOM), ("<ssreflect_plugin::ssrcase@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrcase@1>", Type.SSR_ML)],
                      [("compute", Type.ATOM)],
                      [("intros", Type.ATOM)],
                      [("red", Type.ATOM)],
                      [("split", Type.ATOM)],
                      [("simpl", Type.ATOM)],
                      [("<ssreflect_plugin::ssrcongr@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrelim@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrhave@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrmove@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrmove@1>", Type.SSR_ML), ("<ssreflect_plugin::ssrmove@2>", Type.SSR_ML), ("<ssreflect_plugin::ssrmove@3>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrpose@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrpose@1>", Type.SSR_ML), ("<ssreflect_plugin::ssrpose@2>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrrewrite@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrset@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrsuff@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrsuffices@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrtclby@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrtcldo@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrtclintros@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrtclseq@0>", Type.SSR_ML)],
                      [("<ssreflect_plugin::ssrwithoutloss@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwithoutlossss@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwlog@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwlogs@0>", Type.SSR_ML), ("<ssreflect_plugin::ssrwlogss@0>", Type.SSR_ML)],               
                      [("ml4tp.MYDONE", Type.SSR_AUX)],   # ssr done
                      [("ml4tp.SI", Type.SSR_AUX)],       # ssr internal intros inside tclintros
                      [("ml4tp.SC", Type.SSR_AUX)],       # ssr internal clear inside tclintros
                      [("ml4tp.SPS", Type.SSR_AUX)],      # ssr internal simpl pattern
                      [("ml4tp.SPC2", Type.SSR_AUX)]      # ssr internal case pattern
                      ]


TACTICS_EQUIV = [[tac[0] for tac in tacs] for tacs in TACTICS_INFO_EQUIV]
