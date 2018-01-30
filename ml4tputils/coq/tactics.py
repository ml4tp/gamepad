from enum import Enum

from lib.myhist import MyHist


"""
[Note]

str s.mltac_plugin ++ str "::" ++ str s.mltac_tactic ++ str "@" ++ int i
"""


class Type(Enum):
    BASE = 0
    BODY = 1


class TacKind(Enum):
    NAME = 1
    ATOMIC = 2
    NOTATION = 3
    ML = 4


TACTIC_INFO = [("<coretactics::intro@0>", Type.BASE),
               ("<coretactics::assumption@0>", Type.BASE),
               ("<coretactics::clear@0>", Type.BASE),
               ("<coretactics::clearbody@0>", Type.BASE),
               ("<coretactics::constructor@0>", Type.BASE),
               ("<coretactics::constructor@1>", Type.BASE),
               ("<coretactics::exact@0>", Type.BASE),
               ("<coretactics::exists@1>", Type.BASE),
               ("<coretactics::left@0>", Type.BASE),
               ("<coretactics::reflexivity@0>", Type.BASE),
               ("<coretactics::right@0>", Type.BASE),
               ("<coretactics::right_with@0>", Type.BASE),
               ("<coretactics::split@0>", Type.BASE),
               ("<coretactics::symmetry@0>", Type.BASE),
               ("<coretactics::transitivity@0>", Type.BASE),
               ("<extratactics::contradiction@0>", Type.BASE),
               ("<extratactics::discriminate@0>", Type.BASE),
               ("<g_auto::auto@0>", Type.BASE),
               ("<g_auto::eauto@0>", Type.BASE),
               ("<g_auto::trivial@0>", Type.BASE),
               ("<ssreflect_plugin::ssrapply@0>", Type.BODY),
               ("<ssreflect_plugin::ssrapply@1>", Type.BASE),
               ("<ssreflect_plugin::ssrcase@0>", Type.BODY),
               ("<ssreflect_plugin::ssrcase@1>", Type.BASE),
               ("<ssreflect_plugin::ssrclear@0>", Type.BASE),
               ("<ssreflect_plugin::ssrcongr@0>", Type.BASE),
               ("<ssreflect_plugin::ssrelim@0>", Type.BODY),
               ("<ssreflect_plugin::ssrexact@0>", Type.BODY),
               ("<ssreflect_plugin::ssrexact@1>", Type.BODY),
               ("<ssreflect_plugin::ssrhave@0>", Type.BODY),
               ("<ssreflect_plugin::ssrmove@0>", Type.BASE),
               ("<ssreflect_plugin::ssrmove@1>", Type.BODY),
               ("<ssreflect_plugin::ssrmove@2>", Type.BASE),
               ("<ssreflect_plugin::ssrpose@0>", Type.BASE),
               ("<ssreflect_plugin::ssrpose@2>", Type.BASE),
               ("<ssreflect_plugin::ssrrewrite@0>", Type.BODY),
               ("<ssreflect_plugin::ssrset@0>", Type.BASE),
               ("<ssreflect_plugin::ssrsuff@0>", Type.BASE),
               ("<ssreflect_plugin::ssrsuffices@0>", Type.BODY),
               ("<ssreflect_plugin::ssrtclby@0>", Type.BODY),
               ("<ssreflect_plugin::ssrtcldo@0>", Type.BODY),
               ("<ssreflect_plugin::ssrtclintros@0>", Type.BODY),
               ("<ssreflect_plugin::ssrtclseq@0>", Type.BODY),
               ("<ssreflect_plugin::ssrwithoutloss@0>", Type.BASE),
               ("<ssreflect_plugin::ssrwithoutlossss@0>", Type.BASE),
               ("<ssreflect_plugin::ssrwlog@0>", Type.BASE),
               ("<ssreflect_plugin::ssrwlogs@0>", Type.BASE),
               ("<ssreflect_plugin::ssrwlogss@0>", Type.BASE),
               ("ml4tp.MYDONE", Type.BASE),   # ssr done
               ("ml4tp.SI", Type.BASE),       # ssr internal intros inside tclintros
               ("ml4tp.SC", Type.BASE),       # ssr internal clear inside tclintros
               ("ml4tp.SPS", Type.BASE),      # ssr internal simpl pattern
               ("ml4tp.SPC2", Type.BASE)      # ssr internal case pattern
               ]


TACTICS = [info[0] for info in TACTIC_INFO]


TACTIC_HIST = MyHist(TACTICS)
