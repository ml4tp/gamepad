from enum import Enum


class Conn(Enum):
	ONE2ONE = 0
	ONE2MANY = 1
	MANY2MANY = 2
	WEIRD = 3


class Type(Enum):
	BASE = 0
	BODY = 1


# has_body?
# connection mode?
# 1-1, 1-many, many-many?

# NOTE(deh): str s.mltac_plugin ++ str "::" ++
#            str s.mltac_tactic ++ str "@" ++ int i
# NOTE(deh): wtf, ssrapply@0 different from ssrapply@1?
# NOTE(deh): wtf, ssrcase@0 different from ssrcase@1?
# NOTE(deh): wtf, ssrmove@0/ssrmove@2 different from ssrmove@1?


TACTICS = {"<coretactics::intro@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::assumption@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::clear@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::clearbody@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::constructor@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::constructor@1>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::exact@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::exists@1>": (Conn.WEIRD, Type.BASE),
           "<coretactics::left@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::right@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::right_with@0>": (Conn.ONE2MANY, Type.BASE),
           "<coretactics::split@0>": (Conn.WEIRD, Type.BASE),
           "<coretactics::symmetry@0>": (Conn.ONE2ONE, Type.BASE),
           "<coretactics::transitivity@0>": (Conn.ONE2MANY, Type.BASE),
           "<extratactics::contradiction@0>": (Conn.ONE2ONE, Type.BASE),
           "<extratactics::discriminate@0>": (Conn.ONE2ONE, Type.BASE),
           "<g_auto::auto@0>": (Conn.WEIRD, Type.BASE),
           "<g_auto::eauto@0>": (Conn.WEIRD, Type.BASE),
           "<g_auto::trivial@0>": (Conn.ONE2ONE, Type.BASE),
           "<ssreflect_plugin::ssrapply@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrapply@1>": (Conn.WEIRD, Type.BASE),
           "<ssreflect_plugin::ssrcase@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrcase@1>": (Conn.WEIRD, Type.BASE),
           "<ssreflect_plugin::ssrclear@0>": (Conn.ONE2ONE, Type.BASE),
           "<ssreflect_plugin::ssrcongr@0>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrelim@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrexact@0>": (Conn.ONE2ONE, Type.BODY),
           "<ssreflect_plugin::ssrexact@1>": (Conn.ONE2ONE, Type.BODY),
           "<ssreflect_plugin::ssrhave@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrmove@0>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrmove@1>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrmove@2>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrpose@0>": (Conn.ONE2ONE, Type.BASE),
           "<ssreflect_plugin::ssrpose@2>": (Conn.ONE2ONE, Type.BASE),
           "<ssreflect_plugin::ssrrewrite@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrset@0>": (Conn.ONE2ONE, Type.BASE),
           "<ssreflect_plugin::ssrsuff@0>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrsuffices@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrtclby@0>": (Conn.WEIRD, Type.BODY),
           "<ssreflect_plugin::ssrtcldo@0>": (Conn.WEIRD, Type.BODY),
           "<ssreflect_plugin::ssrtclintros@0>": (Conn.WEIRD, Type.BODY),
           "<ssreflect_plugin::ssrtclseq@0>": (Conn.ONE2MANY, Type.BODY),
           "<ssreflect_plugin::ssrwithoutloss@0>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrwithoutlossss@0>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrwlog@0>": (Conn.ONE2ONE, Type.BASE),
           "<ssreflect_plugin::ssrwlogs@0>": (Conn.ONE2MANY, Type.BASE),
           "<ssreflect_plugin::ssrwlogss@0>": (Conn.ONE2MANY, Type.BASE)
           }
