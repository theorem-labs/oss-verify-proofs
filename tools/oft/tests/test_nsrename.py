"""oft rename-namespace: the Rocq namespace in plain text and inside the three stored encodings, on texts taken from
the tree; the rename of a tree, its gates and `--verify`."""
import io
import os
import shutil
import subprocess
import unittest
from unittest import mock

from oft import facts, generate, names, nsrename as ns, paths
from oft.tests import helpers

# Every blob below is copied out of the tree named above it, unchanged.

# projects/boost-json/fuzz_parse/proofs/lib/As/AW_PoisonRemap1.v:17 (KReplay.lz_vm)
LZ_TABLE = ("##9`K47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I"
            "!sg+4Init9Datatypes6option!sH>4list00i8?OssFuzzTheorems6Proofs:boost_json:fuzz_parse3"
            "lib2As?AW_PoisonRemap14RENV00C!ssU3Lib5Frame5munch!siawmono!wAG1!t6`=disjoint_from!x4"
            ">Z02C!sD+5Lists7ListDef3map!tSZ4TacX2wzK!xJA1!t,`b8K!vAZCells4cell04k!yun1!t_f!v2\\Ste"
            "p8rw_cells!w?B2C!tw_:!t1$_sizeC56Stdlib6ZArith6BinInt1Z6of_nat!{'`B!uD'_transpor!svW2"
            "As5ASegs5asegsI!wie!#4a,!|^60!~<G3!u?Y8AsShadow3mem!vz`3ivl!tR[llocRep9AGOT_VALS!#3f?1")

# projects/boost-json/fuzz_parse/proofs/lib/As/AW_PoisonRemap1.v:18 (CDef.cdeft)
CDEF_TABLE = ("7fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame0ddisjoint_from37Corelib"
              "7Numbers7BinNumskb4Npos35stdpp9bitvectorbdefinitionsmb2bv7fOssFuzzTheorems6Proofsab"
              "oost_jsonafuzz_parse3lib2AsfAW_PoisonRemap1od4RENV37Corelib4Init9Datatypest94listt9"
              "6option7fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib2As5ASegshg15asegs7fOssFuz"
              "zTheorems6Proofsaboost_jsonafuzz_parse3lib2As8AsShadowhk53mem03ivl05munch05wmono")

# the `zQ` stream of the same file
CDEF_STREAM = ("b0!jc!m4!o8!t2!v1!v8!hjc!ho3!hoa!hof!hp6>1g@1$2@1$1#k0>1b@1$2@1$1#8>1m$7>2m'>0@1$2"
               "@1$1#k0@1$5@1$2@1$1#8>1W@1$4$8>0@3$3^5^4^3>0@3$9^2^4^3>0@3$a$6^5^4>0@3$0^4+hrlln8"
               "+n8>0@3$0^5+hsgij8+8>0@3$0^6+hsgvi0+h8>0@3$0^7+ilhtu0+8>0@3$0^8+ilhtv8+8>0@3$0^9+"
               "ilhuk3+1>0@3$0^a+ilhulc+1>0@3$0^b+hrnlq0+8>0@3$0^c+ikvsu0+8>0@3$0^d+nhkmp8+8>0@3$"
               "0^e+hrmji8+8>0@3$0^f+nhkkh8+8@3$3^h4^h3^h1")

# projects/boost-json/fuzz_parse/proofs/lib/Agent/ASlot_M5P.v:47 (KReplay.run1)
KR_STREAM = ("h01mh11rh23ridh32stp;2g00>Ej21Tg00DKj20Tg00K2g000Dg00V=g00J6g00L:f3f0'1'0W2W1W0W3o")

OLD = ns.OLD_DEFAULT
NEW = "OSSVerify"
OS = "oss-fuzz-theorems"
NS = "oss-verify"

# projects/leptonica/pix_orient_fuzzer/proofs/lib/V23/V23Exit.v at main 197065e565af (blob 1de275ed1b47), lines 20-21
# and 98-100: a plain KReplay table of a variant this parser does not read, which holds no namespace, and a stream
LEPT_PATH = "projects/leptonica/pix_orient_fuzzer/proofs/lib/V23/V23Exit.v"
LEPT_TABLE = ('K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums'
              '1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9D'
              'atatypes6option00I5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs;exit_common00I6ARocqVerifyHar'
              'ness?AgentSubmission6Common4Musl9StdioDefs;exit_common00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitve'
              'ctor;definitions2bv01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrI47Corelib4Init5Logic2'
              'eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z'
              '2leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?Lin'
              'uxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Coreli'
              'b4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4In'
              'it9Datatypes6option01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs'
              '<atexit_stateC5ARocqVerifyHarness?AgentSubmission3V23;V23ExitBase=stdio_globalsC5ARocqVerifyHarness?'
              'AgentSubmission3V23;V23ExitBase:file_cleanK6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs'
              ';exit_common01C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC4ELinuxProcessSemantics?Linux'
              'ProcessSem>RiscvSemantics@word_to_le_bytesC5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzze'
              'r_ubsan1M?loaded_segments____________________K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers'
              '7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocK47Corelib4Init5Logic4True01I'
              '47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Cor'
              'elib7Numbers7BinNums1Z01I6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs;foe_variant00I5AR'
              'ocqVerifyHarness?AgentSubmission3V23<V23StdioDefs>stdout_pending00I6ARocqVerifyHarness?AgentSubmissi'
              'on6Common4Musl9StdioDefs>stdout_pending00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6o'
              'f_natC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs9ssp_cellsK6A'
              'RocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs>stdout_pending01C56Stdlib6ZArith6BinInt1Z3ad'
              'dC5ARocqVerifyHarness?AgentSubmission3V23<V23StdioDefs8exit_preK47Corelib4Init9Datatypes6option02I47'
              'Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcess'
              'Semantics?LinuxProcessSem5State8m_haltedC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_d'
              'eltac5ARocqVerifyHarness?AgentSubmission3V237V23Exit=exit_common_GK47Corelib4Init5Logic3and01K47Core'
              'lib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission3V237V23Exit@stdout_pending_GK47Corelib4Init5'
              'Logic2or02K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProc'
              'essSemantics?LinuxProcessSem5State9fd_lookupI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?Linux'
              'ProcessSem5State9m_vm_lazyC6ARocqVerifyHarness?AgentSubmission6Common4Musl9StdioDefs8exit_preC6ARocq'
              'VerifyHarness?AgentSubmission6Common4Musl8ExitBase:file_cleanI4ELinuxProcessSemantics?LinuxProcessSe'
              'm5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c5ARocqVerifyHarness?AgentSub'
              'mission3V237V23Exit5FOE23C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC6ARocqVerif'
              'yHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7s'
              'eg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcess'
              'Sem3Run6config01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4'
              'm_fsC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_exitI5ARocqVerifyHarness?AgentSubmission6'
              'Common8ShapeAlg8realizes00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4I'
              'nit5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit>ref_exit_cleanC5ARocqVerifyHar'
              'ness?AgentSubmission3V23<V23RelocCode8v23_codeC5ARocqVerifyHarness?AgentSubmission3V23=V23RelocSites'
              '9v23_sitesC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_dataC5ARocqVerifyHarness?AgentSub'
              'mission3V23<V23RelocMusl6v23_rwc5ARocqVerifyHarness?AgentSubmission3V237V23Exit5CXF23I47Corelib7Numb'
              'ers7BinNums1N00C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec1WC5ARocqVerifyHarness?Agen'
              'tSubmission6Common8ShapeAlg6t_emitC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit>ref_exit_flu'
              'shC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit?t_emit_nil_exitc5ARocqVerifyHarness?AgentSub'
              'mission3V237V23Exit:exit_pre_GC6ARocqVerifyHarness?AgentSubmission6Common4Musl4Exit8ref_exitC6ARocqV'
              'erifyHarness?AgentSubmission6Common4Musl4Exit:ref_exit_Z')
LEPT_FILE = "\n".join([
    'From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.',
    'Ltac2 kr_t_V23Exit () := "%s".',
    'Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).',
    'Proof.',
    'ltac2:(KReplay.run1 (kr_t_V23Exit ()) ["VP3"] "g014bo"). Qed.',
]) % LEPT_TABLE + "\n"

# projects/boost-json/fuzz_parse/proofs/lib/Agent/ASlot_M4P.v at main 197065e565af (blob 1eedd10afab3), lines 9-19,
# 166-167: its Require lines, its LZ table and a plain stream
ASLOT_PATH = "projects/boost-json/fuzz_parse/proofs/lib/Agent/ASlot_M4P.v"
ASLOT_TABLE = ('#%#gC8?OssFuzzTheorems6Proofs:boost_json:fuzz_parse3lib4Spec6Malloc4aptrI47Corelib4Init5Logic2eq00C!'
               "s@76eq_ind!sB87f_equalI35stdpp9countable9C!s0'00C56Stdlib6PArith6BinPos3Pos4iter!t%88!tE%_r!sd,Z!sd$"
               "9BinIntDef1Z!se%!tK&8fin_maps:map_insert!vNV3Lib2Nd9ex_elimF2!tm29Datatypes3fst!tK'4base:decide_rel!"
               's>+gmap;gmap_lookup!s?0:!s?$empty!s>0B!s>$partial_al!u\\-!sF$9!sF$fmap!s=6o!s=3!t4%merge!sl7old!wh>9i'
               'ter_succ!w-4@!uH%!w1&_eq!uk6fin!t]/base4f!s836!v92!s:$!x/&!tCBne!{ycoptrI!t436FinMap00!tN47MapFold!t'
               "{05E!x10!u\\$FM!un3O!s83<P!xP%A!xO0!sw$MergeI!vn/!s'$!t_,9!z&$able;prod_eq_de!wj+!}?,>!sD$!s5+I!{3;4p"
               "rod00K!sF+7Numbers7BinNums1Z02!}B36!}B%1Z3add!t%<6option!t'/!sH:1!sHD!tQ=2l!xyda!u<5!#4;$3and!wA,!z^"
               "%!~J%!#4j73not!sn26Specif7sumbool!v&>4list01I!sFA0K4!u~&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Fo"
               'rmula!t587EnvRing5PExpr01K!stL1C!sQ55Tauto8B!sJ&K!#:;:!sb7:Z!t2+=Z!sn$CheckerC!uu<4find!sqAC!sq0_sou'
               'ndK!y+<1!zO<7add_0!#:_4!|C,mul!sd=mul_0_r!v/:x!|:4!s@&or02!#=^;sym!sB89False_i!u_:2or!u^/!#=\\4succ!}'
               'O>t!tC88iff_refl!wU6;ZifyClasses5mkre!vG;5Pos2Z:pos_is_pos!{~@2!{5E!sIF3!u#B;rew_!uS%v!#>{<snd!t9>3P'
               'ol!|iF5Psatz03!sOK2!#3};3na!v>9!sn85!sOK6K!|z@;!x;%Proof!tk>!#5J$2!xJ@3!#:Y<8positive!|C/!sK=!xqF!uv'
               '7!#4x%G!#5D&!y=C6eq_iff!sLB9and_morphC5!u1+!u%&6!#G-&!#3P$!sE=add!#G0\\:and!#G1$3!~b>9peano!#3I5!#?I2'
               '1!#KF9x00!s@9or!#9}7!w534!sJF5!#3qDapp!soF8!#A^?1!#?obUNITI!t0?0!#<8;5eKin!#Bj<4unit!vn>4kind!#Bf=!s'
               'f%!#4GD3Op205I!||F0!#8$?8inj_succ!v,>N00C4!#By$7n!sB%1N6!#G7%!s?3Z6!#GP:;N!#GM+!sD6Z!sD,!#3KF3I!#5OL'
               '0!vmI3!xD=!#E&B!sF$!}095False!tRK1!#97@1!#8=M!|4c7s_slots!#?_;4iterc!t3U5Agent9ASlot_M4P?pos_!#Re$lo'
               "ts'!~Z@3!#93D6!u$<3opp!v4b9set!v6&!sobadd!so%I!soa6mstat!~G=1Z3pow!sC=sub!sC<=pow_le_mono!#H8=>pow_p"
               'os_nonneg!sN<:pow!sJC7compare!{PN!#@%=1N!#?UF7!sIE4!u#<9pow_add_r!y$cmask_upto!#3O74True!#=[3!#3#+:!'
               'vW%ison00!tYb3wr8!sib8put_metaK!{Ei1!|5b4meta00!sldctx!sld6region!sneshadow!uLeare!v:fghdr!z9d9zero_'
               "hdrs!#9QeA!zC'_wr8_comm!#P?;7nat_!#Ca>3nat!uTd<ge!t_&rec!vHcs_!y^%!#:%b8s_!y_%!t_chdr_havoc!t_egroup"
               '!#?b=landK!zng!#A]earea!wJc6s_tick!slb:s_next_rid!spereserve!spc3ctx!sib5c_br!v:c>c_mmap!#K,$e!#=Cb@'
               'c_free!~&%head!#6;a8brk!#CN&!#5NaW145stFin!sof4recF!snf3stD!sm\\<!vA%Kit_ABE!#6@-_put_same!{Tdet_acti'
               "ve!tti>rec_!s{f!v`,8st_model!srf?!sr'_eq_rec!#<Xe6sm_re!#ht<3eqb!wkcm!vp$next!spiprev!spb7m_avail!sm"
               'b;!t_%!sqnfre!#7`c9!sq%mem!sob>!so%last_idx!stifreeab!#z4c?!st%sizeclas!#=^b5usage!#Vcf!sog8upd_meta'
               '!t_cput!#Bq$!}0cget_strid!uQc6!#6Xa8!#5d%9?!so%_!vI^!sx%9!tg%RepA!sy&!#8O,!#5n:8eqb_spec!#K>;7reflec'
               't!$8N3!sI,4negb!sD=and!#6zcsize_!|/$K!#T6f1!#7hd!#3Ti8m_maplen!#6ve!#3J&!#oHE7!#gsA!$0W<6modulo!sF<9'
               "mod_smal!$%3<4one!#Mr<9land_!sI$!#?Qd=rec_!#O~^!#B;5=!#B;&!#5yZ!ts8!#59'!#ADe@!#f['_first'!$'$75proj"
               "1!}n<2!#O'dget!#U1h7r_cell!yK=3di!#B&b5!y;$!#ry&!$9H%;from_!s2%!u:chav_!#}AX!#`K0_havpK!#`Ih1!#L$f!x"
               'Q&!yz<2!vXc!t{&!|$f8smg_projK!#iZ<1!t6f;smg!~,%_p!#=hb_fp;grp_hdr_cov!tlf>!tl+s_ol!zPfbas!$B=cconc!#'
               "A3e9meta_slot!#8<hD!sv+_same!#_Tg5m_mem!x7f:smg!#CiGrefl!$2Bf5!u'krec_mt!u'<7eqb_neq!$//'4Bool!s'$;a"
               'ndb_true_r!t\\k!#J1$!#3fh_ml_nz!srf9!th$lot!#o:ccell_read!w6<3ltb!#9Ia7cellval02!sok1!}x]F_m!sr$_big='
               "!uu+_hh!#slb!tk+!#:+f7sm_proj!$VE3<!$Wm%empty!t7f<!ya$hadow_p!}'=div_mo!y<==mod_pos_boun!sMBneg!sM25"
               "omega8PreOmega1Z;div_0_r_ext!sL>mod!sL'!$E-J4!vRf@!vR-oth!$32g!#<g-in!#=af?!sx%!#>\\nC!sy2_old!#BYjco"
               "n!#fmf=smg_!#>#d:!~2%Tree8pans!#=+i<sm_!#6q+!sv[@!#4r'enframe3rdv!uag3mem!#<F'!}r&4Zdiv:Z_mod_mul!#="
               '/<8mul_com!vFg9sm!#<hl9!#lp$_mt!#Ond!#Z,X!#E`2@!#]K+_ran!#d|c;round_up_pg!$UrB3!sGC!$TzK!$4gV!#L,27s'
               "lot_ok!#;{g@!$9^'!vt%'!zj<=sub!$>=+!#3}h!#7d&ri!#;F<2gt!|n;div!|nA!$aM%l!#Ebislot0!#5%i!#6n^!#tc1!#r"
               "}f:m!#q:'!#cwE6K!{,n1!t?F!$`+K7!#>Dh!#6H%_mod16!$NlH6!#E0jret_span")
ASLOT_FILE = "\n".join([
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_big.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3 ASlot_W9 ASlot_W14.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.',
    'Require Import OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.',
    'From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib Require KReplay.',
    'Ltac2 kr_t_ASlot_M4P () := KReplay.lz_vm "%s".',
    'Proof.',
    'ltac2:(KReplay.run1 (kr_t_ASlot_M4P ()) ["SM"] "p;6g02\\Oj60Tp,3stTp,2scp,3cntp,2aip,2mtp,1pE0o"). Qed.',
]) % ASLOT_TABLE + "\n"


# a proof library file with the four encodings above, as boost-json/fuzz_parse's hold them
WHOLE_FILE = ('From OssFuzzTheorems.Proofs.boost_json.fuzz_parse.lib Require KReplay.\n'
              'Ltac2 kr_t_T () := KReplay.lz_vm "%s".\n'
              'Local Ltac2 zQ s := CDef.cdeft "%s" s.\n'
              'Lemma a : True. Proof. ltac2:(zQ "%s"). Qed.\n'
              'Lemma b : True. Proof. ltac2:(KReplay.run1 (kr_t_T ()) [] "%s"). Qed.\n'
              % (LZ_TABLE, CDEF_TABLE, CDEF_STREAM, KR_STREAM))


def kr_entry(kind, comps, tail=""):
    """A KReplay table entry, as the encoder writes it (KReplay.v:67-92)."""
    out = [kind, chr(48 + len(comps))]
    for c in comps:
        out.append(chr(48 + len(c)))
        out.append(c)
    return "".join(out) + tail

class LZ(unittest.TestCase):
    """The port of `LZ.lz_inflate` (KReplay.v:640-710) and the encoder that feeds it."""

    def test_real_blob_inflates_and_its_header_is_the_length(self):
        plain = ns.lz_inflate(LZ_TABLE)
        self.assertEqual(ns._num88(len(plain), 4), LZ_TABLE[:4])
        self.assertIn(OLD, plain)
        self.assertEqual(plain, ns._plain("kr_table_lz", LZ_TABLE))

    def test_real_blob_re_compresses_to_the_same_text(self):
        plain = ns.lz_inflate(LZ_TABLE)
        again = ns.lz_deflate(plain)
        self.assertEqual(ns.lz_inflate(again), plain)
        self.assertLessEqual(len(again), len(LZ_TABLE) * 11 // 10)

    def test_a_match_copies_what_it_overlaps(self):
        # four header bytes, the literal "abcd", then a short-form match of
        # length 6 at distance 2: "cdcdcd"
        blob = "####abcd" + "!" + ns._digit(76) + ns._digit(1) + ns._digit(2)
        self.assertEqual(ns.lz_inflate(blob), "abcdcdcdcd")

    def test_the_long_form_reaches_further_than_the_short_one(self):
        text = "x" * 2000 + "abcdefgh" + "y" * 2000 + "abcdefgh"
        blob = ns.lz_deflate(text)
        self.assertEqual(ns.lz_inflate(blob), text)

    def test_text_holding_the_escape_is_refused(self):
        with self.assertRaises(ns.Error):
            ns.lz_deflate("a!b")

    def test_a_blob_the_step_limit_cuts_short_is_refused(self):
        with mock.patch.object(ns, "LZ_FUEL", 2):
            # two outer rounds of two steps, and a literal run of at most three
            self.assertEqual(ns.lz_inflate("####abcdefghijkl"), "abcdefghijkl")
            with self.assertRaises(ns.Error):
                ns.lz_inflate("####abcdefghijklmnopqrst")

    def test_every_digit_round_trips(self):
        for d in range(88):
            self.assertEqual(ns._dval(ord(ns._digit(d))), d)
            self.assertNotIn(ns._digit(d), '!"()*.')

    def test_a_match_before_the_start_of_the_output_is_refused(self):
        # the Rocq `getrange` reads nothing there; the port refuses the blob
        blob = "####ab" + "!" + ns._digit(76) + ns._digit(4) + ns._digit(0)
        with self.assertRaises(ns.Error):
            ns.lz_inflate(blob)


class KReplayTable(unittest.TestCase):
    """A table is a concatenation of entries that streams reach by byte offset."""

    def test_the_real_table_parses_to_its_end_and_re_serialises(self):
        plain, entries = ns.check_blob("kr_table_lz", LZ_TABLE)
        self.assertEqual(entries[-1].end, len(plain))
        self.assertEqual("".join(e.render() for e in entries), plain)
        self.assertTrue(any(e.comps and e.comps[0] == OLD for e in entries))

    def test_an_inductive_entry_keeps_its_index_pair(self):
        tab = kr_entry("I", [OLD, "Core"], "00") + kr_entry("C", ["Corelib", "Init"])
        entries = ns.kr_parse_table(tab)
        self.assertEqual([e.tail for e in entries], ["00", ""])
        self.assertEqual("".join(e.render() for e in entries), tab)

    def test_a_renamed_entry_is_padded_back_to_its_old_length(self):
        tab = kr_entry("C", [OLD, "Core", "Images"]) + kr_entry("I", ["Corelib"], "00")
        stats = ns._zero()
        fresh = ns.rename_blob("kr_table", tab, OLD, NEW, stats)
        self.assertEqual(len(fresh), len(tab))
        self.assertEqual(stats["entries"], 1)
        entries = ns.kr_parse_table(tab)
        self.assertEqual(ns.kr_entry_at(fresh, 0).comps, [NEW, "Core", "Images"])
        # the second entry is still where the streams' offsets say it is
        self.assertEqual(ns.kr_entry_at(fresh, entries[1].start).render(),
                         entries[1].render())
        # and the filler that holds the entry's old length is itself an entry
        self.assertEqual([e.start for e in ns.kr_parse_table(fresh)],
                         [0, len(NEW) - len(OLD) + entries[1].start, entries[1].start])

    def test_the_filler_is_a_sequence_of_entries_of_the_length_asked_for(self):
        with self.assertRaises(ns.Error):
            ns.kr_filler(1)
        self.assertEqual(ns.kr_filler(0), "")
        for gap in list(range(2, 100)) + [164, 165, 166]:
            filler = ns.kr_filler(gap)
            self.assertEqual(len(filler), gap)
            self.assertEqual("".join(e.render() for e in ns.kr_parse_table(filler)),
                             filler)

    def test_a_rename_that_would_grow_an_entry_is_refused(self):
        tab = kr_entry("C", ["Ab", "Core"])
        with self.assertRaises(ns.Error):
            ns.rename_blob("kr_table", tab, "Ab", "AbCdEfGh", ns._zero())

    def test_a_table_that_does_not_end_on_an_entry_is_refused(self):
        with self.assertRaises(ns.Error):
            ns.kr_parse_table(kr_entry("C", ["Core"]) + "C")


class KReplayStream(unittest.TestCase):
    """The opcode stream of `run1` (decode_ph, KReplay.v:369-600)."""

    def test_the_real_stream_parses_to_its_end_and_re_serialises(self):
        plain, pieces = ns.check_blob("kr_stream", KR_STREAM)
        self.assertEqual(ns.kr_render_stream(pieces), KR_STREAM)
        self.assertEqual(plain, KR_STREAM)

    def test_an_inline_global_is_renamed_and_the_stream_shrinks(self):
        stream = "p/" + kr_entry("C", [OLD, "Core"]) + "o"
        stats = ns._zero()
        fresh = ns.rename_blob("kr_stream", stream, OLD, NEW, stats)
        self.assertEqual(stats["inline"], 1)
        self.assertEqual(fresh, "p/" + kr_entry("C", [NEW, "Core"]) + "o")
        self.assertEqual(len(fresh), len(stream) - (len(OLD) - len(NEW)))
        self.assertNotIn(OLD, fresh)

    def test_a_soft_inline_global_is_renamed_too(self):
        stream = "p0" + kr_entry("I", [OLD, "Core"], "00") + "o"
        fresh = ns.rename_blob("kr_stream", stream, OLD, NEW, ns._zero())
        self.assertEqual(fresh, "p0" + kr_entry("I", [NEW, "Core"], "00") + "o")

    def test_bytes_after_the_terminating_opcode_are_refused(self):
        with self.assertRaises(ns.Error):
            ns.kr_parse_stream(KR_STREAM + "0")

    def test_an_unknown_opcode_is_refused(self):
        with self.assertRaises(ns.Error):
            ns.kr_parse_stream("(o")

    def test_a_stream_with_no_terminating_opcode_is_refused(self):
        with self.assertRaises(ns.Error):
            ns.kr_parse_stream("W2W1")


class CDefTable(unittest.TestCase):
    """Directory and global records at the offsets a `zQ` header names (CDef.v:170-225)."""

    def test_numbers_round_trip(self):
        for v in list(range(300)) + [1023, 4095, 65535]:
            self.assertEqual(ns.cdef_num_at(ns.cdef_num(v) + "0", 0), (len(ns.cdef_num(v)), v))

    def test_the_real_table_is_covered_by_the_records_its_stream_names(self):
        offsets = ns.cdef_parse_stream(CDEF_STREAM)
        records = ns.cdef_records(CDEF_TABLE, offsets)
        for r in records.values():
            self.assertEqual(CDEF_TABLE[r.start:r.end], r.render())
        self.assertEqual(ns.coverage_gaps(CDEF_TABLE, records), [])
        dirs = [r for r in records.values() if r.comps]
        self.assertTrue(dirs)
        self.assertTrue(all(d.comps[0] == OLD for d in dirs if OLD in d.comps))

    def test_an_identifier_stored_in_pieces_is_read_whole(self):
        table = "2" + "0" + "2" + "7OssFuzz" + "8Theorems" + "4Core"
        rec = ns.cdef_dir_at(table, 0)
        self.assertEqual(rec.comps, [OLD, "Core"])
        self.assertEqual(rec.end, len(table))

    def test_a_renamed_directory_is_padded_and_the_later_offsets_hold(self):
        table = "2f" + OLD + "4Core" + "06Images"
        offsets = [len("2f" + OLD + "4Core")]
        records = ns.cdef_records(table, offsets)
        stats = ns._zero()
        fresh = ns.rename_cdef_table(table, records, OLD, NEW, stats)
        self.assertEqual(stats["dirs"], 1)
        self.assertEqual(len(fresh), len(table))
        self.assertEqual(ns.cdef_dir_at(fresh, 0).comps, [NEW, "Core"])
        self.assertEqual(ns.cdef_glob_at(fresh, offsets[0]).name, "Images")
        self.assertNotIn(OLD, fresh)

    def test_a_header_that_misses_its_mark_is_refused(self):
        with self.assertRaises(ns.Error):
            ns.cdef_parse_stream("11" + "0")

    def test_a_stream_must_decode_to_its_exact_end(self):
        self.assertEqual(ns.cdef_parse_stream("10!5$0"), [5])
        for bad in ("00", "10!5$0P", "10!5$1", "01&~0P", "00~0"):
            with self.assertRaises(ns.Error, msg=bad):
                ns.cdef_parse_stream(bad)

    def test_a_case_takes_as_many_branches_as_the_stream_holds(self):
        # `M` global 0, return type, scrutinee, then two branches
        self.assertEqual(ns.cdef_parse_stream("10!5M0PZPS"), [5])
        self.assertEqual(ns.cdef_parse_stream("11!5&P@1~0M0PZ"), [5])


class Literals(unittest.TestCase):
    """Which call a string literal belongs to."""

    def test_each_call_shape_is_recognised(self):
        text = ('Ltac2 kr_t_U () := KReplay.lz_vm "a".\n'
                'Ltac2 kr_t_V () := "b".\n'
                'Local Ltac2 zQ s := CDef.cdeft "c" s.\n'
                'ltac2:(zQ "d").\n'
                'ltac2:(KReplay.run1 (kr_t_U ()) ["Sec"; "Two"] "e").\n'
                'ltac2:(KReplay.run1z (kr_t_U ()) [] "f").\n'
                'ltac2:(KReplay.run ["S"] "g").\n'
                'Ltac2 other () := "h".\n')
        got = [(text[s:e], kind) for s, e, kind in ns.literals(text)]
        self.assertEqual(got, [("a", "kr_table_lz"), ("b", "kr_table"), ("c", "cdef_table"),
                               ("d", "cdef_stream"), ("Sec", "text"), ("Two", "text"),
                               ("e", "kr_stream"), ("f", "kr_stream_lz"), ("S", "text"),
                               ("g", "kr_stream"), ("h", None)])

    def test_a_doubled_quote_is_one_quote(self):
        """Rocq reads `""` inside a literal as one quote: the literal goes on."""
        self.assertEqual(ns.literals('Ltac2 x := "a""b".'), [(12, 16, None)])

    def test_a_literal_after_a_call_s_sentence_belongs_to_no_call(self):
        # projects/ (then old layout) proofs/jsoncons/fuzz_ubjson_encoder/lib/PeACRdVal.v: the stream is in a
        # side file, and the next literal is a Tactic Notation's
        text = ('ltac2:(KReplay.run1 (kr_t_P ()) [] (P_blobs1.kr_b_005 ())). Qed.\n'
                'Tactic Notation "wr_mem" := idtac.\n')
        self.assertEqual([k for _, _, k in ns.literals(text)], [None])

    def test_a_side_file_stream_is_a_stream(self):
        # projects/ (then old layout) proofs/jsoncons/fuzz_ubjson_encoder/lib/PeACRdVal_blobs1.v
        text = ('From X.lib Require KReplay.\n'
                'Ltac2 kr_b_001 () := "W2W1W0W3o".\n')
        self.assertEqual([k for _, _, k in ns.literals(text)], ["kr_stream"])

    def test_a_side_file_of_another_codec_is_not_a_stream(self):
        # ossv/candidates proofs/jsoncons/fuzz_json_encoder/lib/PmTopAW/ReadXAW_blobs1.v
        text = ('From X.lib Require Rpl.\n'
                'Ltac2 kr_b_001 () := "S00!1,0|F2be020;".\n')
        self.assertEqual([k for _, _, k in ns.literals(text)], [None])

    def test_a_call_of_the_other_codec_is_not_a_stream(self):
        # projects/ (then old layout) proofs/boost-beast/http_request/lib/Common/KReplay.v:272-313 takes two
        # arrays, and its globals are plain text
        text = 'ltac2:(KReplay.run [| constr:(@X) |] [| @y |] "abc").\n'
        self.assertEqual([k for _, _, k in ns.literals(text)], [None])

    def test_runc_is_not_read_as_run(self):
        text = 'ltac2:(KReplay.runc [| constr:(@X) |] [| @y |] "abc").\n'
        self.assertEqual([k for _, _, k in ns.literals(text)], [None])


class Bytes(unittest.TestCase):
    """A Rocq string is bytes; the .v file holding it is UTF-8."""

    def test_lengths_count_bytes(self):
        # a two-byte name: its length byte says 2
        stream = "h01" + chr(48 + 2) + "\u0398" + "o"
        text = 'ltac2:(KReplay.run1 (kr_t_X ()) [] "%s").\n' % stream
        blobs = ns._codec_blobs(text, ns.literals(text))
        self.assertEqual(len(blobs[0][4]), len(stream) + 1)
        self.assertEqual(ns.write_body(blobs[0][4]), stream)

    def test_deflate_keeps_every_character_whole(self):
        text = ("ab\u0398cd" * 40).encode("utf-8").decode("latin-1")
        blob = ns.lz_deflate(text)
        self.assertEqual(ns.lz_inflate(blob), text)
        ns.write_body(blob)          # raises unless the blob is valid UTF-8


class CDefForms(unittest.TestCase):
    """Records stored in pieces, and table bytes no stream reaches."""

    # projects/ (then old layout) proofs/boost-json/fuzz_parse/lib/AsMainIfacePre.v, the record at 887
    PIECES = ("7fOssFuzzTheorems6Proofsaboost_jsonafuzz_parse3lib2As"
              "0d1A1s1P1r1i1n1t1f1F1i1r1s1t")

    def test_a_record_in_pieces_re_serialises_to_itself(self):
        r = ns.cdef_dir_at(self.PIECES, 0)
        self.assertEqual(r.comps[-1], "AsPrintfFirst")
        self.assertEqual(r.render(), self.PIECES)

    def test_a_renamed_record_in_pieces_keeps_its_pieces(self):
        stats = ns._zero()
        r = ns.cdef_dir_at(self.PIECES, 0)
        g = ns.CdefRecord(len(self.PIECES), len(self.PIECES) + 3, diroff=0, name="x",
                          pieces=None)
        table = self.PIECES + "01x"
        fresh = ns.rename_cdef_table(table, {0: r, g.start: g}, OLD, NEW, stats)
        self.assertEqual(len(fresh), len(table))
        now = ns.cdef_dir_at(fresh, 0)
        self.assertEqual(now.comps[0], NEW)
        self.assertEqual(now.comps[-1], "AsPrintfFirst")
        self.assertEqual(ns.cdef_glob_at(fresh, g.start).name, "x")

    def test_unread_bytes_holding_the_old_name_are_padded(self):
        stats = ns._zero()
        dead = "1f" + OLD
        table = "01x" + dead
        g = ns.CdefRecord(0, 3, diroff=0, name="x")
        fresh = ns.rename_cdef_table(table, {0: g}, OLD, NEW, stats)
        self.assertEqual(fresh, "01x" + ns.PAD * len(dead))
        self.assertEqual(stats["dead_cleared"], len(dead))



class Text(unittest.TestCase):
    """rename_text: the word rule (c) everywhere outside a .v file's literals, a dotted-name literal renamed by its
    components (b), a stored encoding renamed by its codec or left byte for byte (a), and every other literal that
    holds the old name refused (plan D12, Review Focus 1)."""

    def rename(self, rel, text):
        return ns.rename_text(rel, text, OLD, NEW, OS, NS)

    def test_plain_forms_are_renamed(self):
        text = ("From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import A B.\n"
                "Require Import OssFuzzTheorems.Core.Shapes.\n"
                "Import OssFuzzTheorems.Core.Images.\n"
                "Definition x := OssFuzzTheorems.zlib.checksum_fuzzer.Statements.plain_halts.\n"
                "From Stdlib Require Import\n  OssFuzzTheorems.Core.Shapes.\n"
                "Ltac2 l () := [\"@OssFuzzTheorems.Proofs.x.lib.A\"; \"Corelib.Init.Datatypes.\"].\n"
                "(* see OssFuzzTheorems.Core *)\n")
        got = self.rename("projects/zlib/checksum_fuzzer/proofs/lib/A.v", text)
        self.assertEqual(got, text.replace(OLD, NEW))
        dune = "(rocq.theory\n (name OssFuzzTheorems.Core)\n (package rocq-oss-fuzz-theorems-core))\n"
        self.assertEqual(self.rename("theories/dune", dune),
                         "(rocq.theory\n (name OSSVerify.Core)\n (package rocq-oss-verify-core))\n")

    def test_the_stem_rule_renames_only_opam_names(self):
        text = ("schema: oss-fuzz-theorems/harness/1\n"
                "image: ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:00\n"
                "depends: \"rocq-oss-fuzz-theorems-core\" rocq-oss-fuzz-theorems\n")
        self.assertEqual(self.rename("x.yaml", text),
                         "schema: oss-fuzz-theorems/harness/1\n"
                         "image: ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:00\n"
                         "depends: \"rocq-oss-verify-core\" rocq-oss-verify\n")

    def test_a_dotted_name_literal_is_renamed(self):
        for body, want in (("@OssFuzzTheorems.Proofs.x.lib.A", "@OSSVerify.Proofs.x.lib.A"),
                           ("OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanK.APK.acs",
                            "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanPlanK.APK.acs"),
                           ("OssFuzzTheorems.", "OSSVerify."),
                           ("Corelib.Init.Datatypes.", "Corelib.Init.Datatypes.")):
            text = 'Ltac2 other () := "%s".\n' % body
            self.assertEqual(self.rename("a/B.v", text), 'Ltac2 other () := "%s".\n' % want)

    def test_an_unknown_encoding_holding_the_old_name_is_refused(self):
        # a literal no codec reads: a length byte (`?`, 15) then the name, as a new KReplay variant would store it
        text = ('From OssFuzzTheorems.Proofs.x.lib Require KReplay.\n'
                'Ltac2 tbl () := "x7?OssFuzzTheorems6Proofs".\n')
        with self.assertRaises(ns.Error) as e:
            self.rename("projects/x/y/proofs/lib/T.v", text)
        self.assertIn("projects/x/y/proofs/lib/T.v:2:", str(e.exception))
        self.assertIn("x7?OssFuzzTheorems6Proofs", str(e.exception))

    def test_a_non_word_length_byte_after_the_name_is_refused(self):
        # `:` is chr(48 + 10), the length byte of a 10-character component: no word character, so a word rule would
        # rename the encoded name and leave its length byte saying 15
        text = 'Ltac2 tbl () := "C3?OssFuzzTheorems:boost_json".\n'
        with self.assertRaises(ns.Error):
            self.rename("projects/x/y/proofs/lib/T.v", text)

    def test_the_name_inside_a_longer_word_is_refused(self):
        with self.assertRaises(ns.Error):
            self.rename("notes/x.md", "OssFuzzTheoremsX is no namespace\n")

    def test_a_bash_string_in_a_non_v_file_takes_the_word_rule(self):
        line = '  stmt_mod="OssFuzzTheorems.Tests.$project.$harness.Statements"\n'      # tests/check.sh
        self.assertEqual(self.rename("tests/check.sh", line),
                         '  stmt_mod="OSSVerify.Tests.$project.$harness.Statements"\n')

    def test_a_file_without_either_name_is_returned_unread(self):
        text = 'Definition s := "an unterminated literal.\n'
        self.assertIs(self.rename("a/B.v", text), text)

    def test_a_plain_blob_without_the_old_name_is_left_unparsed(self):
        # V23Exit.v's table is of a KReplay variant this parser does not read, and holds no namespace: it is left
        # byte for byte, as its stream is, and only the Require line changes
        with self.assertRaises(ns.Error):
            ns.check_blob("kr_table", LEPT_TABLE)
        self.assertEqual(self.rename(LEPT_PATH, LEPT_FILE), LEPT_FILE.replace(OLD, NEW))
        self.assertNotIn(OLD, LEPT_TABLE)

    def test_an_encoded_table_and_its_plain_lines_in_one_file(self):
        got = self.rename(ASLOT_PATH, ASLOT_FILE)
        self.assertNotIn(OLD, got)
        lits = ns.literals(got)
        blob = [got[s:e] for s, e, k in lits if k == "kr_table_lz"][0]
        before = ns.check_blob("kr_table_lz", ASLOT_TABLE)[1]
        after = ns.check_blob("kr_table_lz", blob.encode("utf-8").decode("latin-1"))[1]
        # the inflated new table is the old one with only the names changed: every entry where it was, renamed,
        # and the bytes a shorter entry freed are filler entries
        self.assertEqual([(e.start, e.kind, [NEW if c == OLD else c for c in e.comps], e.tail) for e in before],
                         [(e.start, e.kind, e.comps, e.tail) for e in after if not ns._filler(e)])
        self.assertTrue(any(ns._filler(e) for e in after))
        # the plain lines around it are the text rename's
        self.assertEqual(got.split("\n")[:10], ASLOT_FILE.replace(OLD, NEW).split("\n")[:10])

    def test_a_compressed_blob_hiding_the_name_is_renamed(self):
        # "OssFuzz" and "Theorems" stand apart before the entry that joins them, so the compressed text holds the
        # name only as two back-references: the file's text does not hold it
        table = (kr_entry("C", ["OssFuzzA", "x"]) + kr_entry("C", ["Theorems", "y"])
                 + kr_entry("C", [OLD, "Core", "Shapes"]))
        blob = ns.lz_deflate(table)
        self.assertNotIn(OLD, blob)
        text = 'Ltac2 kr_t_X () := KReplay.lz_vm "%s".\n' % blob
        got = self.rename("projects/x/y/proofs/lib/X.v", text)
        self.assertNotEqual(got, text)
        fresh = [got[s:e] for s, e, k in ns.literals(got) if k == "kr_table_lz"][0]
        self.assertNotIn(OLD, ns.lz_inflate(fresh))
        self.assertIn(NEW, ns.lz_inflate(fresh))

    def test_a_literal_after_a_call_keeps_the_codec_its_call_names(self):
        text = ('From OssFuzzTheorems.Proofs.x.lib Require KReplay.\n'
                'ltac2:(KReplay.run1 (kr_t_T ()) [] "%s").\n' % KR_STREAM)
        self.assertEqual(self.rename("projects/x/y/proofs/T.v", text), text.replace(OLD, NEW))

    def test_a_blob_that_holds_the_name_and_does_not_parse_is_refused(self):
        text = 'ltac2:(KReplay.run1 (kr_t_T ()) [] "(OssFuzzTheorems").\n'
        with self.assertRaises(ns.Error) as e:
            self.rename("projects/x/y/proofs/T.v", text)
        self.assertIn("projects/x/y/proofs/T.v:1: literal 0 (kr_stream)", str(e.exception))

    def test_a_stem_left_in_another_form_is_refused(self):
        """rocq-<old stem> before neither `-`, a blank, `"`, `)` nor the end is not renamed, and is refused rather than
        left for the after-gate, which runs once files are written."""
        with self.assertRaises(ns.Error) as e:
            self.rename("notes/x.md", "see rocq-oss-fuzz-theorems.opam\n")
        self.assertIn("notes/x.md:1: rocq-oss-fuzz-theorems is still there", str(e.exception))

    def test_a_cdef_component_stored_in_pieces_is_renamed(self):
        """A CDef table may store a component in pieces ("OssFuzz", "Theorems"): the file's text then holds no run of
        the name, and the table is read and renamed all the same."""
        table = "2" + "0" + "2" + "7OssFuzz" + "8Theorems" + "4Core" + "01x"
        stream = "10!" + ns.cdef_num(25) + "$0"
        text = ('Local Ltac2 zQ s := CDef.cdeft "%s" s.\n'
                'Lemma a : True. Proof. ltac2:(zQ "%s"). Qed.\n' % (table, stream))
        self.assertNotIn(OLD, text)
        got = self.rename("projects/x/y/proofs/lib/P.v", text)
        fresh = [got[s:e] for s, e, k in ns.literals(got) if k == "cdef_table"][0]
        self.assertEqual(ns.cdef_dir_at(fresh, 0).comps, [NEW, "Core"])
        self.assertEqual(ns.cdef_glob_at(fresh, 25).name, "x")
        self.assertEqual(len(fresh), len(table))

    def test_a_compressed_blob_that_does_not_inflate_is_refused_even_without_the_name(self):
        """Its bytes do not show what it decodes to, so it may hide the name: refused, as rename_tree refuses it."""
        text = 'Ltac2 kr_t_L () := KReplay.lz_vm "####ab!%s%s%s".\n' % (ns._digit(76), ns._digit(4), ns._digit(0))
        with self.assertRaises(ns.Error) as e:
            self.rename("projects/x/y/proofs/lib/L.v", text)
        self.assertIn("projects/x/y/proofs/lib/L.v:1: literal 0 (kr_table_lz)", str(e.exception))

    def test_a_quote_before_the_name_is_no_identifier_character(self):
        """The whole-tree run on the T3 tree (2026-11-01) refused six files for this: a `'` before the name.  A prime
        continues a Rocq identifier only after an identifier character, and is a quote in Python and bash."""
        for rel, line in (
                # projects/libreac/fuzz_ctrl/proofs/lib/A/ACtlCutP.v:102, in a comment
                ("projects/libreac/fuzz_ctrl/proofs/lib/A/ACtlCutP.v",
                 "(* a script:\n     ROOT='OssFuzzTheorems.Proofs.libreac.fuzz_ctrl.'\n*)\n"),
                # projects/reac-repacer/fuzz_uci/proofs/provenance/evidence/core-B/imgtop-require.py:13
                ("projects/reac-repacer/fuzz_uci/proofs/provenance/evidence/core-B/imgtop-require.py",
                 "mod = f'OssFuzzTheorems.Proofs.reac_repacer.{unit}.lib'\n"),
                # tests/check.sh:187
                ("tests/check.sh",
                 "  { (cd \"$B/theories\" && find . -name '*.vo' -printf 'OssFuzzTheorems.Core.%P\\n')\n")):
            self.assertEqual(self.rename(rel, line), line.replace(OLD, NEW), rel)

    def test_a_prime_after_an_identifier_keeps_the_name_in_it(self):
        """`x'OssFuzzTheorems`, `OssFuzzTheorems'`, `\u03b1OssFuzzTheorems` and `\u03b1'OssFuzzTheorems` are other
        Rocq identifiers (a Unicode letter is an identifier character): not renamed, so refused."""
        for text in ("Definition x'OssFuzzTheorems := 0.\n", "Definition OssFuzzTheorems' := 0.\n",
                     "Definition \u03b1OssFuzzTheorems := 0.\n", "Definition \u03b1'OssFuzzTheorems := 0.\n"):
            with self.assertRaises(ns.Error, msg=text):
                self.rename("projects/x/y/proofs/lib/I.v", text)

    def test_an_escaped_quote_in_a_literal_is_read_as_rocq_reads_it(self):
        """projects/plugin-hostd/fuzz_command/proofs/lib/Prog/RecFacts.v:298 holds a literal whose body is
        `resp 0 ""<path>""`; the whole-tree run refused the file because the lexer refused a doubled quote."""
        text = ('From OssFuzzTheorems.Proofs.plugin_hostd.fuzz_command.lib Require Import A.\n'
                'Definition t := [("descriptor_get", "resp 0 ""<path>""");\n   ("track_info", "resp 0")].\n')
        self.assertEqual(self.rename("projects/plugin-hostd/fuzz_command/proofs/lib/Prog/RecFacts.v", text),
                         text.replace(OLD, NEW))

    def test_a_stored_encoding_with_a_quote_is_refused(self):
        text = 'ltac2:(KReplay.run1 (kr_t_T ()) [] "p0%s""o").\n' % kr_entry("I", [OLD, "Core"], "00")
        with self.assertRaises(ns.Error) as e:
            self.rename("projects/x/y/proofs/T.v", text)
        self.assertIn("literal 0 (kr_stream): it holds a quote, which no stored encoding has", str(e.exception))


def proof_tree(t):
    """t, the fixture rendered, with a proof of zlib/checksum_fuzzer/plain_halts in the per-project layout whose
    library holds the four stored encodings of a boost-json file and V23Exit.v's unparsed table, a test script, these
    tools (less their tests: `verify` renders with a tree's own tools) and the two exempt documents, as a git
    repository; its commit."""
    st = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/plain_halts")
    t.put_yaml(PROOF + "/plain_halts/proof.yaml", {"schema": "oss-fuzz-theorems/proof/1",
                                                   "proves": st.id, "fingerprint": st.fingerprint})
    t.write(PROOF + "/plain_halts/Proof.v",
            "From OssFuzzTheorems.zlib.checksum_fuzzer Require Import Statements.\n"
            "From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import T.\n"
            "Theorem holds : True. Proof. exact I. Qed.\n")
    t.write(PROOF + "/lib/T.v", WHOLE_FILE)
    t.write(PROOF + "/lib/V23Exit.v", LEPT_FILE)
    t.write("tests/check.sh", '#!/bin/bash\nstmt_mod="OssFuzzTheorems.Tests.$project.$harness.Statements"\n')
    os.chmod(t.path("tests", "check.sh"), 0o755)     # pr.yml runs it as ./tests/check.sh
    shutil.copytree(os.path.dirname(os.path.abspath(ns.__file__)), t.path("tools", "oft"),
                    ignore=shutil.ignore_patterns("tests", "__pycache__"))
    t.write("docs/versioning.md", "The theories are hashed with the namespace read as `OssFuzzTheorems`.\n")
    t.write("CHANGELOG.md", "- the namespace was OssFuzzTheorems\n")
    assert t.generate() == 0, t.last_output
    return helpers.git_repo(t.root)


PROOF = "projects/zlib/checksum_fuzzer/proofs"


class Tree(unittest.TestCase):
    """`oft rename-namespace --to NAME --opam-stem STEM`: the before-gate, every file staged, nothing written unless
    every one passed, then release.yaml, the opam files, the render and the after-gate."""

    def setUp(self):
        self.t = helpers.Tree()
        self.addCleanup(self.t.close)
        self.first = proof_tree(self.t)

    def run_tool(self, **kw):
        out = io.StringIO()
        code = ns.rename_tree(self.t.root, NEW, NS, out=out, jobs=1, **kw)
        return code, out.getvalue()

    def snapshot(self):
        out = {}
        for rel in self.t.files():
            with open(self.t.path(rel), "rb") as fh:
                out[rel] = fh.read()
        return out

    def test_the_rename_renames_every_file_and_the_gates_pass(self):
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertRegex(out, r"rename-namespace: \d+ file\(s\) renamed \(\d+ encoded literals, 0 dotted-name "
                              r"literals, \d+ plain lines\); 3 blob\(s\) left unparsed \(listed above\); \d+ opam "
                              r"files renamed; 0 problem\(s\)\n$")
        left = subprocess.run(["git", "-C", self.t.root, "grep", "-l", "-e", OLD, "-e", "rocq-" + OS, "--", ".",
                               ":!tools", ":!docs/versioning.md", ":!CHANGELOG.md", ":!README.md", ":!index",
                               ":!projects/*/README.md"], capture_output=True, text=True)
        self.assertEqual((left.returncode, left.stdout), (1, ""))
        lib = self.t.read(PROOF + "/lib/T.v")
        self.assertIn("From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.", lib)
        buf = io.StringIO()
        self.assertEqual(generate.run(self.t.root, check=True, out=buf, shared=False), 0, buf.getvalue())

    def test_the_summary_names_each_unparsed_blob(self):
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertIn("unparsed %s/lib/T.v kr_stream 3\n" % PROOF, out)
        self.assertIn("unparsed %s/lib/V23Exit.v kr_table 0\n" % PROOF, out)
        self.assertIn("unparsed %s/lib/V23Exit.v kr_stream 2\n" % PROOF, out)
        self.assertIn("unparsed in zlib/checksum_fuzzer: 3 blob(s)\n", out)

    def test_check_writes_nothing(self):
        before = self.snapshot()
        code, out = self.run_tool(check=True)
        self.assertEqual(code, 0, out)
        self.assertIn("rename-namespace --check: ", out)
        self.assertEqual(self.snapshot(), before)

    def test_the_exempt_files_are_left_alone(self):
        before = self.snapshot()
        self.assertEqual(self.run_tool()[0], 0)
        after = self.snapshot()
        for rel in ("tools/oft/names.py", "docs/versioning.md", "CHANGELOG.md"):
            self.assertEqual(after[rel], before[rel], rel)

    def test_the_provenance_evidence_is_left_alone(self):
        # libdiginet/fuzz_transport's evidence holds a dump with an encoded literal no codec reads and a script whose
        # regex names the old namespace; renamed, it would record runs that never happened
        dump = PROOF + "/provenance/evidence/fakestack/RULE24-LOOKUP.txt"
        script = PROOF + "/provenance/evidence/srcreloc/relocate.py"
        self.t.write(dump, 'tbl "C3?OssFuzzTheorems6Proofs:boost_json"\n')
        self.t.write(script, "import re\nOLD = re.compile(r'\\bOssFuzzTheorems\\.')\n")
        helpers.git_commit(self.t.root, "evidence of runs made before the rename")
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        after = self.snapshot()
        for rel in (dump, script):
            self.assertEqual(after[rel], before[rel], rel)

    def test_the_stream_tools_are_left_alone(self):
        # dev/stream/ is internal (the release cut removes it): a tool there already names the new namespace by design,
        # and a compiled .glob keeps the old one; neither refuses the rename nor is rewritten
        tool = "dev/stream/lane/tools/test_oft_calls.py"
        glob = "dev/stream/lane/tools/twin-controls/C.glob"
        self.t.write(tool, "NEW = %r\nSTEM = 'rocq-%s'\n" % (NEW, NS))
        self.t.write(glob, "F%s.Proofs.zlib.checksum_fuzzer\n" % OLD)
        helpers.git_commit(self.t.root, "the stream's tools name both namespaces")
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        after = self.snapshot()
        for rel in (tool, glob):
            self.assertEqual(after[rel], before[rel], rel)
        self.assertTrue(ns.exempt("dev/stream/bin/ossv-cuts"))
        self.assertFalse(ns.exempt("dev/streams/x"))
        self.assertIn(":(glob,exclude)dev/stream/**", ns.exclude_pathspecs())

    def test_exempt_reads_a_star_as_one_path_component(self):
        self.assertTrue(ns.exempt("projects/zlib/checksum_fuzzer/proofs/provenance/evidence/a/run.log"))
        self.assertFalse(ns.exempt("projects/zlib/checksum_fuzzer/proofs/provenance/PROVENANCE.yaml"))
        self.assertFalse(ns.exempt("projects/zlib/checksum_fuzzer/proofs/lib/T.v"))
        self.assertFalse(ns.exempt("projects/zlib/proofs/provenance/evidence/run.log"))
        self.assertTrue(ns.exempt("tools/oft/names.py"))
        self.assertTrue(ns.exempt("CHANGELOG.md"))
        self.assertFalse(ns.exempt("CHANGELOG.md.bak"))

    def test_rename_tree_writes_no_shared_file(self):
        for rel in ("README.md", "index/statements.tsv", "projects/zlib/README.md"):
            self.t.write(rel, self.t.read(rel) + "rocq-%s-zlib %s.zlib\n" % (OS, OLD))
        helpers.git_commit(self.t.root, "the shared files name the old stem, as the line's render wrote them")
        before = self.snapshot()
        shared = [rel for rel in before if paths.is_shared(rel)]
        self.assertTrue({"README.md", "index/statements.tsv", "projects/zlib/README.md"} <= set(shared))
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        after = self.snapshot()
        for rel in shared:
            self.assertEqual(after[rel], before[rel], rel)

    def test_rename_tree_writes_nothing_when_one_file_fails(self):
        self.t.write(PROOF + "/lib/Bad.v", 'Ltac2 tbl () := "C3?OssFuzzTheorems:boost_json".\n')
        helpers.git_commit(self.t.root, "a literal no codec reads")
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused %s/lib/Bad.v:1: a string literal holds" % PROOF, out)
        self.assertIn("rename-namespace: 1 problem(s); nothing written\n", out)
        self.assertEqual(self.snapshot(), before)

    def test_a_blob_that_does_not_parse_refuses_the_tree_even_without_the_name(self):
        # an LZ blob is always parsed: its bytes do not show what it decodes to
        self.t.write(PROOF + "/lib/Lz.v", 'Ltac2 kr_t_L () := KReplay.lz_vm "####ab!' + ns._digit(76)
                     + ns._digit(4) + ns._digit(0) + '".\n')
        helpers.git_commit(self.t.root, "a blob that does not inflate")
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused %s/lib/Lz.v:1: literal 0 (kr_table_lz)" % PROOF, out)

    def test_rename_tree_renames_the_opam_files_and_sets_release_yaml(self):
        old_opam = "projects/zlib/rocq-oss-fuzz-theorems-zlib.opam"
        self.assertIn(old_opam, self.t.files())
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        files = self.t.files()
        self.assertNotIn(old_opam, files)
        self.assertIn("projects/zlib/rocq-oss-verify-zlib.opam", files)
        self.assertEqual(facts.read_release_names(self.t.root), (NEW, NS))
        self.assertIn("date: 2026-11-02\nnamespace: OSSVerify\nopam_stem: oss-verify\n", self.t.read("release.yaml"))
        self.assertIn("(name oss-verify)", self.t.read("dune-project"))

    def test_a_second_rename_is_refused(self):
        self.assertEqual(self.run_tool()[0], 0)
        helpers.git_commit(self.t.root, "renamed")
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused release.yaml already names the namespace OSSVerify\n", out)
        self.assertEqual(self.snapshot(), before)

    def test_the_new_name_already_in_the_tree_is_refused(self):
        self.t.write("notes/zlib.md", self.t.read("notes/zlib.md") + "OSSVerify is the new name.\n")
        helpers.git_commit(self.t.root, "the new name, early")
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused notes/zlib.md: already holds OSSVerify or rocq-oss-verify", out)
        self.assertEqual(self.snapshot(), before)

    def test_a_path_holding_the_old_name_is_refused(self):
        self.t.write("notes/OssFuzzTheorems.md", "a note\n")
        helpers.git_commit(self.t.root, "a path with the name")
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused notes/OssFuzzTheorems.md: a path that holds OssFuzzTheorems\n", out)

    def test_a_file_keeps_its_mode(self):
        """tests/check.sh is 100755 and names the namespace; pr.yml runs it as ./tests/check.sh."""
        self.assertEqual(helpers.git(self.t.root, "ls-files", "-s", "tests/check.sh").split()[0], "100755")
        code, out = self.run_tool()
        self.assertEqual(code, 0, out)
        self.assertIn("OSSVerify.Tests", self.t.read("tests/check.sh"))
        self.assertTrue(os.stat(self.t.path("tests", "check.sh")).st_mode & 0o111)
        self.assertEqual(helpers.git(self.t.root, "diff", "--summary", "--", "tests/check.sh"), "")

    def test_a_sparse_checkout_is_refused_and_nothing_is_written(self):
        """A tracked file that is not in the checkout would be left with the old name: the rename refuses the tree
        before it writes anything."""
        os.remove(self.t.path("tests", "check.sh"))
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused 1 tracked file(s) are not in this checkout (a sparse checkout, say), among them "
                      "tests/check.sh: the rename runs on a whole checkout\n", out)
        self.assertEqual(self.snapshot(), before)

    def test_a_checkout_with_changes_that_are_not_committed_is_refused(self):
        """A change to an old-stem opam file that is not committed would make the rename's git rm fail after it wrote
        the staged files: the rename refuses the tree before it writes anything."""
        opam = "projects/zlib/rocq-oss-fuzz-theorems-zlib.opam"
        self.t.write(opam, self.t.read(opam) + "# a local change\n")
        before = self.snapshot()
        code, out = self.run_tool()
        self.assertEqual(code, 1, out)
        self.assertIn("refused 1 tracked file(s) differ from HEAD, among them %s: commit or drop them first" % opam,
                      out)
        self.assertIn("nothing written", out)
        self.assertEqual(self.snapshot(), before)


class Verify(unittest.TestCase):
    """`oft rename-namespace --verify A B`: B compared with the rename of A."""

    def setUp(self):
        self.t = helpers.Tree()
        self.addCleanup(self.t.close)
        self.a = proof_tree(self.t)
        out = io.StringIO()
        self.assertEqual(ns.rename_tree(self.t.root, NEW, NS, out=out, jobs=1), 0, out.getvalue())
        self.b = helpers.git_commit(self.t.root, "the rename")

    def verify(self, b):
        """(problems, files compared, encoded literals decoded)."""
        return ns._verify(self.t.root, self.a, b, jobs=1)

    def change(self, rel, edit):
        helpers.git(self.t.root, "checkout", "-q", self.b)
        self.t.write(rel, edit(self.t.read(rel)))
        return helpers.git_commit(self.t.root, "a change after the rename")

    def test_verify_accepts_the_tool_s_output(self):
        problems, compared, decoded = self.verify(self.b)
        self.assertEqual(problems, [])
        self.assertEqual(ns.verify(self.t.root, self.a, self.b, jobs=1), [])
        self.assertGreaterEqual(compared, 5)
        self.assertEqual(decoded, 3)     # T.v's LZ table, CDef table and CDef stream; every other blob is unparsed
        out = io.StringIO()
        self.assertEqual(ns.verify_cli(self.t.root, self.a, self.b, jobs=1, out=out), 0)
        self.assertRegex(out.getvalue(), r"^verify: \d+ file\(s\) compared, \d+ encoded literals decoded; "
                                         r"0 problem\(s\)\n$")

    def test_verify_names_a_changed_plain_byte(self):
        b = self.change(PROOF + "/plain_halts/Proof.v", lambda s: s.replace("exact I", "exact  I"))
        problems = self.verify(b)[0]
        self.assertEqual(problems, ["%s/plain_halts/Proof.v: is not the rename of %s's blob" % (PROOF, self.a)])

    def test_verify_names_a_changed_decoded_component(self):
        """One component of the renamed LZ table changed, its length kept, and the table compressed again."""
        rel = PROOF + "/lib/T.v"

        def edit(text):
            s, e, _k = [x for x in ns.literals(text) if x[2] == "kr_table_lz"][0]
            plain, entries = ns.check_blob("kr_table_lz", text[s:e])
            entry = [x for x in entries if x.comps and x.comps[0] == NEW][0]
            entry.comps = entry.comps[:-1] + [entry.comps[-1][:-1] + "Q"]
            plain = plain[:entry.start] + entry.render() + plain[entry.end:]
            return text[:s] + ns.lz_deflate(plain) + text[e:]

        b = self.change(rel, edit)
        problems = self.verify(b)[0]
        self.assertEqual(len(problems), 1, problems)
        self.assertRegex(problems[0], r"^%s:\d+: literal 0 \(kr_table_lz\) its entries are not A's renamed$" % rel)

    def test_verify_names_a_file_left_with_the_old_name(self):
        b = self.change("notes/zlib.md", lambda s: s + "OssFuzzTheorems\n")
        problems = self.verify(b)[0]
        self.assertIn("notes/zlib.md: still holds OssFuzzTheorems or rocq-oss-fuzz-theorems in %s" % b, problems)

    def test_verify_names_a_changed_shared_file(self):
        b = self.change("README.md", lambda s: s + "x\n")
        self.assertIn("README.md: a shared generated file differs (the line's render writes it)", self.verify(b)[0])

    def test_verify_names_a_generated_file_that_is_not_its_render(self):
        """A generated file is judged by what B's own tools render from B's facts: here dune-project names the old
        opam stem in its (name ...) line, which no old-name search finds (it has no rocq- before it)."""
        b = self.change("dune-project", lambda s: s.replace("(name %s)" % NS, "(name %s)" % OS))
        self.assertEqual(self.verify(b)[0],
                         ["dune-project: %s's own tools render it otherwise (oft generate --check --skip-shared: "
                          "differs from its rendering)" % b])

    def test_verify_finds_a_fault_the_rename_makes_every_time(self):
        """verify reads A's encodings itself: B made by a rename whose codec also renames Corelib to Corelix (the same
        length, so every gate of the rename passes) is not the rename of A, though the rename makes it every time."""
        helpers.git(self.t.root, "checkout", "-q", self.a)
        real = ns._renamed

        def faulty(comps, old, new):
            comps, hit = real(comps, old, new)
            if comps[:1] == ["Corelib"]:
                return ["Corelix"] + comps[1:], True
            return comps, hit

        with mock.patch.object(ns, "_renamed", faulty):
            out = io.StringIO()
            self.assertEqual(ns.rename_tree(self.t.root, NEW, NS, out=out, jobs=1), 0, out.getvalue())
        b = helpers.git_commit(self.t.root, "a faulty rename")
        problems = ns.verify(self.t.root, self.a, b, jobs=1)
        self.assertTrue(problems)
        self.assertTrue(all(p.startswith(PROOF + "/lib/T.v:") for p in problems), problems)
        self.assertTrue(any("(kr_table_lz) its entries are not A's renamed" in p for p in problems), problems)

    def test_verify_reads_a_file_the_rename_left_that_hides_the_name(self):
        """A file whose compressed table holds the old name only as back-references, which B leaves as A has it: no
        search of B's bytes finds the name, and verify decodes it."""
        table = (kr_entry("C", ["OssFuzzA", "x"]) + kr_entry("C", ["Theorems", "y"])
                 + kr_entry("C", [OLD, "Core", "Shapes"]))
        hide = PROOF + "/lib/H.v"
        helpers.git(self.t.root, "checkout", "-q", self.a)
        self.t.write(hide, 'Ltac2 kr_t_H () := KReplay.lz_vm "%s".\n' % ns.lz_deflate(table))
        a = helpers.git_commit(self.t.root, "a file that hides the name")
        out = io.StringIO()
        self.assertEqual(ns.rename_tree(self.t.root, NEW, NS, out=out, jobs=1), 0, out.getvalue())
        helpers.git_commit(self.t.root, "the rename")
        helpers.git(self.t.root, "checkout", a, "--", hide)
        b = helpers.git_commit(self.t.root, "the rename, with H.v left as it was")
        self.assertEqual(ns.verify(self.t.root, a, b, jobs=1),
                         ["%s: a stored encoding still decodes to %s" % (hide, OLD)])


class ToolFiles(unittest.TestCase):
    def test_only_four_tool_files_name_the_old_namespace(self):
        """names.py (NAMESPACE_DEFAULT), facts.py (FINGERPRINT_NAMESPACE), nsrename.py (OLD_DEFAULT) and lint.py (the
        finding's message): every other name in the tools comes from release.yaml."""
        if not os.path.isdir(os.path.join(helpers.REPO, ".git")) and not os.path.isfile(
                os.path.join(helpers.REPO, ".git")):
            self.skipTest("no git checkout beside tools/oft")
        got = subprocess.run(["git", "-C", helpers.REPO, "grep", "-l", OLD, "--", "tools", ":!tools/oft/tests",
                              ":!tools/enroll/tests"], capture_output=True, text=True).stdout.split()
        self.assertEqual(sorted(got), ["tools/oft/facts.py", "tools/oft/lint.py", "tools/oft/names.py",
                                       "tools/oft/nsrename.py"])
        self.assertEqual(ns.OLD_DEFAULT, names.NAMESPACE_DEFAULT)


if __name__ == "__main__":
    unittest.main()
