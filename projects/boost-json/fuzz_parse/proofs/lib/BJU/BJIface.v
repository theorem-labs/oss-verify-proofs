(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat46Stdlib6ZArith6BinInt1Zja3add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~l8cROPDEL_STACKja3mulja6of_natl83ehkl8cROPNEW_STACKl88eh_STACK79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface~~~~~~tabRDTOR_STACKja3max04Npos35stdpp9bitvectorbdefinitionshj22bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hl53mem37Corelib4Init5Logichq73andja2lehj2bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ht65rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ihc4cellhc4conshc3nilhq72eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU5BJRep~~~~~~in3abj_statics69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ird5hceilihc2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~jg74frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jk83stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~job7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jt08rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kh72wzl87eh_idlel8bhs_rauxv_okhl54RATPja3powja3subhq72exhc4listl85framehq75Falsel88chain_spl8beh_chain_okl8bfr_callsite3h5LinuxProcessSemanticsfLinuxProcessSem3Runks96config3h5LinuxProcessSemanticsfLinuxProcessSem5Statekvf5Model3h5LinuxProcessSemantics5Riscv7Preludelj65bvmaphl55blockhc6optionks99cfg_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~lo46PStatehc4None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslt1dmachine_stateks96cfg_ms89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface5Iface~~~~~~mi3h0bj_env_post_corejk83mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mo32MSmo36ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mt07seg_roml87hs_KRELl88hs_MPRESl88hs_RHEAPhl5arheap_presin37jheighthc3app37Corelib4Init5Peanonl92leks95mkCfgmi3bbj_env_coremi3fdtor_value_posttabRDTOR_VALUEin38blocks_vin32jvin36val_atl85hs_SRhl5drclient_rangehc4prodhc4pairmi34vs_Xihcacells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~og55xpresin37vs_tempin36vsitem37Corelib5Lists7ListDefom26Forallmi3eRDTOR_VS_STACKmi3cdtor_vs_postta8RVS_DTORin39blocks_vsin3bitem_heightin35vs_atin38vs_itemsin36vstackja2ltmi3bbj_env_postin36vs_capin38vs_charsin34vs_nlt16ms_meml86EH_IVSl84eh_Xhq73iffin34Jarrin35VSvalin3bjvs_of_listin36vs_bufhq72orhc4Somehc6lengthmi36bj_envmi38chain_atmi3fpush_array_postmi3epush_array_unwmi36vsvalstacRVS_PUSH_ARRtah2RVS_PUSH_ARR_STACKl83csrl87fr_livel85mkCSRl8bsaves_clearja6moduloin33kvshc3sndin34Jobjin3akvs_heighthl58blk_addrjob8bytes_athl58blk_size36Stdlib5Lists4Listqle2Inin36pstatein35ps_vsin36ps_endin38ps_depthhc4boolin37ps_morehc5false37Corelib4Init3Natqra3addmi37junk_okmi38parser_Xin39parser_atin38ps_ecsetja6to_natmi38input_okmi3h0parse_value_postmi3fparse_value_unwmi3h5parse_value_stmt_at_din35VSkeymi39RPV_STACKmi3eparse_key_posttacRP_KEYSTRINGmi39any_firstta8RP_VALUEta8RP_ARRAYta9RP_OBJECTmi3h3parse_value_stmt_atta9RP_STRINGmi39RPN_STACKta7RP_NUM0ta9RP_NUMNEGta9RP_NUMPOSta7RP_NULLta7RP_TRUEta8RP_FALSEmi3h2parse_value_stmt_dmi3h2parse_array_stmt_dmi3h3parse_object_stmt_dmi3h0parse_array_stmtmi3h1parse_object_stmtmi3h0parse_value_stmtl83hmf" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RDTOR_VALUE   : Z := 0x56fec.   (* [comment removed for export] *)
Definition RVS_DTOR      : Z := 0x59738.   (* [comment removed for export] *)
Definition RVS_MAYBEGROW : Z := 0x5b584.   (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RVS_PUSH_ARR  : Z := 0x59864.   (* [comment removed for export] *)
Definition RUA_DTOR      : Z := 0x599f4.   (* [comment removed for export] *)
Definition RVS_PUSH_OBJ  : Z := 0x59acc.   (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RVS_PUSH_CHARS: Z := 0x6683c.   (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RVS_PUSH_STR  : Z := 0x59dc8.   (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RSTR_RESERVE  : Z := 0x56cdc.   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RPARSER_REL   : Z := 0x4ec78.   (* [comment removed for export] *)
Definition RBP_DTOR      : Z := 0x4ee18.   (* [comment removed for export] *)
Definition RDS_DTOR      : Z := 0x5a728.   (* [comment removed for export] *)
Definition RWRITE_SOME   : Z := 0x4fc44.
Definition RP_DOCUMENT   : Z := 0x5d4d4.   (* [comment removed for export] *)
Definition RP_VALUE      : Z := 0x5dcc0.   (* [comment removed for export] *)
Definition RP_MSUSPEND   : Z := 0x5dbec.   (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_NULL       : Z := 0x5e570.
Definition RP_TRUE       : Z := 0x5e724.
Definition RP_FALSE      : Z := 0x5e8fc.
Definition RP_FAIL       : Z := 0x5eaa4.   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RP_STRING     : Z := 0x5eeb0.   (* [comment removed for export] *)
Definition RP_ARRAY      : Z := 0x5f1b4.
Definition RP_OBJECT     : Z := 0x5f4e8.
Definition RP_NUM0       : Z := 0x5f97c.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_NUMNEG     : Z := 0x61464.   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RP_NUMPOS     : Z := 0x638bc.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RP_KEYSTRING  : Z := 0x66a10.   (* [comment removed for export] *)   (* [comment removed for export] *)
Definition RJSON_PARSE   : Z := 0x4e79c.   (* [comment removed for export] *)
Definition RFUZZ_PARSE   : Z := 0x47484.
Definition RLLVM_FUZZ    : Z := 0x47534.   (* [comment removed for export] *)
Definition RMEMCPY : Z := 0xee250.  
 

(* [comment removed for export] *)
Definition RDTOR_STACK : ltac2:(zQ "20!j4!h9>1h$0$1") := ltac2:(zQ "50!l2!j4!pc!qb!r1\1h$1@2$0@2$0@2$3+n0@1$4^1+h0$2").   (* [comment removed for export] *)
Definition RVS_GROW_STACK : ltac2:(zQ "20!h9!ra>1E$1$0") := ltac2:(zQ "40!l2!s0!sf!ra\1E$3@2$0@2$0+j0$1@1$2^1").     (* [comment removed for export] *)
Definition RVS_PUSH_STACK : ltac2:(zQ "20!h9!ra>1E$1$0") := ltac2:(zQ "40!l2!s0!sf!ra\1E$3@2$0@2$0+m0$1@1$2^1").     (* [comment removed for export] *)
Definition RVS_PUSH_ARR_STACK : ltac2:(zQ "20!h9!ra>1E$1$0") := ltac2:(zQ "60!l2!hh8!s0!sf!ra!hi6\1E$4@2$0+l0@2$5@2$0@2$0+k0$2@1$3^1@2$0+j0@1$1Ni1").   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!sr8$0").
  Variable E : ltac2:(zQ "10!ra$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).

  (* [comment removed for export] *)
  Definition bj_env : ltac2:(zQ "40!hic!hkf!h9!hq0>1m$3>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2lo$2>1B$2>6budget$2>4errv@1$1@1$0#k0>2fc@1$1@1$0#i0P") := ltac2:(zQ "ha0!hrb!hic!hkf!hs2!hs7!h9!ih3!il8!im0!im7!imd!iqf!iv8!jg1!jk0!jo4!js5!kgb!kl2!kl8!km2!kn0!hq0!l2!kn8!kne\1m$h6\2sp@1$2@1$1#k0\2tp@1$2@1$1#k0\2lo$5\1B$5\6budget$5\4errv@1$2@1$1#k0\2fc@1$2@1$1#i0@2$0@3$h4?1H^8^4@2$0@2$0@2$3@2$4@1$1#k0^7^4@2$3^4@2$h8+2+k0@2$0@4$f$6^8^5@2$4@1$1#k0^7@2$0@2$3@1$c?5HCEIL^5@2$0@2$3^5@2$h9@2$4@1$1#k0^7^3@2$0@4$h1$6^8@2$h7@2$4@1$1#k0^6-q4@3$8$7@1$d^2@1$9$7@2$0@2$h0$6^8@2$0@3$a@1$2@1$1#k0^6@1$h2$h5@2$0@1$b^8@2$0@2$h3?1E^8@1$e^1").                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bj_env_post : ltac2:(zQ "40!hic!h9!hkf!hq0>2m'$3>2sp@1$2@1$0#k0>2tp@1$2@1$0#k0>2lo$1>1B$1P") := ltac2:(zQ "h30!hic!hrb!hkf!ih3!h9!il8!hs7!im0!im7!ko4!iqf!jg1!jo4!js5!kgb!kl8!km2!hq0!l2\2m'$h1\2sp@1$2@1$0#k0\2tp@1$2@1$0#k0\2lo$4\1B$4@2$1@3$h0?1H^5^1@2$1@4$c$3^5^2@2$6@1$0#k0^4@2$1@2$9@1$2@1$0#k0\5errv'@1$2@1$0#k0@4$e$3^6@2$h2@2$6@1$0#k0^4-q4@3$7$5@1$b^1@1$8$5@2$1@2$d$3^5@2$1@1$a^5@2$f?1E^5").
  (* [comment removed for export] *)
  Definition bj_env_core : ltac2:(zQ "40!hic!hkf!h9!hq0>1m$3>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2lo$2>1B$2>6budget$2>4errv@1$1@1$0#k0>2fc@1$1@1$0#i0P") := ltac2:(zQ "h80!hrb!hic!hkf!hs2!hs7!h9!ih3!il8!im0!im7!imd!iqf!iv8!jg1!jo4!js5!kgb!kl2!km2!kn0!hq0!l2!kn8!kne\1m$h4\2sp@1$2@1$1#k0\2tp@1$2@1$1#k0\2lo$5\1B$5\6budget$5\4errv@1$2@1$1#k0\2fc@1$2@1$1#i0@2$0@3$h2?1H^8^4@2$0@2$0@2$3@2$4@1$1#k0^7^4@2$3^4@2$h6+2+k0@2$0@4$e$6^8^5@2$4@1$1#k0^7@2$0@2$3@1$c?5HCEIL^5@2$0@2$3^5@2$h7@2$4@1$1#k0^7^3@2$0@4$h0$6^8@2$h5@2$4@1$1#k0^6-q4@3$8$7@1$d^2@1$9$7@2$0@2$f$6^8@2$0@3$a@1$2@1$1#k0^6@1$h1$h3@1$b^8").
  (* [comment removed for export] *)
  Definition bj_env_post_core : ltac2:(zQ "40!hic!h9!hkf!hq0>2m'$3>2sp@1$2@1$0#k0>2tp@1$2@1$0#k0>2lo$1>1B$1P") := ltac2:(zQ "h20!hic!hrb!hkf!ih3!h9!il8!hs7!im0!im7!ko4!iqf!jg1!jo4!js5!kgb!km2!hq0!l2\2m'$h0\2sp@1$2@1$0#k0\2tp@1$2@1$0#k0\2lo$4\1B$4@2$1@3$f?1H^5^1@2$1@4$c$3^5^2@2$6@1$0#k0^4@2$1@2$9@1$2@1$0#k0\5errv'@1$2@1$0#k0@4$e$3^6@2$h1@2$6@1$0#k0^4-q4@3$7$5@1$b^1@1$8$5@2$1@2$d$3^5@1$a^5").

  (* [comment removed for export] *)
  Definition chain_at : ltac2:(zQ "50!hic!hkf!koa!kp1!hq0>1G@1$2$3>1m$4>2sp@1$1@1$0#k0>2ra@1$1@1$0#k0P") := ltac2:(zQ "f0!koa!hic!kp1!hkf!hrb!imd!kp9!h9!kl2!kq2!kqd!krb!hq0!l2!hs7\1G@1$0$2\1m$c\2sp@1$3@1$1#k0\2ra@1$3@1$1#k0@2$4@3$a?1E^4^3@2$4@3$5$7@1$9^4@2$e@1$1#k0^2M0\1G@1$0$2P^4$6\1g$2\1l@1$0$2@3$5@1$3@1$1#k0^3@1$8@2$d@1$b^2+4").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dtor_value_post : ltac2:(zQ "90!hic!hkf!h9!koa!kv5!lid!llc!lm5!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$7>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "hd1!hic!hkf!ko4!hrb!lme!h9!ln7!ls0!lsa!koa!imd!mg8!mh9!kv5!lid!llc!mm7!mnc!ms0!ms6!ngf!nha!ni4!nif!lm5!hq0!nja!ih3!hs7&>0@1$1@1$0#k0@1$4@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$f@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$h8\2lo$5\1B$5\1m$h9\2mo$e\1c$d@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$7\2s'$7@2$3@3$a$b@1$c^h2@7$h2@hf$h1^i9^i8^i7^i6^h1^h0^f^i5^i4^e^d^c^b^a^9^8^7^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^6^5^4^3^h9@1$h3^i9^h8@1$8@1$1@1$0#k0^2@1$h4$hb@2$3@3$h5?1H^1@1$6^h2@2$3@3$h6?1H^h3@1$6^h2@2$3@4$h7?1H^1^h7^2@2$3@5$h0^2^i8^i6^h6^h5@4$ha^h7@2$hc@1$0#k0^i8^h4^2").

  Definition dtor_value_stmt : ltac2:(zQ "00P") := ltac2:(zQ "hf0!hic!hkf!hs7!h9!nk8!lm5!lsa!nl3!koa!nmd!nn3!lid!llc!nnc!nob!hh8!npe!nqc!nr8!nre!mnc!ms0!ngf!kl2!nha!nif!ns8!hq0!nt0!ih3!ls0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hb>1s$he>4REST@1$8$5>1v$h2>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$b>0@4$h9?1H^7@3$7$5@1$h1^5^6^8>0@3$h8?1H^8^2>0@8$d^a^ia^i8^6^5@1$f@1$4^7^4^b>0@4$h3?5HCEIL^b@2$2@1$0#k0^i3^8>0@2$9@1$4^9Ni1>0@4$hc^b@2$2@1$0#k0^id@2$2@1$0#k0^i5+h8@3$ha?1H@h7$e^if^ie^id^ic^i8^i7^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h0^f^c^a^9^e^7@2$a@7$h5@hf$h4^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0@1$h7$h0^f@1$6@1$1@1$0#k0^e@1$h6$hd^7").

  (* [comment removed for export] *)
  (* [comment removed for export] *)   (* [comment removed for export] *)
  Definition vs_X : ltac2:(zQ "30!h9!koa!nu1>2va$0@1$1@2$2$0$0") := ltac2:(zQ "60!h9!nu1!im0!im7!nu8!l2\2va$0@3$2@2$1$0$0@4$4$0$0^1@2$5^1+k0@1$3@2$1$0$0").

  (* [comment removed for export] *)
  Definition RDTOR_VS_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!hh8!l2@2$1+i0@1$0Ni1").
  Definition dtor_vs_post : ltac2:(zQ "90!hic!hkf!h9!koa!kv5!lid!llc!lm5!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$7>2va$2>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "i21!hic!hkf!ko4!hrb!h9!koa!lme!imd!ln7!il8!ih3!ls0!lsa!mg8!mh9!kv5!lid!llc!mm7!nuf!nv7!mnc!ms0!ms6!ngf!kgb!ok4!nha!ni4!nif!lm5!hq0!r1!hs7&>0@1$1@1$0#k0@1$6@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h1@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$5$he\2va$4\2lo$4\1B$4\1m$hf\2mo$h0\1c$f@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$b\2s'$b@2$3@3$7$d@1$e^h2@7$h6@hf$h5^ia^i9^i8^i7^h1^h0^f^i6^i5^e^d^c^b^a^9^8^7^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@1$h7^ia^h9@1$c@1$1@1$0#k0^2@1$h8$a@2$3@3$hb?1H^1@1$8^h2@2$3@3$hc?1H^h3@1$8^h2@2$3@4$hd?1H^1^h8^2@2$3@5$h2^2^i9^i7^h6^h5@2$3@5$ha^h8@2$i1@1$0#k0^i9@1$h3^h7^h4^2@2$2@1$5$9\2cs@1$5$9@2$3@4$h9$a^3^h8^1@3$7$4@1$i0@1$h4^1+k0").   (* [comment removed for export] *)
  Definition dtor_vs_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i80!hic!hkf!hs7!hs2!hrb!h9!okd!ol8!lm5!lsa!nl3!koa!nmd!on9!nn3!lid!llc!oo3!nnc!op5!oq5!or0!ord!osc!ot5!ou1!iv8!mnc!ms0!ngf!kl2!nha!nif!ns8!hq0!ih3!ls0!l2!oub!kn8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i2>1s$i4>4REST@1$b$8>2st$h9>2lo$5>1B$5>4errv@1$1@1$0#k0>2mo$f>0@4$i0?1H^7@3$a$8@1$h5^5^6^8>0@3$hf?1H^8^2>0@8$h2^a^ia^i8^6^5$h1^4^b>0@4$h7?5HCEIL^b@2$2@1$0#k0^i3^8>0@3$d$7\2it$7@2$c@1$h6^1Ni1@1$h8^9>0@2$4@2$3@2$2@1$0#k0^id@2$2@1$0#k0^i5@2$3@2$i5@2$2@1$0#k0^i5+k0^8>0@2$4@2$3@1$ha?5HCEIL@1$6^b@2$i6@1$6^b@2$i7+2+k0@3$i1?1H@h8$h3^j0^if^ie^id^i9^i8^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h1^h0^d@2$2@1$0#k0^i7^b^a^f^8@2$e@7$hc@hf$hb^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1@1$he$h4^h0@1$9@1$1@1$0#k0^f@1$hd$i3^8").

  Definition maybe_grow_post : ltac2:(zQ "a0!hic!hkf!h9!koa!kv5!lid!llc!ou1!lm5!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2va$2>2st$7>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "i91!hic!hkf!ko4!hrb!h9!imd!ou1!koa!lme!ln7!ot5!okd!lm5!ls0!lsa!nl3!mg8!mh9!kv5!lid!llc!ov0!nuf!or0!osc!ovf!pg9!ph5!ol8!mnc!ms0!ms6!ngf!ok4!nha!ni4!nif!hq0!ih3!oub!hs7&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h4@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$7$c\2va$4\2st$6\2lo$4\1B$4\1m$i5\2mo$h3\1c$h2@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$d\2s'$d@2$2$6\3st'$6@2$3@3$5$h0@1$h1^h3@7$he@hf$hd^ic^ib^ia^i9^h2^h1^h0^i8^i7^f^e^d^c^b^a^9^8^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^7^6^5^4^hc@1$hf^ic^hb@1$e@1$1@1$0#k0^3@1$i0$i6@2$3@3$i2?1H^2@1$9^h3@2$3@3$i3?1H^h4@1$9^h3@2$3@4$i4?1H^2@3$f$c@1$h7^1^ha^3@2$3@4$h8?5HCEIL^3^h9^1@2$3@3$5@1$7$hc@1$a^1@1$a^h8@2$3@3$5$4@1$ha^1Z@2$3@3$5$4@1$b^1@1$b^h8@2$3@2$i7@1$hb^1@1$h9^1@2$3@5$h5^3^ib^i9^h7^h6@5$i1^ha@2$i8@1$0#k0^ib@1$h6^h9^h5^3").

  (* [comment removed for export] *)
  Definition maybe_grow_unw : ltac2:(zQ "a0!h9!koa!hic!hkf!kv5!lid!ou1!kp1!lm5!hq0>2sp@1$3@1$2#k0>1G@1$1$7>4REST@1$1$8>2va$0>2st$6>2lo$0>1B$0>2fc@1$3@1$2#i0>1m$9>2mo$5>0$4P") := ltac2:(zQ "hb0!h9!hrb!hic!phd!mh9!nl3!koa!lm5!ls0!hkf!nu1!ko4!ln7!kv5!lid!nuf!iqf!or0!osc!ou1!ok4!pi7!pj0!kp1!ni4!hq0!hs7\2sp@1$9@1$2#k0\1G@1$6$h7\4REST@1$6$7\2va$0\2st$h3\2lo$0\1B$0\2fc@1$9@1$2#i0\1m$h9\2mo$e\1c$d@2$b$8\2s'$8@2$1@8$h6?1E^b^1@3$5$7@1$h1^8^a^7^6^5^2@2$1@3$h8?1H^3@1$c^2@2$1@4$h2?5HCEIL@1$3@1$4^2^9^8@2$1@1$h0@1$3@1$4^2@5$h4^a@2$ha@1$2#k0^c@3$5@2$a$0$0@1$f^9$h5^4@1$3@1$4^2").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint vsvals (l : list vsitem) : option (list jv) :=
    match l with
    | [] => Some []
    | VSval v :: r => match vsvals r with Some vs => Some (v :: vs) | None => None end
    | VSkey _ :: _ => None
    end.

  Definition push_array_post : ltac2:(zQ "c0!hic!hkf!koa!h9!kv5!lid!llc!nr8!ol8!ou1!lm5!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$2$a>2va$3>2st$9>4keep@1$2$8>2es@1$2$7>2lo$3>1B$3>1m$b>2mo$5>0$4P") := ltac2:(zQ "id1!hic!hkf!ko4!hrb!h9!imd!lm5!koa!lme!ol8!nr8!ou1!lsa!nl3!im7!ln7!okd!ls0!im0!pj7!mg8!mh9!kv5!lid!llc!ov0!nuf!pje!pk6!or0!pkf!osc!pg9!ot5!mnc!ms0!ms6!ngf!ok4!nha!ni4!nif!hq0!ih3!hs7&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$7$6\2va$4\2st$b\4keep@1$7$9\2es@1$7$a\2lo$4\1B$4\1m$ia\2mo$h7\1c$h6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h1\2s'$h1@2$2$b\3st'$b@2$2@1$8$6\1t@1$8$6@2$2$4\3cap$4@2$3@3$5$h4@1$h5^h5@7$i3@hf$i2^j0^if^ie^id^h4^h3^h2^ic^ib^h1^h0^f^e^d^c^b^a^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^9^8^7^6^i0@1$i4^j0^hf@1$c@1$1@1$0#k0^5@1$i5$ib@2$3@3$i7?1H^4@1$f^h5@2$3@3$i8?1H^h6@1$f^h5@2$3@4$i9?1H^4@3$d$6@1$hd^3^he^5@2$3@4$hf?5HCEIL^5^hd^3@2$3@3$5@1$7$9@1$i1^3@3$d$9^hb@3$h2$9@1$hc@3$hb^2^1@1$he^ha@1$e$9@2$3@3$5$4@1$i0^3Z@2$3@3$5$4@1$h0^3@1$h0^hc@2$3@2$h3@3$5@1$7$a^ha@1$e$a@3$5@1$8$6^2@1$c$6@2$3@5$h9^5^if^id^h9^h8@5$i6^he@2$ic@1$0#k0^if@1$ha^hd^h7^5").

  (* [comment removed for export] *)
  Definition push_array_unw : ltac2:(zQ "b0!koa!h9!hic!hkf!kv5!lid!ol8!ou1!kp1!lm5!hq0>2sp@1$3@1$2#k0>1G@1$0$8>4REST@1$0$9>2va$1>2st$7>4keep@1$0$6>2lo$1>1B$1>2fc@1$3@1$2#i0>1m$a>2mo$5>0$4P") := ltac2:(zQ "i40!hrb!h9!imd!koa!hic!phd!mh9!ot5!ol8!ou1!lm5!nl3!ko4!ple!ovf!okd!ls0!hkf!lme!nu1!pm8!ln7!kv5!lid!nuf!iqf!or0!osc!pg9!ok4!pi7!pj0!kp1!ni4!hq0!hs7\2sp@1$h1@1$4#k0\1G@1$3$i0\4REST@1$3$a\2va$1\2st$9\4keep@1$3$8\2lo$1\1B$1\2fc@1$h1@1$4#i0\1m$i2\2mo$h7\1c$h6@2$c$h0\2s'$h0@2$c$9\3st'$9@2$0@8$hf?1E^d^2@3$b$a@1$ha^1^c^8^7^6^3@2$0@3$i1?1H^4@1$h5^3@2$0@4$hb?5HCEIL@1$5@1$6^3^b^1@2$0@1$h9@1$5@1$6^3@2$0@2$h4@3$2@1$3$8@1$7^1^9@3$2@1$3$8@1$7^1@1$7^a@2$0@3$2$1@1$hc^1Z@2$0@3$2$1@1$f^1@1$f^a@2$0@3$2@1$h2$a@1$d^1@1$d^a@2$0@3$2$1@1$e^1@1$e^a@5$hd^c@2$i3@1$4#k0^e@3$b@2$h3$1$1@1$h8^b$he^5@1$5@1$6^3").

  Definition push_array_stmt : ltac2:(zQ "00P") := ltac2:(zQ "jd0!hic!hkf!koa!hs7!imd!nr8!ol8!kp1!h9!im0!hs2!nl3!hrb!okd!kl2!lm5!l2!oub!kn8!lsa!pme!pn5!lme!pm8!nmd!on9!kv5!nn3!lid!llc!pne!po8!pp4!pq7!nuf!pr9!ps3!pt2!or0!nk8!osc!pg9!ot5!ph5!ou1!iv8!mnc!ms0!ngf!pu8!pue!nha!nif!ns8!pv8!qg0!hq0!ih3!ls0!qge!r1>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hd@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j8>1s$ja>4REST@1$2$f>2st$ic>2lo$8>1B$8>4errv@1$1@1$0#k0>2mo$hc>1g$7>1G@1$2$7>4keep@1$2$6>3top@1$2$6>2es@1$2$5>0@4$j4?1H^c@3$b$f@1$i6^a^b^d>0@3$j3?1H^d^7>0@8$he^f^if^id^b^a@1$i5?1E^9^h0>0@4$i8?5HCEIL^h0@2$3@1$0#k0^i8^d>0@3$4$8@1$i9^eZ>0@3$4@1$2$6@1$ia^f@3$b$6^8^7>0@3$4@1$h6@1$2$5@1$i3^8@2$h4@1$2$5^7>0@3$4@1$1@1$0#k0^ib@1$e@1$jc@2$h5$6^9>0@3$h9$5\1v$5@2$h8@1$i7^1Ni0^9>0@2$h1@2$h0@1$ib^h3+1@2$h2+2+ha>0@2$c@2$a@2$3@1$0#k0^j7@2$3@1$0#k0^if@2$a@2$h0@2$3@1$0#k0^if+k0^h2>0@2$c@2$a@1$id?5HCEIL@1$d^h5@2$h1@1$d^h5@2$h2+2+k0>0@4$hf@3$9$7^h1^h0^h9^j9^ja>0@3$4$j1@1$j2^h2@d$j6^ja^j4^j3^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1>0@3$j7?1E@3$9$7^h3^h2@1$i2@2$3@1$0#k0^j3>0@3$4$8@2$jb@2$3@1$0#k0^j4+8Z@3$j5?1H\1c$ha@2$h7@hc$i0^jf^je^jd^jc^j8^j7^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i0^hf^hc@2$3@1$0#k0^j6^hb^h4^h2^ha^h9^he^h7^1@c$i1^je@3$9$7^h6^h5^hc@2$3@1$0#k0^j6^hb^h4^ha^h9^hf^he^h7^1@2$hb@7$if@hf$ie^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf@1$e$i4^he@1$h3@1$1@1$0#k0^hd@1$j0$j9^h6").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint vskvs (l : list vsitem) : option (list (block * jv)) :=
    match l with
    | [] => Some []
    | VSkey b :: VSval v :: r => match vskvs r with Some kv => Some ((b, v) :: kv) | None => None end
    | _ => None
    end.
  Definition RVS_PUSH_OBJ_STACK (E : ehk) : Z := 400 + ROPNEW_STACK + eh_STACK E + RDTOR_STACK 33.

  Definition push_object_post : ltac2:(zQ "d0!hic!hkf!koa!h9!lm5!nu1!kv5!lid!llc!nr8!ol8!ou1!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$8@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$2$4>2va$3>2st$b>4keep@1$2$a>3kvl@1$2@2$5$4$9>2lo$3>1B$3>1m$c>2mo$7>0$6P") := ltac2:(zQ "j41!hic!hkf!ko4!lm5!hrb!h9!imd!nr8!koa!lme!nu1!ol8!ou1!lsa!nl3!im7!nmd!ln7!qh7!okd!ls0!im0!j4!qhe!pj7!on9!mg8!mh9!kv5!lid!llc!ov0!nuf!qi4!pk6!or0!nk8!qic!osc!pg9!ot5!mnc!ms0!ms6!ngf!ok4!nha!ni4!nif!hq0!ih3!hs7&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$he@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$8$3\2va$5\2st$c\4keep@1$8$b\3kvl@1$8@2$a$3$7\2lo$5\1B$5\1m$j1\2mo$hd\1c$hc@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h4\2s'$h4@2$2$c\3st'$c@2$2@1$9$3\1t@1$9$3@2$2$5\3cap$5@2$2$h2\2ss$h2@2$4@3$6$ha@1$hb^h6@7$ia@hf$i9^j1^j0^if^ie^h5^h4^h3^id^ic^h2^h1^h0^f^e^d^c^b^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^a^9^8^7^i1@1$ib^j1^i0@1$d@1$1@1$0#k0^6@1$ic$j2@2$4@3$ie?1H^5@1$h1^h6@2$4@3$if?1H^h7@1$h1^h6@2$4@4$j0?1H^5@3$e$3@1$i3^4^hf^6@2$4@4$i6?5HCEIL^6^he^4@2$4@3$6@1$8$b@1$i8^4@3$e$b^hc@3$h5$b@1$i2@3$i1^3^2^1@1$f$b@2$4@3$6$5@1$i7^4Z@2$4@3$6$5@1$h3^4@1$h3^hd@2$4@2$h8@3$6@1$8@2$a$3$7^hb@1$f@2$a$3$7@3$6@1$9$3^3@1$d$3@2$4>1h$h6>0@3$h9@2$a$3$7\2bv@2$a$3$7@2$h0@1$i4@3$h7$3$7^1^2^hc@2$h0@1$i5^3^2@2$4@5$hf^6^j0^ie^ha^h9@5$id^hf@2$j3@1$0#k0^j0@1$i0^he^h8^6").

  Definition push_object_unw : ltac2:(zQ "b0!koa!h9!hic!hkf!kv5!lid!ol8!ou1!kp1!lm5!hq0>2sp@1$3@1$2#k0>1G@1$0$8>4REST@1$0$9>2va$1>2st$7>4keep@1$0$6>2lo$1>1B$1>2fc@1$3@1$2#i0>1m$a>2mo$5>0$4P") := ltac2:(zQ "i10!hrb!h9!koa!imd!hic!phd!mh9!ot5!ol8!ou1!nl3!ko4!okd!lm5!ls0!hkf!nu1!pm8!ln7!kv5!lid!nuf!iqf!or0!osc!pg9!ok4!pi7!pj0!kp1!ni4!hq0!hs7\2sp@1$f@1$4#k0\1G@1$2$hd\4REST@1$2$d\2va$1\2st$9\4keep@1$2$8\2lo$1\1B$1\2fc@1$f@1$4#i0\1m$hf\2mo$h4\1c$h3@2$b$e\2s'$e@2$b$9\3st'$9@2$0@8$hc?1E^d^2@3$a$d@1$h7^1^c^8^7^6^3@2$0@3$he?1H^4@1$h2^3@2$0@4$h8?5HCEIL@1$5@1$6^3^b^1@2$0@1$h6@1$5@1$6^3@2$0@2$h1@3$3@1$2$8@1$7^1^9@3$3@1$2$8@1$7^1@1$7^a@2$0@3$3$1@1$h9^1Z@2$0@3$3$1@1$c^1@1$c^a@5$ha^c@2$i0@1$4#k0^e@3$a@2$h0$1$1@1$h5^b$hb^5@1$5@1$6^3").

  Definition push_object_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (REST : list block) (st : vstack) (lo B : Z) (errv : word)
           (mo : Model) (g : frame) (G : list frame) (keep top : list vsitem) (kvl : list (block * jv)),
      RHEAP s (blocks_vs st ++ REST) m -> KREL s mo ->
      bj_env m sp tp lo B (RVS_PUSH_OBJ_STACK E) errv fc ->
      vs_at m (bv_unsigned a0) st -> vs_chars st = 0 ->
      vs_items st = keep ++ top -> vskvs top = Some kvl -> a1 = wz (Z.of_nat (length kvl)) ->
      Forall (fun bv => (jheight (snd bv) <= 32)%nat) kvl ->
      vs_n st + 1 < 2^26 ->
      bv_unsigned sp <= bv_unsigned a0 /\ bv_unsigned a0 + 64 <= B -> hceil <= vs_temp st < 2^64 ->
      chain_at (g :: G) m sp ra -> fr_live g = mkCSR sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
      saves_clear E (g :: G) (vs_X (bv_unsigned a0)) ->
      bv_unsigned a0 mod 8 = 0 ->                                             (* [comment removed for export] *)
      SR (fun c =>    push_object_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc REST (bv_unsigned a0) st keep kvl lo B m mo c
                   \/ push_object_unw sp (g :: G) REST (bv_unsigned a0) st keep lo B fc m mo c)
         (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz RVS_PUSH_OBJ) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition input_ok : ltac2:(zQ "60!h9!koa!hic!lm5!hq0!hkf>4REST@1$1$3>2sp@1$5@1$2#k0>1m$4>2p0$0>3len$0P") := ltac2:(zQ "h50!hrb!hic!h9!lm5!hkf!koa!l2!hs2!imd!ko4!qja!pn5!pm8!qk6!ql2!hq0!ih3!qn1!oub!r1!kn8\4REST@1$5$3\2sp@1$4@1$1#k0\1m$f\2p0$2\3len$2@2$0@2$9@1$5@1$4@1$1#8\2bs@1$5@1$4@1$1#8@2$0@3$8$2@1$h3@2$b@1$4@1$1#8^1^2@4$d$h0^4^3^1@2$0@2$c@3$8$2^1Z@2$9$3\1b$3@2$0@3$h1$3^1^6@2$0@2$7@1$a^1^3@2$7@2$6^3^2@2$6@1$a^1@1$e^1@2$0@2$7Z^2@2$h2@2$6^2^1@2$h4+2+if").          (* [comment removed for export] *)

  Definition parser_X : ltac2:(zQ "30!h9!koa!nu1>2pa$0@1$1@2$2$0$0") := ltac2:(zQ "60!h9!nu1!im0!im7!nu8!l2\2pa$0@3$2@2$1$0$0@4$4$0$0^1@2$5^1+hh8@1$3@2$1$0$0").

  (* [comment removed for export] *)
  Definition junk_ok : ltac2:(zQ "20!koa!ol8>1l@1$0$1P") := ltac2:(zQ "50!ol8!koa!nmd!on9!ord\1l@1$1$0@3$3$0\2it$0@2$2@1$4^1Ni1^1").

  Definition parse_value_post : ltac2:(zQ "a0!hic!hkf!h9!koa!kv5!lid!llc!qn7!lm5!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2pa$2>2ps$7>1p$2>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "jb1!hic!hkf!ko4!hrb!imd!h9!qo1!ol8!qoa!koa!ot5!hs7!nl3!llc!qp4!qn7!hs2!qq0!lme!ln7!nr8!qq7!okd!lm5!ls0!lsa!im0!qr2!im7!pm8!qsc!nmd!mg8!mh9!kv5!lid!ov0!qt3!qte!pk6!or0!nk8!qua!qv7!pg9!jk0!mnc!ms0!ms6!ngf!ok4!nha!ni4!nif!hq0!ih3!l2!oub!rg3&>0@1$1@1$0#k0@1$h2@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$d@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$h7\2pa$5\2ps$f\1p$5\2lo$5\1B$5\1m$j6\2mo$i3\1c$i2@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h8\2s'$h8@2$2$f\3ps'$f@2$2@2$d@1$0#5@1$1@1$0#k0\2F'@2$d@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$4$i0@1$i1^h5@7$if@hf$ie^if^ie^id^ic^h4^h3^h2^ib^ia^h1^h0^f^e^d^c^b^a^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^9^8^7^6^2@1$j0^if^1@1$h9@1$1@1$0#k0^5@1$j1$j7@2$3@1$id^1@2$3@3$j3?1H^4@1$h3^h5@2$3@3$j4?1H^h6@1$h3^h5@2$3@4$j5?1H^4@3$c$h7@1$i8@1$6^3^hd^5@2$3@4$ia?5HCEIL^5^hc^3@2$3@3$4$5@1$h6@1$6^3@1$h6@1$6^hb@2$3@3$4$h1@1$h5^3@1$h5^hb@2$3@2$hd@2$2$h4\1v$h4@2$3@2$3@2$j9^hb@2$b@1$0#k0^h2@2$h0@2$b@1$0#k0^h2@1$8^hc@2$3@3$4$5@1$8^4@1$8^hc@2$3@3$4$5@1$e^4@1$e^hc@2$3@3$4$h1@1$ib^4$hb@2$3@3$4@1$9$7@1$a@1$6^4@3$c$7@1$a@1$6^hc@3$ha$7@1$i7^1@1$hc$7@2$3@2$hf@1$i9^1@2$he@1$ja@1$e^hcN1@3$4$5@1$ic@1$6^4Z@2$2@1$9$7\4junk@1$9$7@2$3@3$4$5@2$b@1$0#k0^h2@2$j8^hd+1@2$3@2$3@2$h0^hb@1$8^4@2$h0@1$8^4@1$8^hc@2$3@3$4@1$9$7@1$a@1$6^4@3$c$7@1$a@1$6^hc^1@1$i5^1@2$3@5$i4^5^ie^ic^h9^h8@5$j2^hd@2$b@1$0#k0^ie@1$i6^hc^h7^5").

  Definition parse_value_unw : ltac2:(zQ "a0!h9!koa!hic!hkf!kv5!lid!qn7!kp1!lm5!hq0>2sp@1$3@1$2#k0>1G@1$1$7>4REST@1$1$8>2pa$0>2ps$6>2lo$0>1B$0>2fc@1$3@1$2#i0>1m$9>2mo$5>6budget$0>0$4P") := ltac2:(zQ "i20!hrb!h9!koa!hic!qo1!ko4!ol8!hkf!nl3!phd!mh9!qn7!imd!ot5!okd!lm5!ls0!nu1!ln7!kv5!lid!qt3!qte!iqf!or0!qua!jk0!ok4!pi7!pj0!kp1!ni4!hq0!hs7\2sp@1$7@1$3#k0\1G@1$2$he\4REST@1$2$f\2pa$1\2ps$b\2lo$1\1B$1\2fc@1$7@1$3#i0\1m$i0\2mo$h4\6budget$1\1c$h3@2$5$h0\2s'$h0@2$5$b\3ps'$b@2$5@1$2$6\4junk@1$2$6@2$5@1$7@1$3#i0\3fc'@1$7@1$3#i0@2$0@1$ha^1@2$0@8$hd?1E^f^4@3$8$f@1$h8@1$4^3^e^b^a^1^5@2$0@3$hf?1H^7@1$h2^5@2$0@4$h9?5HCEIL@1$9@1$a^5^d^3@2$0@1$h7@1$9@1$a^5@2$0@3$c$1@1$e@1$4^3@1$e@1$4^c@2$0@3$c@1$2$6@1$d@1$4^3@3$8$6@1$d@1$4^c^2@2$0@1$h5^2@5$hb^e@2$i1@1$3#k0^h0@3$8@2$h1$1$1@1$h6^d$hc^8@1$9@1$a^5").

  (* [comment removed for export] *)
  Definition parse_value_stmt_at_d : ltac2:(zQ "10!h9>5entry$0>6budget>0$0$0>5first>0$0P>1d$0P") := ltac2:(zQ "k00!hic!hkf!hs7!h9!imd!l2!qo1!kl2!kp1!im0!hrb!qp4!qoa!hs2!qq0!qr2!koa!ol8!lm5!ih3!oub!qge!lsa!nl3!im7!ko4!pm8!nmd!on9!kv5!nn3!lid!llc!pne!po8!rgc!rh8!rid!qte!or0!ord!qua!qv7!qq7!qn7!pg9!ot5!ph5!okd!mnc!ms0!qk6!ngf!pu8!pue!nha!nif!ns8!pv8!qg0!hq0!ls0!kn8!kne\5entry$3\6budget>0$3$3\5first>0$3P\1d$3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$jc>1s$jd>4REST@1$h0$h2>2ps$ic>2p0$3>3len$3>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$hf>1g$8>1G@1$h0$8>0@3$4$3@1$b^9^ie>0@4$j8?1H^c@3$h7$h2@1$i7@1$6^a^b^d>0@3$j7?1H^d^5>0@8$i1^f^if^id^9^8@1^j3@1$b^c^7^h0>0@4$i9?5HCEIL^h0@2$2@1$0#k0^i8^d>0@3$4$e@1$ib^e$f>0@3$4$e@1$ia^f$f>0@3$4$3@1$id@1$6^h0Z>0@5$i3^h2^j4^h4^h0^f>0@2$a@2$d^h1@2$2@1$0#k0^ic@2$h4@2$2@1$0#k0^ic@1$c^h2>0@3$4$3@1$c^h3@2$5^h2^h1>0@2$h9@1$1@1$0#8\1b@1$1@1$0#8@2$a@4$j3$h3^h8@2$2@1$0#k0^if@3$9@1$1@1$0#8^1@1$h8@1$1@1$0#8@1^jb@2$2@1$0#8^1>0@3$4@1$1@1$0#k0^ie@1$7Z>0@3$4@1$1@1$0#k0^id@1$7Z>0@3$4@1$1@1$0#k0^id@1$7Z>0@3$4@1$1@1$0#k0^id@1$7Z>0@2$a@2$d@2$5@2$2@1$0#k0^jc+o8@2$2@1$0#k0^j4@2$d@2$5@2$5@2$2@1$0#k0^j4+hh8+hg0^h5>0@3$4$3@1$j0@1$6^ha@2$5@2$2@1$0#k0^j5+hh8>0@2$h4@2$5@1$if@1$6^hb@2$jf@1$c^hb@2$2@1$0#k0^j5@2$je+2+ha>0@3$hc$h1\2it$h1@2$hb@1$i8^1Ni1@1$ie@1$6^hc>0@4$i2@3$9$8^h6^h5^i0^k0^k1>0@3$4$j5@1$j6^h7@d$ja^k1^jb^ja^j1^j0^if^ie^id^ic^ib^ia^i9^i8>0@3$jb?1E@3$9$8^h8^h7@1$i6@2$2@1$0#k0^ja>0@3$4$3@2$h5@2$2@1$0#k0^jb+8Z>0@3$4$3@2$h5@2$2@1$0#k0^k4+h0Z@3$j9?1H\1c$hd@2$ha@hb$i4^k7^k6^k5^k4^k0^jf^j6^j5^j4^j3^j2^j1^j0^if^ie^id^i8^i7^i4@2$2@1$0#k0^je^i3@2$2@1$0#k0^jd^i0^hf^i6^hd^1@c$i5^k6@3$9$8^hc^hb^i4@2$2@1$0#k0^je^i3^i0^hf^i7^i6^hd@1^ka@1$b^i3^1@2$he@7$j2@hf$j1^k6^k5^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7@1$7^ka^i6@1$h6@1$1@1$0#k0^i5@1$j4$h3^hc").

  Definition parse_value_stmt_at : ltac2:(zQ "10!h9>5entry$0>6budget>0$0$0>5first>0$0PP") := ltac2:(zQ "20!h9!rk0\5entry$0\6budget>0$0$0\5first>0$0P>1d$0@4$1^4^3^2^1").

  (* [comment removed for export] *)
  Definition RPV_STACK : ltac2:(zQ "10!h9>1d$0$0") := ltac2:(zQ "60!l2!h9!hh8!s0!sf!qb\1d$1@2$0@2$0@2$0@2$0@2$5+n0^1+kg0$3@1$4?1E@1$2Ni1").

  (* [comment removed for export] *)
  Definition parse_key_post : ltac2:(zQ "a0!hic!hkf!h9!koa!kv5!lid!llc!qn7!lm5!hq0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2pa$2>2ps$7>1p$2>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "j61!hic!hkf!ko4!hrb!imd!h9!qo1!ol8!qoa!koa!ot5!lm5!hs7!nl3!llc!qn7!hs2!qq0!lme!ln7!qp4!qq7!okd!ls0!lsa!im0!qr2!im7!pm8!mg8!mh9!kv5!lid!ov0!qt3!qte!rla!or0!qua!qv7!pg9!jk0!mnc!ms0!ms6!ngf!ok4!nha!ni4!nif!hq0!ih3!l2!oub&>0@1$1@1$0#k0@1$h2@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$e@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$b\2pa$5\2ps$f\1p$5\2lo$5\1B$5\1m$j2\2mo$i0\1c$hf@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h7\2s'$h7@2$2$f\3ps'$f@2$2@2$e@1$0#5@1$1@1$0#k0\2F'@2$e@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$4$hd@1$he^h5@7$ib@hf$ia^if^ie^id^ic^h4^h3^h2^ib^ia^h1^h0^f^e^d^c^b^a^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^9^8^7^6^2@1$ic^if^1@1$h8@1$1@1$0#k0^5@1$id$j3@2$3@1$i9^1@2$3@3$if?1H^4@1$h3^h5@2$3@3$j0?1H^h6@1$h3^h5@2$3@4$j1?1H^4@3$d$b@1$i5@1$6^3^hd^5@2$3@4$i6?5HCEIL^5^hc^3@2$3@3$4$5@1$h6@1$6^3@1$h6@1$6^hb@2$3@3$4$h1@1$h5^3@1$h5^hb@2$3@2$hc@2$2$b\1b$b@2$3@2$3@2$j5^hb@2$c@1$0#k0^h2@2$h0@2$c@1$0#k0^h2@1$8^hc@2$3@3$4$5@1$8^4@1$8^hc@2$3@3$4$5@1$h4^4@1$h4^hc@2$3@3$4$h1@1$i7^4$ha@2$3@3$4@1$9$7@1$a@1$6^4@3$d$7@1$a@1$6^hc@3$h9$7@1$i4^1@1$hb$7@3$4$5@1$i8@1$6^4Z@2$2@1$9$7\4junk@1$9$7@2$3@3$4$5@2$c@1$0#k0^h2@2$j4^hd+1@2$3@2$3@2$h0^hb@1$8^4@2$h0@1$8^4@1$8^hc@2$3@3$4@1$9$7@1$a@1$6^4@3$d$7@1$a@1$6^hc^1@1$i2^1@2$3@5$i1^5^ie^ic^h9^h8@5$ie^hd@2$c@1$0#k0^ie@1$i3^hc^h7^5").

  Definition parse_key_stmt : ltac2:(zQ "00P") := ltac2:(zQ "k20!hic!hkf!hs7!imd!h9!l2!qo1!kp1!im0!kl2!hrb!qoa!hs2!qq0!qr2!koa!rm3!qp4!ol8!lm5!ih3!oub!qge!lsa!nl3!im7!ko4!pm8!nmd!on9!kv5!nn3!lid!llc!pne!po8!rgc!rn0!rid!qte!ro2!or0!ord!qua!qv7!qq7!qn7!pg9!ot5!ph5!okd!mnc!ms0!qk6!ngf!pu8!pue!nha!nif!ns8!pv8!qg0!hq0!ls0!kn8!kne>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i1@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$je>1s$jf>4REST@1$f$h3>2ps$ie>2p0$4>3len$4>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$i0>1g$7>1G@1$f$7>0@4$ja?1H^b@3$h8$h3@1$i9@1$6^9^a^c>0@3$j9?1H^c^4>0@8$i2^e^ie^ic^8^7@1$h0@1$h1^b^6^f>0@4$ib?5HCEIL^f@2$2@1$0#k0^i7^c>0@3$3$d@1$id^d$e>0@3$3$d@1$ic^e$e>0@3$3$4@1$if@1$6^fZ>0@5$i4^h1^j3^h3^f^e>0@2$a@2$c^h0@2$2@1$0#k0^ib@2$h5@2$2@1$0#k0^ib@1$b^h1>0@3$3$4@1$b^h2@2$5^h1^h0>0@2$ha@1$1@1$0#8\1b@1$1@1$0#8@2$a@4$j5$h4^h7@2$2@1$0#k0^ie@3$8@1$1@1$0#8^1@1$h9@1$1@1$0#8@3$3$4@2$2@1$0#8^1+i2>0@3$3@1$1@1$0#k0^id@1$9Z>0@3$3@1$1@1$0#k0^ic@1$9Z>0@3$3@1$1@1$0#k0^ic@1$9Z>0@2$a@2$c@2$5@2$2@1$0#k0^ja+o8@2$2@1$0#k0^j2@2$c@2$5@2$5@2$2@1$0#k0^j2+hh8+hg0^h3>0@3$3$4@1$j2@1$6^h8@2$5@2$2@1$0#k0^j3+hh8>0@2$h5@2$5@1$j1@1$6^h9@2$k1@1$b^h9@2$2@1$0#k0^j3@2$k0+2+ha>0@3$hd$h2\2it$h2@2$hc@1$ia^1Ni1@1$j0@1$6^ha>0@4$i3@3$8$7^h4^h3^he^je^jf>0@3$3$j7@1$j8^h5@d$jc^jf^j9^j8^if^ie^id^ic^ib^ia^i9^i8^i7^i6>0@3$jd?1E@3$8$7^h6^h5@1$i7@2$2@1$0#k0^j8>0@3$3$4@2$h6@2$2@1$0#k0^j9+8Z>0@3$3$4@2$h6@2$2@1$0#k0^k2+h0Z@3$jb?1H\1c$he@2$hb@hb$i5^k5^k4^k3^k2^je^jd^j4^j3^j2^j1^j0^if^ie^id^ic^ib^i6^i5^i2@2$2@1$0#k0^jc^i1@2$2@1$0#k0^jb^he^hd^i4^hb^1@c$i6^k4@3$8$7^ha^h9^i2@2$2@1$0#k0^jc^i1^he^hd^i5^i4^hb@1$h0@1$h1^i1^1@2$hf@7$j4@hf$j3^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5@1$9$i8^i4@1$h7@1$1@1$0#k0^i3@1$j6$h4^ha").

  Definition any_first (_ : Z) : Prop := True.
  Definition parse_value_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!rm3!rp1!rk0!rpe\1d$0@4$3$4$1$2^1").
  Definition parse_array_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!imd!rm3!rk0!rq9\1d$0@4$3$4$2\1b$0@3$1$0^1+lb^1").
  Definition parse_object_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!imd!rm3!rk0!rr4\1d$0@4$3$4$2\1b$0@3$1$0^1+nb^1").
  Definition parse_value_stmt : ltac2:(zQ "00P") := ltac2:(zQ "40!rm3!rp1!rs0!rpe@3$2$3$0$1").
  Definition parse_array_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!rm3!rs0!rq9@3$3$4$2\1b$0@3$1$0^1+lb").   (* [comment removed for export] *)
  Definition parse_object_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!rm3!rs0!rr4@3$3$4$2\1b$0@3$1$0^1+nb").  (* [comment removed for export] *)
  Definition parse_string_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!rm3!rs0!rt8@3$3$4$2\1b$0@3$1$0^1+i2").   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RPN_STACK : ltac2:(zQ "10!h9>1d$0$0") := ltac2:(zQ "30!h9!rm3!kne\1d$0@2$2@1$1^1+i0").
  Definition parse_num0_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!ru4!rs0!rv1@3$3$4$2\1b$0@3$1$0^1+j0").
  Definition parse_numneg_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!ru4!rs0!rvb@3$3$4$2\1b$0@3$1$0^1+id").
  Definition parse_numpos_stmt : ltac2:(zQ "00P") := ltac2:(zQ "60!hs2!hrb!h9!ru4!rs0!sg7@3$4$5$3\1b$2@2$1@2$0+j1^1@2$0^1+j9").
  Definition parse_null_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!rm3!rs0!sh3@3$3$4$2\1b$0@3$1$0^1+me").
  Definition parse_true_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!rm3!rs0!shd@3$3$4$2\1b$0@3$1$0^1+n4").
  Definition parse_false_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!imd!rm3!rs0!si7@3$3$4$2\1b$0@3$1$0^1+m6").
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma parse_family_by_depth : ltac2:(zQ "a2!h9!hrb!sj2!sk9!sm0!hs2!oub!sn8!sod!sq3&>0@2$1@2$5Z^1@2$6^1^2@1$2^2&>2d'$0~0>0>1d$0>0~1@1$3^2>0>1d$0>0~1@1$4^2>0>1d$0>0@1$3^1>0@1$4^2@1$2^3@2$1$9@2$1$7$8").
  Proof.
    intros PA PO PV.
    assert (ALL : forall n : nat, forall d, d < Z.of_nat n -> parse_value_stmt_d d).
    { induction n as [|n IH]; intros d Hd.
      - apply PV; [apply PA| apply PO]; intros d' Hd'; exfalso; lia.
      - apply PV; [apply PA| apply PO]; intros d' Hd'; apply IH; lia. }
    assert (V : forall d, parse_value_stmt_d d).
    { intros d. destruct (Z.le_gt_cases 0 d).
      - apply (ALL (S (Z.to_nat d))). lia.
      - apply (ALL 0%nat). lia. }
    split; [exact V|]. split; intros d; [apply PA| apply PO]; intros d' _; apply V.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RLLVM_FUZZ_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!l2!rm3@2$0@2$0@2$0@2$0@2$0@2$0+h0+m0+in0+k0+k0+l0@1$1+i0").   (* [comment removed for export] *)

      (* [comment removed for export] *)

End Iface.
(* [comment removed for export] *)
