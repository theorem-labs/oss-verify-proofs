(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres BJKitArith.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat46Stdlib6ZArith6BinInt1Zja3add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~l8bAFREE_STACKja3mulja6of_natl8cAOPNEW_STACK79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJIface~~~~~~s1bADTOR_STACKs1bAGROW_STACKja3max04Npos35stdpp9bitvectorbdefinitionshi72bvl83mem37Corelib4Init5Logichl03andhi7bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hna5asegsja2lehl02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hs94cellhc4conshc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB5BJRep~~~~~~ihaabj_statics79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsConst~~~~~~im46ACONSTl83ATPl8bas_rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~irf5aceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsStack0~~~~~~jg66stack0hs92C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~jl44frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jp53stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jt87mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~khd8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~km42wzja2ltja6moduloja3powja3subhl02exiha6vstackhc4booliha8vs_charsiha4vs_nja3divja3eqbhc6optionl85blockiha6vs_bufiha6vs_cap89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJIface5Iface~~~~~~lhb4vs_ulhb5nvalsiha8vs_itemshc4listihacblocks_itemslhb5vs_ibl8bclass_byteshc6lengthlhb5vs_nvlhb5vs_bpl88lb_byteslhb6vs_bpal86AK_CLShl02orlhb5rc_allhb6rc_clslhb6rc_cntlhb7rc_livelhb7pots_lelhbbvs_capshapel85as_Cfl85as_Cmja2gehc3applhb6RC_CLSiha9blocks_vsl8fas_LIVE_CNT_MAXl8bas_LIVE_MAXl84bptrhc4prodhc4pairl8aalloc_rooml85as_TRl88trace_okl88blk_size36Stdlib5Lists4Listmrdafold_right79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJKitArith~~~~~~mte5agcaplhb8grow_caplhb9grow_costja3ltblhb9push_costihacarr_tbl_sizeiha2jvhc3fsthc3snd37Corelib5Lists7ListDefnn63maplhb9cf_blocksiha8blocks_vihacobj_tbl_sizemrd6concatlhbasite_tr_okl89APC0_FREE3h5LinuxProcessSemanticsfLinuxProcessSem3Runnu16config3h5LinuxProcessSemanticsfLinuxProcessSem5Stateoh75Model3h5LinuxProcessSemantics5Riscv7Preludeoke5bvmapl85as_Stl86fframel85as_ALhc4None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsopddmachine_statenu19cfg_modelnu16cfg_mslhbbbj_env_postl88as_AKRELl88as_MPRESl86as_RFSl88as_RHEAPl86as_VIS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep~~~~~~pje5xpresjp53mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~poa2MSpoa6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~pt77seg_romnu15mkCfgiha7jheight37Corelib4Init5Peanoqj52les1cA_DTOR_VALUElhbbbj_env_corelhbfdtor_value_postlhbh0dtor_value_tr_okiha6val_atl85as_SR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5AsObj~~~~~~qq74aobjirfaaccessiblelhb4vs_Xirfbaddressablehs9acells_sizeiha7vs_tempiha6vsiteml86as_FSBnn66Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB6AXpres~~~~~~rk57inframes19A_VS_DTORlhbeADTOR_VS_STACKlhbcdtor_vs_postlhbddtor_vs_tr_okihabitem_heightiha5vs_atl88AFS_SIZEs1aA_GROW_ONElhb6bj_envlhbdgrow_one_postlhbegrow_one_tr_oks1bA_PUSH_BOOLs1bA_PUSH_NULLlhbdpush_sca_sitehl03ifflhb8arr_costiha4Jarriha5VSvalihabjvs_of_listhc4Somehl03nots1fAPUSH_ARR_STACKs1aA_PUSH_ARRlhbfpush_array_postlhbh0push_array_tr_oklhb6vsvalsiha3kvslhb9obj_spentiha4Jobjihaablocks_kvsihaakvs_height36Stdlib7SortingbPermutationti0bPermutations1fAPUSH_OBJ_STACKs1aA_PUSH_OBJlhb8obj_costlhbh0push_object_postlhbh1push_object_tr_oklhb5vskvsl88blk_addrirfain_app_memirf5shvisjt88bytes_atmrd2Inlhbepush_sca_tr_oks1aA_PUSH_DBLs1aA_PUSH_I64s1aA_PUSH_U64iha6pstateiha5ps_vsiha6ps_endiha8ps_depthlhb8pv_spentiha7ps_morehc5false37Corelib4Init3Natulf3addlhb7junk_oklhb8parser_Xlhb5pv_leiha9parser_atiha8ps_ecset79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsCXXHeap~~~~~~ur1afs_scratchja6to_natlhb8input_oklhbh0parse_value_postlhb7pv_costlhb7pv_roomlhb8pv_tr_okl8bAFS_MAXLIVElhbh5parse_value_stmt_at_dlhb9APV_STACKiha5VSkeys1bA_KEYSTRINGlhbeparse_key_posts19A_P_VALUElhb9any_firsts19A_P_ARRAYs1aA_P_OBJECTlhbh3parse_value_stmt_ats1aA_P_STRINGs16A_NUM0lhbdAPV_NUM_STACKs18A_NUMNEGs18A_NUMPOSs1aA_LIT_NULLs1aA_LIT_TRUEs1bA_LIT_FALSElhbh2parse_value_stmt_dlhbh2parse_array_stmt_dlhbh3parse_object_stmt_dlhbh0parse_array_stmtlhbh1parse_object_stmtlhbh0parse_value_stmtl83asr" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_DTOR_VALUE   : Z := 0xe6174.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_VS_DTOR      : Z := 0xee3f8.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DS_DTOR      : Z := 0xf07f0.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GROW_ONE     : Z := 0xf2b78.   (* [comment removed for export] *)
Definition A_PUSH_ARR     : Z := 0xee720.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_OBJ     : Z := 0xeead4.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_CHARS   : Z := 0xf2e7c.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_STR     : Z := 0xeeff4.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_I64     : Z := 0xf3d7c.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_U64     : Z := 0xf414c.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_DBL     : Z := 0xf451c.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_BOOL    : Z := 0xf48ec.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PUSH_NULL    : Z := 0xf4cd0.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_OBJ_CTOR     : Z := 0xc7204.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_OBJ_FIND     : Z := 0xc61a8.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_WRITE_SOME   : Z := 0xd289c. (* [comment removed for export] *)
Definition A_P_DOCUMENT   : Z := 0xf7fdc.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_P_VALUE      : Z := 0xf8c84.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_MSUSPEND     : Z := 0xf8a88.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
 (* [comment removed for export] *) (* [comment removed for export] *)
 (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_SUSPEND5     : Z := 0x106a34.  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_SUSPEND6     : Z := 0x1085c0.  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LIT_NULL     : Z := 0xf99fc. (* [comment removed for export] *)
Definition A_LIT_TRUE     : Z := 0xf9e24. (* [comment removed for export] *)
Definition A_LIT_FALSE    : Z := 0xfa2d4. (* [comment removed for export] *)
Definition A_FAIL         : Z := 0xfa77c.   (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_P_STRING     : Z := 0xfb248.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_P_ARRAY      : Z := 0xfb5dc. (* [comment removed for export] *)
Definition A_P_OBJECT     : Z := 0xfba80. (* [comment removed for export] *)
Definition A_NUM0         : Z := 0xfc1c0.   (* [comment removed for export] *)
Definition A_NUMNEG       : Z := 0xff3cc.   (* [comment removed for export] *)
Definition A_NUMPOS       : Z := 0x103974.   (* [comment removed for export] *)
Definition A_ESCAPED      : Z := 0x106df8.  (* [comment removed for export] *) (* [comment removed for export] *)
 (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_KEYSTRING    : Z := 0x108cb8.  (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_JSON_PARSE   : Z := 0xcedd0.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_RELEASE      : Z := 0xcfc34.   (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ADTOR_STACK : ltac2:(zQ "20!j4!h9>1h$0$1") := ltac2:(zQ "50!l2!j4!p5!q3!q9\1h$1@2$0@2$0@2$3+q0@1$4^1+h0$2").   (* [comment removed for export] *)   (* [comment removed for export] *)
Definition AGROW_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!r2!l2@2$1+o0$0").   (* [comment removed for export] *)                              (* [comment removed for export] *)
Definition APUSH_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!r2!l2@2$1+o0$0").                              (* [comment removed for export] *)
Definition APUSH_ARR_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "40!vf!hgd!l2!hhb@2$2+p0@2$3$1@1$0Ni1").    (* [comment removed for export] *)
Definition APUSH_OBJ_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "50!l2!vf!hgd!r2!hhb@2$0+k0@2$4@2$0@2$0+hp0$3@1$1Ni1$2").  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!hgtd$0").
  Abbreviation SR := (as_SR H).  Abbreviation VIS := (as_VIS H).  Abbreviation AKREL := (as_AKREL H).  Abbreviation MPRES := (as_MPRES H).
  Abbreviation RHEAP := (as_RHEAP H).  Abbreviation RFS := (as_RFS H).  Abbreviation rauxv_ok := (as_rauxv_ok H).
  Abbreviation AL := (as_AL H).  Abbreviation Cm := (as_Cm H).  Abbreviation Cf := (as_Cf H).  Abbreviation TR := (as_TR H).

  (* [comment removed for export] *)
  Definition bj_env : ltac2:(zQ "40!hi1!hk4!h9!hka>1m$3>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2lo$2>1B$2>6budget$2>4errv@1$1@1$0#k0>2fc@1$1@1$0#i0P") := ltac2:(zQ "hd0!hm4!hi1!hmb!hk4!h9!hr5!hre!hs3!ig5!igd!ih4!il6!iq1!iqb!ir1!hka!ivd!jk4!jke!jod!jt1!kh2!kl8!kpf!l2!kq5!kqa!kr3!kr9\1m$f\2sp@1$3@1$1#k0\2tp@1$3@1$1#k0\2lo$4\1B$4\6budget$4\4errv@1$3@1$1#k0\2fc@1$3@1$1#i0@2$0@3$e?1H^8^4@2$0@2$0@2$6@2$2@1$1#k0^7^4@2$h9^4@2$hb+2+k0@2$0@4$h4$5^8^5@2$2@1$1#k0^7@2$0@2$6@1$h0?5HCEIL^5@2$0@2$6^5@2$hc@2$2@1$1#k0^7^3@2$0@4$h6$5^8@2$h8@2$2@1$1#k0^6-q4@3$9$8@1$h2^2@1$a$8@2$0@2$h5$5^8@2$0@3$7@1$3@1$1#k0^6@1$h7$d@2$0@1$b^8@2$0@1$h3^1@2$0@3$7$4@2$ha@2$2@1$1#k0^7+h0Z@2$0@1$c^8@4$h1?5HCEIL^8^5@2$2@1$1#k0^7").   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bj_env_post : ltac2:(zQ "40!hi1!h9!hk4!hka>2m'$3>2sp@1$2@1$0#k0>2tp@1$2@1$0#k0>2lo$1>1B$1P") := ltac2:(zQ "h40!hi1!hm4!hk4!hr5!hmb!h9!ig5!igd!ih4!krf!il6!iq1!ir1!hka!jk4!jke!jt1!kh2!kl8!l2\2m'$d\2sp@1$2@1$0#k0\2tp@1$2@1$0#k0\2lo$5\1B$5@2$1@3$c?1H^5^1@2$1@4$h0$3^5^2@2$4@1$0#k0^4@2$1@2$9@1$2@1$0#k0\5errv'@1$2@1$0#k0@4$h2$3^6@2$h3@2$4@1$0#k0^4-q4@3$7$6@1$f^1@1$8$6@2$1@2$h1$3^5@2$1@1$a^5@2$1@1$b^5@4$e?5HCEIL^5^2@2$4@1$0#k0^4").
  (* [comment removed for export] *)
  Definition bj_env_core : ltac2:(zQ "40!hi1!hk4!h9!hka>1m$3>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2lo$2>1B$2>6budget$2>4errv@1$1@1$0#k0>2fc@1$1@1$0#i0P") := ltac2:(zQ "hc0!hm4!hi1!hmb!hk4!h9!hr5!hre!hs3!ig5!igd!ih4!il6!iq1!iqb!ir1!hka!ivd!jk4!jke!jt1!kh2!kl8!kpf!l2!kq5!kqa!kr3!kr9\1m$f\2sp@1$3@1$1#k0\2tp@1$3@1$1#k0\2lo$4\1B$4\6budget$4\4errv@1$3@1$1#k0\2fc@1$3@1$1#i0@2$0@3$e?1H^8^4@2$0@2$0@2$6@2$2@1$1#k0^7^4@2$h8^4@2$ha+2+k0@2$0@4$h3$5^8^5@2$2@1$1#k0^7@2$0@2$6@1$h0?5HCEIL^5@2$0@2$6^5@2$hb@2$2@1$1#k0^7^3@2$0@4$h5$5^8@2$h7@2$2@1$1#k0^6-q4@3$9$8@1$h2^2@1$a$8@2$0@2$h4$5^8@2$0@3$7@1$3@1$1#k0^6@1$h6$d@2$0@1$b^8@2$0@3$7$4@2$h9@2$2@1$1#k0^7+h0Z@2$0@1$c^8@4$h1?5HCEIL^8^5@2$2@1$1#k0^7").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vs_u : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "80!l2!ksf!kt6!h9!ku2!ks5!kua!kv0\2st$5@2$0@1$4^1M1\0$1$3@2$7@1$2^1ZZ@2$0+1@2$6@2$0@1$2^1+h7+h8").
  Definition vs_bufbytes : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "70!kv6!kvf!h9!lg7!lh1!ks5!q3\2st$5M0\1x@1$0$1$2@1$3^1\1b$1@2$6+h8@1$4^2Z").
  Definition vs_bp : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "c0!kv6!lh1!kvf!q3!h9!llf!lg7!ks5!l2!kua!hhb!kr9\2st$7M0\1x@1$0$2$4@1$6^1\1b$2@2$8@2$3+h8@1$1^2@2$3+j0@2$aZ@2$b@1$5^2@2$9@1$1^2+2+ho0").
  Definition vs_bpa : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "c0!kv6!lh1!kvf!q3!h9!llf!lg7!ks5!l2!kua!hhb!kr9\2st$7M0\1x@1$0$2$4@1$6^1\1b$2@2$8@2$3+h8@1$1^2@2$3+s0@2$aZ@2$b@1$5^2@2$9@1$1^2+2+jg0").
  Fixpoint nvals (l : list vsitem) : Z := match l with [] => 0 | VSval _ :: r => 1 + nvals r | VSkey _ :: r => nvals r end.
  Definition vs_nv : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "30!lm7!ln0!ks5\2st$2@1$0@1$1^1").                     (* [comment removed for export] *)
  Definition vs_ib : ltac2:(zQ "30!lnc!ks5!kvf>2st$1@1$0$2") := ltac2:(zQ "30!lo3!ln0!ks5\2st$2@1$0@1$1^1").
  Definition rc_cls : ltac2:(zQ "20!h9!ks5>2st$1>1k$0>1c$0$0") := ltac2:(zQ "70!h9!l2!lp3!ku2!ks5!lpc!q3\2st$4\1k$0\1c$0@2$1@2$5@1$2^3^1@2$6+i0@2$1@1$3^3^2").
  Definition rc_cnt : ltac2:(zQ "20!h9!ks5>2st$1>1k$0$0") := ltac2:(zQ "90!l2!lqa!h9!lp3!lr3!ks5!kvf!q3!q9\2st$5\1k$2@2$0@2$0@2$7+2@1$8@2$1$6@1$3^2@1$4^2^1").
  Definition rc_live : ltac2:(zQ "20!h9!ks5>2st$1>1k$0$0") := ltac2:(zQ "80!l2!q3!h9!lrc!lp3!ku2!ks5!ls5\2st$6\1k$2@2$0@2$0@2$0@1$7@1$4^2@1$3^2@2$1+h8@1$5^2@2$1+i8^1").
  Definition rc_al : ltac2:(zQ "20!h9!ks5>2st$1>1k$0$0") := ltac2:(zQ "80!l2!q3!h9!lt0!lp3!ku2!ks5!ls5\2st$6\1k$2@2$0@2$0@2$0@1$7@1$4^2@1$3^2@2$1+j0@1$5^2@2$1+hg0^1").
  Definition RC_CLS : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!lta!kr3!kr9@2$2$0@2$1+2+h1").
  (* [comment removed for export] *)
  Definition vs_capshape : ltac2:(zQ "10!ks5>2st$0P") := ltac2:(zQ "a0!h9!hs3!lh1!hm4!krf!lu3!ks5!hre!q3!kr3\2st$6@2$5@3$1$0@1$2^1Z@2$4$0\1j$0@2$3@2$7Z^1@3$1$0@1$2^2@2$8+h0@2$9+2^1").
  (* [comment removed for export] *)
  Definition pots_le : ltac2:(zQ "20!h9!ks5>3st'$1>2k'$0>2st$1>1k$0>2xc$0>2xn$0>2xb$0>2xa$0P") := ltac2:(zQ "90!h9!hre!hm4!l2!lu9!lv2!lvc!mg6!ks5\3st'$8\2k'$0\2st$8\1k$0\2xc$0\2xn$0\2xb$0\2xa$0@2$2>1c$0>0@2$2@2$1+1^1@2$1^1+he@2$1@3$5^a^9^2@2$3@3$5^8^7^2^6@2$2@2$1@2$6^8^7@2$3@2$6^6^5^3@2$2@2$1@2$7^8^7@2$3@2$7^6^5^2@2$1@2$4^8^7@2$3@2$4^6^5^1").
  (* [comment removed for export] *)
  Definition pv_le : ltac2:(zQ "20!h9!ks5>3st'$1>2k'$0>2st$1>1k$0P") := ltac2:(zQ "60!hm4!h9!ks5!mh1!mhc!hre\3st'$2\2k'$1\2st$2\1k$1@2$0@8$3^4^3^2^1ZZ+i8+hg0@2$0@2$5Z^3@1$4^4").
  (* [comment removed for export] *)
  Definition pv_cost : ltac2:(zQ "20!h9!ks5>2st$1>1k$0$0") := ltac2:(zQ "60!l2!lu9!h9!ks5!mib!mj3\2st$3\1k$2@2$0@2$5?1H@2$0@2$1^2^1+hg0@2$4?1H@2$0@2$1^2^1+hg0").
  Definition pv_spent : ltac2:(zQ "20!h9!ks5>2st$1>1k$0>2lo$0>3AL0$0>3AL'$0P") := ltac2:(zQ "b0!h9!l2!hm4!lu9!hre!kr9!krf!ks5!mib!mj3!mjb\2st$7\1k$0\2lo$0\3AL0$0\3AL'$0@2$6$0\1q$0@2$2@2$2@2$4^4^1@2$4^1@2$1@2$3^6^5+hg0@2$2@2$4Z^1@2$a^2@2$5^3@2$1@2$9?1H@2$5@2$1@2$3^6^5+hg0^1@2$8?1H@2$5@2$1@2$3^6^5+hg0^1").
  (* [comment removed for export] *)
  Definition pv_room : ltac2:(zQ "40!lnc!h9!ks5!kvf>2LB@1$0$3>2st$2>1k$1P") := ltac2:(zQ "h70!hm4!hre!kvf!l2!lnc!h9!ls5!q3!mk0!lqa!hs3!krf!mk6!lv2!lvc!mg6!mhc!ml0!ks5!mld!mmf!lpc!q9\2LB@1$4$2\2st$h2\1k$5@2$b@1$4$2\1R@1$4$2@2$0@3$a@1$4$2^4@3$8$2@1$h1^3^1@2$0@2$1Z^2@2$0@1$h0^3@2$0>1c$5>0@2$0@2$1+1^1@2$1^1+he@2$1@2$3@2$h5^3^2@3$d^5^4^2$c@2$0@2$1@2$3@2$3@2$7+2@1$h6@2$9$2^1@2$e^3^2+8@2$7+2@1$h3?1H@2$0@2$1@2$3@2$3@2$3@1$6^1@2$f^3^2+i8+kg0@1$h4?1H@2$1Z@1$6^1").
  (* [comment removed for export] *)
  Definition room_after_grow : ltac2:(zQ "40!h9!lnc!ks5!kvf>2st$2>4REST@1$1$3>6newcap$0>1n$0P") := ltac2:(zQ "d0!h9!mnd!mo4!mob!kvf!mk0!igd!lnc!lo3!ln0!ks5!mp2!q3\2st$a\4REST@1$7$4\6newcap$0\1n$0>1p$1>1A$0@3$b?1H@3$6@2$2@2$2$1$0$0@4$3@2$2$1$0$0@4$3$1$0^2^1@2$c+h8^4@3$5$4@1$8@1$9^6^5^3").

  (* [comment removed for export] *)
  Definition site_tr_ok : ltac2:(zQ "10!h9>3pc0$0>7ra_site$0P") := ltac2:(zQ "50!h9!igd!ih4!mpf!mq7\3pc0$0\7ra_site$0@3$4@1$3?1H^2@3$1$0^1@1$2$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cf_blocks : ltac2:(zQ "30!lnc!h9!kvf>1l@1$0$2$1") := ltac2:(zQ "70!kvf!h9!lnc!mib!mr2!mt0!l2\1l@1$2$0@5$5$1$0\1b$0\3acc$1@2$6@2$3?1H@1$4^2^1Z^1").
  (* [comment removed for export] *)
  Definition grow_cap : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "30!h9!nhf!l2\1n$0@1$1@2$2^1+1").       (* [comment removed for export] *)
  Lemma grow_cap_bounds : ltac2:(zQ "90!hre!hm4!ni8!kr3!l2!h9!kq5!hhb!q3>1n$5>0@2$1@2$0Z^1@2$6^1@2$3+2+i8@2$1@2$0@2$4^2+1@1$2^2@2$1@2$0+h0@1$2^2@2$1@2$0@1$2^2@2$7+h0@2$8+2^2>0@2$0@2$4^2+1@2$3+2+ha@2$0@1$2^3@2$3+2+ha").
  Proof.
    intros n Hn. unfold grow_cap. npose (agcap_bounds (n + 1) ltac:(lia)) as (A & B & C).
    split; [exact A|]. split; [exact B|]. split.
    - unfold agcap in *. destruct (gcap_from_shape 36 16 (n + 1) ltac:(lia)) as [E|(c0 & P0 & P1 & E)]; rewrite E in *; lia.
    - intros Hle. exact (agcap_le_2p26 (n + 1) Hle).
  Qed.
  Definition grow_cost : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "c0!kv6!kvf!h9!ni8!lg7!lh1!ks5!mib!mj3!mr2!l2!q3\2st$6@2$a@2$8?1H@2$b+h8@1$3@1$5^1M0\1x@1$0$1$2@1$4^1\1b$1@2$7?1H@1$9^1Z").
  (* [comment removed for export] *)
  Definition push_cost : ltac2:(zQ "20!h9!ks5>2st$1$0") := ltac2:(zQ "70!ksf!h9!nj4!lh1!ku2!ks5!nk1\2st$5M0\0$0$1@2$6@1$4^1@1$3^1Z@1$2^1").
  Definition arr_cost : ltac2:(zQ "20!h9!ks5>2st$1>1n$0$0") := ltac2:(zQ "70!ksf!h9!nk7!nl4!ks5!mj3!kv0\2st$4\1n$1M0\0$0$1@2$6^1Z@1$2^2@2$5?1H@1$3^1").
  Definition obj_cost : ltac2:(zQ "60!h9!lnc!mo4!nm4!ks5!kvf>2st$4>1n$0>3kvl@1$1@2$2$5$3$0") := ltac2:(zQ "h30!kvf!nm4!mo4!ksf!lnc!h9!igd!nma!nn0!nod!np4!nk7!nq1!nqd!ks5!mj3!nrd!l2!kv0\2st$e\1n$5\3kvl@1$4@2$2$0$1M3\0$3$5@2$h2^2Z@1$b^3@2$h1@2$f?1H@1$d^2@1$a@2$h0$0@4$9@2$2$0$1@1$4$0\2bv@2$2$0$1@3$6$0@3$7$0$1^1@1$c@3$8$0$1^1^1").
    (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dtor_value_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "30!ns7!nt5!hm4@2$2@2$0$1+smprc@2$2@2$0$1+ulog8@2$2@2$0$1+sgnvc@2$0$1+smqr4").
    (* [comment removed for export] *)
  Definition dtor_value_post : ltac2:(zQ "c0!hi1!hk4!lnc!h9!ogd!ok5!on4!nm4!ond!kvf!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$8?1H>4REST@1$2$9>2LF@1$2$a>1v$7>2lo$3>1B$3>1m$b>2mo$5>0$4P") := ltac2:(zQ "i81!hi1!hk4!krf!hm4!h9!ond!lnc!kv6!ooe!op6!ih4!mo4!hs3!ot4!ou5!ov2!ogd!ok5!on4!ovc!np4!nq1!nm4!hr5!pgb!ph6!pi1!pia!pj5!kvf!oo5!hka!pna!po3!ps7!psd!qh6!mjb!kr9!hmb&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h2@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$5?1H\4REST@1$6$hd\2LF@1$6$he\1v$h6\2lo$4\1B$4\1m$hf\2mo$h1\1c$h0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$5?1H\2s'@1$5?1H@2$3@3$c$d@3$hc?1H^1@1$f^h2@7$i2@hf$i1^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$i3^ic^hb@1$9@1$1@1$0#k0^2@1$i4$h7@2$3@3$h8?1H^1^h2@2$3@3$h9?1H^h3@1$e^h2@2$3@4$hb?1H^1^h9^2@2$3@5$h3^2^ib^i9^h6^h5@2$3@3$ha?1H^h8^2@2$3@7$i0?5HCEIL?1H^h9@2$i7@1$0#k0^ib@1$a@2$b$4$4^h4^2@2$i5@2$8?1H^1@2$i6@2$8?1H^ha@1$h4@1$h5^h7").

  Definition dtor_value_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i90!hi1!hk4!hmb!lnc!h9!ot4!qi1!nq1!qia!kvf!op6!mk0!hs3!qk9!ok5!on4!vf!qkf!qle!np4!qmd!qo0!nm4!qp5!hr5!pgb!ooe!pi1!pia!qpf!ond!pj5!oo5!hka!qu2!qua!po3!ps7!qh6!kpf!hre>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$f@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$5>1m$i1>1s@1$he?1H>4REST@1$3$9>2LF@1$3$i0>1v$h6>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$e>0@3$c$5@3$hf?1H^8^a@7$i5@hf$i4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c@1$i7$h1^b@1$a@1$1@1$0#k0^9@1$i6$h8>0@4$hc?1H^9@3$b$9@1$7^6^8^a>0@3$h9?1H^a@2$6^c^3>0@8$h2^c^id^ib^7^6@1$h0@1$8^8^5^e>0@3$hb?1H^a^d>0@4$h7?5HCEIL^e@2$2@1$0#k0^i7^a>0@2$d@1$8^bNi1>0@4$i2^e^d@2$2@1$0#k0^i9+h8>0@3$i3^h1@2$2@1$0#k0^ia+h8>0@2$i8@1$h3@1$7^e@2$ha?1H^h1>0$h5@3$hd?1H@ha$h4^j6^j5^j4^j3^if^ie^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^h7^h6^h3^h2^h1^h0^f^e^h4^c@2$6^h5^c").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vs_X : ltac2:(zQ "30!h9!lnc!mo4>2va$0@1$1@2$2$0$0") := ltac2:(zQ "60!h9!mo4!igd!ih4!mob!l2\2va$0@3$2@2$1$0$0@4$4$0$0^1@2$5^1+k0@1$3@2$1$0$0").
  Definition ADTOR_VS_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!vf!l2@2$1+l0@1$0Ni1").   (* [comment removed for export] *)
  Definition dtor_vs_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "40!hm4!qo0!ns7!nt5@2$0$1@2$2$3+uulp0").   (* [comment removed for export] *)   (* [comment removed for export] *)
  Definition dtor_vs_post : ltac2:(zQ "c0!hi1!hk4!h9!lnc!ogd!ok5!on4!ks5!ond!kvf!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$8?1H>4REST@1$3$9>2LF@1$3$a>2va$2>2st$7>2lo$2>1B$2>1m$b>2mo$5>0$4P") := ltac2:(zQ "ic1!hi1!hk4!krf!hm4!lnc!h9!ond!kv6!hs3!hr5!ooe!ig5!op6!ot4!ou5!ov2!ogd!ok5!on4!ovc!np4!qv8!ml0!ks5!pgb!ph6!pi1!pia!pj5!kvf!oo5!hka!rg0!pna!rgf!po3!ps7!psd!qh6!kl8!mjb!q9!kr9!hmb&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h2@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$6?1H\4REST@1$4$hd\2LF@1$4$he\2va$5\2st$h7\2lo$5\1B$5\1m$hf\2mo$h1\1c$h0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$6?1H\2s'@1$6?1H@2$3@3$8$d@3$hc?1H^1@1$f^h2@7$i4@hf$i3^id^ic^ib^ia^h1^h0^f^i9^i8^e^d^c^b^a^9^8^7^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^6^5^4^3^hd@1$i5^id^hc@1$c@1$1@1$0#k0^2@1$i6$9@2$3@3$h8?1H^1^h2@2$3@3$h9?1H^h3@1$e^h2@2$3@4$hb?1H^1^ha^2@2$3@5$h3^2^ic^ia^h6^h5@2$3@3$ha?1H^h9^2@2$3@7$i1?5HCEIL?1H^ha@2$ib@1$0#k0^ic@1$h5^h8^h4^2@2$3@2$2@1$4$b\2cs@1$4$b@2$3@4$i7$9^3^h9^1@3$8$5@1$i9@1$i2^1+k0@2$3@3$i0^2^h8+k0@2$i8@2$a?1H^1@2$ia@2$a?1H^hb@1$h4@1$h6^h7").
  Definition dtor_vs_stmt : ltac2:(zQ "00P") := ltac2:(zQ "j20!hi1!hk4!hmb!lnc!h9!ot4!qi1!ml0!rhd!ri8!rj2!kvf!hre!op6!mk0!hm4!hs3!qk9!rjb!ok5!on4!ro2!rod!rp9!qle!np4!rqb!rrb!rsc!rtb!ln0!ks5!hr5!ru4!pgb!ooe!pi1!pia!qpf!ond!pj5!oo5!hka!rg0!po3!ps7!qh6!kpf!l2!kq5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$5>1m$ia>1s@1$i7?1H>4REST@1$3$b>2LF@1$3$i9>2st$hf>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$h3>0@3$h0$5@3$i8?1H^8^a@7$id@hf$ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c@1$if$h6^b@1$d@1$1@1$0#k0^9@1$ie$i0>0@4$i5?1H^9@3$e$b@1$7^6^8^a>0@3$i2?1H^a@2$6^c^3>0@8$h8^c^id^ib^7^6$h7^5^e>0@3$i4?1H^a^d>0@4$hd?5HCEIL^e@2$2@1$0#k0^i7^a>0@3$h2$9\2it$9@2$h1@1$hc^1Ni1@1$he^b>0@3$h5^d@2$2@1$0#k0^i9+k0>0@3$ib^h1@2$2@1$0#k0^ia+k0>0@2$f@2$c@1$a?1H@1$8^e@2$j1@1$8^e@2$j0@1$a?1H$i1>0@2$c@1$h9@1$7^f@2$i3?1H^h2>0$hb@3$i6?1H@hb$ha^j7^j6^j5^j4^j0^if^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^h8^h7^h4^h3^h2@2$2@1$0#k0^ie^h1^h0^f^h5^d@2$6^h6^d").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition grow_one_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "20!ns7!nt5@2$0$1+vitm8").   (* [comment removed for export] *)   (* [comment removed for export] *)
  Definition grow_one_post : ltac2:(zQ "c0!hi1!hk4!h9!lnc!ogd!ok5!on4!ks5!ond!kvf!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$8?1H>4REST@1$3$9>2LF@1$3$a>2va$2>2st$7>2lo$2>1B$2>1m$b>2mo$5>0$4P") := ltac2:(zQ "j21!hi1!hk4!krf!hm4!h9!hs3!lnc!lh1!ks5!ond!kv6!ln0!rhd!ooe!kvf!op6!mk0!ot4!ou5!ov2!ogd!ok5!on4!ovc!ni8!nj4!qv8!ml0!rtb!kt6!ku2!ri8!hr5!pgb!ph6!pi1!pia!pj5!oo5!hka!rg0!pna!po3!ps7!psd!qh6!mjb!kq5!kr9!hmb&>0@1$1@1$0#k0@1$a@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h6@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$9?1H\4REST@1$6$e\2LF@1$6$i6\2va$4\2st$8\2lo$4\1B$4\1m$i7\2mo$h5\1c$h4@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$9?1H\2s'@1$9?1H@2$2$8\3st'$8@2$3@3$5$h1@3$i5?1H^2@1$h3^h3@7$ib@hf$ia^ie^id^ic^ib^h2^h1^h0^ia^i9^f^e^d^c^b^a^9^8^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^7^6^5^4^he@1$ic^ie^hd@1$f@1$1@1$0#k0^3@1$id$i0@2$3@3$i1?1H^2^h3@2$3@3$i2?1H^h4@1$h2^h3@2$3@4$i4?1H^2@3$h0$e@1$hb^1^hb^3@2$3@4$hc?5HCEIL^3^h9^1@2$3@3$5@1$6$hf@1$b^1@1$b^h8@2$3@3$5$4@1$hd^1Z@2$3@3$5$4@1$c^1@1$c^h8@2$3@2$if@1$he^1@1$7^1@2$3@3$5$4@1$7^1@1$h8@1$7^h8@2$3@5$h7^3^id^ib^h7^h6@2$3@3$i3?1H^ha^3@2$3@7$i9?5HCEIL?1H^hb@2$j1@1$0#k0^id@1$ha^h9^h5^3@2$3@3$i8^3^h9+k0@2$ie@2$d?1H^2@2$j0@2$d?1H^hc@1$h9^h8").
  Definition grow_one_stmt : ltac2:(zQ "00P") := ltac2:(zQ "j40!hi1!hk4!h9!hmb!hs3!kvf!mk0!lnc!ot4!qi1!ml0!lh1!ku2!rhd!rj2!l2!hre!kq5!op6!hm4!ok5!on4!ro2!hgd!ruf!rvc!ni8!nj4!sg6!sh7!rtb!kt6!ks5!hr5!ru4!mp2!pgb!ooe!pi1!pia!qpf!ond!pj5!oo5!hka!rg0!po3!ps7!qh6!kpf!q3!kr3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$8>1m$ic>1s@1$i9?1H>4REST@1$7$5>2LF@1$7$ib>2st$i0>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$h4>0@3$4$8@3$ia?1H^8^a@7$if@hf$ie^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c@1$j1$h8^b@1$h2@1$1@1$0#k0^9@1$j0$i1>0@4$i7?1H^9@3$6$5@1$a^6^8^a>0@3$i4?1H^a@2$9^c^3>0@8$h9^c^id^ib^7^6$h7^5^e>0@3$i6?1H^a^d>0@4$he?5HCEIL^e@2$3@1$0#k0^i7^a>0@3$4$2@1$hf^bZ>0@3$4$2@1$c^c@1$b^c>0@2$h1@2$f@1$c^d+1@2$j3+2+ha>0@3$h6^f@2$3@1$0#k0^ib+k0>0@3$id^h3@2$3@1$0#k0^ic+k0>0@2$h3@2$h0@1$e?1H@1$d^h0@2$h1@1$d^h0@2$f@1$e?1H$i2>0@3$i3?1H@3$6$5@1$a^h1^h3@2$j2+h8@1$ha@1$b^h1>0@2$h0@1$hb^h2@2$i5?1H^h5>0$hd@3$i8?1H@hb$hc^ja^j9^j8^j7^j3^j2^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hb^ha^h7^h6^h5@2$3@1$0#k0^j1^h4^h3^h2^h8^h0@2$9^h9^h0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition push_sca_site : ltac2:(zQ "10!h9>5entry$0$0") := ltac2:(zQ "60!ksf!h9!l2!kv0!si9!sj7\5entry$1M0\0$0$1@2$3^1$4@2$2^1+hv8M0\0$0$1@2$3^1$5@2$2^1+hv0@2$2^1+hv4").
  Definition push_sca_tr_ok : ltac2:(zQ "10!h9>5entry$0P") := ltac2:(zQ "40!h9!sk5!ns7!nt5\5entry$0@2$2$3@1$1^1").   (* [comment removed for export] *)

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint vsvals (l : list vsitem) : option (list jv) :=
    match l with
    | [] => Some []
    | VSval v :: r => match vsvals r with Some vs => Some (v :: vs) | None => None end
    | VSkey _ :: _ => None
    end.
  Definition push_array_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "10!sh7$0").   (* [comment removed for export] *)
  Definition push_array_post : ltac2:(zQ "e0!hi1!hk4!lnc!h9!ogd!ok5!on4!nm4!ri8!ks5!ond!kvf!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$a?1H>4REST@1$2$b>2LF@1$2$c>2va$3>2st$9>4keep@1$2$8>2es@1$2$7>2lo$3>1B$3>1m$d>2mo$5>0$4P") := ltac2:(zQ "jb1!hi1!hk4!krf!hm4!hs3!h9!lnc!nm4!kvf!kv6!lh1!ri8!ih4!ks5!ond!op6!mk0!lqa!rhd!ooe!q9!igd!sl6!lu3!ot4!ou5!ov2!ogd!ok5!on4!sld!ovc!ni8!qv8!sm9!sn1!ml0!sna!rtb!kt6!ln0!ku2!hr5!pgb!ph6!pi1!pia!pj5!oo5!hka!rg0!pna!po3!ps7!psd!qh6!mjb!kr9!hmb&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$hd@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$e?1H\4REST@1$6$8\2LF@1$6$j0\2va$5\2st$d\4keep@1$6$b\2es@1$6$7\2lo$5\1B$5\1m$j1\2mo$hc\1c$hb@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$e?1H\2s'@1$e?1H@2$2$d\3st'$d@2$2@1$9$8\1t@1$9$8@2$2$5\3cap$5@2$3@3$4$h8@3$if?1H^4@1$ha^h5@7$j5@hf$j4^j2^j1^j0^if^h4^h3^h2^ie^id^h1^h0^f^e^d^c^b^a^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^9^8^7^6^i2@1$j6^j2^i1@1$f@1$1@1$0#k0^5@1$j7$ia@2$3@3$ib?1H^4^h5@2$3@3$ic?1H^h6@1$h9^h5@2$3@4$ie?1H^4@3$h0$8@1$i4^3^hf^5@2$3@4$i6?5HCEIL^5^hd^3@2$3@3$4@1$6$b@1$i8^3@3$h0$b^hb@3$h5$b@1$i3@3$i2^2^1@1$i5^ha@1$c$b@2$3@3$4$5@1$i7^3Z@2$3@3$4$5@1$h2^3@1$h2^hc@2$3@2$h6@3$4@1$6$7^ha@1$c$7@3$4@1$9$8^2@1$f$8@2$3@3$4$5^1@1$h4@2$h1$7^ha@2$3@2$h7@3$4$5@1$a^3@1$a^hc@2$3@3$4@1$6$7^ha@1$c$7@2$3@3$4$5@1$i9^hc@1$a^hc@3$4$5@1$a^3@1$i0@1$a^hc@2$3@5$hf^5^j1^if^h9^h8@2$3@3$id?1H^he^5@2$3@7$j3?5HCEIL?1H^hf@2$ja@1$0#k0^j1@1$i1^hd^h7^5@2$3@3$j2^5^hd+k0@2$j8@2$h3?1H^4@2$j9@2$h3?1H^i0@2$he^hc@1$h4@2$h1$7^ha").
  Definition push_array_stmt : ltac2:(zQ "00P") := ltac2:(zQ "k40!hi1!hk4!ri8!lnc!hs3!hmb!h9!nm4!mk0!kvf!lqa!ml0!l2!q9!ih4!ot4!qi1!lh1!ku2!rhd!mp2!rj2!kpf!hre!kq5!op6!so9!kv6!hm4!sp0!qk9!rjb!ok5!on4!ro2!sp7!sq9!sld!rvc!ni8!sr6!ss9!ste!nl4!qia!rtb!kt6!ln0!ks5!hr5!ru4!pgb!ooe!pi1!pia!qpf!ond!pj5!oo5!hka!rg0!jk4!po3!ps7!qh6!kqa!q3!kr3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i1@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$f>1m$jb>1s@1$j8?1H>4REST@1$3$9>2LF@1$3$ja>2st$j0>2lo$6>1B$6>4errv@1$1@1$0#k0>2mo$i0>4keep@1$3$2>3top@1$3$2>2es@1$3$7>0@3$4$f@3$j9?1H^b^d@7$jf@hf$je^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$h6$i4^e@1$h9@1$1@1$0#k0^c@1$k0$j1>0@4$j6?1H^c@3$8$9@1$b^9^b^d>0@3$j3?1H^d@2$h0^f^6>0@8$i6^f^j0^ie^a^9$i3^8^h1>0@3$j5?1H^d^h0>0@4$jd?5HCEIL^h1^c@2$c@2$5@1$0#k0^j2+k0>0@4$id?5HCEIL^h2@2$5@1$0#k0^ib^e>0@3$4$6@1$ie^fZ>0@3$4@1$3$2@1$if^h0@3$8$2^b^a>0@3$4@1$hb@1$3$7@1$ia^b@2$ha@1$3$7^a>0@3$4@1$1@1$0#k0^ie@1$h6@1$d@2$a$2^c>0@3$hf$7\1v$7@2$he@1$ic^1Ni0^c>0@2$h8@2$c@1$h2^h4+1@2$k3+2+ha>0@3$i2^h6@2$5@1$0#k0^j2+k0>0@3$jc^ha@2$5@1$0#k0^j3+k0>0@2$hc@2$h7@1$h5?1H@1$h3^h7@2$h8@1$h3^h7@2$c@1$h5?1H$j2>0@3$4$6@2$k1@2$5@1$0#k0^j5+8Z>0>0@3$4@1$3$2^h3@1$e$2>0@3$4$6@1$h2^ha@1$h1^ha@3$h4?1H@3$8$9@1$b^hb^hd@2$k2+h8@1$i7@1$h1^hb>0>0@1$hd@3$4@1$3$2^h4@1$e$2@3$h4?1H@3$8$9@1$b^hb^hd@1$ib@1$d@2$a$2^h5>0@2$h7@2$i5^hb@1$d@2$a$2^h5@2$j4?1H^he>0$i9@3$j7?1H@hd$i8^k3^k2^k1^k0^jc^jb^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i4^i3^i0^hf^he@2$5@1$0#k0^ja^hd^h8^h6^hc^hb^i1^h9@2$h0^i2^h9").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint vskvs (l : list vsitem) : option (list (block * jv)) :=
    match l with
    | [] => Some []
    | VSkey b :: VSval v :: r => match vskvs r with Some kv => Some ((b, v) :: kv) | None => None end
    | _ => None
    end.
  Definition push_object_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "50!hm4!ns7!nt5!qo0!sh7@2$0$4@2$0$3@2$0@2$1$2+snon4@2$1$2+snunc").  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition obj_spent : ltac2:(zQ "40!h9!lnc!ks5!kvf>2st$2>1n$0>7dropped@1$1$3$0") := ltac2:(zQ "b0!ksf!h9!lnc!np4!nk7!nqd!ks5!mj3!kvf!l2!kv0\2st$6\1n$1\7dropped@1$2$8M0\0$0$1@2$a^2Z@1$4^3@2$9@2$7?1H@1$5^2@1$3^1").
  Definition push_object_post : ltac2:(zQ "f0!hi1!hk4!lnc!h9!kvf!mo4!ogd!ok5!on4!nm4!ri8!ks5!ond!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$8@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$c?1H>4REST@1$2$4>2LF@1$2$d>2va$3>2st$b>4keep@1$2$a>3kvl@1$2@2$5$4$9>2lo$3>1B$3>1m$e>2mo$7>0$6P") := ltac2:(zQ "k82!hi1!hk4!kvf!krf!hm4!nm4!mo4!hs3!h9!lnc!kv6!lh1!ri8!mk0!ih4!ks5!ond!op6!igd!lqa!nn0!qk9!su8!rhd!ooe!q9!nma!j4!sl6!lu3!rjb!nod!ot4!ou5!ov2!ogd!ok5!on4!ovc!ni8!suf!qv8!svc!sn1!tg4!nq1!ml0!qia!th2!rtb!kt6!ln0!ku2!hr5!pgb!ph6!pi1!pia!pj5!oo5!hka!rg0!pna!po3!ps7!psd!qh6!nrd!tjc!mjb!kr9!hmb&>0@1$1@1$0#k0@1$a@1$1@1$0#8&@3$7@1$9@2$6$2$5^hb@1$e@2$6$2$5\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$i5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$h0?1H\4REST@1$9$2\2LF@1$9$jb\2va$8\2st$f\4keep@1$9$c\3kvl@1$9@2$6$2$5\2lo$8\1B$8\1m$jc\2mo$i4\1c$i3@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a0@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$3@1$h0?1H\2s'@1$h0?1H@2$3$f\3st'$f@2$3@1$a$2\1t@1$a$2@2$3$8\3cap$8@2$3$h6\2ss$h6@2$4@3$7$i0@3$ja?1H^5@1$i2^h6@7$k0@hf$jf^j3^j2^j1^j0^h5^h4^h3^if^ie^h2^h1^h0^f^e^d^c^b^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^a^9^8^7^i3@1$k1^j3^i2@1$h1@1$1@1$0#k0^6@1$k2$j5@2$4@3$j6?1H^5^h6@2$4@3$j7?1H^h7@1$i1^h6@2$4@4$j9?1H^5@3$d$2@1$ie^4^i0^6@2$4@4$j1?5HCEIL^6^he^4@2$4@3$7@1$9$c@1$j3^4@3$d$c^hc@3$h2$c@1$ib@3$ia^3^2^1@1$e$c@2$4@3$7$8@1$j2^4Z@2$4@3$7$8@1$h7^4@1$h7^hd@2$4@2$hc~1@3$7@1$a$2^3@1$h1$2@2$4@3$7$8^2@1$h9@2$h3@2$6$2$5^hb@2$4>1h$hb>0@3$he@2$6$2$5\2bv@2$6$2$5@2$h5@1$if@3$h4$2$5^1^2^hc@2$h5@1$j0^3^2@2$4@2$hd@3$7$8@1$b^4@1$b^hd@2$4~1@2$4@3$7$8@1$j4^hd@1$b^hd@3$7$8@1$b^4@1$i7@1$b^hd@2$4@5$i6^6^j2^j0^ha^h9@2$4@3$j8?1H^hf^6@2$4@7$je?5HCEIL?1H^i0@2$k7@1$0#k0^j2@1$i9^he^h8^6@2$4@3$jd^6^he+k0@2$3@1$9$2\7dropped@1$9$2@2$4@3$k4$2@2$k3$2@4$hf@2$6$2$5@1$9$2\2bv@2$6$2$5@3$h2$2@3$ha$2$5^1@1$id@3$h4$2$5^1^hc@3$d$2@1$ic^2^1@2$k5@2$h8?1H^6@2$k6@2$h8?1H^i2@3$i8^he@1$h9@2$h3@2$6$2$5^hc^1").
  Definition push_object_stmt : ltac2:(zQ "00P") := ltac2:(zQ "k60!hi1!hk4!kvf!lnc!hs3!nm4!mo4!ri8!hmb!h9!mk0!lqa!ml0!l2!q9!ih4!ot4!qi1!lh1!ku2!rhd!mp2!rj2!kpf!hre!kq5!op6!so9!kv6!nn0!hm4!sp0!qk9!rjb!ok5!on4!ro2!tkb!tld!rvc!ni8!tma!tn6!tob!tq1!qia!nqd!rtb!kt6!ln0!ks5!hr5!ru4!pgb!ooe!pi1!pia!qpf!ond!pj5!oo5!hka!rg0!jk4!po3!ps7!qh6!kqa!q3!kr3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i3@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$h0>1m$jd>1s@1$ja?1H>4REST@1$3$2>2LF@1$3$jc>2st$j2>2lo$9>1B$9>4errv@1$1@1$0#k0>2mo$i2>4keep@1$3$7>3top@1$3$7>3kvl@1$3@2$6$2$5>0@3$4$h0@3$jb?1H^b^d@7$k1@hf$k0^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$h7$i6^e@1$ha@1$1@1$0#k0^c@1$k2$j3>0@4$j8?1H^c@3$a$2@1$c^9^b^d>0@3$j5?1H^d@2$h1^f^6>0@8$i7^f^j0^ie^a^9$i5^8^h1>0@3$j7?1H^d^h0>0@4$jf?5HCEIL^h1^c@2$d@2$8@1$0#k0^j2+k0>0@4$if?5HCEIL^h2@2$8@1$0#k0^ib^e>0@3$4$9@1$j0^fZ>0@3$4@1$3$7@1$j1^h0@3$a$7^b^a>0@3$4@1$hc@1$3@2$6$2$5@1$ic^b@2$hb@1$3@2$6$2$5^a>0@3$4@1$1@1$0#k0^ie@1$h7@1$e@2$b@2$6$2$5^b>0@3$i1@2$6$2$5\2bv@2$6$2$5@2$i0@1$id@3$hd$2$5^1Ni0^c>0@2$h9@2$d@1$h3^h4+1@2$k5+2+ha>0@3$i4^h6@2$8@1$0#k0^j2+k0>0@3$je^ha@2$8@1$0#k0^j3+k0>0@2$he@2$h8@1$h6?1H@1$h4^h7@2$h9@1$h4^h7@2$d@1$h6?1H$j4>0@3$4$9@2$k3@2$8@1$0#k0^j5+8Z>0>0@3$4@1$3$7^h3@1$f$7>0@3$4$9@1$h3^ha@1$h2^ha@3$h5?1H@3$a$2@1$c^hb^hd@2$k4+h8@1$i8@1$h2^hb>0>0@1$hf@3$4@1$3$7^h4@1$f$7@3$h5?1H@3$a$2@1$c^hb^hd@1$ie@1$e@2$b@2$6$2$5^h4>0@2$h8@3$i9^hb@1$e@2$b@2$6$2$5^h4^h4@2$j6?1H^he>0$ib@3$j9?1H@hd$ia^k3^k2^k1^k0^jc^jb^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i4^i3^i0^hf^he@2$8@1$0#k0^ja^hd^h8^h6^hc^hb^i1^h9@2$h1^i2^h9").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition input_ok : ltac2:(zQ "60!h9!lnc!hi1!kvf!hka!hk4>4REST@1$1$3>2sp@1$5@1$2#k0>1m$4>2p0$0>3len$0P") := ltac2:(zQ "h90!hm4!h9!l2!hi1!kvf!hk4!lnc!hs3!hre!krf!tqa!lqa!lu3!hr5!mr2!hka!qua!tr5!ts3!tsc!tt8!kq5!kqa!q9!kr3\4REST@1$6$4\2sp@1$5@1$3#k0\1m$f\2p0$1\3len$1@2$0@2$9@1$6@1$5@1$3#8\2bs@1$6@1$5@1$3#8@2$0@3$7$1@1$h7@2$b@1$5@1$3#8^1^2@4$h3$d^4^3^1@2$0@2$c@3$7$1^1Z@2$9$4\1b$4@2$0@3$h4$4^1^6@2$0@2$8@1$a^1^3@2$8@2$2^3^2@2$2@1$a^1@1$e^1@2$0@2$8Z^2@2$0@2$h5@2$2^2^1@2$h8+2+if@2$0@3$h0^3^2^1@2$0@3$h2^3^2@2$2^2^1@2$0@2$h1^2@2$2^2^1@3$7$1@2$h6^2+h0Z").

  Definition parser_X : ltac2:(zQ "30!h9!lnc!mo4>2pa$0@1$1@2$2$0$0") := ltac2:(zQ "60!h9!mo4!igd!ih4!mob!l2\2pa$0@3$2@2$1$0$0@4$4$0$0^1@2$5^1+hh8@1$3@2$1$0$0").

  (* [comment removed for export] *)
  Definition junk_ok : ltac2:(zQ "20!lnc!ri8>1l@1$0$1P") := ltac2:(zQ "50!ri8!lnc!qk9!rjb!rsc\1l@1$1$0@3$3$0\2it$0@2$2@1$4^1Ni1^1").

  (* [comment removed for export] *)
  Definition pv_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "c0!hm4!tte!si9!tv0!tvd!sj7!uga!qo0!sh7!tob!ns7!nt5@2$0$8@2$0$7@2$0$9@2$0@1$1$4@2$0@1$1$6@2$0@1$1$3@2$0@1$1$2@2$0@1$1$5@2$a$b+vjgt8").   (* [comment removed for export] *)
    (* [comment removed for export] *)

  Definition parse_value_post : ltac2:(zQ "c0!hi1!hk4!h9!lnc!ogd!ok5!on4!uh7!ond!kvf!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$8?1H>4REST@1$3$9>2LF@1$3$a>2pa$2>2ps$7>1p$2>2lo$2>1B$2>1m$b>2mo$5>0$4P") := ltac2:(zQ "k82!hi1!hk4!hm4!krf!h9!ui1!uia!hs3!lnc!ri8!hmb!kr9!mk0!mo4!ln0!ooe!on4!uj4!uh7!ond!hre!ksf!kv6!uk0!ml0!nm4!ukc!rhd!kvf!op6!igd!ul7!ih4!lu3!un1!qk9!rjb!ot4!ou5!ov2!ogd!ok5!ovc!un8!uo3!uof!lu9!sn1!qia!up8!uq5!kt6!hr5!uv0!pgb!ph6!pi1!pia!pj5!oo5!ls5!hka!rg0!pna!jod!po3!ps7!psd!qh6!l2!kq5!uve&>0@1$1@1$0#k0@1$h6@1$1@1$0#8&@2$b@1$6^hd@2$a@1$0#k0^h3\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h0@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$h3?1H\4REST@1$8$hc\2LF@1$8$jb\2pa$4\2ps$h2\1p$4\2lo$4\1B$4\1m$jd\2mo$i9\1c$i8@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a0@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$3@1$h3?1H\2s'@1$h3?1H@2$3$h2\3ps'$h2@2$3@2$h0@1$0#5@1$1@1$0#k0\2F'@2$h0@1$0#5@1$1@1$0#k0@2$3@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@1$8@2$d$4$4\2XS@1$8@2$d$4$4@2$2@3$7$i5@3$ja?1H^5@1$i7^h6@7$k2@hf$k1^j2^j1^j0^if^h5^h4^h3^ie^id^h2^h1^h0^f^e^d^c^b^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^a^9^8^7^3@1$k3^j2^2@1$hd@1$1@1$0#k0^6@1$k4$j4@2$2@1$k0^2@2$2@3$j6?1H^5^h6@2$2@3$j7?1H^h7@1$i6^h6@2$2@4$j9?1H^5@3$c$hc@1$h8@1$5^4^hf^6@2$2@4$j1?5HCEIL^6^hd^4@2$2@3$7$4@1$hb@1$5^4@1$hb@1$5^hc@2$2@3$7$h5@1$ha^4@1$ha^hc@2$2@2$i1@2$3$h9\1v$h9@2$2@2$2@2$k6^hc@2$a@1$0#k0^h3@2$h4@2$a@1$0#k0^h3@1$6^hd@2$2@3$7$4@1$6^5@1$6^hd@2$2@3$7$4@1$h1^5@1$h1^hd@2$2@3$7$h5@1$j2^5$hf@2$2@3$7@1$8$9@1$e@1$5^5@3$c$9@1$e@1$5^hd@3$he$9@1$if^1@1$i0$9@2$2@2$i3@1$j0^1@2$i2@1$k7@1$h1^hdN1@2$2@3$7$4@1$j3@1$5^5Z@2$2@4$id@1$5^5~1@1$5^hd@2$b@1$6^hd^hc@5$h7@1$5^hd@2$b@1$6^hd^hc@2$ie@1$5^5~1@2$f?1H^i1@2$f?1H^6@2$3@1$8$9\4junk@1$8$9@2$2@3$7$4@2$a@1$0#k0^h3@2$k5^he+1@2$2@2$2@2$h4^hc@1$6^5@2$h4@1$6^5@1$6^hd@2$2@3$7@1$8$9@1$e@1$5^5@3$c$9@1$e@1$5^hd^1@2$2@1$ib^1@5$h7@1$5^hd@2$b@1$6^hd^hc@1$jc@1$h8@1$5^5@2$f?1H^i1@2$f?1H^6@2$2@5$ia^6^j1^if^ha^h9@2$2@3$j8?1H^he^6@2$2@3$i4@2$d$4$4@3$j5?5HCEIL?1H^he^1@2$2@7$jf?5HCEIL?1H^hf@2$a@1$0#k0^j1@3$c@2$d$4$4@1$ic^hd^1^h8^6@3$je^6^hd+hh8").

  (* [comment removed for export] *)
  Definition parse_value_stmt_at_d : ltac2:(zQ "10!h9>5entry$0>6budget>0$0$0>5first>0$0P>1d$0P") := ltac2:(zQ "k50!hi1!hk4!h9!hmb!hs3!ui1!uia!kpf!hm4!kvf!l2!hre!kq5!kr9!mk0!ksf!ul7!lnc!qk9!ot4!qi1!ml0!uj4!rhd!ri8!hr5!rj2!oo5!op6!igd!lqa!ih4!krf!un1!rjb!ok5!on4!ro2!rvc!vg7!vh3!vi8!vj3!vje!rsc!up8!uq5!ukc!uh7!kt6!ln0!ku2!vka!ru4!pgb!ooe!pi1!pia!qpf!ond!pj5!hka!rg0!po3!ps7!tsc!qh6!kqa!kr3\5entry$2\6budget>0$2$2\5first>0$2P\1d$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$h3>1m$jd>1s@1$jb?1H>4REST@1$h1$9>2LF@1$h1$hb>2ps$j0>2p0$2>3len$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$i3>0@3$4$2@1$h6^7^ie>0@3$4$h3@3$jc?1H^b^d@7$k0@hf$jf^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$7^j2^e@1$hc@1$1@1$0#k0^c@1$k2$h9>0@4$j9?1H^c@3$e$9@1$h5@1$5^9^b^d>0@3$j6?1H^d@2$h4^f^4>0@8$i6^f^j0^ie^8^7@1^j4@1$h6^b^6^h1>0@3$j8?1H^d^h0>0@2$h2@2$i1@2$he$hb^eN1$j4>0@4$id?5HCEIL^h2@2$3@1$0#k0^ib^e>0@3$4$f@1$if^f$h0>0@3$4$f@1$ie^h0$h0>0@3$4$2@1$j1@1$5^h1Z>0@5$i7^h4^j7^h6^h1^h0>0@2$8@2$b^h2@2$3@1$0#k0^if@2$c@2$3@1$0#k0^if@1$6^h3>0@3$4$2@1$6^h4@2$a^h3^h2>0@2$i0@1$1@1$0#8\1b@1$1@1$0#8@2$8@4$k1$h9^ha@2$3@1$0#k0^j2@3$hd@1$1@1$0#8^1@1$hf@1$1@1$0#8@1^je@2$3@1$0#8^1>0@3$4@1$1@1$0#k0^j1@1$7Z>0@3$4@1$1@1$0#k0^j0@1$7Z>0@3$4@1$1@1$0#k0^j0@1$7Z>0@3$4@1$1@1$0#k0^j0@1$7Z>0@3$i5^hb@2$3@1$0#k0^j7+hh8>0@3$je^hf@2$3@1$0#k0^j8+hh8>0@2$8@2$b@1$ha?1H@1$h7@1$5^hc@2$c@1$h7@1$5^hc@2$a@1$ha?1H$j5>0@2$c@2$a@1$j3@1$5^hd@2$d@1$6^hd@2$3@1$0#k0^j9@2$k4+2+ha>0@3$i2$h8\2it$h8@2$h2@1$ic^1Ni1@1$j2@1$5^he>0@3$4$2@2$k3@2$3@1$0#k0^jc+h0Z>0@3$ia@3$e$9@1$h5@1$5^i0^i2@1$5^i0@2$d@1$6^i0@2$3@1$0#k0^jc>0@2$b@2$i9@1$5^i1@2$d@1$6^i1@2$3@1$0#k0^jd@2$j7?1H^i4>0$ib@3$ja?1H@hc$i8^k9^k8^k7^k6^k2^k1^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ia^i9^i6^i5^i4@2$3@1$0#k0^k0^i3@2$3@1$0#k0^jf^i0^hf^i7^hd@2$h4^i8^hd").

  Definition parse_value_stmt_at : ltac2:(zQ "10!h9>5entry$0>6budget>0$0$0>5first>0$0PP") := ltac2:(zQ "20!h9!vl8\5entry$0\6budget>0$0$0\5first>0$0P>1d$0@4$1^4^3^2^1").

  (* [comment removed for export] *)
  Definition APV_STACK : ltac2:(zQ "10!h9>1d$0$0") := ltac2:(zQ "50!l2!h9!vf!r2!q3\1d$1@2$0@2$0@2$0@2$4+q0^1+og0$3@1$2Ni1").
  (* [comment removed for export] *)
  Definition APV_NUM_STACK : ltac2:(zQ "10!h9>1d$0$0") := ltac2:(zQ "30!h9!vn2!kr9\1d$0@2$2@1$1^1+j0").

  (* [comment removed for export] *)
  Definition parse_key_post : ltac2:(zQ "c0!hi1!hk4!h9!lnc!ogd!ok5!on4!uh7!ond!kvf!oo5!hka>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$8?1H>4REST@1$3$9>2LF@1$3$a>2pa$2>2ps$7>1p$2>2lo$2>1B$2>1m$b>2mo$5>0$4P") := ltac2:(zQ "k32!hi1!hk4!hm4!krf!h9!ui1!uia!hs3!lnc!ri8!hmb!kr9!mk0!mo4!ln0!ooe!kvf!on4!uh7!ond!hre!ksf!kv6!uk0!ml0!uj4!ukc!rhd!op6!igd!ul7!ih4!lu3!rjb!ot4!ou5!ov2!ogd!ok5!ovc!un8!uo3!uof!lu9!vnf!up8!uq5!kt6!hr5!uv0!pgb!ph6!pi1!pia!pj5!oo5!ls5!hka!rg0!pna!jod!po3!ps7!psd!qh6!l2!kq5&>0@1$1@1$0#k0@1$h6@1$1@1$0#8&@2$b@1$6^hd@2$a@1$0#k0^h3\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h1@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$h3?1H\4REST@1$8$h0\2LF@1$8$j7\2pa$4\2ps$h2\1p$4\2lo$4\1B$4\1m$j9\2mo$i6\1c$i5@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a0@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$3@1$h3?1H\2s'@1$h3?1H@2$3$h2\3ps'$h2@2$3@2$h1@1$0#5@1$1@1$0#k0\2F'@2$h1@1$0#5@1$1@1$0#k0@2$3@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@1$8@2$d$4$4\2XS@1$8@2$d$4$4@2$2@3$7$i2@3$j6?1H^5@1$i4^h6@7$je@hf$jd^j2^j1^j0^if^h5^h4^h3^ie^id^h2^h1^h0^f^e^d^c^b^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^a^9^8^7^3@1$jf^j2^2@1$hc@1$1@1$0#k0^6@1$k0$j0@2$2@1$jc^2@2$2@3$j2?1H^5^h6@2$2@3$j3?1H^h7@1$i3^h6@2$2@4$j5?1H^5@3$c$h0@1$h8@1$5^4^hf^6@2$2@4$id?5HCEIL^6^hd^4@2$2@3$7$4@1$hb@1$5^4@1$hb@1$5^hc@2$2@3$7$h5@1$ha^4@1$ha^hc@2$2@2$i0@2$3$h0\1b$h0@2$2@2$2@2$k2^hc@2$a@1$0#k0^h3@2$h4@2$a@1$0#k0^h3@1$6^hd@2$2@3$7$4@1$6^5@1$6^hd@2$2@3$7$4@1$h9^5@1$h9^hd@2$2@3$7$h5@1$ie^5$he@2$2@3$7@1$8$9@1$e@1$5^5@3$c$9@1$e@1$5^hd@3$hd$9@1$ic^1@1$hf$9@2$2@3$7$4@1$if@1$5^5Z@2$2@4$ia@1$5^5~1@1$5^hd@2$b@1$6^hd^hc@5$h7@1$5^hd@2$b@1$6^hd^hc@2$ib@1$5^5~1@2$f?1H^i1@2$f?1H^6@2$3@1$8$9\4junk@1$8$9@2$2@3$7$4@2$a@1$0#k0^h3@2$k1^he+1@2$2@2$2@2$h4^hc@1$6^5@2$h4@1$6^5@1$6^hd@2$2@3$7@1$8$9@1$e@1$5^5@3$c$9@1$e@1$5^hd^1@2$2@1$i8^1@5$h7@1$5^hd@2$b@1$6^hd^hc@1$j8@1$h8@1$5^5@2$f?1H^i1@2$f?1H^6@2$2@5$i7^6^j1^if^ha^h9@2$2@3$j4?1H^he^6@2$2@3$i1@2$d$4$4@3$j1?5HCEIL?1H^he^1@2$2@7$jb?5HCEIL?1H^hf@2$a@1$0#k0^j1@3$c@2$d$4$4@1$i9^hd^1^h8^6@3$ja^6^hd+hh8").

  Definition parse_key_stmt : ltac2:(zQ "00P") := ltac2:(zQ "k70!hi1!hk4!hmb!hs3!ui1!h9!uia!kpf!hm4!kvf!l2!hre!kq5!kr9!mk0!ksf!ul7!lnc!qk9!ot4!qi1!ml0!rhd!ri8!hr5!rj2!oo5!op6!igd!lqa!ih4!krf!un1!rjb!ok5!on4!ro2!vo8!vn2!rvc!vg7!vp6!vi8!vj3!vje!rsc!up8!uj4!uq5!ukc!uh7!kt6!ln0!ku2!vka!ru4!pgb!ooe!pi1!pia!qpf!ond!pj5!hka!rg0!po3!ps7!tsc!qh6!kqa!kr3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i3@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$h3>1m$jf>1s@1$jd?1H>4REST@1$h1$9>2LF@1$h1$ha>2ps$j2>2p0$5>3len$5>2lo$5>1B$5>4errv@1$1@1$0#k0>2mo$i2>0@3$3$h3@3$je?1H^a^c@7$k2@hf$k1^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e@1$7$i5^d@1$hb@1$1@1$0#k0^b@1$k4$h8>0@4$jb?1H^b@3$e$9@1$h5@1$4^8^a^c>0@3$j8?1H^c@2$h4^e^3>0@8$i7^e^if^id^7^6@1$i6@1$if^a^5^h0>0@3$ja?1H^c^f>0@2$h2@2$i0@2$hd$ha^dN1$j6>0@4$ie?5HCEIL^h1@2$2@1$0#k0^ia^d>0@3$3$f@1$j1^e$h0>0@3$3$f@1$j0^f$h0>0@3$3$5@1$j3@1$4^h0Z>0@5$i8^h3^j6^h5^h0^f>0@2$8@2$b^h1@2$2@1$0#k0^ie@2$c@2$2@1$0#k0^ie@1$6^h2>0@3$3$5@1$6^h3@2$a^h2^h1>0@2$hf@1$1@1$0#8\1b@1$1@1$0#8@2$8@4$k3$h8^h9@2$2@1$0#k0^j1@3$hc@1$1@1$0#8^1@1$he@1$1@1$0#8@3$3$5@2$2@1$0#8^1+i2>0@3$3@1$1@1$0#k0^j0@1$7Z>0@3$3@1$1@1$0#k0^if@1$7Z>0@3$3@1$1@1$0#k0^if@1$7Z>0@3$i4^h9@2$2@1$0#k0^j5+hh8>0@3$k0^hd@2$2@1$0#k0^j6+hh8>0@2$8@2$b@1$h9?1H@1$h6@1$4^ha@2$c@1$h6@1$4^ha@2$a@1$h9?1H$j7>0@2$c@2$a@1$j5@1$4^hb@2$d@1$6^hb@2$2@1$0#k0^j7@2$k6+2+ha>0@3$i1$h7\2it$h7@2$h2@1$id^1Ni1@1$j4@1$4^hc>0@3$3$5@2$k5@2$2@1$0#k0^ja+h0Z>0@3$ib@3$e$9@1$h5@1$4^he^i0@1$4^he@2$d@1$6^he@2$2@1$0#k0^ja>0@2$b@2$ia@1$4^hf@2$d@1$6^hf@2$2@1$0#k0^jb@2$j9?1H^i2>0$ic@3$jc?1H@hc$i9^k7^k6^k5^k4^k0^jf^j6^j5^j4^j3^j2^j1^j0^if^ie^id^i8^i7^i4^i3^i2@2$2@1$0#k0^je^i1@2$2@1$0#k0^jd^he^hd^i5^hb@2$h4^i6^hb").

  Definition any_first (_ : Z) : Prop := True.
  Definition parse_value_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!vq8!vn2!vr4!vl8\1d$0@4$4$1$2$3^1").
  Definition parse_array_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!hs3!vs1!vn2!vl8\1d$0@4$4$2$3\1b$0@3$1$0^1+lb^1").
  Definition parse_object_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!hs3!vsd!vn2!vl8\1d$0@4$4$2$3\1b$0@3$1$0^1+nb^1").
  Definition parse_value_stmt : ltac2:(zQ "00P") := ltac2:(zQ "40!vq8!vn2!vr4!vta@3$3$0$1$2").
  Definition parse_array_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!vs1!vn2!vta@3$4$2$3\1b$0@3$1$0^1+lb").   (* [comment removed for export] *)
  Definition parse_object_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!vsd!vn2!vta@3$4$2$3\1b$0@3$1$0^1+nb").  (* [comment removed for export] *)
  Definition parse_string_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!vv2!vn2!vta@3$4$2$3\1b$0@3$1$0^1+i2").   (* [comment removed for export] *)
  Definition parse_num0_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!vvf!hgg8!vta@3$4$2$3\1b$0@3$1$0^1+j0").          (* [comment removed for export] *)
  Definition parse_numneg_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!hgh9!hgg8!vta@3$4$2$3\1b$0@3$1$0^1+id").
  Definition parse_numpos_stmt : ltac2:(zQ "00P") := ltac2:(zQ "60!hre!hm4!h9!hgi4!hgg8!vta@3$5$3$4\1b$2@2$1@2$0+j1^1@2$0^1+j9").
  Definition parse_null_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!hgif!vn2!vta@3$4$2$3\1b$0@3$1$0^1+me").
  Definition parse_true_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!hgjc!vn2!vta@3$4$2$3\1b$0@3$1$0^1+n4").
  Definition parse_false_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!hs3!hgk9!vn2!vta@3$4$2$3\1b$0@3$1$0^1+m6").
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma parse_family_by_depth : ltac2:(zQ "a2!h9!hm4!hgl7!hgme!hgo5!hre!kq5!hgpd!hgr2!hgs8&>0@2$1@2$5Z^1@2$6^1^2@1$2^2&>2d'$0~0>0>1d$0>0~1@1$3^2>0>1d$0>0~1@1$4^2>0>1d$0>0@1$3^1>0@1$4^2@1$2^3@2$1$9@2$1$7$8").
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Iface.
(* [comment removed for export] *)
