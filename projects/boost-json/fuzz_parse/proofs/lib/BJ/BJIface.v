(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~jacROPDEL_STACK46Stdlib6ZArith6BinInt1Zob3addob3mulob6of_natja3ehkjacROPNEW_STACKja8eh_STACKob3max79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface~~~~~~tebRDTOR_STACKteeRVS_GROW_STACK04Npos35stdpp9bitvectorbdefinitionshk02bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hm33mem37Corelib4Init5Logichr43andob2lehk0bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hu35rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ii84cellhc4conshc3nilhr42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~infabj_staticsja7eh_idlejabhs_rauxv_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~iu05hceilii82C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~jia4frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jmb3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jqe7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jv38rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kja2wzhm34RATPob3powob3subhr42exhc4listja5framehr45Falseja8chain_spjabeh_chain_okjabfr_callsite3h5LinuxProcessSemanticsfLinuxProcessSem3Runkt46config3h5LinuxProcessSemanticsfLinuxProcessSem5Statelga5Model3h5LinuxProcessSemantics5Riscv7Preludelk15bvmaphm35blockhc6optionkt49cfg_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~lof6PStatehc4None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsltcdmachine_statekt46cfg_ms89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface5Iface~~~~~~mieh0bj_env_post_coreja7hs_KRELja8hs_MPRESja8hs_RHEAPjmb3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mqd2MSmqd6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mva7seg_romhm3arheap_presinf7jheighthc3app37Corelib4Init5Peanonm32lekt45mkCfgmiebbj_env_coremiefdtor_value_posttebRDTOR_VALUEinf8blocks_vinf2jvinf6val_atja5hs_SRhm3drclient_rangehc4prodhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJFrame~~~~~~nv95xpresmie4vs_Xii8acells_sizeinf7vs_tempinf6vsitem37Corelib5Lists7ListDefoma6ForallmieeRDTOR_VS_STACKmiecdtor_vs_postte8RVS_DTORinf9blocks_vsinfbitem_heightinf5vs_atinf8vs_itemsinf6vstackob2ltmiebbj_env_postinf6vs_capinf8vs_charsinf4vs_nltc6ms_memja6EH_IVSja4eh_Xhr42ormie6bj_envmie8chain_atmiefmaybe_grow_postmieemaybe_grow_unwtedRVS_MAYBEGROWja3csrja7fr_liveja5mkCSRinf4Jscainf5VSvalhr43notmiedpush_sca_postmieasca_pay_okteeRVS_PUSH_STACKii82C8mieh0push_sca_stmt_attedRVS_PUSH_NULLtedRVS_PUSH_BOOLtecRVS_PUSH_I64tecRVS_PUSH_U64tecRVS_PUSH_DBLhr43iffinf4Jarrinfbjvs_of_listinf6vs_bufhc4Somehc6lengthmiefpush_array_postmieepush_array_unwmie6vsvalstecRVS_PUSH_ARRteh2RVS_PUSH_ARR_STACKjabsaves_clearinf3kvshc3sndinf4Jobjinfakvs_heighthm38blk_addrjqe8bytes_athm38blk_size36Stdlib5Lists4Listrj92Ininf6pstateinf5ps_vsinf6ps_endinf8ps_depthhc4boolinf7ps_morehc5false37Corelib4Init3Natrp53addmie7junk_okmie8parser_Xinf9parser_atinf8ps_ecsetob6to_natmie8input_okmieh0parse_value_postmiefparse_value_unwmieh5parse_value_stmt_at_dinf5VSkeymie9RPV_STACKmieeparse_key_posttecRP_KEYSTRINGmie9any_firstte8RP_VALUEte8RP_ARRAYte9RP_OBJECTmieh3parse_value_stmt_atte9RP_STRINGte7RP_NUM0te9RP_NUMNEGte9RP_NUMPOSte7RP_NULLte7RP_TRUEte8RP_FALSEmieh2parse_value_stmt_dmieh2parse_array_stmt_dmieh3parse_object_stmt_dmieh0parse_array_stmtmieh1parse_object_stmtmieh0parse_value_stmtja3hmf" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RDTOR_VALUE   : Z := 0x56db4.   (* [comment removed for export] *)
Definition RVS_DTOR      : Z := 0x5965c.   (* [comment removed for export] *)
Definition RVS_MAYBEGROW : Z := 0x599a4.   (* [comment removed for export] *)
Definition RVS_PUSH_ARR  : Z := 0x5976c.   (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RVS_PUSH_OBJ  : Z := 0x59b40.   (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RVS_PUSH_CHARS: Z := 0x59cb8.   (* [comment removed for export] *)
Definition RVS_PUSH_KEY1 : Z := 0x59e58.   (* [comment removed for export] *)
Definition RVS_PUSH_KEY2 : Z := 0x5a080.   (* [comment removed for export] *)
Definition RVS_PUSH_STR  : Z := 0x5a2a4.   (* [comment removed for export] *)
Definition RVS_PUSH_SV   : Z := 0x5a450.   (* [comment removed for export] *)
Definition RVS_PUSH_ESTR : Z := 0x5a66c.   (* [comment removed for export] *)
Definition RVS_PUSH_I64  : Z := 0x5a7d8.
Definition RVS_PUSH_U64  : Z := 0x5a950.
Definition RVS_PUSH_DBL  : Z := 0x5aac8.
Definition RVS_PUSH_BOOL : Z := 0x5ac40.
Definition RVS_PUSH_NULL : Z := 0x5adb8.
Definition RSTR_ASSIGN   : Z := 0x54bfc.   (* [comment removed for export] *)
Definition RSTR_RESERVE  : Z := 0x56ab0.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RPARSER_REL   : Z := 0x4e614.   (* [comment removed for export] *)
Definition RBP_DTOR      : Z := 0x4e788.   (* [comment removed for export] *)
Definition RDS_DTOR      : Z := 0x5b6b0.   (* [comment removed for export] *)
Definition RWRITE_SOME   : Z := 0x4f498.
Definition RP_DOCUMENT   : Z := 0x5db9c.   (* [comment removed for export] *)
Definition RP_VALUE      : Z := 0x5e1c8.   (* [comment removed for export] *)
Definition RP_MSUSPEND   : Z := 0x5e120.   (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_NULL       : Z := 0x5ec60.
Definition RP_TRUE       : Z := 0x5ed80.
Definition RP_FALSE      : Z := 0x5eeb4.
Definition RP_FAIL       : Z := 0x5efac.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_STRING     : Z := 0x5f25c.   (* [comment removed for export] *)
Definition RP_ARRAY      : Z := 0x5f6e4.
Definition RP_OBJECT     : Z := 0x5fa78.
Definition RP_NUM0       : Z := 0x5fe3c.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_NUMNEG     : Z := 0x6136c.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_NUMPOS     : Z := 0x636e8.   (* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_ESCAPED    : Z := 0x65658.   (* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Definition RP_KEYSTRING  : Z := 0x666ac.   (* [comment removed for export] *)
Definition RJSON_PARSE   : Z := 0x4e130.
Definition RFUZZ_PARSE   : Z := 0x47870.
Definition RLLVM_FUZZ    : Z := 0x47978.   (* [comment removed for export] *)
Definition RMEMCPY : Z := 0xeada8.  
 

(* [comment removed for export] *)
Definition RDTOR_STACK : ltac2:(zQ "20!j4!h9>1h$0$1") := ltac2:(zQ "50!j4!nc!q3!q9!qf\1h$0@2$2@2$3+k0@1$4^1$1").
Definition RVS_GROW_STACK : ltac2:(zQ "20!h9!r8>1E$1$0") := ltac2:(zQ "40!q3!re!sd!r8\1E$3@2$0@2$0+j0$1@1$2^1").     (* [comment removed for export] *)
Definition RVS_PUSH_STACK : ltac2:(zQ "20!h9!r8>1E$1$0") := ltac2:(zQ "40!q3!re!sd!r8\1E$3@2$0@2$0+m0$1@1$2^1").     (* [comment removed for export] *)
Definition RVS_PUSH_ARR_STACK : ltac2:(zQ "20!h9!r8>1E$1$0") := ltac2:(zQ "70!q3!t8!hhb!hi9!re!sd!r8\1E$6@2$0+m0@2$1@1$3^1@2$1@2$0$4@1$5^1@2$0+i0@1$2Ni1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!to6$0").
  Variable E : ltac2:(zQ "10!r8$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).

  (* [comment removed for export] *)
  Definition bj_env : ltac2:(zQ "40!hja!hld!h9!hqd>1m$3>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2lo$2>1B$2>6budget$2>4errv@1$1@1$0#k0>2fc@1$1@1$0#i0P") := ltac2:(zQ "ha0!hs8!hja!hld!hsf!ht4!h9!ihf!im4!imc!in3!in9!ira!is8!it2!jhb!ji4!jm3!jq7!ju8!kie!kn5!knb!hqd!q3!ko3!ko9\1m$h6\2sp@1$2@1$1#k0\2tp@1$2@1$1#k0\2lo$5\1B$5\6budget$5\4errv@1$2@1$1#k0\2fc@1$2@1$1#i0@2$0@3$d?1H^8^4@2$0@2$0@2$3@2$4@1$1#k0^7^4@2$3^4@2$h8+2+k0@2$0@4$h1$6^8^5@2$4@1$1#k0^7@2$0@2$3@1$e?5HCEIL^5@2$0@2$3^5@2$h9@2$4@1$1#k0^7^3@2$0@4$h3$6^8@2$h7@2$4@1$1#k0^6-q4@3$8$7@1$f^2@1$9$7@2$0@2$h2$6^8@2$0@3$a@1$2@1$1#k0^6@1$h4$h5@2$0@1$b^8@2$0@2$c?1E^8@1$h0^1").                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bj_env_post : ltac2:(zQ "40!hja!h9!hld!hqd>2m'$3>2sp@1$2@1$0#k0>2tp@1$2@1$0#k0>2lo$1>1B$1P") := ltac2:(zQ "h30!hja!hs8!hld!ihf!h9!im4!ht4!imc!in3!kof!ira!is8!it2!ji4!jq7!ju8!kie!hqd!q3\2m'$h1\2sp@1$2@1$0#k0\2tp@1$2@1$0#k0\2lo$4\1B$4@2$1@3$c?1H^5^1@2$1@4$e$3^5^2@2$6@1$0#k0^4@2$1@2$9@1$2@1$0#k0\5errv'@1$2@1$0#k0@4$h0$3^6@2$h2@2$6@1$0#k0^4-q4@3$7$5@1$d^1@1$8$5@2$1@2$f$3^5@2$1@1$a^5@2$b?1E^5").
  (* [comment removed for export] *)
  Definition bj_env_core : ltac2:(zQ "40!hja!hld!h9!hqd>1m$3>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2lo$2>1B$2>6budget$2>4errv@1$1@1$0#k0>2fc@1$1@1$0#i0P") := ltac2:(zQ "h80!hs8!hja!hld!hsf!ht4!h9!ihf!im4!imc!in3!in9!ira!it2!jhb!ji4!jq7!ju8!kie!kn5!knb!hqd!q3!ko3!ko9\1m$h4\2sp@1$2@1$1#k0\2tp@1$2@1$1#k0\2lo$5\1B$5\6budget$5\4errv@1$2@1$1#k0\2fc@1$2@1$1#i0@2$0@3$c?1H^8^4@2$0@2$0@2$3@2$4@1$1#k0^7^4@2$3^4@2$h6+2+k0@2$0@4$f$6^8^5@2$4@1$1#k0^7@2$0@2$3@1$d?5HCEIL^5@2$0@2$3^5@2$h7@2$4@1$1#k0^7^3@2$0@4$h1$6^8@2$h5@2$4@1$1#k0^6-q4@3$8$7@1$e^2@1$9$7@2$0@2$h0$6^8@2$0@3$a@1$2@1$1#k0^6@1$h2$h3@1$b^8").
  (* [comment removed for export] *)
  Definition bj_env_post_core : ltac2:(zQ "40!hja!h9!hld!hqd>2m'$3>2sp@1$2@1$0#k0>2tp@1$2@1$0#k0>2lo$1>1B$1P") := ltac2:(zQ "h20!hja!hs8!hld!ihf!h9!im4!ht4!imc!in3!kof!ira!it2!ji4!jq7!ju8!kie!hqd!q3\2m'$h0\2sp@1$2@1$0#k0\2tp@1$2@1$0#k0\2lo$4\1B$4@2$1@3$b?1H^5^1@2$1@4$d$3^5^2@2$6@1$0#k0^4@2$1@2$9@1$2@1$0#k0\5errv'@1$2@1$0#k0@4$f$3^6@2$h1@2$6@1$0#k0^4-q4@3$7$5@1$c^1@1$8$5@2$1@2$e$3^5@1$a^5").

  (* [comment removed for export] *)
  Definition chain_at : ltac2:(zQ "50!hja!hld!kp5!kpc!hqd>1G@1$2$3>1m$4>2sp@1$1@1$0#k0>2ra@1$1@1$0#k0P") := ltac2:(zQ "f0!kp5!hja!kpc!hld!hs8!in9!kq4!h9!kqd!kr8!ks6!kn5!hqd!q3!ht4\1G@1$0$2\1m$c\2sp@1$3@1$1#k0\2ra@1$3@1$1#k0@2$4@3$9?1E^4^3@2$4@3$5$7@1$8^4@2$e@1$1#k0^2M0\1G@1$0$2P^4$6\1g$2\1l@1$0$2@3$5@1$3@1$1#k0^3@1$b@2$d@1$a^2+4").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dtor_value_post : ltac2:(zQ "90!hja!hld!h9!kp5!lg0!lj8!lm7!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$7>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "hd1!hja!hld!kof!hs8!ln9!h9!lo2!lsb!lt5!kp5!in9!mh3!mi4!lg0!lj8!lm7!mn1!mo6!mp0!mpb!mq6!mua!mv0!nj9!ln0!hqd!nk4!ihf!ht4&>0@1$1@1$0#k0@1$4@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$f@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$h8\2lo$5\1B$5\1m$h9\2mo$e\1c$d@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$7\2s'$7@2$3@3$a$b@1$c^h2@7$h5@hf$h4^i9^i8^i7^i6^h1^h0^f^i5^i4^e^d^c^b^a^9^8^7^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^6^5^4^3^h9@1$h6^i9^h8@1$8@1$1@1$0#k0^2@1$h7$hb@2$3@3$h1?1H^1@1$6^h2@2$3@3$h2?1H^h3@1$6^h2@2$3@4$h3?1H^1^h7^2@2$3@5$h0^2^i8^i6^h6^h5@4$ha^h7@2$hc@1$0#k0^i8^h4^2").

  Definition dtor_value_stmt : ltac2:(zQ "00P") := ltac2:(zQ "hf0!hja!hld!ht4!h9!nl2!ln0!lt5!nld!kp5!nn7!nnd!lj8!lm7!no6!np5!hhb!nq8!nr6!ns2!ns8!mo6!mpb!nt2!mq6!mua!nj9!kn5!hqd!nta!ihf!lsb>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hb>1s$he>4REST@1$8$5>1v$h2>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$b>0@4$h5?1H^7@3$7$5@1$h1^5^6^8>0@3$h4?1H^8^2>0@8$d^a^ia^i8^6^5@1$f@1$4^7^4^b>0@4$h3?5HCEIL^b@2$2@1$0#k0^i3^8>0@2$9@1$4^9Ni1>0@4$hc^b@2$2@1$0#k0^id@2$2@1$0#k0^i5+h8@3$h6?1H@h7$e^if^ie^id^ic^i8^i7^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h0^f^c^a^9^e^7@2$a@7$h8@hf$h7^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0@1$ha$h0^f@1$6@1$1@1$0#k0^e@1$h9$hd^7").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vs_X : ltac2:(zQ "30!h9!kp5!nub>2va$0@1$1@2$2$0$0") := ltac2:(zQ "60!h9!nub!imc!in3!nv2!q3\2va$0@3$2@2$1$0$0@4$4$0$0^1@2$5^1+k0@1$3@2$1$0$0").

  (* [comment removed for export] *)
  Definition RDTOR_VS_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!hhb!q3@2$1+i0@1$0Ni1").
  Definition dtor_vs_post : ltac2:(zQ "90!hja!hld!h9!kp5!lg0!lj8!lm7!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$7>2va$2>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "i21!hja!hld!kof!hs8!h9!kp5!ln9!in9!lo2!im4!ihf!lsb!lt5!mh3!mi4!lg0!lj8!lm7!oj6!mn1!ojf!mo6!mp0!mpb!ok7!mq6!mua!mv0!nj9!kie!ln0!hqd!qf!ht4&>0@1$1@1$0#k0@1$6@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h1@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$5$he\2va$4\2lo$4\1B$4\1m$hf\2mo$h0\1c$f@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$b\2s'$b@2$3@3$7$d@1$e^h2@7$ha@hf$h9^ia^i9^i8^i7^h1^h0^f^i6^i5^e^d^c^b^a^9^8^7^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@1$hb^ia^h9@1$c@1$1@1$0#k0^2@1$hc$a@2$3@3$h5?1H^1@1$8^h2@2$3@3$h6?1H^h3@1$8^h2@2$3@4$h7?1H^1^h8^2@2$3@5$h3^2^i9^i7^h6^h5@2$3@5$h2^h8@2$i1@1$0#k0^i9@1$h4^h7^h4^2@2$2@1$5$9\2cs@1$5$9@2$3@4$hd$a^3^h8^1@3$7$4@1$i0@1$h8^1+k0").   (* [comment removed for export] *)
  Definition dtor_vs_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i80!hja!hld!ht4!hsf!hs8!h9!ol5!om0!ln0!lt5!nld!kp5!nn7!oo1!nnd!lj8!lm7!oob!no6!opd!oqd!or8!os5!ot4!otd!ou9!mo6!mpb!nt2!jhb!mq6!mua!nj9!kn5!hqd!ihf!lsb!q3!ov3!ko3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i2>1s$i4>4REST@1$b$8>2st$h9>2lo$5>1B$5>4errv@1$1@1$0#k0>2mo$f>0@4$hb?1H^7@3$a$8@1$h5^5^6^8>0@3$ha?1H^8^2>0@8$h2^a^ia^i8^6^5$h1^4^b>0@4$h7?5HCEIL^b@2$2@1$0#k0^i3^8>0@3$d$7\2it$7@2$c@1$h6^1Ni1@1$h8^9>0@2$4@2$3@2$2@1$0#k0^id@2$2@1$0#k0^i5@2$3@2$i5@2$2@1$0#k0^i5+k0^8>0@2$4@2$3@1$hd?5HCEIL@1$6^b@2$i6@1$6^b@2$i7+2+k0@3$hc?1H@h8$h3^j0^if^ie^id^i9^i8^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h1^h0^d@2$2@1$0#k0^i7^b^a^f^8@2$e@7$hf@hf$he^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1@1$i1$h4^h0@1$9@1$1@1$0#k0^f@1$i0$i3^8").

  Definition maybe_grow_post : ltac2:(zQ "a0!hja!hld!h9!kp5!lg0!lj8!lm7!ou9!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2va$2>2st$7>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "i91!hja!hld!kof!hs8!h9!in9!ou9!kp5!ln9!lo2!otd!ol5!ln0!lsb!lt5!nld!mh3!mi4!lg0!lj8!lm7!oj6!ov8!ojf!or8!ot4!pg7!ph1!phd!om0!mo6!mp0!mpb!mq6!mua!mv0!nj9!hqd!ihf!ov3!ht4&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h4@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$7$c\2va$4\2st$6\2lo$4\1B$4\1m$i5\2mo$h3\1c$h2@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$d\2s'$d@2$2$6\3st'$6@2$3@3$5$h0@1$h1^h3@7$i2@hf$i1^ic^ib^ia^i9^h2^h1^h0^i8^i7^f^e^d^c^b^a^9^8^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^7^6^5^4^hc@1$i3^ic^hb@1$e@1$1@1$0#k0^3@1$i4$i6@2$3@3$he?1H^2@1$9^h3@2$3@3$hf?1H^h4@1$9^h3@2$3@4$i0?1H^2@3$f$c@1$h8^1^ha^3@2$3@4$h9?5HCEIL^3^h9^1@2$3@3$5@1$7$hd@1$a^1@1$a^h8@2$3@3$5$4@1$hb^1Z@2$3@3$5$4@1$b^1@1$b^h8@2$3@2$i7@1$hc^1@1$ha^1@2$3@5$h6^3^ib^i9^h7^h6@5$h5^ha@2$i8@1$0#k0^ib@1$h7^h9^h5^3").

  (* [comment removed for export] *)
  Definition maybe_grow_unw : ltac2:(zQ "a0!h9!kp5!hja!hld!lg0!lj8!ou9!kpc!ln0!hqd>2sp@1$3@1$2#k0>1G@1$1$7>4REST@1$1$8>2va$0>2st$6>2lo$0>1B$0>2fc@1$3@1$2#i0>1m$9>2mo$5>0$4P") := ltac2:(zQ "hb0!h9!hs8!hja!pi5!mi4!nld!kp5!ln0!lsb!hld!nub!kof!lo2!lg0!lj8!oj6!ojf!ira!or8!ot4!ou9!pif!pj8!kpc!mp0!hqd!ht4\2sp@1$9@1$2#k0\1G@1$6$h7\4REST@1$6$7\2va$0\2st$h4\2lo$0\1B$0\2fc@1$9@1$2#i0\1m$h9\2mo$e\1c$d@2$b$8\2s'$8@2$1@8$h6?1E^b^1@3$5$7@1$h2^8^a^7^6^5^2@2$1@3$h8?1H^3@1$c^2@2$1@4$h3?5HCEIL@1$3@1$4^2^9^8@2$1@1$h1@1$3@1$4^2@5$f^a@2$ha@1$2#k0^c@3$5@2$a$0$0@1$h0^9$h5^4@1$3@1$4^2").

  Definition maybe_grow_stmt : ltac2:(zQ "00P") := ltac2:(zQ "if0!hja!hld!ht4!kpc!h9!hsf!imc!kp5!hs8!in9!ol5!ln0!q3!ov3!ko3!lt5!nld!pjf!lg0!nnd!lj8!lm7!pk5!pkf!plb!pme!hi9!po0!or8!ot4!ph1!phd!ou9!pp0!pp6!mo6!mpb!nt2!pq0!jhb!mq6!mua!nj9!kn5!hqd!ihf!lsb>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$ic>1s$ie>4REST@1$7$b>2st$i0>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$h4>1g$3>1G@1$7$3>0@4$i4?1H^9@3$h0$b@1$hc^7^8^a>0@3$i3?1H^a^4>0@8$h6^c^ic^ia^8^7@1$ha?1E^6^d>0@4$hd?5HCEIL^d@2$2@1$0#k0^i5^a>0@3$9$4@1$he^bZ>0@2$d@2$c@1$hf^c+1@2$e+2+ha>0@2$8@2$5@2$2@1$0#k0^j0@2$2@1$0#k0^i8@2$5@2$c@2$2@1$0#k0^i8+k0^b>0@2$8@2$5@1$i7?5HCEIL@1$a^e@2$d@1$a^e@2$e+2+k0>0@4$h7@3$6$3^a^9^h2^j2^j3>0@3$9$i1@1$i2^b@d$i6^j3^id^ic^i3^i2^i1^i0^hf^he^hd^hc^hb^ha@3$i5?1H\1c$h2@2$h1@ha$h8^j6^j5^j4^j3^if^ie^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^h7^h6^h3@2$2@1$0#k0^id^h2^h1^h0^h5^e^1@b$h9^j5@3$6$3^d^c^h3@2$2@1$0#k0^id^h2^h1^h0^h6^h5^e^1@2$h3@7$i9@hf$i8^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@1$ib$hb^h5@1$f@1$1@1$0#k0^h4@1$ia$id^d").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition push_sca_post : ltac2:(zQ "a0!hja!hld!h9!kp5!lg0!lj8!lm7!ou9!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2va$2>2st$7>1k$2>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "ia1!hja!hld!kof!hs8!h9!in9!om0!lm7!ou9!nld!kp5!ln9!lo2!otd!ol5!ln0!lsb!lt5!imc!in3!mh3!mi4!lg0!lj8!oj6!ov8!ojf!pq8!pr0!or8!ot4!ph1!mo6!mp0!mpb!mq6!mua!mv0!nj9!hqd!ihf!ht4&>0@1$1@1$0#k0@1$b@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$7@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$a$f\2va$4\2st$8\1k$4\2lo$4\1B$4\1m$i7\2mo$h7\1c$h6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h0\2s'$h0@2$2$8\3st'$8@2$2@2$7@1$0#5@1$1@1$0#k0\2F'@2$7@1$0#5@1$1@1$0#k0@2$3@3$5$h4@1$h5^h4@7$i4@hf$i3^ie^id^ic^ib^h3^h2^h1^ia^i9^h0^f^e^d^c^b^a^9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^8^7^6^5^1@1$i5^ie^hd@1$h1@1$1@1$0#k0^4@1$i6$i8@2$3@3$i0?1H^3@1$c^h4@2$3@3$i1?1H^h5@1$c^h4@2$3@4$i2?1H^3@3$9$f@1$hd^2^hc^4@2$3@4$he?5HCEIL^4^hb^2@2$3@3$5@1$a$6@1$d^2@3$9$6@1$d^ha@3$h2$6@1$hc@1$hb^h9@1$h3$6@2$3@3$5$4@1$hf^2Z@2$3@3$5$4@1$e^2@1$e^ha@2$3@5$h9^4^id^ib^h8^h7@5$h8^hc@2$i9@1$0#k0^id@1$ha^hb^h6^4").

  (* [comment removed for export] *)
  Definition sca_pay_ok : ltac2:(zQ "20!h9!im4>1k$0>2pc$1P") := ltac2:(zQ "a0!hja!hld!kq4!im4!h9!hsf!kp5!j4!hs8!in9\1k$4\2pc$3M3\2pc$3P^1\1v@1$1@1$0#k0@2$8@2$5+2^3@2$5^3+4\1v@1$1@1$0#k0$2\1v@1$1@1$0#k0$2\1b@1$1@1$0#8@3$9$4^3+1\1n$7\2bs@1$6@1$1@1$0#8$2").

  Definition push_sca_stmt_at : ltac2:(zQ "10!h9>5entry$0>1k$0P") := ltac2:(zQ "j40!hja!hld!ht4!h9!hsf!q3!hs8!in9!im4!imc!pjf!kpc!pr9!ihf!kp5!in3!ol5!kie!kn5!ln0!ov3!ko3!lt5!nld!lg0!nnd!lj8!lm7!pk5!pkf!pme!ps0!pt1!ptf!or8!ot4!ph1!phd!ou9!pp0!pp6!mo6!mpb!nt2!pq0!jhb!pv0!mq6!mua!nj9!hqd!lsb\5entry$3\1k$3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hb@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j2>1s$j3>4REST@1$e$h3>2st$i6>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$ha>1g$b>1G@1$e$b>5pcell$8>0@4$ia?1H^a@3$h7$h3@1$i2^8^9^b>0@3$i9?1H^b^5>0@8$hc^d^id^ib^9^8@1$i1?1E^7^e>0@4$i3?5HCEIL^e@2$2@1$0#k0^i6^b>0@3$7$3@1$i4^cZ>0@2$6@2$4@2$2@1$0#k0^j0@2$2@1$0#k0^i8@2$4@2$5@2$2@1$0#k0^i8+k0^b>0@2$6@2$4@1$id?5HCEIL@1$h0^e@2$h4@1$h0^e@2$h5+2+k0>0>0@1$c@3$7$3^j4Z@2$6@2$i0^j5^9@2$6@4$h1$d^h3@2$2@1$0#k0^ia@3$9$8^9@1$f$8@2$6@2$4@2$2@1$0#k0^j3@2$2@1$0#k0^ia@2$a@2$4@2$5@2$2@1$0#k0^ia+8@2$2@1$0#k0^ib@2$4@2$5@2$2@1$0#k0^ib+k0@2$2@1$0#k0^ia>0>0@1$c@3$7$3^j5Z@4$h1$d^h4@2$2@1$0#k0^ia@3$9$8@1$ie@1$h2Z@1$f$8>0>0@1$c@3$7$3^j6Z@2$a@3$7$3@2$2@1$0#k0^ib@2$5@2$2@1$0#k0^id+j8@2$6@2$4@2$2@1$0#k0^j5@2$2@1$0#k0^ib@2$a@2$4@2$5@2$2@1$0#k0^ib+8@2$2@1$0#k0^id@2$4@2$5@2$2@1$0#k0^id+k0@2$2@1$0#k0^ib>0@2$h4@2$5@1$i5^h2+1@2$h5+2+ha>0@4$hd@3$9$b^e^d^h6^j6^j7>0@3$7$i7@1$i8^f@d$ic^j7^j1^j0^i7^i6^i5^i4^i3^i2^i1^i0^hf^he@3$ib?1H\1c$h8@2$a@hb$hf^ja^j9^j8^j7^j3^j2^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hb^ha^h7@2$2@1$0#k0^j1^h6^jb^h5^h4^h9^h2^1@b$he^j9@3$9$b^h1^h0^h7@2$2@1$0#k0^j1^h6^h5^h4^ha^h9^h2^1@2$h9@7$j0@hf$if^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha@1$h2^jb^h9@1$h6@1$1@1$0#k0^h8@1$j1$d^h1").
  Definition push_null_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!pv6!qgb@2$0$1Z").
  Definition push_bool_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!pv6!qhb@2$0$1+1").
  Definition push_i64_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!pv6!qib@2$0$1+2").
  Definition push_u64_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!pv6!qja@2$0$1+3").
  Definition push_dbl_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!pv6!qk9@2$0$1+4").
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint vsvals (l : list vsitem) : option (list jv) :=
    match l with
    | [] => Some []
    | VSval v :: r => match vsvals r with Some vs => Some (v :: vs) | None => None end
    | VSkey _ :: _ => None
    end.

  Definition push_array_post : ltac2:(zQ "c0!hja!hld!kp5!h9!lg0!lj8!lm7!ns2!om0!ou9!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$2$a>2va$3>2st$9>4keep@1$2$8>2es@1$2$7>2lo$3>1B$3>1m$b>2mo$5>0$4P") := ltac2:(zQ "id1!hja!hld!kof!hs8!h9!in9!ln0!kp5!ln9!om0!ns2!ou9!lt5!nld!in3!lo2!ol5!lsb!imc!ql8!mh3!mi4!lg0!lj8!lm7!oj6!ov8!ojf!qlf!pr0!or8!qm7!ot4!ph1!otd!mo6!mp0!mpb!mq6!mua!mv0!nj9!hqd!ihf!ht4&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$7$6\2va$4\2st$b\4keep@1$7$9\2es@1$7$a\2lo$4\1B$4\1m$ia\2mo$h7\1c$h6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h1\2s'$h1@2$2$b\3st'$b@2$2@1$8$6\1t@1$8$6@2$2$4\3cap$4@2$3@3$5$h4@1$h5^h5@7$i7@hf$i6^j0^if^ie^id^h4^h3^h2^ic^ib^h1^h0^f^e^d^c^b^a^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^9^8^7^6^i0@1$i8^j0^hf@1$c@1$1@1$0#k0^5@1$i9$ib@2$3@3$i3?1H^4@1$f^h5@2$3@3$i4?1H^h6@1$f^h5@2$3@4$i5?1H^4@3$d$6@1$he^3^he^5@2$3@4$i0?5HCEIL^5^hd^3@2$3@3$5@1$7$9@1$i2^3@3$d$9^hb@3$h2$9@1$hd@3$hc^2^1@1$hf^ha@1$e$9@2$3@3$5$4@1$i1^3Z@2$3@3$5$4@1$h0^3@1$h0^hc@2$3@2$h3@3$5@1$7$a^ha@1$e$a@3$5@1$8$6^2@1$c$6@2$3@5$ha^5^if^id^h9^h8@5$h9^he@2$ic@1$0#k0^if@1$hb^hd^h7^5").

  (* [comment removed for export] *)
  Definition push_array_unw : ltac2:(zQ "b0!kp5!h9!hja!hld!lg0!lj8!om0!ou9!kpc!ln0!hqd>2sp@1$3@1$2#k0>1G@1$0$8>4REST@1$0$9>2va$1>2st$7>4keep@1$0$6>2lo$1>1B$1>2fc@1$3@1$2#i0>1m$a>2mo$5>0$4P") := ltac2:(zQ "i40!hs8!h9!in9!kp5!hja!pi5!mi4!otd!om0!ou9!ln0!nld!kof!qn6!pg7!ol5!lsb!hld!ln9!nub!pjf!lo2!lg0!lj8!oj6!ojf!ira!or8!ot4!ph1!pif!pj8!kpc!mp0!hqd!ht4\2sp@1$h1@1$4#k0\1G@1$3$i0\4REST@1$3$a\2va$1\2st$9\4keep@1$3$8\2lo$1\1B$1\2fc@1$h1@1$4#i0\1m$i2\2mo$h7\1c$h6@2$c$h0\2s'$h0@2$c$9\3st'$9@2$0@8$hf?1E^d^2@3$b$a@1$hb^1^c^8^7^6^3@2$0@3$i1?1H^4@1$h5^3@2$0@4$hc?5HCEIL@1$5@1$6^3^b^1@2$0@1$ha@1$5@1$6^3@2$0@2$h4@3$2@1$3$8@1$7^1^9@3$2@1$3$8@1$7^1@1$7^a@2$0@3$2$1@1$hd^1Z@2$0@3$2$1@1$f^1@1$f^a@2$0@3$2@1$h2$a@1$d^1@1$d^a@2$0@3$2$1@1$e^1@1$e^a@5$h8^c@2$i3@1$4#k0^e@3$b@2$h3$1$1@1$h9^b$he^5@1$5@1$6^3").

  Definition push_array_stmt : ltac2:(zQ "00P") := ltac2:(zQ "jc0!hja!hld!kp5!ht4!in9!ns2!om0!kpc!imc!h9!hsf!nld!hs8!ol5!kn5!ln0!q3!ov3!ko3!lt5!qo0!qo7!ln9!pjf!nn7!oo1!lg0!nnd!lj8!lm7!pk5!pkf!qp0!qq3!ojf!qr5!qrf!qse!or8!nl2!ot4!ph1!otd!phd!ou9!pp0!pp6!mo6!mpb!nt2!pq0!qu4!jhb!mq6!mua!nj9!hqd!ihf!lsb!qf>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hd@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j8>1s$ja>4REST@1$2$f>2st$ic>2lo$9>1B$9>4errv@1$1@1$0#k0>2mo$hc>1g$7>1G@1$2$7>4keep@1$2$6>3top@1$2$6>2es@1$2$5>0@4$j0?1H^c@3$b$f@1$i6^a^b^d>0@3$if?1H^d^7>0@8$he^f^if^id^b^a@1$i5?1E^9^h0>0@4$i8?5HCEIL^h0@2$3@1$0#k0^i8^d>0@3$4$9@1$i9^eZ>0@3$4@1$2$6@1$ia^f@3$b$6^8^7>0@3$4@1$h6@1$2$5@1$i3^8@2$h4@1$2$5^7>0@3$4@1$1@1$0#k0^ib@1$e@1$jb@2$h5$6^9>0@3$h9$5\1v$5@2$h8@1$i7^1Ni0^9>0@2$h1@2$h0@1$ib^h3+1@2$h2+2+ha>0@2$c@2$a@2$3@1$0#k0^j7@2$3@1$0#k0^if@2$a@2$h0@2$3@1$0#k0^if+k0^h2>0@2$c@2$a@1$j4?5HCEIL@1$d^h5@2$h1@1$d^h5@2$h2+2+k0>0@4$hf@3$8$7^h1^h0^h9^j9^ja>0@3$4$id@1$ie^h2@d$j2^ja^j4^j3^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1>0@3$j3?1E@3$8$7^h3^h2@1$i2@2$3@1$0#k0^j3@3$j1?1H\1c$ha@2$h7@hc$i0^je^jd^jc^jb^j7^j6^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^hf^he^hb@2$3@1$0#k0^j5^ha^h3^h1^h9^h8^hd^h6^1@c$i1^jd@3$8$7^h5^h4^hb@2$3@1$0#k0^j5^ha^h3^h9^h8^he^hd^h6^1@2$hb@7$j6@hf$j5^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he@1$e$i4^hd@1$h3@1$1@1$0#k0^hc@1$j7$j9^h5").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint vskvs (l : list vsitem) : option (list (block * jv)) :=
    match l with
    | [] => Some []
    | VSkey b :: VSval v :: r => match vskvs r with Some kv => Some ((b, v) :: kv) | None => None end
    | _ => None
    end.
  Definition RVS_PUSH_OBJ_STACK (E : ehk) : Z := 400 + ROPNEW_STACK + eh_STACK E + RDTOR_STACK 33.

  Definition push_object_post : ltac2:(zQ "d0!hja!hld!kp5!h9!ln0!nub!lg0!lj8!lm7!ns2!om0!ou9!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$8@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$2$4>2va$3>2st$b>4keep@1$2$a>3kvl@1$2@2$5$4$9>2lo$3>1B$3>1m$c>2mo$7>0$6P") := ltac2:(zQ "j41!hja!hld!kof!ln0!hs8!h9!in9!ns2!kp5!ln9!nub!om0!ou9!lt5!nld!in3!nn7!lo2!qv2!ol5!lsb!imc!j4!qv9!ql8!oo1!mh3!mi4!lg0!lj8!lm7!oj6!ov8!ojf!qvf!pr0!or8!nl2!rg7!ot4!ph1!otd!mo6!mp0!mpb!mq6!mua!mv0!nj9!hqd!ihf!ht4&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$he@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$8$3\2va$5\2st$c\4keep@1$8$b\3kvl@1$8@2$a$3$7\2lo$5\1B$5\1m$j1\2mo$hd\1c$hc@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h4\2s'$h4@2$2$c\3st'$c@2$2@1$9$3\1t@1$9$3@2$2$5\3cap$5@2$2$h2\2ss$h2@2$4@3$6$ha@1$hb^h6@7$ie@hf$id^j1^j0^if^ie^h5^h4^h3^id^ic^h2^h1^h0^f^e^d^c^b^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^a^9^8^7^i1@1$if^j1^i0@1$d@1$1@1$0#k0^6@1$j0$j2@2$4@3$ia?1H^5@1$h1^h6@2$4@3$ib?1H^h7@1$h1^h6@2$4@4$ic?1H^5@3$e$3@1$i4^4^hf^6@2$4@4$i7?5HCEIL^6^he^4@2$4@3$6@1$8$b@1$i9^4@3$e$b^hc@3$h5$b@1$i3@3$i2^3^2^1@1$f$b@2$4@3$6$5@1$i8^4Z@2$4@3$6$5@1$h3^4@1$h3^hd@2$4@2$h8@3$6@1$8@2$a$3$7^hb@1$f@2$a$3$7@3$6@1$9$3^3@1$d$3@2$4>1h$h6>0@3$h9@2$a$3$7\2bv@2$a$3$7@2$h0@1$i5@3$h7$3$7^1^2^hc@2$h0@1$i6^3^2@2$4@5$i0^6^j0^ie^ha^h9@5$hf^hf@2$j3@1$0#k0^j0@1$i1^he^h8^6").

  Definition push_object_unw : ltac2:(zQ "b0!kp5!h9!hja!hld!lg0!lj8!om0!ou9!kpc!ln0!hqd>2sp@1$3@1$2#k0>1G@1$0$8>4REST@1$0$9>2va$1>2st$7>4keep@1$0$6>2lo$1>1B$1>2fc@1$3@1$2#i0>1m$a>2mo$5>0$4P") := ltac2:(zQ "i10!hs8!h9!kp5!in9!hja!pi5!mi4!otd!om0!ou9!nld!kof!ol5!ln0!lsb!hld!nub!pjf!lo2!lg0!lj8!oj6!ojf!ira!or8!ot4!ph1!pif!pj8!kpc!mp0!hqd!ht4\2sp@1$f@1$4#k0\1G@1$2$hd\4REST@1$2$d\2va$1\2st$9\4keep@1$2$8\2lo$1\1B$1\2fc@1$f@1$4#i0\1m$hf\2mo$h4\1c$h3@2$b$e\2s'$e@2$b$9\3st'$9@2$0@8$hc?1E^d^2@3$a$d@1$h8^1^c^8^7^6^3@2$0@3$he?1H^4@1$h2^3@2$0@4$h9?5HCEIL@1$5@1$6^3^b^1@2$0@1$h7@1$5@1$6^3@2$0@2$h1@3$3@1$2$8@1$7^1^9@3$3@1$2$8@1$7^1@1$7^a@2$0@3$3$1@1$ha^1Z@2$0@3$3$1@1$c^1@1$c^a@5$h5^c@2$i0@1$4#k0^e@3$a@2$h0$1$1@1$h6^b$hb^5@1$5@1$6^3").

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
      SR (fun c =>    push_object_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc REST (bv_unsigned a0) st keep kvl lo B m mo c
                   \/ push_object_unw sp (g :: G) REST (bv_unsigned a0) st keep lo B fc m mo c)
         (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz RVS_PUSH_OBJ) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition input_ok : ltac2:(zQ "60!h9!kp5!hja!ln0!hqd!hld>4REST@1$1$3>2sp@1$5@1$2#k0>1m$4>2p0$0>3len$0P") := ltac2:(zQ "h50!hs8!hja!h9!ln0!hld!kp5!q3!hsf!in9!kof!rh5!qo7!pjf!ri1!rid!hqd!ihf!rkc!ov3!qf!ko3\4REST@1$5$3\2sp@1$4@1$1#k0\1m$f\2p0$2\3len$2@2$0@2$9@1$5@1$4@1$1#8\2bs@1$5@1$4@1$1#8@2$0@3$8$2@1$h3@2$b@1$4@1$1#8^1^2@4$d$h0^4^3^1@2$0@2$c@3$8$2^1Z@2$9$3\1b$3@2$0@3$h1$3^1^6@2$0@2$7@1$a^1^3@2$7@2$6^3^2@2$6@1$a^1@1$e^1@2$0@2$7Z^2@2$h2@2$6^2^1@2$h4+2+if").          (* [comment removed for export] *)

  Definition parser_X : ltac2:(zQ "30!h9!kp5!nub>2pa$0@1$1@2$2$0$0") := ltac2:(zQ "60!h9!nub!imc!in3!nv2!q3\2pa$0@3$2@2$1$0$0@4$4$0$0^1@2$5^1+hh8@1$3@2$1$0$0").

  (* [comment removed for export] *)
  Definition junk_ok : ltac2:(zQ "20!kp5!om0>1l@1$0$1P") := ltac2:(zQ "50!om0!kp5!nn7!oo1!os5\1l@1$1$0@3$3$0\2it$0@2$2@1$4^1Ni1^1").

  Definition parse_value_post : ltac2:(zQ "a0!hja!hld!h9!kp5!lg0!lj8!lm7!rl2!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2pa$2>2ps$7>1p$2>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "jb1!hja!hld!kof!hs8!in9!h9!rlc!om0!rm5!kp5!otd!ht4!nld!lm7!rmf!rl2!hsf!rnb!ln9!lo2!ns2!ro2!ol5!ln0!lsb!lt5!imc!rod!in3!pjf!rq7!nn7!mh3!mi4!lg0!lj8!oj6!ov8!rqe!rr9!pr0!or8!nl2!rs5!rt2!ph1!mo6!mp0!mpb!jm3!mq6!mua!mv0!nj9!hqd!ihf!q3!ov3!rte&>0@1$1@1$0#k0@1$h2@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$d@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$h7\2pa$5\2ps$f\1p$5\2lo$5\1B$5\1m$j6\2mo$i3\1c$i2@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h8\2s'$h8@2$2$f\3ps'$f@2$2@2$d@1$0#5@1$1@1$0#k0\2F'@2$d@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$4$i0@1$i1^h5@7$j3@hf$j2^if^ie^id^ic^h4^h3^h2^ib^ia^h1^h0^f^e^d^c^b^a^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^9^8^7^6^2@1$j4^if^1@1$h9@1$1@1$0#k0^5@1$j5$j7@2$3@1$j1^1@2$3@3$ie?1H^4@1$h3^h5@2$3@3$if?1H^h6@1$h3^h5@2$3@4$j0?1H^4@3$c$h7@1$i9@1$6^3^hd^5@2$3@4$ib?5HCEIL^5^hc^3@2$3@3$4$5@1$h6@1$6^3@1$h6@1$6^hb@2$3@3$4$h1@1$h5^3@1$h5^hb@2$3@2$hd@2$2$h4\1v$h4@2$3@2$3@2$j9^hb@2$b@1$0#k0^h2@2$h0@2$b@1$0#k0^h2@1$8^hc@2$3@3$4$5@1$8^4@1$8^hc@2$3@3$4$5@1$e^4@1$e^hc@2$3@3$4$h1@1$ic^4$hb@2$3@3$4@1$9$7@1$a@1$6^4@3$c$7@1$a@1$6^hc@3$ha$7@1$i8^1@1$hc$7@2$3@2$hf@1$ia^1@2$he@1$ja@1$e^hcN1@3$4$5@1$id@1$6^4Z@2$2@1$9$7\4junk@1$9$7@2$3@3$4$5@2$b@1$0#k0^h2@2$j8^hd+1@2$3@2$3@2$h0^hb@1$8^4@2$h0@1$8^4@1$8^hc@2$3@3$4@1$9$7@1$a@1$6^4@3$c$7@1$a@1$6^hc^1@1$i6^1@2$3@5$i5^5^ie^ic^h9^h8@5$i4^hd@2$b@1$0#k0^ie@1$i7^hc^h7^5").

  Definition parse_value_unw : ltac2:(zQ "a0!h9!kp5!hja!hld!lg0!lj8!rl2!kpc!ln0!hqd>2sp@1$3@1$2#k0>1G@1$1$7>4REST@1$1$8>2pa$0>2ps$6>2lo$0>1B$0>2fc@1$3@1$2#i0>1m$9>2mo$5>6budget$0>0$4P") := ltac2:(zQ "i20!hs8!h9!kp5!hja!rlc!kof!om0!hld!nld!pi5!mi4!rl2!in9!otd!ol5!ln0!lsb!nub!lo2!lg0!lj8!oj6!rqe!rr9!ira!or8!rs5!pif!pj8!kpc!mp0!jm3!hqd!ht4\2sp@1$7@1$3#k0\1G@1$2$hd\4REST@1$2$f\2pa$1\2ps$b\2lo$1\1B$1\2fc@1$7@1$3#i0\1m$i0\2mo$h4\6budget$1\1c$h3@2$5$h0\2s'$h0@2$5$b\3ps'$b@2$5@1$2$6\4junk@1$2$6@2$5@1$7@1$3#i0\3fc'@1$7@1$3#i0@2$0@1$hf^1@2$0@8$hc?1E^f^4@3$8$f@1$h9@1$4^3^e^b^a^1^5@2$0@3$he?1H^7@1$h2^5@2$0@4$ha?5HCEIL@1$9@1$a^5^d^3@2$0@1$h8@1$9@1$a^5@2$0@3$c$1@1$e@1$4^3@1$e@1$4^c@2$0@3$c@1$2$6@1$d@1$4^3@3$8$6@1$d@1$4^c^2@2$0@1$h6^2@5$h5^e@2$i1@1$3#k0^h0@3$8@2$h1$1$1@1$h7^d$hb^8@1$9@1$a^5").

  (* [comment removed for export] *)
  Definition parse_value_stmt_at_d : ltac2:(zQ "10!h9>5entry$0>6budget>0$0$0>5first>0$0P>1d$0P") := ltac2:(zQ "jf0!hja!hld!ht4!h9!in9!q3!rlc!kpc!kn5!imc!hs8!rmf!rm5!hsf!rnb!rod!kp5!om0!ln0!ihf!ov3!lt5!nld!in3!kof!pjf!nn7!oo1!lg0!nnd!lj8!lm7!pk5!pkf!ru7!rv3!sg8!rr9!or8!os5!rs5!rt2!ro2!rl2!ph1!otd!phd!ol5!pp0!pp6!mo6!mpb!nt2!pq0!qu4!mq6!mua!ri1!nj9!hqd!lsb!ko3!ko9\5entry$3\6budget>0$3$3\5first>0$3P\1d$3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hf@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$jb>1s$jc>4REST@1$h0$h2>2ps$ib>2p0$3>3len$3>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$he>1g$7>1G@1$h0$7>0@3$4$3@1$b^9^ie>0@4$j3?1H^c@3$h6$h2@1$i6@1$6^a^b^d>0@3$j2?1H^d^5>0@8$i0^f^if^id^9^8@1^j3@1$b^c^7^h0>0@4$i8?5HCEIL^h0@2$2@1$0#k0^i8^d>0@3$4$e@1$ia^e$f>0@3$4$e@1$i9^f$f>0@3$4$3@1$ic@1$6^h0Z>0@5$i2^h2^j4^h4^h0^f>0@2$a@2$d^h1@2$2@1$0#k0^ic@2$h4@2$2@1$0#k0^ic@1$c^h2>0@3$4$3@1$c^h3@2$5^h2^h1>0@2$h8@1$1@1$0#8\1b@1$1@1$0#8@2$a@4$j9$h3^h8@2$2@1$0#k0^if@3$9@1$1@1$0#8^1@1$h7@1$1@1$0#8@1^jb@2$2@1$0#8^1>0@3$4@1$1@1$0#k0^ie@1$8Z>0@3$4@1$1@1$0#k0^id@1$8Z>0@3$4@1$1@1$0#k0^id@1$8Z>0@3$4@1$1@1$0#k0^id@1$8Z>0@2$a@2$d@2$5@2$2@1$0#k0^jc+o8@2$2@1$0#k0^j4@2$d@2$5@2$5@2$2@1$0#k0^j4+hh8+hg0^h5>0@3$4$3@1$if@1$6^ha@2$5@2$2@1$0#k0^j5+hh8>0@2$h4@2$5@1$ie@1$6^hb@2$je@1$c^hb@2$2@1$0#k0^j5@2$jd+2+ha>0@3$hb$h1\2it$h1@2$ha@1$i7^1Ni1@1$id@1$6^hc>0@4$i1@3$9$7^h6^h5^i0^k0^k1>0@3$4$j0@1$j1^h7@d$j5^k1^jb^ja^j1^j0^if^ie^id^ic^ib^ia^i9^i8>0@3$j6?1E@3$9$7^h8^h7@1$i5@2$2@1$0#k0^ja@3$j4?1H\1c$hc@2$h9@hb$i3^k5^k4^k3^k2^je^jd^j4^j3^j2^j1^j0^if^ie^id^ic^ib^i6^i5^i2@2$2@1$0#k0^jc^i1@2$2@1$0#k0^jb^he^hd^i4^hb^1@c$i4^k4@3$9$7^ha^h9^i2@2$2@1$0#k0^jc^i1^he^hd^i5^i4^hb@1^k8@1$b^i1^1@2$hd@7$j8@hf$j7^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5@1$8^k8^i4@1$h5@1$1@1$0#k0^i3@1$ja$h3^ha").

  Definition parse_value_stmt_at : ltac2:(zQ "10!h9>5entry$0>6budget>0$0$0>5first>0$0PP") := ltac2:(zQ "20!h9!shb\5entry$0\6budget>0$0$0\5first>0$0P>1d$0@4$1^4^3^2^1").

  (* [comment removed for export] *)
  Definition RPV_STACK : ltac2:(zQ "10!h9>1d$0$0") := ltac2:(zQ "60!q3!h9!hhb!re!sd!q9\1d$1@2$0@2$0@2$0@2$0@2$5+n0^1+kg0$3@1$4?1E@1$2Ni1").

  (* [comment removed for export] *)
  Definition parse_key_post : ltac2:(zQ "a0!hja!hld!h9!kp5!lg0!lj8!lm7!rl2!ln0!hqd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2pa$2>2ps$7>1p$2>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "j61!hja!hld!kof!hs8!in9!h9!rlc!om0!rm5!kp5!otd!ln0!ht4!nld!lm7!rl2!hsf!rnb!ln9!lo2!rmf!ro2!ol5!lsb!lt5!imc!rod!in3!pjf!mh3!mi4!lg0!lj8!oj6!ov8!rqe!rr9!sj5!or8!rs5!rt2!ph1!mo6!mp0!mpb!jm3!mq6!mua!mv0!nj9!hqd!ihf!q3!ov3&>0@1$1@1$0#k0@1$h2@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$e@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$b\2pa$5\2ps$f\1p$5\2lo$5\1B$5\1m$j2\2mo$i0\1c$hf@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$h7\2s'$h7@2$2$f\3ps'$f@2$2@2$e@1$0#5@1$1@1$0#k0\2F'@2$e@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$4$hd@1$he^h5@7$if@hf$ie^if^ie^id^ic^h4^h3^h2^ib^ia^h1^h0^f^e^d^c^b^a^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^9^8^7^6^2@1$j0^if^1@1$h8@1$1@1$0#k0^5@1$j1$j3@2$3@1$id^1@2$3@3$ia?1H^4@1$h3^h5@2$3@3$ib?1H^h6@1$h3^h5@2$3@4$ic?1H^4@3$d$b@1$i6@1$6^3^hd^5@2$3@4$i7?5HCEIL^5^hc^3@2$3@3$4$5@1$h6@1$6^3@1$h6@1$6^hb@2$3@3$4$h1@1$h5^3@1$h5^hb@2$3@2$hc@2$2$b\1b$b@2$3@2$3@2$j5^hb@2$c@1$0#k0^h2@2$h0@2$c@1$0#k0^h2@1$8^hc@2$3@3$4$5@1$8^4@1$8^hc@2$3@3$4$5@1$h4^4@1$h4^hc@2$3@3$4$h1@1$i8^4$ha@2$3@3$4@1$9$7@1$a@1$6^4@3$d$7@1$a@1$6^hc@3$h9$7@1$i5^1@1$hb$7@3$4$5@1$i9@1$6^4Z@2$2@1$9$7\4junk@1$9$7@2$3@3$4$5@2$c@1$0#k0^h2@2$j4^hd+1@2$3@2$3@2$h0^hb@1$8^4@2$h0@1$8^4@1$8^hc@2$3@3$4@1$9$7@1$a@1$6^4@3$d$7@1$a@1$6^hc^1@1$i3^1@2$3@5$i2^5^ie^ic^h9^h8@5$i1^hd@2$c@1$0#k0^ie@1$i4^hc^h7^5").

  Definition parse_key_stmt : ltac2:(zQ "00P") := ltac2:(zQ "k10!hja!hld!ht4!in9!h9!q3!rlc!kpc!imc!kn5!hs8!rm5!hsf!rnb!rod!kp5!sje!rmf!om0!ln0!ihf!ov3!lt5!nld!in3!kof!pjf!nn7!oo1!lg0!nnd!lj8!lm7!pk5!pkf!ru7!skb!sg8!rr9!sld!or8!os5!rs5!rt2!ro2!rl2!ph1!otd!phd!ol5!pp0!pp6!mo6!mpb!nt2!pq0!qu4!mq6!mua!ri1!nj9!hqd!lsb!ko3!ko9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$jd>1s$je>4REST@1$f$h3>2ps$id>2p0$4>3len$4>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$hf>1g$7>1G@1$f$7>0@4$j5?1H^b@3$h7$h3@1$i8@1$6^9^a^c>0@3$j4?1H^c^4>0@8$i1^e^ie^ic^8^7@1$h0@1$h1^b^6^f>0@4$ia?5HCEIL^f@2$2@1$0#k0^i7^c>0@3$3$d@1$ic^d$e>0@3$3$d@1$ib^e$e>0@3$3$4@1$ie@1$6^fZ>0@5$i3^h1^j3^h3^f^e>0@2$a@2$c^h0@2$2@1$0#k0^ib@2$h5@2$2@1$0#k0^ib@1$b^h1>0@3$3$4@1$b^h2@2$5^h1^h0>0@2$h9@1$1@1$0#8\1b@1$1@1$0#8@2$a@4$jb$h4^h7@2$2@1$0#k0^ie@3$8@1$1@1$0#8^1@1$h8@1$1@1$0#8@3$3$4@2$2@1$0#8^1+i2>0@3$3@1$1@1$0#k0^id@1$9Z>0@3$3@1$1@1$0#k0^ic@1$9Z>0@3$3@1$1@1$0#k0^ic@1$9Z>0@2$a@2$c@2$5@2$2@1$0#k0^ja+o8@2$2@1$0#k0^j2@2$c@2$5@2$5@2$2@1$0#k0^j2+hh8+hg0^h3>0@3$3$4@1$j1@1$6^h8@2$5@2$2@1$0#k0^j3+hh8>0@2$h5@2$5@1$j0@1$6^h9@2$k0@1$b^h9@2$2@1$0#k0^j3@2$jf+2+ha>0@3$hc$h2\2it$h2@2$hb@1$i9^1Ni1@1$if@1$6^ha>0@4$i2@3$8$7^h4^h3^he^je^jf>0@3$3$j2@1$j3^h5@d$j7^jf^j9^j8^if^ie^id^ic^ib^ia^i9^i8^i7^i6>0@3$j8?1E@3$8$7^h6^h5@1$i6@2$2@1$0#k0^j8@3$j6?1H\1c$hd@2$ha@hb$i4^k3^k2^k1^k0^jc^jb^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i4^i3^i0@2$2@1$0#k0^ja^hf@2$2@1$0#k0^j9^hc^hb^i2^h9^1@c$i5^k2@3$8$7^h8^h7^i0@2$2@1$0#k0^ja^hf^hc^hb^i3^i2^h9@1$h0@1$h1^hf^1@2$he@7$ja@hf$j9^k2^k1^k0^jf^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3@1$9$i7^i2@1$h6@1$1@1$0#k0^i1@1$jc$h4^h8").

  Definition any_first (_ : Z) : Prop := True.
  Definition parse_value_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!sje!smc!shb!sn9\1d$0@4$3$4$1$2^1").
  Definition parse_array_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!in9!sje!shb!so4\1d$0@4$3$4$2\1b$0@3$1$0^1+lb^1").
  Definition parse_object_stmt_d : ltac2:(zQ "10!h9>1d$0P") := ltac2:(zQ "50!h9!in9!sje!shb!sof\1d$0@4$3$4$2\1b$0@3$1$0^1+nb^1").
  Definition parse_value_stmt : ltac2:(zQ "00P") := ltac2:(zQ "40!sje!smc!spb!sn9@3$2$3$0$1").
  Definition parse_array_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!so4@3$3$4$2\1b$0@3$1$0^1+lb").   (* [comment removed for export] *)
  Definition parse_object_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!sof@3$3$4$2\1b$0@3$1$0^1+nb").  (* [comment removed for export] *)
  Definition parse_string_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!sr3@3$3$4$2\1b$0@3$1$0^1+i2").   (* [comment removed for export] *)
  Definition parse_num0_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!srf@3$3$4$2\1b$0@3$1$0^1+j0").
  Definition parse_numneg_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!ss9@3$3$4$2\1b$0@3$1$0^1+id").
  Definition parse_numpos_stmt : ltac2:(zQ "00P") := ltac2:(zQ "60!hsf!hs8!h9!sje!spb!st5@3$4$5$3\1b$2@2$1@2$0+j1^1@2$0^1+j9").
  Definition parse_null_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!su1@3$3$4$2\1b$0@3$1$0^1+me").
  Definition parse_true_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!sub@3$3$4$2\1b$0@3$1$0^1+n4").
  Definition parse_false_stmt : ltac2:(zQ "00P") := ltac2:(zQ "50!h9!in9!sje!spb!sv5@3$3$4$2\1b$0@3$1$0^1+m6").
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma parse_family_by_depth : ltac2:(zQ "a2!h9!hs8!tg0!th7!tie!hsf!ov3!tk6!tlb!tn1&>0@2$1@2$5Z^1@2$6^1^2@1$2^2&>2d'$0~0>0>1d$0>0~1@1$3^2>0>1d$0>0~1@1$4^2>0>1d$0>0@1$3^1>0@1$4^2@1$2^3@2$1$9@2$1$7$8").
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
  Definition RLLVM_FUZZ_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!q3!sje@2$0@2$0@2$0@2$0@2$0+h0+m0+in0+k0+k0@1$1+i0").   (* [comment removed for export] *)

      (* [comment removed for export] *)

End Iface.
(* [comment removed for export] *)
