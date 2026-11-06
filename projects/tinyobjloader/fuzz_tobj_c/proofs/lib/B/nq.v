(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.

(* [comment removed for export] *)
Module FpsC_a0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_0 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U0U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a0.

(* [comment removed for export] *)
Module FpsC_a1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_1 : ltac2:(tb__ "0|1|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U8M0G0A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a1.

(* [comment removed for export] *)
Module FpsC_a2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_2 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U10U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a2.

(* [comment removed for export] *)
Module FpsC_a3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_3 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U18U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a3.

(* [comment removed for export] *)
Module Fps_tailCdefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Datatypes"; "cons"; "false"; "nat"; "andb"; "bool"; "option"; "negb"; "nil"; "app"; "length"; "orb"; "list"; "pair"; "prod"; "true"; "None"; "S"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "sstate"; "SLit"; "SVar"; "ss_next"; "ss_objs"; "sv_eqb"; "ob_hi"; "ob_lo"; "swf"; "SAlu"; "SPEq"; "SPUle"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "DList"; "DRom"; "DUnknown"; "cell"; "dflt_writable"; "is_arr"; "sprop_eqb"; "ss_facts"; "ss_lenient"; "ss_pc"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "pow"; "opp"; "eqb"; "of_nat"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXMerge"; "AXRebase"; "apply_axforms"; "AXSplit"; "AXUnbase"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "ax_base"; "dflt_eqb"; "sobj_eqb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "app_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs"; "osome_eqb"; "tailC_out"; "URNG"; "lastobj"; "FC1"; "obj_lowb"; "xr_lowb"; "FIN"; "FSC"; "O_strR"; "TCO"; "XM"; "XWC"; "big_facts_C"; "blC"; "selR"; "splitsC"; "subC1"; "tailC"; "unk_keep"; "unlistk_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "O_strS"; "sX"; "factsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "BASEF"; "facts_fps"; "runp"; "fs_ok"; "set_facts"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "dropL"; "FWBIG"; "NULF"; "tailA_out"; "x_ok"; "WS"; "bexps_eqb"; "tailA_post"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "FERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "HSE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "two62"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymBytes SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform ListCommitA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition URNG (v : positive) : sprop := ltac2:(tb__ "0|0|
S23S21S43S69S1aVv;A1A3S19S38S34Z2Z2fA2Z10A2A1A2").
Definition big_facts_C (a : Z) (v : positive) : list sprop := ltac2:(tb__ "0|0|
SbS17S3S17S76S1aVv;A1A1S3S17S75Va;Vv;A2S3S17S55Vv;A1SaS17A1A3A3A3SbS17S6aS6dA3A3").
Definition T8C (a : Z) (T7 : axst) : axst := ltac2:(tb__ "0|0|
S8bS60Va;S71VT7;A1A2VT7;A2").

Definition FC1 (a : Z) (v : positive) : list sprop := ltac2:(tb__ "0|3|
SbS17S6cSbS17S3S17S22S1aVv;A1M0S1aP10A1M1A2S3S17S23G1S19Z1ffffA1A2SaS17A1M2A3A3SbS17S79S3S17S76G0A1S3S17S75Va;Vv;A2S3S17S55Vv;A1G2A3A3A3A3A3A3").

Definition FSC (a : Z) (v : positive) : list (list sprop) := ltac2:(tb__ "0|2|
S3SeS17A1M0S57Va;Vv;A2M1S3G0S6cS3G0S6cS3G0G1SaG0A1A3A3A3A3").
Definition FIN (v : positive) : list sprop := ltac2:(tb__ "0|0|
S3S17S22S1aVv;A1S1aP10A1A2S3S17S55Vv;A1S6dA3A3").

Definition XWC : list axform := ltac2:(tb__ "0|1|
S3S3aS3dU0M0A1S3S3aS3bS3S5G0S3S5U9S3S5UaS3S5U2S3S5U3S3S5U4S3S5U5S3S5U6S3S5UbS3S5UcS3S5UdS3S5UeS3S5U7S3S5U8S3S5U1SaS5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S3S3aS3cG0A1SaS3aA1A3A3A3").
Definition splitsC (a : Z) (S : sstate) : option sstate := ltac2:(tb__ "0|1|
S51S18S18S4dVS;U0S19N468A1A3S18S51S18S18S4dR1U1S19N448A1A3S18S51S18S18S4dR1U2S19N1d0M0A1A3S18S51S18S18S4dR1U3S19S33G0Va;A2A1A3S18S51S18S18S4dR1U5S19S33S7dZ78A2A1A3S18S4dR1U6S19S33S7dZ7cA2A1A3LS5;A4LS4;A4LS3;A4LS2;A4LS1;A4").

Definition O_strR (v : positive) : sobj := ltac2:(tb__ "0|0|
S24S69S19Z0A1S1aVv;A1SaS2bA1S29P6A1A5").
Definition subC1 (a : Z) (v : positive) (Cs : sstate) : wsub := ltac2:(tb__ "0|2|
SbS10S0S15A2M0S3G0SfS0S15PcS21S43S1aPaM1A1S19N1d0A1A3A4S3G0SfS0S15PdS19Va;A1A4S3G0SfS0S15PeS69A4S3G0SfS0S15PfS1aVv;A1A4SaG0A1A3A3A3A3S89G1VCs;S45S72A1A3A3").
Definition blC (l : list Z) : list bexp := map BLit l.

Definition unk_keep (o : sobj) : sobj := ltac2:(tb__ "0|0|
S24S25Vo;A1S1fVo;A1S1eVo;A1S26Vo;A1S2aA5").
Definition unlistk_at (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S8S16A1S18Lx;S4eS16S1cVS;A1M0Vi;A3S16S8aVS;SbS16S82S16Vi;G0A3S3S16S66R1A1S84S16S13Vi;A1G0A3A3A3A2Lo;VS;X8x2").

Definition obj_lowb (o : sobj) : bool := ltac2:(tb__ "0|1e|
S15S7Lx;M0S25Vo;A1S1S1S7Lz;R1G0S1fVo;A1M1S1G0S1eVo;A1M2S1S6S6S32Z0M3R2A2S32R2R1A2M4A2S32R1S86A2A2Lh;S0S4Li;M5S41S15S15S4Lb;La;M6Lop;M7G7S42G6Lop;M8G8S7S2S15S4La;Lw;Lsgn;M9S0S15S1S4Lk;MaLi;MbLl0;X15x8Ll;G5G7G7G8G8G9S0GbLl;McX15x8S0S4Lp;MdGdX1x3Lz;S0S0S7Li;MeR1GdS0S0S7Lp;MfR1S0S0S7Lp0;M10R1S0S4Lp1;M11S0S0S7Lp1;M12R1S0S4Lp2;M13G13G0G1S1G0G2S1S6S6S32S35S90A1R2A2M14G4A2S32R1G3A2A2Lh;S0S4Li0;M15G7G7G8G8G9S0S15GaLi0;M16Ll0;M17X15x8Ll;G15G7G7G8G8G9S0G16Ll;M18X15x8X0x3Lp1;S4X0x3Lp0;S0S4Lp0;M19S4X0x3Lp;S4X0x3Li;S41S15S15S41S7Lop;R3S15S7La;R2S1S4Lz;S0GeR1GdS0GfR1S0G10R1G11S0G12R1G13G13S15S7Lb;R5S1G0G1S1G0G2S1S6S6S6S6S32S35S34Z2Z28A2A1R3A2S32R3G3A2A2G14A2G4A2S32S33R3R1A2G3A2A2Lh;G15S41S15S15S4Lb0;La0;M1aLop0;M1bG1bS42G1aLop0;M1cG1cS7S2S15S4La0;Lw;Lsgn;M1dG17X15x8Ll;G15G1bG1bG1cG1cG1dG18X15x8Lc;G15G1bG1bG1cG1cG1dG18X15x8X0x3Lp1;S4X0x3Lp0;G19S4X0x3Lp;S4X0x3Li;G1bG1bG1cG1cG1dGcX15x8S4S4S4S4S4S4S4S4S4X41xaLb;La;Lop;G7G8G8G9GcX15x8").

Definition xr_lowb (r : sv * sv) : bool := ltac2:(tb__ "0|2b|
S10S15S15A2S7Lr;Vr;S15S15S15S7Ls;R2S1S15S7Ls0;M0R2S1S6S6S32Z0M1R2A2S32G1R1A2M2A2S32S33R2R1A2M3S34Z2M4Z2fA2A2A2Ll;S0S4Li;S41S15S15S4Lb0;M5La;M6Lop;M7G7S42G6Lop;M8G8S7S2S15S4La;Lw;Lsgn;M9S0S15S1S4Lk;MaLi;Ll;MbX15x8Lb;S0S0S7Li;McR1S0S4Lp;MdS0S0S7Lp;MeR1S0S0S7Lp0;MfR1S0S4Lp1;M10S0S0S7Lp1;M11R1S0S4Lp2;M12S0S0S7Lp2;R1S0S4Lp3;M13G13G0R6S1S4Lz;M14S0S0S7Li0;M15R1S0S0S7Lp3;M16R1S0S0S7Lp4;M17R1S0S4Lp5;M18S0S0S7Lp5;M19R1S0S4Lp6;M1aS0S0S7Lp6;M1bR1S0S4Lp7;M1cG1cS11X0x3Lp6;S4X0x3Lp5;S4X0x3Lp4;S0S4Lp4;M1dS4X0x3Lp3;G13S4X0x3Li0;S41S15S15S41S7Lop;M1eR3S15S7La;M1fR2G14S0G15R1S0G16R1S0G17R1G18S0G19R1G1aS0G1bR1G1cG1cS15S7Lb;M20R6S1S6S32N8R1A2S32R1G1A2A2Lc;S0S4Li1;S41S15G5La0;M21Lop0;M22G22S42G21Lop0;M23G23S7S2S15S4La0;Lw;Lsgn;M24S0S15GaLi1;Ll;X15x8X0x3Lp6;S4X0x3Lp5;S4X0x3Lp4;G1dS4X0x3Lp3;G13S4X0x3Li0;G22G22G23G23G24S0S15GaLi0;Ll;M25X15x8S4S4S4S4S4S4S4S4S4X41xaLb;La;Lop;S41S15S15S4Lb;La;M26Lop;M27S42G26Lop;M28G28G9G25X15x8X0x3Lp2;S4X0x3Lp1;S4X0x3Lp0;S0S4Lp0;M29S4X0x3Lp;S4X0x3Li;S41S15S15G1eR3G1fR2G14S0GcR1GdS0GeR1S0GfR1G10S0G11R1G12G12G20R5S1G0R9S1S6S6S6S32S35S34G4Z28A2A1R2A2S32R2G1A2A2G2A2S32G3G1A2A2Ll;S0S4Li0;M2aG22G22G23G23G24G25X15x8Lc;G2aG22G22G23G23G24G25X15x8X0x3Lp1;S4X0x3Lp0;G29S4X0x3Lp;S4X0x3Li;G22G22G23G23G24GbX15x8S4S4S4S4S4S4S4S4S4X41xaLb;La;Lop;G27G28G28G9GbX15x8Ls0;Ls;X10x1").

Definition selR : list nat := ltac2:(tb__ "0|1|
SbS5S3S5U0S3S5U1SaS5A1M0A3A3SbS5S83U3U11A2S3S5U2G0A3A3A3").
Definition XM : list axform := ltac2:(tb__ "0|13|
S3S3aS3dU0M0A1S3S3aS3bS3S5U3M1S3S5G0S3S5U4M2S3S5U1M3S3S5U5M4S3S5U13S3S5U8M5S3S5U9M6S3S5UaM7S3S5UbM8S3S5UcM9S3S5U11S3S5U12S3S5U6MaS3S5U2MbS3S5U7McS3S5UdMdS3S5UeMeS3S5UfS3S5U10SaS5A1MfA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S3S3aS3dG1A1S3S3aS3cG0A1M10S3S3aG10S3S3aG10S3S3aG10S3S3aS3cG6A1M11S3S3aG11S3S3aS3fG0S19N400M12A1A2S3S3aS3bS3S5G0S3S5GbS3S5G1S3S5G2S3S5G4S3S5GaS3S5GcS3S5G5S3S5G6S3S5G3S3S5G7S3S5G8S3S5G9S3S5GdS3S5GeGfA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S3S3aS40G0G12A2SaS3aA1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition lastobj (S : sstate) : option sobj := ltac2:(tb__ "0|1|
S4eS16S1cVS;A1M0S81ScS16G0A2U1A2A3").
Definition osome_eqb (x : option sobj) (o : sobj) : bool := ltac2:(tb__ "0|0|
S8S16A1S7Lx;Vx;S16S4aR1Vo;A2Ly;S4X8x2").

Record tailC_out := TCO { tc_W1 : axst; tc_S6 : sstate; tc_L6 : sstate; tc_Cs : sstate; tc_s : wsub; tc_R : list sobj; tc_T : axst;
                          tc_T1 : axst; tc_T2 : axst; tc_T3 : axst; tc_M : axst; tc_W0 : axst; tc_o : tailA_out }.

Definition tailC (pre suf : list Z) (a : Z) (v : positive) (T8 : axst) : option tailC_out := ltac2:(tb__ "0|25|
S37ScS1Vsuf;A2A1S1S7S8S54A1M0L_;M1S9S6S6S6S6S6S6S36Va;S37ScS1Vpre;A2A1A2S32Z1M2Va;A2A2S32G2R1A2A2S32Va;Z50M3A2A2S32R1G3A2A2S6fS3SeS17A1M4S57Va;Vv;A2S3G4S6cS3G4S5aVv;A1M5SaG4A1A3A3A3S45VT8;A1M6A2A2S53S4eS16S1cG6A1U1M7A3S68A2A2A1S12S54A1M8S8S44A1G0Lx;M9S6eS5bVa;Vv;A2MaVT8;A2S44G1S9S6S36S31S45R1A1MbA1Zd6760A2S4cS1bG6A1S1bGbA1McA2A2A1G8G9S3eS70R1G5A2MdS5fA2S44G1S9S6S6S6S4fS17S17S50S17S2eR1A1S2fS45R2A1MeA1A3Lf;G5A3S4bGcS1bGeA1MfA2A2S4fS10S15S15A2M10S59S47R1A1A3A2S1dS48R1A1S19S85A1M11A2A2A1G8S8S18A1G0Lx;S63Va;GbA2S18S8S16A1G0Lx;M12S4eS16S1cR1A1U3M13A3S16S8SeS87A1M14A1G0Lx;S88S26R1A1S19N1d0M15A1M16Z0M17S39Va;A1A4G14G1S9S6S6S6S6S6S6S6S6S6S6S6S7aR1S61Vpre;A1A2S9S6bP5M18R3A2A1A2S9S6bP6M19R3A2A1A2S2cS27R2A1M1aA1A2S9S2dG1aA1A1A2S1dS1fR2A1G16A2A2S1dS1eR2A1S19S33G15Va;A2A1A2A2S80G18S1cR3A1M1bA2A2S80G19G1bA2A2S7cScS16G1bA2U14M1cA2A2S53S56R3A1S68A2A2S4bS1bR3A1M1dS1bS45R4A1A1A2A2A1G8S8fR3G13G18A3S18S74R1A1S18S52R1S5cVv;A1M1eA2S18S46R7R1A2S44S64Va;Vv;R2A3S7fG1S9S6S6S6S6S6S6S6S78R9G1dA2S20R3A1A2S4fS16S58S1cR4A1A3A2S9S6bG19R4A2A1A2S4bS1bR5A1M1fS1bS45R9A1A1M20A2A2S4bG1dG20A2A2S7cScS16S1cR5A1A2G1cA2A2S53S56R5A1S68A2A2A1G8S8SeS16A1M21A1G0Lx;S8dR2S72R1A3G21G1S9S6S6S8cR3S72R2R1S3S44S73SaS44A1A3A5S1dS7eR2PdA2S19Va;A1A2A2S1dS7eR2PfA2S1aVv;A1A2A2A1G8S8eR2S72S73R3R1A5S44G1SdS30GbA1M22S9S4cG1fGcA2A1A2G8G9S3eGdS3S3aS3bS62A1SaS3aA1A3A2S44G12S4eS16S1cS74GbA1A1G7A3S16G1S9S6S6S6S6S6S7cScS16S1cGeA1M23A2G1cA2S53S56GeA1G1eA2A2S49S27R1A1S28G18A1A2A2S4bGfS1bS45R3A1A1A2A2S1dS48R2A1G11A2A2S4fG10S59S47R2A1A3A2A1G8S46R2S67S74GeA1G7A2A2S44S46R1S52GbS68A2A2S44G1S9S6S6S6S6S20GeA1S20GbA1A2S4fS16S58G23A3A2S4bGfS1bS45R5A1A1M24A2A2S4bGcG24A2A2A1G8G9S3eR1S5eA2S44G1SdSdSdSdSdG22S9S4bGcS1bS45R6A1A1A2A1A2S6bG18GbA2A2S6bG19GbA2A2S9S53S4eS16S1cGbA1G7A3S68A2A1A2S9S78R1GcA2A1A2G8G9S6eGaR1A2S44S8S77A1G0Lx;S7bSaS1A1Vsuf;G17R13VT8;R1A6S77S14S54S5dR12R11ReRcRaR9R8R7R5R4R3R2R1AdA2Lo;G8X8x2LW0;G8X8x2X7x2LM;G8X8x2X7x2TT3;TT2;X7x2Lob1;G8X8x2LT1;G8X8x2X7x2TT;X7x2LR;G8X8x2X7x2Ts;TC;TCs;TD6;TL6;X7x2Lbl;G8X8x2Lo8;G8X8x2LS6;G8X8x2X7x2LW1;G8X8x2X7x2LW1';G8X8x2X7x2Tb;").
Definition tailC_ok (pre suf : list Z) (a : Z) (v : positive) (T8 : axst) : bool := ltac2:(tb__ "0|0|
S8S54A1S7Lx;S65Vpre;Vsuf;Va;Vv;VT8;A5S54S11Lt;S4X8x2").
End Fps_tailCdefs.

