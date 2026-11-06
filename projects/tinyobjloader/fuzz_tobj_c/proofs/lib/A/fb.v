(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew fe.

(* [comment removed for export] *)
Module Lib_builder_dispose_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "edescA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "SLit"; "SVar"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "true"; "andb"; "app"; "nil"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builder_dispose"; "NP"; "cutsE"; "exitsE"; "FUEL_bd"; "NV"; "bd_chk_live"; "chkM"; "cutpcs_bd"; "lives"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_builder_dispose_chk"; "H_bd_ejcert_ok"; "keep_bd_ejcert_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideE"; "hide_setE"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_builder_dispose.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr BDAddr.

Lemma bd_chk_ok : ltac2:(tb__ "0|0|
SdS7SaS19S8S16SfU0S14A2A3S19S8S15S18A3A2S9A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_bd_ejcert_ok : list sprop := ltac2:(tb__ "0|2|
S6S2S3S5PcA1S4Z800000000000A1M0A2S6S2S3S4Z646000A1S5P10A1M1A2S6S2S3G1G0A2ScS2A1A3A3A3").
Definition H_bd_ejcert_ok : list sprop := ltac2:(tb__ "0|0|
S1eS1cSbS0S11S12A3A2").
Lemma bd_ejcert_ok : ltac2:(tb__ "0|1|
SdS7S1S1aS10S13S17S10SeS0S0S1dS1bA1M0S11A4SeS0S0G0S12A4A7S9A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_builder_dispose_chk.

(* [comment removed for export] *)
Module Lib_builder_dispose_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "ss_facts"; "sv_eqb"; "sprop"; "ss_next"; "SLit"; "SPBranch"; "sprop_eqb"; "SPNot"; "ob_hi"; "ob_lo"; "obj_range"; "rw"; "ss_objs"; "cell"; "holds"; "mkObj"; "ob_base"; "odefault"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "prod"; "nat"; "list"; "pair"; "andb"; "bool"; "true"; "nil"; "S"; "cons"; "option"; "fst"; "snd"; "Some"; "false"; "None"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "edescA"; "ND"; "PTrue"; "nd_below"; "emeasA"; "JA_pre"; "ffinA"; "ANone"; "JA"; "JLA"; "NDA"; "nd_tv"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builder_dispose"; "NP"; "ndL"; "lives"; "NV"; "nlive"; "rL"; "bdK"; "tvL"; "E_"; "live"; "fr_obj"; "fr_xr"; "tvE"; "C_"; "Pre_ms"; "s_of"; "z0"; "L_ms"; "M_"; "N_"; "R_of"; "cutsE"; "s_ms"; "L_"; "P_bd"; "Pre_bd"; "chkE"; "chkM"; "chkN"; "exitsE"; "isSomeb"; "live_from"; "ndP"; "Cnode"; "Mnode"; "Nd_"; "Nnode"; "chkC"; "didx"; "lit_in"; "nobj"; "sL"; "sN"; "vAl"; "vB"; "xf_back"; "xf_ms"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkPA"; "J_ofPA"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "pow"; "mul"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_builder_dispose_pf"; "P0_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "Pre_free"; "L_free"; "JL_free"; "JL_pure"; "J_free_pre"; "J_memset_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "bud_le"; "KU"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_builder_dispose_pf.Sum"; "Posts_bd"; "JLb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "robjs_checkA"; "T_afterA"; "call_checkTA"; "cmaddrA"; "site_okA"; "payA";
"@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tv_sub_eqb"; "tnz"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builder_dispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_builder_dispose_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr BDAddr.

Lemma chkE_unfold : forall j, chkE j = ltac:(let b := eval cbv beta delta [chkE chkE'] in (chkE j) in exact b).
Proof. intros j. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.
Lemma chkN_unfold : ltac2:(tb__ "0|d|
S1bS2cS1fS5eR1A1S24S2A1S1fLx;S76S2SfS16S55R1A1A1A1S68R1A1A3S2S1eS1eS1eS1eS1eS1eS1eS1eS1eS4S13R1A1S25S0S0S4eR2A1M0A3M1A2S4ScR1A1S7Z0A1M2A2A2S4SbR1A1S26S0S0G0A3A2A2S75S5S9S8SaaG1G2A3A1S3S16S55R2A1M3A1A1A3A2S18S65R2G3A2M4S54R2A1S6cR2G3A2M5A3A2Sa1G5S42A2A2Sb6S42S6S16G4A1M6A1M7A2A2S34G7S32SbaS1aS0S0A2M8U0S23G8G0S49S22R2A1M9A1MaA3A3MbS21S1aS1aS0S2bA2S0A2A1S48S46R2A1A1McA3A2A2SbbG5GbGaA3A2S9aS3G6A1S98G5S48S46G9A1A1A2GcA3A2Lo;S28X24x2A3Fj;").
Proof. intros j. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.
Lemma chkM_unfold : forall j, chkM j = ltac:(let b := eval cbv beta delta [chkM] in (chkM j) in exact b).
Proof. intros j. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.
Lemma exitsE_eq : ltac2:(tb__ "0|3|
S2cS1cS31A1S5fS2aS31Sa5S1bS31S63S44A4S2aS31Sa5S1bS31S66S44A4S2aS31Sa5S1bS31S64Sa7U0S45A2A4S23S1aS1aS15S30A2M0S1aS2bS0A2M1A2M2S1dG0G1S1dS15S30S5aS62A4S1dS2bS0Z0S52A4A4S21G2A1A3A3A3A3A3").
Proof. match goal with |- _ = ?b => exact (@eq_refl _ b) end. Qed.

Lemma lives_specb : ltac2:(tb__ "0|0|
S2cS1fS74S1bS1bS1eSc5R1S45A2S4bR1A1A2Lj;S44A3S20A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lives_spec : ltac2:(tb__ "0|0|
S1bS73S1bR1S44A3S2dS87R2S45A2S2cS1fS4bR2A1S20A3A2F_;Fj;").
Proof.
  intros j H. pose proof (proj1 (forallb_forall _ _) lives_specb j H) as X. cbn beta in X.
  apply andb_prop in X as [A B]. apply Nat.ltb_lt in A. split; [exact A | exact B].
Qed.
Lemma live_from_cons : ltac2:(tb__ "0|0|
S1bS87R1S45A2S2cS1fS4bR2A1S20A3S2cS1cS1bA1S61R3A1S23S1bR3S61S22R3A1A1A3A3F_;F_;Fj;").
Proof.
  intros j Hj Hl. unfold live_from.
  replace (NV - j)%nat with (S (NV - S j))%nat by lia. cbn [seq List.filter]. rewrite Hl. reflexivity.
Qed.
Lemma tvL_cons : ltac2:(tb__ "0|1|
S1bS87R1S45A2S2cS1fS4bR2A1S20A3S2cS1cS1aS0S0A2M0A1S49R3A1S23G0S4eR3A1S49S22R3A1A1A3A3F_;F_;Fj;").
Proof. intros j Hj Hl. unfold tvL. rewrite (live_from_cons j Hj Hl). reflexivity. Qed.
Lemma nlive_cons : ltac2:(tb__ "0|0|
S1bS87R1S45A2S2cS1fS4bR2A1S20A3S2cS2bS46R3A1S81S46S22R3A1A1Z1A2A3F_;F_;Fj;").
Proof. intros j Hj Hl. unfold nlive. rewrite (live_from_cons j Hj Hl). cbn [length]. lia. Qed.
Lemma ndL_cons : ltac2:(tb__ "0|0|
S1bS87R1S45A2S2cS1fS4bR2A1S20A3S2cS30S43R3A1S32S23S1aS0S0A2S4eR3A1S49S22R3A1A1A3S21S1aS1aS0S2bA2S0A2A1S48S46R3A1A1A3A3F_;F_;Fj;").
Proof. intros j Hj Hl. unfold ndL. rewrite (tvL_cons j Hj Hl). reflexivity. Qed.

Lemma chk_live_at : ltac2:(tb__ "0|0|
S1bS73S1bR1S44A3S2dS2cS1fS67R2A1S20A3S2dS2cS1fS5cR2A1S20A3S2cS1fS5eR2A1S20A3A2A2F_;Fj;").
Proof.
  intros j Hin. pose proof bd_chk_ok as H. apply andb_prop in H as [_ H].
  pose proof (proj1 (forallb_forall _ _) H j Hin) as X. cbn beta in X.
  apply andb_prop in X as [X1 X]. apply andb_prop in X as [X2 X3].

  split; [exact X1 | split; [exact X2 | exact X3]].
Qed.
Lemma chkM_at : ltac2:(tb__ "0|0|
S1bS87R1S45A2S2cS1fS5dR2A1S20A3F_;Fj;").
Proof.
  intros j Hj. pose proof bd_chk_ok as H. apply andb_prop in H as [H _].
  exact (proj1 (forallb_forall _ _) H j ltac:(apply in_seq; lia)).
Qed.

Lemma R_of_spec : ltac2:(tb__ "0|2|
S1bS15S2cS1fS60S1cS2A1M0S79R1S8bS88S21S8aA1S89A3M1S51R2R1A2A3A2S20A3S2cS24G0A1S79R2G1S51R3R2A2A3S27G0S56R3R2A2A2A3F_;FE;Fj;").
Proof. intros j E H. unfold R_of, optR. destruct (entails_frA E (Pre_free AE_A [] UStopLe) (s_of j E)); [reflexivity | discriminate]. Qed.

Lemma L_in_cutsE : ltac2:(tb__ "0|3|
S1bS87R1S45A2S73S1aS1aS15S30A2M0S1aS2bS0A2M1A2S1dG0G1S1dS15S30S59S22R2A1M2A1S43G2A1A4S1dS2bS0S47G2A1S52A4A4S57A3F_;Fj;").
Proof.
  intros j Hj. unfold cutsE. right. apply in_or_app. left.
  apply (in_map Lnode (seq 1 NV) (S j)). apply in_seq. lia.
Qed.
Lemma T_in_cutsE : ltac2:(tb__ "0|6|
S1bS73S1bR1S44A3S73S1aS1aS15S30A2M0S1aS2bS0A2M1A2S1dG0G1S1dS15S30Sb1S8bS88S21S8aA1M2S89A3S4aR2A1M3S51R2G3A2S56R2G3A2S8cS88G2S89A3A5S3bSbaS1aS0S0A2M4U0S23G4S4eR2A1S49S22R2A1M5A1A3A3S21S1aS1aS0S2bA2S0A2A1S48S46G5A1A1S38A4A4S1dS2bS0S80S47R2A1Z3A2S52A4A4S57A3F_;Fj;").
Proof. intros j Hin. unfold cutsE. right. apply in_or_app. right. exact (in_map Tnode lives j Hin). Qed.

Lemma edesc_eq3 : ltac2:(tb__ "0|2|
S15S15S30S30S1aS2bS0A2M0G0S2cS1aS1aS15S30A2M1G0A2S1dG1G0S1dS15S30R6R4A4R2A4S1dG1G0S1dS15S30R5R3A4R1A4A3S2dS2cS15R7R6A3S2dS2cS30R5R4A3S2cG0R3R2A3A2A2F_;Fc';Fc;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' c c' H. injection H as E1 E2 E3. subst. auto. Qed.
Lemma edesc_eq2 : ltac2:(tb__ "0|0|
S15S15S30S30S2cS1aS15S30A2S1dS15S30R4R2A4S1dS15S30R3R1A4A3S2dS2cS15R5R4A3S2cS30R3R2A3A2F_;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' H. injection H as E1 E2. subst. auto. Qed.

Lemma rL_S : ltac2:(tb__ "0|0|
S1bS2cS2bS47S22R1A1A1S80S47R1A1ZaA2A3Fj;").
Proof. intros j. unfold rL. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma rL_pos : ltac2:(tb__ "0|0|
S1bS87R1S45A2S7dZ12S47S22R2A1A1A2F_;Fj;").
Proof. intros j Hj. unfold rL, NV in *. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S15S30S2bS1S2cS2bS35S1dS1aS15S30A2S1aS2bS0A2S1dS15S30R4R3A4S1dS2bS0R2S52A4A4R1A2S7fR2S7eZ2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros T nd r rho. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho z0)) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Definition P0_bd (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S2dSafVFF;S72Q40M0SeVr;PcA2A2Z518A3SafVFF;S72G0SeVr;P10A2A2Z30A3A2").

Lemma lit_in_sound : ltac2:(tb__ "0|2|
S1S0S0S0S2bS2bS1cS10A1S14S7cR4S7eZ2Z3eA2A2S2cS1fS69R7R6R5A3S20A3S2dS7dS25S2bS2bSdRaS12R9R8R7R4R3A5A2M0A3R5A2S7cR5S26S2bS2bG0A3A2A2S2dS7dS95RbRaA2M1R6A2S7cR6S81G1R7A2A2A2F_;F_;F_;Fdflt;Fcells;Fa;Fn;Fhi;Flo;Fbase;Frho;").
Proof.
  intros rho base lo hi n a cells dflt Hn H Hr. unfold lit_in in H.
  destruct lo as [l| | | | | | |]; try discriminate. destruct hi as [h| | | | | | |]; try discriminate.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite (soff_lit_small rho l), (soff_lit_small rho h) in Hr by lia. unfold uval. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sa2S1S1cS71Q40A1A1Sa8OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S93S2fVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2bSc1VCST;R1A2S2dS7dZ0R2A2S7cR2Sc0A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2bSc1VXGL;R1A2S2dS7dZ0R2A2S7cR2Sc0A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1cS1aS1aS2bS2bA2S2bA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Variable rho0 : valuation.

Definition JLb (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;VKc;S82VFB;VFF;A2VFB;VFF;VBX;S33Vnd;Aa").
Definition Posts_bd : list (axst * jpostA) := ltac2:(tb__ "0|1|
S23S1aS15S77A2M0S1dS15S77S5aSacS62A1A4S21G0A1A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S39VAInv;VCST;VXGL;S42VKc;Vrho0;S82VFB;VFF;A2VFB;VFF;VBX;S33Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S1aS15S30A2Sc2Fn;") := ltac2:(tb__ "0|0|
S3dVAInv;VCST;VXGL;S42VKc;Vrho0;S82VFB;VFF;A2VFB;VFF;VBX;S33Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S78S2fS42Vrho0;Vtp0;SabA5").

Lemma P0b_now : ltac2:(tb__ "0|0|
S1SadS42Vrho0;R1A3S82VFB;VFF;Vrho0;A3S2dSafVFF;S95R3S6eA2Z518A3SafVFF;S95R3S6dA2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav [H1 H2]. unfold uval, vB, vAl. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 16%positive eq_refl). split; [exact H1 | exact H2].
Qed.

Lemma fr_obj_cmaddrA : ltac2:(tb__ "0|1|
Sa2S1S24S2bA1S2S2bSadS42Vrho0;R4A3S82VFB;VFF;Vrho0;A3S37VFF;R7A2S2cS1fS4cR5A1S20A3S2dS7dS25S2bS2bSdR8R6A2M0A3R5A2S7cR5S26S2bS2bG0A3A2A2Sb3VCST;RaR8R6A4F_;F_;F_;F_;F_;Fa;Fo;Fxo;Frho;FAi;").
Proof.
  intros Ai rho xo [base lo hi cells dflt] a Hav HP0 HFF H Hr. destruct (P0b_now rho Hav HP0) as [PB PA].
  unfold fr_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hl]; apply sv_eqb_sound in Hb; subst base.
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PB | exact (lit_in_sound rho vB lo hi 1304 a cells dflt ltac:(lia) Hl Hr)].
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PA | exact (lit_in_sound rho vAl lo hi 48 a cells dflt ltac:(lia) Hl Hr)].
Qed.
Lemma fr_xr_cmaddrA : ltac2:(tb__ "0|1|
Sa2S1S24S2bA1S1aS0S0A2S2bSadS42Vrho0;R4A3S82VFB;VFF;Vrho0;A3S37VFF;R7A2S2cS1fS4dR5A1S20A3S2dS7dS95R8S25S0S0R6A3A2M0R5A2S7cR5S81G0S95R8S26S0S0R6A3A2A2A2A2Sb3VCST;RaR8R6A4F_;F_;F_;F_;F_;Fa;Fr;Fxo;Frho;FAi;").
Proof.
  intros Ai rho xo [rb rn] a Hav HP0 HFF H Ha. destruct (P0b_now rho Hav HP0) as [PB PA].
  unfold fr_xr in H. cbn [fst snd] in H, Ha. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hn]; apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hn; subst rb rn.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PB | exact Ha].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PA | exact Ha].
Qed.

Lemma site_M : ltac2:(tb__ "0|1|
S15Sa0S1cS2A1S1S1cS1aS0S0A2M0A1S1cS96A1S2cS1fSb0S3S16R6A1A1R2S29S1bA1S4cR4A5S20A3S2cS1fS74G0S4dS17R7A1A3S20A3Sb4VAInv;VCST;VXGL;S42Vrho0;S82VFB;VFF;A2VFB;VFF;R8R7R6R5S32R4S21S1aS1aS0S2bA2S0A2A1R3A3S29S2bA1Sa2Sa4S2eL_;L_;AfF_;F_;Fbd;Ftv;Frho;FR;Fs;FMx;").
Proof.
  intros Mx s R rho tv bd HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr ND] in HN, HD, HZ, HFR.
  split; [|split; [|exact I]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S Mx)) tv None fr_obj R None r1 t1 m1 HM HF HN HD HZ HTK HR); [|exact I].
    intros o a Ho Hfo Hr. exact (fr_obj_cmaddrA Ai rho None o a Hav HP0 HFF Hfo Hr).
  - intros r a Hr Ha. left. exact (fr_xr_cmaddrA Ai rho None r a Hav HP0 HFF (proj1 (forallb_forall _ _) HX r Hr) Ha).
Qed.

Lemma site_E : ltac2:(tb__ "0|3|
S15Sa0S1cS2A1S1S1aS0S0A2M0S1cG0A1S1cS96A1S2cS1fSb0S3S16R7A1A1S23G0R3R2A3S27S1bU0A2S4cR5A5S20A3S2cS1fS74G0S4dS17R8A1A3S20A3S2cS1fS4S25S0S0R5A3S9dR8PcM1A2A2S20A3S2cS1fS4S26S0S0R6A3S9dR9PdM2A2A2S20A3S2cS1fS75S5S9SaS8SaaS25S0S0R7A3S7Z0A1A3A1A1S3S16RbA1A1A3S20A3Sb4VAInv;VCST;VXGL;S42Vrho0;S82VFB;VFF;A2VFB;VFF;RcRbRaR9S32S23G0R8R7A3S21S1aS1aS0S2bA2S0A2A1R6A3S27S2bS95R9S9dRbG1A2A2A2Sa2Sa4S2dSbcRbRaA2S2dS2cS1aS2bS2bA2SbdRbRaA2S1dS2bS2bS95RbS9dRdG1A2A2S95RbS9dRdG2A2A2A4A3S94S21S8aA1S89S9fS9eRbRcR1A3RdA2A3A2A2Lms;LAi;AfF_;F_;F_;F_;F_;Fbd;Ftv;Ft;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho t tv bd HR HX H12 H13 Hnzb Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr ND] in HN, HD, HZ, HFR.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13. rewrite <- H12, <- H13.
  assert (Hnz : tnz rho t).
  { pose proof (holds_mem _ _ _ HF Hnzb) as X. apply (proj1 (holds_nbeq _ _ _)) in X. unfold tnz. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in X. rewrite uval_lit in X by lia. exact X. }
  split; [|split; [|split; [exact Hnz | split; [reflexivity | exact I]]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E)) (t :: tv) (Some 0%nat) fr_obj R _ r1 t1 m1 HM HF HN HD HZ HTK HR).
    + intros o a Ho Hfo Hr. exact (fr_obj_cmaddrA Ai rho _ o a Hav HP0 HFF Hfo Hr).
    + exists t. split; [reflexivity|]. split; [exact Hnz | reflexivity].
  - intros r a Hr Ha. left. exact (fr_xr_cmaddrA Ai rho _ r a Hav HP0 HFF (proj1 (forallb_forall _ _) HX r Hr) Ha).
Qed.

Lemma SPA_drop_null_dat : ltac2:(tb__ "0|2|
S30S1S15S1bS2S1aS0S0A2M0S1cS71Q40A1A1S86S2cS24S2A1S76S2SfS16R6A1A1R5A3S27S2R4A2A3S73G0R4S3cR9A1A3S2cS1fS4ScR6A1S7Z0A1M1A2S20A3S2cS1fS4SbR7A1S26S0S0R6A3A2S20A3S2cS1fS75S5S9S8SaaS25S0S0R7A3G1A3A1S3S16RaA1A1A3S20A3S3fS2fVJAv;RdA1RbRcR7R6A6S3fS2fVJAv;ReA1S19RcSbfS16RcA1RbA2A2RdR8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Ft;Fo;Fi;FA;Frho;Fnd;").
Proof.
  intros nd rho A i o t tp w Hn Hin Hlo Hhi Hz Hw.
  apply sv_eqb_sound in Hlo. apply sv_eqb_sound in Hhi.
  assert (HJ : exists tr md, JAv nd rho tp tr md).
  { destruct w as [tr [ms md]]. destruct Hw as [_ HJ]. exists tr, md. exact HJ. }
  destruct HJ as (tr & md & HJ).
  apply (SPA_drop_empty segs (JAv nd) rho A i o tp w Hn); [|exact Hw].
  intros HF. pose proof (holds_mem _ _ _ HF Hz) as X. apply (proj1 (holds_beq _ _ _)) in X.
  change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in X. rewrite uval_lit in X by lia.
  pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue nd rho tp tr md t HJ Hin X) as Hs0.
  unfold obj_hi_of, obj_lo_of. rewrite Hlo, Hhi. rewrite soff_lit_small by lia.
  rewrite (soff_smallu rho (snd t)) by (unfold uval; rewrite Hs0; lia). unfold uval. rewrite Hs0. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S1cS5A1S1cS96A1S2cS1fS99R1A1S20A3Sb5S42Vrho0;S82VFB;VFF;A2R3S7Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S2bS1cS71Q40A1A1S83F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S40S15S1S1cS71Q40A1A1S83Sa6S5S11R3A1S3S16R4A1A1A3VTR;S3fS2fR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S83S83S83S86R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S40S40S15S15Sa0S1cS2A1M0S1cS1aS15S77A2M1A1S1cS1aS0S0A2M2A1S83S1S1cS71Q40A1A1M3G2S73G2R1R5A3S73G2R2S17RbA1A3F_;Fr;S2cS24G0A1S79RaR9R8A3S27G0R7A2A3S2cS1fS7aRbRaR9R8Sa5G1S15S25S15S77A2R7A4A5S20A3S1G3VTR;S3fS2fRfRdR2R1A5S78S2fS6S16RdA1A1R2R1RaA5A2Ftp1;Frho1;S1cSa9A1M4Sa4Sa8S41S2fR9R8R10S1dG4Sb7R3Sb8R2R1A2A4A5R13RaR9R4R2A4R13S9fS9eRbRfSa3R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S15S77G4Sa4Sa8S1G3G4Sa4Sa8S73G1S1dS15S77RaR9A4R14A3S41S2fR12R11R19S1dG4Sb7R9Sb8R8R7A2A4A5R1cR13R12RaR8A4SadS6S16R1aA1A1S9fS9eR14R18Sa3R9R13RaA3A3R19A2R8A3S41S2fR9R8ReS1dG4Sb7R7Sb8R6R5A2A4A5ReS9fS9eR16R1aSa3RbR15RcA3A3R1bA2R15RaR9R8R6A6S2dSc3R17Sa3RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1SaeR18Sa3RdR17ReA3R1cR1dS16R1eA1S16R1fA1S16R11A1R1RcA9VTR;S3fS2fS7bR11S9fS9eR19R1dSa3ReR18RfA3A3R1eA2R18RdRcA5Sc4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S3fS2fR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CFREE : ltac2:(tb__ "0|2|
Sa2S1S1cS71Q40A1A1VTR;S3fS2fS8fVAInv;S21S8aA1M0S89R3VKc;A5S8bS88G0S89A3R2R1A5S78S2fSb9R2R1S23S1aS15S77A2M1S1dS15S77S8cS88G0S89A3S8dVAInv;VCST;VXGL;R3VKc;A5A4S21G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
Sa2S1S1cS71Q40A1A1VTR;S3fS2fS90VAInv;R3VKc;A3S50R2R1A5S78S2fSb9R2R1S23S1aS15S77A2M0S1dS15S77S53S8eVAInv;VCST;VXGL;R3VKc;A5A4S21G0A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis MINI : ltac2:(tb__ "0|1|
S1bS1S1cS71Q40A1A1M0S83S73S1bR4S44A3S1G0VTR;S3fS2fVJAv;S43R7A1A1S4aR7A1R2R1A5R4A2Ftp';Frho';VTR;S3fS2fVJAv;S43R6A1A1S4fR6A1R5R4A5R3A2F_;F_;FQ';Ftp;Frho;Fj;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S15S30S1aS2bS0A2M0S1S1cS71Q40A1A1M1S2bG1S73S1aS1aS15S30A2M2G0A2S1dG2G0S1dS15S30R7R6A4R5A4S57A3S2dS7dZ0S35S1dG2G0S1dS15S30R8R7A4R6A4R5A2M3A2S7cG3R3A2A2VTR;S3fS2fVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S15S30S1S1cS71Q40A1A1M0S2bG0S73S1aS15S77A2S1dS15S77R6SacR5A1A4SabA3VTR;S3fS2fVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Lemma X_M : ltac2:(tb__ "0|1|
S1bS1S1cS71Q40A1A1M0S2bG0S87R5S45A2S7cS7fS47S22R6A1A1S7eZ2Z40A2A2R3A2VTR;S3fS2fVJAv;S43S22R7A1A1A1S54R7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hj Hb. pose proof (chkM_at j Hj) as HK. rewrite (chkM_unfold j) in HK.
  destruct (apply_axforms (M_ j) (xf_ms j)) as [Mx|] eqn:HX; [|discriminate].
  destruct (entails_frA Mx Pre_ms (s_ms Mx)) as [R|] eqn:He; [|discriminate]. cbv zeta in HK.
  apply andb_prop in HK as [HK HT].
  apply andb_prop in HK as [HK HXr]. apply andb_prop in HK as [HK HR]. apply andb_prop in HK as [HK Hwp]. apply andb_prop in HK as [HK Hbb].
  apply andb_prop in HK as [HK Hnb]. apply andb_prop in HK as [HK Hnp]. apply andb_prop in HK as [Hchk Htp].
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs (JAv (ndL (S j))) (xf_ms j) rho (M_ j) Mx tp w HX Hw)|].
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] Mx (s_ms Mx) R rho tp (ndL (S j)) (bdK (nlive (S j))) (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Htp.
  - exact Hnp.
  - exact Hnb.
  - exact Hbb.
  - cbn [nd_bd ndL ND]. apply payA_same. exact Hwp.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - unfold ndL. exact (site_M Mx (s_ms Mx) R rho (tvL (S j)) (bdK (nlive (S j))) HR HXr).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai Mx memset_pc (s_ms Mx) R rho tp tr ms md Hsm HM HX' He).
  - intros L rho' tp' [<-|[]] Hag. cbn [nd_tv nd_fr nd_am ndL ND].
    destruct (apply_axforms (T_afterA Pre_ms Mx (s_ms Mx) R L_ms) (xf_back j (nobj (T_afterA Pre_ms Mx (s_ms Mx) R L_ms)))) as [T'|] eqn:HX2; [|discriminate].
    apply andb_prop in HT as [HT Hbl]. apply andb_prop in HT as [HT Htv]. apply andb_prop in HT as [HT Hnb2]. apply andb_prop in HT as [HT Hnp2].
    apply andb_prop in HT as [Hent Hid].
    eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ _ rho' _ T' tp' w HX2 Hw)|].
    eapply TR_pre.
    { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc T' (L_ (S j)) (sL j T') (ndL (S j)) (ndL (S j)) rho' tp' w
                      Hent Hid Hnp2 Hnb2 Htv eq_refl Hbl eq_refl Hw). }
    apply (REENTER (L_ (S j)) (ndL (S j)) (rL (S j), z0) _ tp' b tp0 (L_in_cutsE j Hj)). rewrite emeas_z0. pose proof (rL_pos j Hj). lia.
Qed.

Lemma X_N : ltac2:(tb__ "0|1|
S1bS1S1cS71Q40A1A1M0S2bG0S73S1bR5S44A3S7cS7fS47S22R6A1A1S7eZ2Z40A2A2R3A2VTR;S3fS2fVJAv;S43R7A1A1S55R7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hin Hb. destruct (lives_spec j Hin) as [Hj Hl].
  destruct (chk_live_at j Hin) as (_ & _ & HK). rewrite (chkN_unfold j) in HK.
  destruct (nth_error (ss_objs (ax_S (N_ j))) (didx j)) as [o|] eqn:Ho; [|discriminate].
  apply andb_prop in HK as [HK Hbl]. apply andb_prop in HK as [HK Htv]. apply andb_prop in HK as [HK Hnb]. apply andb_prop in HK as [HK Hnp].
  apply andb_prop in HK as [HK Hid]. apply andb_prop in HK as [HK Hent]. apply andb_prop in HK as [HK Hz].
  apply andb_prop in HK as [HK Hhi]. apply andb_prop in HK as [Hb0 Hlo].
  rewrite (ndL_cons j Hj Hl).
  eapply TR_pre.
  { intros w Hw.
    pose proof (SPA_drop_null_dat (ND (tvE j :: tvL (S j)) [] (bdK (nlive j))) rho (N_ j) (didx j) o (tvE j) tp w Ho ltac:(left; reflexivity) Hlo Hhi Hz Hw) as Hw1.
    revert Hw1. apply (SPA_JA_drop_tv_fact segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue (tvE j :: tvL (S j)) [] (bdK (nlive j)) 0%nat
                         (ax_setS (N_ j) (drop_obj_at (ax_S (N_ j)) (didx j))) rho tp w).

    intros t Ht. cbn [nth_error] in Ht. injection Ht as <-.
    assert (EF : forall (A : axst) i, ss_facts (ax_S (ax_setS A (drop_obj_at (ax_S A) i))) = ss_facts (ax_S A)) by (intros; reflexivity).
    rewrite EF. exact Hz. }
  eapply TR_pre.
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc (Nd_ j (N_ j)) (M_ j) (sN j (N_ j))
                    (ND (remove_nth 0 (tvE j :: tvL (S j))) [] (bdK (nlive j))) (ndL (S j)) rho tp w Hent Hid Hnp Hnb Htv eq_refl Hbl eq_refl Hw). }
  apply X_M; [exact Hj | exact Hb].
Qed.

Lemma X_E : ltac2:(tb__ "0|1|
S1bS1S1cS71Q40A1A1M0S2bG0S73S1bR5S44A3S7cS7fS80S47R6A1Z3A2S7eZ2Z40A2A2R3A2VTR;S3fS2fVJAv;S43R7A1A1S4aR7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hin Hb. destruct (lives_spec j Hin) as [Hj Hl].
  destruct (chk_live_at j Hin) as (_ & HK & _). rewrite (chkE_unfold j) in HK.
  apply andb_prop in HK as [HK HXr]. apply andb_prop in HK as [HK HR]. apply andb_prop in HK as [HK Hnz]. apply andb_prop in HK as [HK H13].
  apply andb_prop in HK as [HK H12]. apply andb_prop in HK as [HK Hpay]. apply andb_prop in HK as [HK Hbb]. apply andb_prop in HK as [HK Hnb].
  apply andb_prop in HK as [HK Hnp]. apply andb_prop in HK as [HK Htp]. apply andb_prop in HK as [Hsome Hchk].
  apply (R_of_spec j (E_ j)) in Hsome.
  rewrite (ndL_cons j Hj Hl).
  apply (free_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe (E_ j) (s_of j (E_ j)) (R_of j (E_ j)) rho tp (ND (tvE j :: tvL (S j)) [] (bdK (nlive j))) 0%nat (tvE j) (bdK (nlive (S j))) (FAM b tp0) CFREE
           Hsome Hchk Htp Hnp Hnb Hbb (@eq_refl _ (Some (tvE j)))).
  - cbn [nd_bd ND]. apply payA_of_bud_pay. exact Hpay.
  - intros A A' _ _. exact I.
  - exact (site_E (E_ j) (s_of j (E_ j)) (R_of j (E_ j)) rho (tvE j) (tvL (S j)) (bdK (nlive j)) HR HXr H12 H13 Hnz).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ND].
    apply (REENTER _ _ (rL j - 3, z0) rho' tp' b tp0 (T_in_cutsE j Hin)). rewrite emeas_z0. pose proof (rL_pos j Hj). rewrite rL_S in *. lia.
Qed.

Lemma X_C : ltac2:(tb__ "0|1|
S1bS1S1cS71Q40A1A1M0S2bG0S73S1bR5S44A3S7cS7fS80S47R6A1Z3A2S7eZ2Z40A2A2R3A2VTR;S3fS2fVJAv;S43R7A1A1S4fR7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hin Hb. apply (MINI j rho tp (FAM b tp0) Hin). intros rho' tp'. apply X_E; [exact Hin | exact Hb].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S15S30S1aS2bS0A2M0S1S1cS71Q40A1A1M1G1S73S1aS1aS15S30A2M2G0A2S1dG2G0S1dS15S30R6R5A4R4A4S5fA3VTR;S3fS2fVJAv;R6A1R7R4R3A5VFAM;S35S1dG2G0S1dS15S30R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. rewrite exitsE_eq in Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]]].
  - apply in_map_iff in Hin as (j & Heq & Hj). destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). destruct (lives_spec j Hj) as [Hlt _].
    apply X_C; [exact Hj|]. rewrite emeas_z0. pose proof (rL_pos j Hlt). nia.
  - apply in_map_iff in Hin as (j & Heq & Hj). destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). destruct (lives_spec j Hj) as [Hlt _].
    apply X_N; [exact Hj|]. rewrite emeas_z0, rL_S. pose proof (rL_pos j Hlt). nia.
  - apply in_map_iff in Hin as (j & Heq & Hj). destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). apply in_seq in Hj.
    apply X_M; [lia|]. rewrite emeas_z0, rL_S. pose proof (rL_pos j ltac:(lia)). nia.
  - destruct Hin as [Heq|[]]. destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). apply POST. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S3eS2fVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S91S2fS88VAInv;VCST;VXGL;A5").

Lemma MINI_s : ltac2:(tb__ "0|1|
S83S1bS1S1cS71Q40A1A1M0S83S73S1bR4S44A3S1G0S85S2fVok;S3fS2fVJAv;S43R7A1A1S4aR7A1R2R1A5R4A4Ftp';Frho';S85S2fVok;S3fS2fVJAv;S43R6A1A1S4fR6A1R5R4A5R3A4F_;F_;FQ';Ftp;Frho;Fj;FQF;").
Proof.
  intros QF j rho tp Q' Hin HE. destruct (chk_live_at j Hin) as (HC & _ & _). unfold chkC in HC.
  apply (cfg_sound_JA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA FUEL_bd cutpcs_bd NP
           (map edropA [Cnode j]) (map edropA [Enode j]) ok Q' Hok (ejcertA_jcertA segs NP _ _ _ _ _ HC)) with (ndT := ndL j); [|left; reflexivity].
  intros X ndX rho1 tp1 [H|[]]. cbn [edropA Enode eda_state eda_nd fst snd] in H. destruct (edesc_eq2 _ _ _ _ H) as [<- <-].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HE].
Qed.

Theorem builder_dispose_sum : ltac2:(tb__ "0|0|
S1cS71Q40A1A1S85S2fVok;S3fS2fS36VAInv;VCST;VXGL;VKc;S82VFB;VFF;A2VFB;VFF;VBX;S33S43U0A1AaS5bVrho0;R1A5S78S2fS42Vrho0;R1SabA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA_h segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA H_bd_ejcert_ok FUEL_bd cutpcs_bd NP cutsE exitsE ok (Q tp0) Hok bd_ejcert_ok)
         with (ndT := ndL 0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros j rho1 tp1 Q' Hj HE. exact (MINI_s (Q tp0) j rho1 tp1 Q' Hj HE).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NP Kc (P0_bd FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_bd P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S92S2fS88VAInv;VCST;VXGL;A5").

Lemma MINI_e : ltac2:(tb__ "0|1|
S1bS1S1cS71Q40A1A1M0S83S73S1bR4S44A3S1G0S84S2fS3fS2fVJAv;S43R7A1A1S4aR7A1R2R1A5R4A3Ftp';Frho';S84S2fS3fS2fVJAv;S43R6A1A1S4fR6A1R5R4A5R3A3F_;F_;FQ';Ftp;Frho;Fj;").
Proof.
  intros j rho tp Q' Hin HE. destruct (chk_live_at j Hin) as (HC & _ & _). unfold chkC in HC.
  apply (cfg_complete_JA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA FUEL_bd cutpcs_bd NP [Cnode j] [Enode j] Q' HC)
    with (ndT := ndL j) (rv := (rL j - 1, z0)); [|left; reflexivity].
  intros X ndX rv rho1 tp1 [H|[]]. destruct (edesc_eq3 _ _ _ _ _ _ H) as (<- & <- & <-).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HE].
Qed.

Theorem builder_dispose_sum_ex : ltac2:(tb__ "0|0|
S1cS71Q40A1A1S84S2fS3fS2fS36VAInv;VCST;VXGL;VKc;S82VFB;VFF;A2VFB;VFF;VBX;S33S43U0A1AaS5bVrho0;R1A5S78S2fS42Vrho0;R1SabA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA_h segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA H_bd_ejcert_ok FUEL_bd cutpcs_bd NP cutsE exitsE (Q tp0) bd_ejcert_ok)
         with (ndT := ndL 0) (rv := (rL 0, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros j rho1 tp1 Q' Hj HE. exact (MINI_e j rho1 tp1 Q' Hj HE).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NP Kc (P0_bd FB FF) FB FF BX PTrue rho0 tp0 nd Posts_bd P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_builder_dispose_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epiD_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "bool"; "true"; "nil"; "cons"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "holds"; "sobj"; "SLit"; "sprop_eqb"; "SPUle"; "eval"; "ss_next"; "ss_objs"; "sv_eqb"; "SPBranch"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "NDA"; "amode"; "TPA"; "frinA"; "tvinA"; "JA"; "JA_pre"; "fbinA"; "ffinA"; "JAi"; "tvals"; "untrackedZ"; "ANone"; "nd_am"; "ok_frameKA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "True"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "PhisD"; "nd_d2"; "gp"; "nd_d1"; "nd_e"; "nd_d0"; "nd_z"; "cutsD1"; "cutsD2"; "cutsD3"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_fa"; "exitsD1"; "exitsD2"; "exitsD3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "ldef"; "P0_lo"; "@Stdlib.Lists.List"; "In"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BXok_d"; "bxt"; "bd_wpos"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "W2"; "L_f8"; "L_ms"; "Pre_f8"; "Pre_ms"; "vF"; "vFL"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiD_pf.BDP"; "P0_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tnz"; "tvd"; "T_ok"; "tvv"; "tvz"; "FBx"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "AE_A"; "UStopLe"; "JL_free"; "JL_stack_free"; "J_free_pre"; "J_memset_pre"; "J_pure_pre"; "J_stack_free_pre"; "V_FL"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "L_ok"; "E_s80"; "vG"; "E_fa0"; "E_fd0"; "E_ms0"; "L_L1"; "L_L3";
"X_A"; "X_B"; "X_fa0"; "X_fa1"; "vNx"; "nB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "P_errL"; "L_sf"; "Pre_sf"; "Ee_sf"; "Ee_sf0"; "Te_s82"; "X_sx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "kept_bd"; "K_disp"; "L_fr"; "PDk_bd"; "Pre_fr"; "E_bd0"; "L_j1s"; "Lb_j1"; "R_bd"; "E_bd"; "E_flG"; "PD_bd"; "Xk_bd"; "passed_bd"; "s_bd"; "szL"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1.BD"; "NP"; "Pre_bd"; "ndL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "extraXlo"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pdescA"; "robjs_okF"; "pclMA"; "robjs_okL"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "site_okA"; "cmaddrA"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk"; "ent_chk"; "two52"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BDP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_builder_dispose_pf. End BDP.

Lemma h0_ltBD : (h0 < BD.NP)%positive. Proof. reflexivity. Qed.
Lemma efmeas_z0 : ltac2:(tb__ "0|1|
SfS24S3S12S15S3aS12S41S0S1S1SfS24A2M0S3A2S1S12S14A2S0G0S3S0SfS24R5R4A4R3A4S0S12S14R2S6bA4A4R1A2S7bR2S7cZ2Z40A2A2A3Frho;Fr;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA, ef_rank, ef_var, z0. cbn [fst snd]. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Lemma tvd_nth_remove : ltac2:(tb__ "0|1|
S15S2S1S14S14A2M0A1S3G0G0S8eR5R4A2S3aSaG0A1S66G0R5R4A3S8G0R3A2A3S65G0R3S8cG0R5R6A3A3S8dR8R5A2S8dR9R5A2S3dS3aS1S12S12A2S90RaR7A2S90RaR6A2A3A1F_;F_;F_;F_;F_;Ft';Ft;Fi;Ftv;Frho;").
Proof.
  intros rho tv. induction tv as [|h r IH]; intros [|i] t t' HD Hn Hin Hz Hz'; cbn in Hn, Hin; try discriminate; try contradiction.
  - injection Hn as ->. destruct HD as [H _]. exact (H t' Hin Hz Hz').
  - destruct HD as [H HD']. destruct Hin as [<-|Hin].
    + intros E. exact (H t (nth_error_In _ _ Hn) Hz' Hz (eq_sym E)).
    + exact (IH i t t' HD' Hn Hin Hz Hz').
Qed.

Section DropTv.
Variable AInv : ltac2:(tb__ "0|0|
S68S15S2S35Q40A1A1S70OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1S12S12A2S12A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Lemma untrackedZ_remove_null : ltac2:(tb__ "0|1|
S15S2S1S14S14A2M0A1S3S1S12S12A2G0S3aSaG0A1S66G0R4R3A3S8G0R1A2A3S3dS8dR6R2A2A1F_;Ft;S40S31S30R5R4A2R2A2S31S30R5S8cG0R3R4A3A2R2A2A2F_;Fbn;Fi;Ftv;Frho;").
Proof.
  intros rho tv i bn HNULL. unfold untrackedZ, tvals. split.
  - intros H v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht). apply H; [apply in_map; exact (remove_nth_In _ _ _ Ht) | exact Hnz].
  - intros H v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht).
    destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.In_remove_nth_or tv i t Ht) as [E|E]; [exfalso; exact (HNULL t E Hnz)|].
    apply H; [apply in_map; exact E | exact Hnz].
Qed.
Lemma JAi_drop_tv_am : ltac2:(tb__ "0|1|
S2S1S14S14A2M0A1S2S1S1S14S12A2S14A2A1S2S74A1S27S3S68S12S15S2S35Q40A1A1S2S71A1S70G0S3aSaG0A1S66G0RcR8A3S8G0R1A2A3S3dS8dR6R2A2A1F_;Ft;S2fVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26RcRbRaR9A4R7R6R5R4R3R2A12S2fVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26S8cG0R9RdA3RcRbRaA4R8R7R6R5R4R3A12F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fi;Fam;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd am i Ai kc rho tp tr md HNULL (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am] in *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|split; [exact HPA|split; [exact HCK|
    unfold capN in *; cbn [nd_tv]; rewrite (cntS_remove_nth_null rho tv i HNULL); exact HCN]]]]]]]].
  - split; [|split].
    + unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht.
    + apply tvd_remove. exact HD.
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht.
  - unfold XA in *.
    refine (proj1 (XAz_transport FB FB (am_eval rho am) Ai Ai (rm rho) (rm rho) (tvals rho tv) (tvals rho (remove_nth i tv)) kc HXA _ _ _ _)).
    + intros b n H1 H2 H3. split; [exact H1|]. split; [exact H2|]. exact (proj1 (untrackedZ_remove_null rho tv i (b, n) HNULL) H3).
    + intros; reflexivity.
    + intros b n a _ _ _ _. split; [intros _; reflexivity | intros j _ H; exact H].
    + intros bn H1 _ H3 H4. split; [exact H1|]. split; [exact H3|]. exact (proj2 (untrackedZ_remove_null rho tv i bn HNULL) H4).
Qed.
Variable segs' : list Segment.
Lemma SPA_JA_drop_tv_am_fact : ltac2:(tb__ "0|1|
S2S1S14S14A2M0A1S2S1S1S14S12A2S14A2A1S2S74A1S27S3SfS15S2S35Q40A1A1S6fG0S3aSaG0A1S66G0RaR6A3S8G0R1A2A3S3aS4S67S16S1bS21Se8S9S14S14R2A3S1aZ0A1A3A1S17S10R6A1A1A3S5A3F_;Ft;S37Vsegs';S2bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26RaR9R8R7A4AcR5R4R3R2A6S37Vsegs';S2bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S26S8cG0R7RbA3RaR9R8A4AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FS;Fi;Fam;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd am i S rho tp [tr [ms md]] HZ [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  apply JAi_drop_tv_am; [|exact HJ]. intros t Ht Hnz.
  pose proof (smatchA_facts segs' _ _ _ _ Hsm) as HF.
  pose proof (holds_mem _ _ _ HF (HZ t Ht)) as X. apply (proj1 (holds_beq _ _ _)) in X.
  unfold tnz in Hnz. rewrite X in Hnz. apply Hnz. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). apply uval_lit. lia.
Qed.
End DropTv.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S68S15S2S35Q40A1A1S70OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa1S23VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S12Sd5VCST;R1A2S3bS78Z0R2A2S79R2Se7A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S12Sd5VXGL;R1A2S3bS78Z0R2A2S79R2Se7A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S12SebR1A1Sd5VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1S12S12A2S12A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S15OFr;") := ltac2:(tb__ "0|0|
S64VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;S7dVKc;Vrho0;VP0;VFB;VFF;VBX;S25Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S45VAInv;VCST;VXGL;S7dVKc;Vrho0;VP0;VFB;VFF;VBX;S25VPhi;Vnd;Ad").

Lemma lo_robjsF0 : ltac2:(tb__ "0|0|
S68S15S2S16A1S2S1S14S14A2A1S2S19A1S15S2S35Q40A1A1S70VAInv;R8R3R2R1A4S85S16S18R8A1R7A3VP0;Vrho0;A1Sb8S7dVrho0;RaA3S28Vrho0;RcA2S8fRcS6aS69RdA1A1A2S2aVFB;ReRdRbA4S8eReRcA2S91RfRdA2S29VFF;R11R10S61A4S3aS4SccR10RfS61S62ReA5S5A3SdcVCST;Vrho0;VFB;VFF;R12R10S61RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
Qed.
Lemma lo_robjsR0 : ltac2:(tb__ "0|0|
S68S15S2S16A1S2S1S14S14A2A1S2S19A1S15S2S35Q40A1A1S70VAInv;R8R3R2R1A4S85S16S18R8A1R7A3VP0;Vrho0;A1Sb8S7dVrho0;RaA3S28Vrho0;RcA2S8fRcS6aS69RdA1A1A2S2aVFB;ReRdRbA4S8eReRcA2S91RfRdA2S29VFF;R11R10S61A4S3aS4Sd6R10RfS61S62ReA5S5A3Se4VCST;Vrho0;VFB;VFF;R12R10S61RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkR_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
Qed.

Lemma site_rt_lo0 : ltac2:(tb__ "0|0|
SfS8bS2S19A1S15S2S1S14S14A2A1S2S74A1S27S3aS4SccS17S10R7A1A1R3S61S62R5A5S5A3S3aS4SceS17S10R8A1A1R4S61ScdS11R8A1A5S5A3Se1VAInv;VCST;VXGL;S7dVrho0;VP0;VFB;VFF;R9R8R7R6S26R5S61R4R3A4SdS12A1S68S93S3fL_;L_;AfF_;F_;Fam;Fbd;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv bd am CR CX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (lo_robjsF0 Ai rho _ tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR) as HRF.
  pose proof (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tv (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX) as HXF.
  assert (HN' : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.fbinA_FBx FB Ai rho tv [] HBf HN') as FBX. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.ffinA_FFx FF Ai rho frL HFF HFR) as FFX.
  split; [|split; [|exact I]].
  - intros o a Ho Hr. eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact (HRF o a Ho Hr)].
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact Hc].
Qed.

Lemma pclMA_cmaddrA_x : ltac2:(tb__ "0|1|
S68S15S2S1S14S14A2M0A1S3G0S12S15S2S35Q40A1A1S70VAInv;R9R3R2R1A4S2dVFB;RaA2S2eVFF;RbA2S28Vrho0;RcA2S2aVFB;RdRcRbA4S8eRdRcA2S29VFF;RfReS61A4S3aSaG0A1S66G0ReRdA3S8G0RcA2A3S8dR10RdA2SddVCST;Vrho0;S92VFB;R11S8cG0RfR10A3A3SdaVFF;R11S61A3RdA5Se2VCST;R13S8S12S9S12S12S90R12RfA2A3A2ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;Fa;Ft;Fi;Ftv;Frho;FAi;").
Proof using ALA.
  intros Ai rho tv i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hz Hp.
  pose proof (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hn) Hz) as (_ & HtL & HtF).
  destruct Hp as [Hs | [Hc | [(b & n & Hin & Hr) | (f & s & fl & Hin & Hr)]]].
  - left. destruct HT as [_ HT2]. rewrite HT2. exact Hs.
  - right. left. exact Hc.
  - right. right. left. exists b, n.
    assert (HbL : In (b, n) (aa_live Ai) /\ (b, n) <> tvv rho t).
    { apply In_FBx in Hin as [Hin|(t' & Ht' & Hz' & E)].
      - split; [exact (HBf _ Hin)|]. intros E. apply HtF. rewrite <- E. exact Hin.
      - split.
        + rewrite <- E. exact (proj1 (proj2 (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hz'))).
        + rewrite <- E. intros E'. exact (tvd_nth_remove rho tv i t t' HD Hn Ht' Hz Hz' (eq_sym E')). }
    destruct HbL as [HbL Hne]. split; [exact HbL|]. split; [|exact Hr].
    intros E. assert (E' : b = fst (tvv rho t)) by congruence.
    apply (blocks_bases_differA segs AInv CST ALA Ai rho1 tp1 md1 b n (fst (tvv rho t)) (snd (tvv rho t)) HM HbL);
      [rewrite <- surjective_pairing; exact HtL | rewrite <- surjective_pairing; exact Hne | exact E'].
  - right. right. right. exists f, s.
    destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.ffinA_FFx FF Ai rho frL HFF HFR f s fl Hin) as [H _]. split; [exact H | exact Hr].
Qed.

Lemma site_free : ltac2:(tb__ "0|3|
SfS8bS2S19A1S15S2S1S14S14A2M0A1S3G0S2S74A1S27S3aSaG0A1S66G0R5R4A3S8G0R3A2A3S3aS4SccS17S10RaA1A1S8cG0R5R6A3S61S62R8A5S5A3S3aS4SceS17S10RbA1A1S8cG0R6R7A3S61ScdS11RbA1A5S5A3S3aS4S20S9S14S14R6A3S88RbPcM1A2A2S5A3S3aS4S20ScS14S14R7A3S88RcPdM2A2A2S5A3S85S16S18RbA1S17S10ReA1A1A3S8dRcR9A2F_;Se1VAInv;VCST;VXGL;S7dVrho0;VP0;VFB;VFF;RfReRdRcS26RbS61R8R7A4S8S12S73RcS88ReG1A2A2A2S68S93S3bS8dReRbA2S3bS3aS1S12S12A2S90ReRbA2S0S12S12S73ReS88R10G1A2A2S73ReS88R10G2A2A2A4A3Sa2S7eS97S8aS89ReRfR1A3R10A2A3A2A2Lms;LAi;AfF_;F_;F_;F_;F_;F_;Fam;Fbd;Ft;Fi;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv i t bd am Hn CR CX H12 H13 Hnzf Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13. rewrite <- H12, <- H13.
  pose proof (Hnzf HF) as Hnz.
  assert (HNr : tvinA FB Ai rho (remove_nth i tv)) by (apply (tvinA_sublist FB Ai rho tv); [intros x Hx; exact (remove_nth_In _ _ _ Hx) | exact HN]).
  assert (HDr : tvd rho (remove_nth i tv)) by (apply tvd_remove; exact HD).
  assert (HZr : tvz rho (remove_nth i tv)) by (apply (tvz_sublist rho tv); [intros x Hx; exact (remove_nth_In _ _ _ Hx) | exact HZ]).
  pose proof (lo_robjsF0 Ai rho _ _ R rho1 tp1 md1 HM HF HP0 Hav HT HTK HNr HDr HZr HFR CR) as HRF.
  pose proof (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ _ (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HNr HDr HZr HFR CX) as HXF.
  split; [|split; [|split; [exact Hnz | split; [reflexivity | exact I]]]].
  - intros o a Ho Hr. exact (pclMA_cmaddrA_x Ai rho tv i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hnz (HRF o a Ho Hr)).
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    exact (pclMA_cmaddrA_x Ai rho tv i t a rho1 tp1 md1 HM HBf HFF HT HN HD HFR Hn Hnz Hc).
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S2S16A1S2S74A1S3aS4S77R1A1S5A3Se3S7dVrho0;VP0;R3S1aZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma szL_val : ltac2:(tb__ "0|0|
S15S2S16A1S85S16S18R2A1R1A3S3aS4S67S16S1bS1cSd9S1aZffffffffA1A2A1R2A3S5A3S3aS12S73R4Sc9A2S7bZ10S73R4Sd9A2A2A3F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF C. pose proof (holds_mem _ _ _ HF C) as H. rewrite h_ule, uval_lit in H by lia.
  pose proof (uval_range rho xLK) as R. unfold szL, kb. apply uval_mul_lit; lia.
Qed.

Lemma HIN_bd : ltac2:(tb__ "0|1|
S15S93S68S15S2S35Q40A1A1S70S85S16S18R6A1S17S10Sc3A1A1A3VP0;Vrho0;A1Sb8S7dVrho0;R8A3VAInv;R7R6R5R4A4S28Vrho0;R8A2S8fRbS6aS69R9A1A1A2S2dVFB;RaA2S2eVFF;RbA2S2aVFB;RcReSeS1S14S14A2SbaSc7A3M0A4S8eRfG0A2S91R10G0A2S29VFF;RfR11S61A4S3bSdcVCST;Vrho0;VFB;VFF;R12SbaS61Sc2A8S3bSdfVCST;VXGL;Vrho0;VFB;VFF;R12SbaS61Sc6A9S87S92VFB;R12SbaA3SdaVFF;R12S61A3S8aS89R12Sc2R11A3Sc8A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof epiD_chk_bd as (CR & CX & _ & _ & _ & _ & _ & F5 & _).
  assert (HNk : tvinA FB Ai rho kept_bd) by (apply (tvinA_sublist FB Ai rho (kept_bd ++ passed_bd)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_bd) by (exact (tvd_app_l rho kept_bd passed_bd HD)).
  assert (HZk : tvz rho kept_bd) by (apply (tvz_sublist rho (kept_bd ++ passed_bd)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF0 Ai rho _ kept_bd R_bd rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_bd Xk_bd rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold BDP.P0_bd. rewrite !rw_call'.
    change (wsub_get s_bd 12) with bA. change (wsub_get s_bd 16) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    pose proof (holds_mem _ _ _ HF F5) as HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6eF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S38SfS15S2S35Q40A1A1S6eS85S16S18R3A1S17S10R4A1A1A3VTR;S37S23R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S6eS6eS6eS6fR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S6eOS6eS6fR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S38S38SfSfS8bS2S19A1M0S2S1SfS5cA2M1A1S2S1S14S14A2M2A1S6eS15S2S35Q40A1A1M3G2S65G2R1R5A3S65G2R2S11RbA1A3F_;Fr;S3aSaG0A1S60RaR9R8A3S8G0R7A2A3S3aS4S5fRbRaR9R8S86G1SfS9SfS5cA2R7A4A5S5A3S15G3VTR;S37S23RfRdR2R1A5S5dS23S1eS10RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S71A1M4S93S70S39S23R9R8R10S0G4ScaR3ScbR2R1A2A4A5R13RaR9R4R2A4R13S8aS89RbRfS94R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SfS5cG4S93S70S15G3G4S93S70S65G1S0SfS5cRaR9A4R14A3S39S23R12R11R19S0G4ScaR9ScbR8R7A2A4A5R1cR13R12RaR8A4Sb8S1eS10R1aA1A1S8aS89R14R18S94R9R13RaA3A3R19A2R8A3S39S23R9R8ReS0G4ScaR7ScbR6R5A2A4A5ReS8aS89R16R1aS94RbR15RcA3A3R1bA2R15RaR9R8R6A6S3bSf2R17S94RcR16RdA3R1bR1cR1dR10R1eR19RbA9S15Sb9R18S94RdR17ReA3R1cR1dS10R1eA1S10R1fA1S10R11A1R1RcA9VTR;S37S23S5eR11S8aS89R19R1dS94ReR18RfA3A3R1eA2R18RdRcA5Sf3R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S37S23R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S15OF_;S24SfS15S2S35Q40A1A1S6eR6R3A1VTR;S37S23VJAv;R6A1R5R4R3A5R2A2F_;VTR;S37S23VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CBD : ltac2:(tb__ "0|1|
S2S1S12S12A2M0A1S2S1G0S12A2A1S76S15S2S35Q40A1A1S75Z5R3A2VTR;S37S23S2cVAInv;VCST;VXGL;VKc;S87R6R5A2R6R5R4S25Sd3ScfSbSd2U0A1A3AaSd1R3R2A5S5dS23Sd0R3R2Sd4VAInv;VCST;VXGL;VKc;S87S25SbdR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CFREE : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1VTR;S37S23S9aVAInv;S7eS97R3VKc;A5SbeR2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cSbcS98VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CUT1 : ltac2:(tb__ "0|5|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1S12G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4S51A3S42S4aR7R5A3S3bS78Z0S41S0G3G0S0G2S3S0SfS24RaR9A4R8A4R7A4R6A2M4A2S79G4R4A2A2VTR;S37S23VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUT2 : ltac2:(tb__ "0|5|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1S12G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4S52A3S42S4aR7R5A3S3bS78Z0S41S0G3G0S0G2S3S0SfS24RaR9A4R8A4R7A4R6A2M4A2S79G4R4A2A2VTR;S37S23VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma X_E_bd0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU0M1A2S4fA2SbfR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SbfS4fA4G1A4S0S12S14Z185S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldef rho) in HPHI.
  pose proof epiD1_checks_bd as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cxk & Chand & Chb & Cnb & Cbr & Cnp & CT0 & CB & Ctidy & Cwf & Ckept & Cktv & Cbd' & Cam' & _).
  pose proof epiD_chk_bd as (CR & CX & Cwp & F1 & F2 & F3 & F4 & F5 & F6 & CVb).
  apply (TR_pre (SPA segs (JAv (ndEp tv_bd bd_disp)) E_bd rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv (ndEp tv_bd bd_disp)) xf_bd rho E_bd0 E_bd tp w Cxf).
    unfold ndEp. apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL tv_bd frL bd_disp (AHead pH false) E_bd0 rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndEp] in HZ. intros E0.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [unfold tv_bd; apply in_or_app; left; rewrite Ckept; left; reflexivity|].
    unfold tnz. cbn [fst]. intros H. exact (H E0). }
  intros Hnull.
  unfold ndEp, tv_bd.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX BDP.P0_bd PTrue (fun _ H => H) (fun _ _ _ H => H)
           BD.Pre_bd (ndh h0 false (BD.ndL 0)) PDk_bd BD.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CBD eq_refl
           E_bd s_bd R_bd Xk_bd rho tp kept_bd passed_bd frL bd_disp brest_bd (AHead pH false) (FAM (efmeasA (E_bd0, nd_d0, 0%nat, (389, z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand, Chb. apply payA_same. exact Cwp.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_bd rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndLd] PsiL] rho' tp' Hd Hag HK _.
    cbn [PDk_bd liftPD PDh PD_bd map In fst snd] in Hd. destruct Hd as [Hd|[]]. injection Hd as <- <- <-. cbn [fst snd].
    rewrite Cktv, Cbd', Cam', CT0.
    apply (TR_pre (SPA segs (JAv nd_d1) T_bd rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_d1) xfb_bd rho' T_bd0 B_bd tp' w CB Hw). }
    apply (CUT1 T_bd nd_d1 0%nat (380, z0) rho' tp'); [right; left; reflexivity | | rewrite !efmeas_z0; lia].

    change (ldef rho').
    assert (E466 : uval rho' xLD = uval rho xLD) by (apply (uval_rw rho rho' 466 xLD eq_refl); apply (proj1 Hag); reflexivity).
    assert (E468 : uval rho' xLK = uval rho xLK) by (apply (uval_rw rho rho' 468 xLK eq_refl); apply (proj1 Hag); reflexivity).
    pose proof (szL_val rho _ HF F2) as ESZ.
    intros z Hz. rewrite E466, E468 in Hz.
    destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
    pose proof (holds_mem _ _ _ HF F3) as H3. rewrite h_ule, uval_lit in H3 by lia.
    pose proof (holds_mem _ _ _ HF F1) as H1. rewrite h_ule, uval_lit in H1 by lia. fold szL in H1.
    pose proof (holds_mem _ _ _ HF F4) as H4. rewrite h_ule in H4. fold szL in H4.
    pose proof (holds_mem _ _ _ HF F6) as H6. rewrite h_ule, uval_lit in H6 by lia.
    rewrite (uval_add_small rho xLD szL) in H4 by lia.
    rewrite (keptK_lines CST FB FF rho0 rho kept_bd frL rho' HK ltac:(rewrite Ckept; left; reflexivity) Hnz ltac:(lia) ltac:(unfold B32, Lib_vec_reserve.B32; lia) z Hz).
    exact (HPHI z Hz).
Qed.

Lemma X_L_j1s : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU0M1A2S4dA2Sc0R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sc0S4dA4G1A4S0S12S14Z17bS6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_j1 as (C1 & _ & Crm). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD1_checks_j1 as (_ & _ & _ & _ & _ & Cz).
  pose proof epiD1_checks_fl as (_ & _ & _ & _ & _ & _ & _ & Cnth & _).
  apply (TR_pre (SPA segs (JAv nd_d2) K_j1 (rho_sub rho s_j1s) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_j1s K_j1 s_j1s nd_d1n nd_d2 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    unfold nd_d1n, ndEp. rewrite <- Crm.
    apply (SPA_JA_drop_tv_am_fact AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue segs kept_bd frL brest_bd (AHead pH false) 0%nat L_j1s rho tp w); [|exact Hw].
    intros t Ht. rewrite Cnth in Ht. injection Ht as <-. exact Cz. }
  apply (CUT2 K_j1 nd_d2 1%nat (360, z0) (rho_sub rho s_j1s) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_Lb_j1 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2Sc1R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sc1S4bA4G1A4S0S12S14Z171S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_j1 as (_ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_d2) K_j1 (rho_sub rho s_j1b) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb_j1 K_j1 s_j1b nd_d2 nd_d2 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUT2 K_j1 nd_d2 1%nat (360, z0) (rho_sub rho s_j1b) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_L_fl : ltac2:(tb__ "0|3|
SfS15S2S35Q40A1A1M0G0S3aS4SecR4Sc4S6S1S13S14A2A1S4dS4dA5S5A3VTR;S37S23VJAFv;S42S4aU0M1A2S4dA2R5R4R3A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24R5S4dA4G1A4S0S12S14Z17bS6bA4A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FL;").
Proof.
  intros L rho tp tp0 CE. apply TR_JAF. intros HPHI. change (ldef rho) in HPHI.
  apply ent_chk_unf in CE as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD_chk_fl as (_ & _ & CidV & F1 & F2 & Csite & Ccarve & CdX & Ffsz & CR & CX & Fdnz & Cpay & Cbb & CT0 & Crm).
  pose proof epiD1_checks_fl as (_ & _ & CflF & Cfb & Fdnz0 & CwfC & Cbase & Cnth & CwfE & Cent & Cchk & Cta & Cnp' & Cnb' & C12 & C13 & Ctidy & CwfT & _).
  set (rho1 := rho_sub rho []).
  assert (HPHI1 : ldef rho1) by (exact (phi_sub V_ld ldef ldef_reads [] rho CidV HPHI)).
  apply (TR_pre (SPA segs (JAv nd_d1) E_flG rho1 tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L E_flG [] nd_d1 nd_d1 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply TR_facts. intros HFG.
  pose proof (szL_val rho1 _ HFG F2) as ESZ.
  apply (TR_pre (SPA segs (JAv nd_d1) E_fl rho1 tp)).
  { intros [tr [ms md]] Hw.
    assert (HwF : SPA segs (JAv nd_d1) E_flF rho1 tp (tr, mkCfg ms md)).
    { rewrite <- CflF. apply (SPA_refacts_JA segs _ rho1 _ _ tp _ Hw Cfb).
      intros tr' md' HJ _. apply Forall_app. split; [|exact HFG]. constructor; [|constructor].
      destruct HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (HN & _ & _) & _). cbn [nd_tv nd_d1 ndEp] in HN.
      pose proof (holds_mem _ _ _ HFG Fdnz0) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
      change (bv_unsigned (eval rho1 (SLit 0))) with (uval rho1 (SLit 0)) in Hd. rewrite uval_lit in Hd by lia.
      destruct (proj1 (Forall_forall _ _) HN (xLD, szL) (nth_error_In _ _ Cnth) Hd) as (Hpos & _).
      unfold fact_sz. rewrite h_ule, uval_lit by lia. unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho1 szL)) with (uval rho1 szL) in Hpos. lia. }
    rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0)|].
    rewrite <- Ccarve.
    refine (proj1 (JA_carve_tr segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HNP kept_bd frL brest_bd (AHead pH false) 0%nat xLD szL xLD szL E_flF rho1 tp tr ms md
                     Cnth Cbase ltac:(rewrite Ccarve; exact CwfC) _ _ _ HwF)).
    - intros r HFr. pose proof (holds_mem _ _ _ HFr Ffsz) as Hs. unfold fact_sz in Hs. rewrite h_ule, uval_lit in Hs by lia. lia.
    - apply (carve_site_chk_sound segs AInv CST ALA HCST NP rho0 P0 FB FF E_flF kept_bd frL 0%nat extraLO rho1 Csite).
      intros Ai tp1 md1 _ HP0 Hav _ _ _ _ _ _ _ _ _ o a Ho HE Hr. left. exact (extraLO_pclMA CST rho0 FB FF rho1 _ frL o a Hav HP0 HE Hr).
    - intros z Hz. apply HPHI1. rewrite <- ESZ. exact Hz. }
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_fl s_fl R_fl rho1 tp nd_d1 0%nat (xLD, szL) KU1 (FAM (efmeasA (L, nd_d1, 0%nat, (379, z0)) rho) tp0) CFREE
           Cent Cchk Cta Cnp' Cnb' Cbb Cnth).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fl s_fl R_fl rho1 kept_bd 0%nat (xLD, szL) brest_bd (AHead pH false) Cnth); [rewrite Crm; exact CR | rewrite Crm; exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. pose proof (holds_mem _ _ _ HFE Fdnz) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
    change (bv_unsigned (eval rho1 (SLit 0))) with (uval rho1 (SLit 0)) in Hd. rewrite uval_lit in Hd by lia. exact Hd.
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_d1 ndEp]. unfold Pre_fr, L_fr in CT0. rewrite Crm, CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) T_fl rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT1 T_fl nd_d2 1%nat (370, z0) rho' tp'); [right; right; left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Hypothesis CUT3 : ltac2:(tb__ "0|5|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1S12G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4S53A3S42S4aR7R5A3S3bS78Z0S41S0G3G0S0G2S3S0SfS24RaR9A4R8A4R7A4R6A2M4A2S79G4R4A2A2VTR;S37S23VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma popN_site : ltac2:(tb__ "0|1|
S2S1S14S14A2A1S2S74A1S27SfS15S2S35Q40A1A1S6fS37S23VJAv;S26R7S61R6R5A4A1R4R3R2R1A6S3aS4Sd6S17S10R5A1M0A1R8S61S62S1fG0A1A5S5A3S3aS4S49S17S10R6A1A1R9S11R6A1A3S5A3S3bSe4VCST;Vrho0;VFB;VFF;R6RaS61S1fS10R7A1A1A8Se5R6S11R7A1A2A2F_;F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ftv;").
Proof using ALA HCST.
  intros tv bd am A rho tp [tr [ms md]] [Hsm (Ai & kc & HJ)] CR CX.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _). cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
  split.
  - exact (lo_robjsR0 Ai rho _ tv _ rho tp md HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai rho _ tv _ rho tp md HM HF HN HZ CX).
Qed.

Lemma gp_val : ltac2:(tb__ "0|0|
S15S14S12S2S16A1S85S16S18R4A1R1A3S3aS4S67S16S1bS1cR4S1aSedA1A2A1R2A3S5A3S3bS78Z0R4A2S79R4Z1000A2A2S3aS12S36Q40S1dR7S4cR6R5A2A2A2S7aS73R7R6A2R5A2A3F_;F_;F_;Ffacts;Fk;Fg;Frho;").
Proof.
  intros rho g k facts HF C Hk. pose proof (holds_mem _ _ _ HF C) as H. rewrite h_ule, uval_lit in H by (unfold two52, TobjJAD.two52; lia).
  unfold two52, TobjJAD.two52 in H. pose proof (uval_range rho g) as R.
  change (bv_unsigned (eval rho (gp g k))) with (uval rho (gp g k)). unfold gp.
  assert (Ek : uval rho (SLit k) = k) by (apply uval_lit; lia). rewrite <- Ek at 2. apply uval_add_small. rewrite Ek. lia.
Qed.
Lemma efmeas_gp : ltac2:(tb__ "0|2|
SfS24S3S12S14S12S15S3aS12S41S0S1S1SfS24A2M0S3A2S1S12S14A2S0G0S3S0SfS24R7R6A4R5A4S0S12S14R4S4cR3R2A2M1A4A4R1A2S7aS7bR4S7cZ2Z40A2A2S36Q40S1dR1G1A2A2A2A3Frho;Fc;Fg;Fr;Fk;Fnd;FT;").
Proof. reflexivity. Qed.

Lemma X_X_fa0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2SadR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SadS4bA4G1A4S0S12S14Z167S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & Cz & _).
  apply (TR_pre (SPA segs (JAv nd_fa) K_fa (rho_sub rho s_fa0) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc X_fa0 K_fa s_fa0 nd_fa nd_fa rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (JA_head0_none segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX tvA frL KU1 pH false X_fa0 rho tp w Cz Hw). }
  apply (CUT3 K_fa nd_fa 1%nat (250, z0) (rho_sub rho s_fa0) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_X_fa1 : ltac2:(tb__ "0|4|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S54SafSa5A2M2A2SaeR3R2A5VFAM;S41S0S1S1SfS24A2M3S3A2S1S12S14A2S0G3S3S0SfS24SaeG2A4G1A4S0S12S14Z12bS6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & _ & Cz & _).
  apply (TR_pre (SPA segs (JAv nd_fa) K_fa (rho_sub rho s_fa1) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc X_fa1 K_fa s_fa1 nd_fa nd_fa rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (JA_headN_none segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX tvA frL KU1 vNx vG X_fa1 rho tp w Cz Hw). }
  apply (CUT3 K_fa nd_fa 1%nat (250, z0) (rho_sub rho s_fa1) tp); [left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_X_A : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4bA2SabR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SabS4bA4G1A4S0S12S14Z167S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & _ & _ & CnpA & CnbA & CnpA1 & CnbA1 & CR & CX & Cnd & _).
  pose proof epiD2_checks_loop1 as (_ & _ & ClenN & CwfA1 & Cpop & CwfA2 & CbaseA1 & Chnz & _).
  apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_A2) X_A2 rho2 tp w)).
  { intros w Hw.
    destruct (JA_lenN segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX ALA HKc tvA frL KU1 pH false X_A rho tp w ltac:(rewrite ClenN; exact CwfA1) CnpA CnbA Hw) as (rho1 & _ & Hw1).
    rewrite ClenN in Hw1. fold gA in Hw1.
    destruct (JA_popN segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX ALA HCST HXGL HKc HNP tvA frL KU1 pH gA X_A1 rho1 tp w ltac:(rewrite Cpop; exact CwfA2) CbaseA1 CnpA1 CnbA1 Chnz
                ltac:(intros; exact (popN_site tvA KU1 (AHeadN pH gA) X_A1 rho1 tp w Hw1 CR CX)) Hw1) as (rho2 & _ & Hw2 & _).
    exists rho2. rewrite Cpop in Hw2. unfold nx in Cnd. rewrite Cnd in Hw2. exact Hw2. }
  apply TR_exw. intros rho2.
  apply (CUT2 X_A2 nd_A2 1%nat (350, z0) rho2 tp); [right; left; reflexivity | exact I | rewrite !efmeas_z0; lia].
Qed.

Lemma X_L_L1 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S55A2Sa9R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa9S55A4G1A4S0S12S14Z15dS6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & C1 & _). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_CL) C_L (rho_sub rho s_L1) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_L1 C_L s_L1 nd_A2 nd_CL rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUT2 C_L nd_CL 1%nat (300, gp vG 8) (rho_sub rho s_L1) tp); [right; right; left; reflexivity | exact I |].
  rewrite efmeas_z0, efmeas_gp. pose proof (bv_urange (eval (rho_sub rho s_L1) (gp vG 8))) as R. lia.
Qed.
Lemma X_L_L3 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S56A2SaaR3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24SaaS56A4G1A4S0S12S14Z12cS4cS22Sf5Sb0P3A2A1ZbA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & _ & C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FgL & Csub). apply ent_chk_unf in C1 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply TR_facts. intros HF.
  apply (TR_pre (SPA segs (JAv nd_CL) C_L (rho_sub rho s_L3) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_L3 C_L s_L3 nd_B2 nd_CL rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw). }
  apply (CUT2 C_L nd_CL 1%nat (300, gp vG 8) (rho_sub rho s_L3) tp); [right; right; left; reflexivity | exact I |].
  rewrite !efmeas_gp. rewrite <- (eval_subst rho s_L3 (gp vG 8)), Csub.
  rewrite (gp_val rho (SVar (nB + 3)) 8 _ HF FgL) by lia. rewrite (gp_val rho (SVar (nB + 3)) 11 _ HF FgL) by lia.
  pose proof (uval_range rho (SVar (nB + 3))) as R. lia.
Qed.

Lemma gp_val' : ltac2:(tb__ "0|0|
S15S14S12S78S73R3R2A2S7cZ2Z34A2A2S3bS78Z0R2A2S79R2Z1000A2A2S3aS12S36Q40S1dR5S4cR4R3A2A2A2S7aS73R5R4A2R3A2A3F_;F_;Fk;Fg;Frho;").
Proof.
  intros rho g k H Hk. pose proof (uval_range rho g) as R.
  change (bv_unsigned (eval rho (gp g k))) with (uval rho (gp g k)). unfold gp.
  assert (Ek : uval rho (SLit k) = k) by (apply uval_lit; lia). rewrite <- Ek at 2. apply uval_add_small. rewrite Ek. lia.
Qed.

Lemma X_E_fd0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S57A2Sa7R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa7S57A4G1A4S0S12S14Z12cS4cSa5Z7A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD2_checks_fd as (_ & Cxf & CwfE & Cent & Cchk & Cta & Cnp & C12 & C13 & Ctidy & CwfT & _).
  pose proof epiD_chk_fd as (CdX & CR & CX & Fnz & Cpay & Cbb & Cnb & CT0 & Fg & Cgb).
  apply (TR_pre (SPA segs (JAv nd_CL) E_fd rho tp)).
  { intros w Hw. rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0)|].
    exact (SPA_axforms segs (JAv nd_CL) (xf_fd E_fd0) rho E_fd0 E_fd1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_fd s_fd R_fd rho tp nd_CL 0%nat (vNd, e32 vCap) KU1 (FAM (efmeasA (E_fd0, nd_CL, 1%nat, (300, gp vG 7)) rho) tp0) CFREE
           Cent Cchk Cta Cnp Cnb Cbb eq_refl).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fd s_fd R_fd rho ((vNd, e32 vCap) :: tvA) 0%nat (vNd, e32 vCap) (KU1 ++ [BIc 0 1 KU]) (AHeadN vNx vG) eq_refl);
      [exact CR | exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. pose proof (holds_mem _ _ _ HFE Fnz) as Hd. apply (proj1 (holds_nbeq _ _ _)) in Hd.
    change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in Hd. rewrite uval_lit in Hd by lia. exact Hd.
  - intros rho' tp' Hag _. cbn [nd_tv nd_fr nd_am nd_CL ndN remove_nth]. unfold Pre_fr, L_fr in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv (ndT vNx vG)) T_fd rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT2 T_fd (ndT vNx vG) 1%nat (300, gp vG 6) rho' tp'); [right; right; right; left; reflexivity | exact I |].
    rewrite !efmeas_gp. rewrite <- (eval_agree_vals _ rho rho' (gp vG 6) Hag Cgb).
    rewrite (gp_val rho vG 6 _ HF Fg) by lia. rewrite (gp_val rho vG 7 _ HF Fg) by lia.
    pose proof (uval_range rho vG) as R. lia.
Qed.

Lemma X_X_B : ltac2:(tb__ "0|4|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S54SafSa5A2M2A2SacR3R2A5VFAM;S41S0S1S1SfS24A2M3S3A2S1S12S14A2S0G3S3S0SfS24SacG2A4G1A4S0S12S14Z12cS4cSa5Z5A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD_chk_loop as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CnpB & CnbB & CRB & CXB & CndB & CnB & FgB & _ & _).
  pose proof epiD2_checks_fd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fnz & Cpop & CwfB2 & CbaseB & _).
  apply TR_facts. intros HF.
  pose proof (holds_mem _ _ _ HF FgB) as HgB. rewrite h_ule, uval_lit in HgB by (unfold two52, TobjJAD.two52; lia). unfold two52, TobjJAD.two52 in HgB.
  apply (TR_pre (fun w => exists rho2, (bv_unsigned (rw rho2 (nB + 3)%positive) + 16 = uval rho vG) /\ SPA segs (JAv nd_B2) X_B2 rho2 tp w)).
  { intros w Hw.
    destruct (JA_popN segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX ALA HCST HXGL HKc HNP tvA frL KU1 vNx vG X_B rho tp w ltac:(rewrite Cpop; exact CwfB2) CbaseB CnpB CnbB Fnz
                ltac:(intros; exact (popN_site tvA KU1 (AHeadN vNx vG) X_B rho tp w Hw CRB CXB)) Hw) as (rho2 & _ & Hw2 & Hg).
    exists rho2. unfold nx in CnB, CndB. rewrite CnB in Hg. split; [exact Hg|]. rewrite Cpop in Hw2. rewrite CndB in Hw2. exact Hw2. }
  apply TR_exw. intros rho2.
  apply (TR_pureP _ (bv_unsigned (rw rho2 (nB + 3)%positive) + 16 = uval rho vG)); [intros w [H _]; exact H|]. intros Hg.
  apply (TR_pre (SPA segs (JAv nd_B2) X_B2 rho2 tp)); [intros w [_ Hw]; exact Hw|].
  apply (CUT2 X_B2 nd_B2 1%nat (300, gp (SVar (nB + 3)) 12) rho2 tp); [right; right; right; right; left; reflexivity | exact I |].
  rewrite !efmeas_gp. rewrite (gp_val rho vG 5 _ HF FgB) by lia.
  assert (Eg : uval rho2 (SVar (nB + 3)) = bv_unsigned (rw rho2 (nB + 3)%positive)) by reflexivity.
  pose proof (uval_range rho2 (SVar (nB + 3))) as R.
  rewrite (gp_val' rho2 (SVar (nB + 3)) 12) by lia. lia.
Qed.

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1VTR;S37S23S9bVAInv;R3VKc;A3S82R2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cS80S95VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1VTR;S37S23S9cVAInv;R3VKc;A3S81R2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cS7fS95VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CSF : ltac2:(tb__ "0|2|
S68S15S2S35Q40A1A1VTR;S37S23S9dVAInv;Z5M0R3VKc;A4Sb3R2R1A5S5dS23S72R2R1S7S1SfS5cA2M1S0SfS5cSb2S99VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A2Ftp1;Frho1;FAi;").

Lemma CXR_s8a : ltac2:(tb__ "0|0|
S3aS4Sd8VXGL;S17S10Sa4A1A1S6S1S14S14A2A1Z44Ze7Sb7Sa4A1A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_s8r : ltac2:(tb__ "0|0|
S3aS4Sd8VXGL;S17S10Sb6A1A1S6S1S14S14A2A1Z20Z40S11Sb6A1A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXL_sf : ltac2:(tb__ "0|0|
S3aS4Se6VXGL;S17S10Sb4A1A1S6S1S14S14A2A1S61S8S3U0A2S6S19A1Sd7S11Sb4A1A8S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma c5_ok : 0 <= 5 <= 6. Proof using . lia. Qed.
Lemma k68 : 0 <= 68. Proof using . lia. Qed.
Lemma k32 : 0 <= 32. Proof using . lia. Qed.
Lemma k68_231 : 68 <= 231 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Lemma k32_64 : 32 <= 64 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Lemma tnz_of_ule4096 : ltac2:(tb__ "0|0|
S15S2S16A1S1S14S14A2S85S16S18R3A1R2A3S3aS4S67S16S1bS1cS1aZ1000A1S9S14S14R2A3A2A1R3A3S5A3S8dR5R3A2F_;F_;Ft;Ffacts;Frho;").
Proof using . intros rho facts t HF C. pose proof (holds_mem _ _ _ HF C) as Hd. rewrite h_ule, uval_lit in Hd by lia. unfold tnz. change (bv_unsigned (eval rho (fst t))) with (uval rho (fst t)). lia. Qed.
Ltac meas_z0 := rewrite !efmeas_z0; vm_compute; split; [discriminate | reflexivity].
Lemma X_sx_incl : ltac2:(tb__ "0|1|
SfS1S14S14A2M0S65G0R1Sb7R2A1A3S65G0R2S11R3A1A3F_;Fr;FE;").
Proof using . intros E r H. unfold X_sx in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma X_E_fa0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S58A2Sa6R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa6S58A4G1A4S0S12S14Zf9S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & _ & _ & _ & CwfE & Cent & Cchk & Cta & Cnp & C12 & C13 & Ctidy & CwfT & _).
  pose proof epiD_chk_fa as (CdX & CR & CX & F4096 & Cpay & Cnb & CT0).
  apply (TR_pre (SPA segs (JAv nd_fa) E_fa rho tp)).
  { intros w Hw. rewrite <- CdX. unfold dropX. apply SPA_x_sub; [intros r0 Hr0; apply filter_In in Hr0; exact (proj1 Hr0) | exact Hw]. }
  unfold Pre_fr, L_fr in Cent, Cchk.
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_fa s_fa R_fa rho tp nd_fa 0%nat (vARn, SLit 64) [] (FAM (efmeasA (E_fa0, nd_fa, 1%nat, (249, z0)) rho) tp0) CFREE
           Cent Cchk Cta Cnp Cnb eq_refl eq_refl).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - apply (site_free E_fa s_fa R_fa rho tvA 0%nat (vARn, SLit 64) KU1 ANone eq_refl); [exact CR | exact CX | rewrite C12; reflexivity | rewrite C13; reflexivity |].
    intros HFE. exact (tnz_of_ule4096 rho _ (vARn, SLit 64) HFE F4096).
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_fa tvA remove_nth]. unfold Pre_fr, L_fr in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_e) T_fa rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT3 T_fa nd_e 1%nat (240, z0) rho' tp'); [right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_E_ms0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4eA2Sa8R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa8S4eA4G1A4S0S12S14ZefS6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD2_checks_fa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CentM & CchkM & _ & Ctidy & Cwf & _).
  pose proof epiD_chk_ms as (Cta & Cnp & Cnb & Cshape & CR & CX & CT0).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call.purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E_ms0 s_ms R_ms rho tp nd_e [] (FAM (efmeasA (E_ms0, nd_e, 1%nat, (239, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMSET Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact CentM.
  - exact CchkM.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - apply payA_same. reflexivity.
  - exact Cshape.
  - exact (site_rt_lo0 E_ms0 s_ms R_ms rho [] [] ANone CR CX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ms0 memset_pc s_ms R_ms rho tp tr ms md Hsm HM HX' CentM).
  - intros L rho2 tp2 [<-|[]] _ _. cbn [nd_tv nd_fr nd_am nd_e]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_e) T_ms rho2 tp2)).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT3 T_ms nd_e 1%nat (230, z0) rho2 tp2); [right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_E_s80 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4eA2Sa4R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sa4S4eA4G1A4S0S12S14Ze5S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD3_checks_s8 as (CwfA & CeqA & Cxf & Cent & Cchk & CT0 & Cxb & Cobjs & Ceq82 & Cwf82 & CeqR & CwfR & Ctidy & CwfT & _).
  pose proof epiD_chk_s8 as (Cbase0 & Chf0 & CR0 & Cta & Cnp & Cnb & Cshape & CR & CX & Cbase1 & Chf1 & Cnb1 & CR1 & Cbase2 & Chf2 & CR2).
  pose proof epiD_chk_sx as (XeqA & XwfA & Xeq82 & XeqR & XwfR & _).
  apply (TR_pre (SPA segs (JAv nd_e) Ee_s8 rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv nd_e) (xf_shcall Ee_s8a 68) rho Ee_s8a Ee_s8 tp w Cxf). rewrite <- XeqA.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] frL [] ANone 0%nat 110%positive 5 120%positive g5 68 231 E_s80 (X_sx E_s80) rho tp w eq_refl c5_ok Cbase0 k68
             k68_231 Chf0 (X_sx_incl E_s80) XwfA); [|exact Hw].
    intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    - exact (lo_robjsR0 Ai rho _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR0).
    - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ [] (X_sx E_s80) rho3 tp3 md3 68 231 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8a). }
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] Ee_s8 (s_s8 Ee_s8) Re_s8 rho tp nd_e [] (FAM (efmeasA (E_s80, nd_e, 1%nat, (229, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - apply payA_same. reflexivity.
  - exact Cshape.
  - exact (site_rt_lo0 Ee_s8 (s_s8 Ee_s8) Re_s8 rho [] [] ANone CR CX).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_e]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_e) Te_s81 rho' tp')).
    { intros w Hw. exact (SPA_axforms segs (JAv nd_e) (xf_shback Te_s80) rho' Te_s80 Te_s81 tp' w Cxb Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_e) Te_s8 rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj g5 68 231 [] DUnknown] (vms md tp' ms)).
      rewrite <- Ctidy. apply SPA_tidy. rewrite <- XeqR.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               [] frL [] ANone 0%nat 110%positive 5 120%positive g5 32 64 Te_s82 (ax_X Te_s82) _ tp' (tr, mkCfg ms md) eq_refl c5_ok Cbase2 k32
               k32_64 Chf2 (fun r H => H) XwfR).
      - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
        + exact (lo_robjsR0 Ai _ _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR2).
        + exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai _ _ [] (ax_X Te_s82) rho3 tp3 md3 32 64 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8r).
      - rewrite <- Xeq82.
        apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
                 [] frL [] ANone 0%nat 110%positive 5 120%positive g5 68 231 [] DUnknown Te_s81 (objs_butlast Te_s81) [] rho' tp' tr ms md
                 eq_refl c5_ok Cbase1 Cobjs k68 k68_231 eq_refl Chf1 eq_refl Cnb1); [|exact Hw].
        intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (lo_robjsR0 Ai rho' _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR1). }
    apply TR_exw. intros rho2.
    apply (CUT3 Te_s8 nd_e 1%nat (220, z0) rho2 tp'); [right; right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma site_sf : ltac2:(tb__ "0|8|
SfS8bS2S19A1S15S3aS4Sf4S17S10R4A1A1S6S1S14S14A2A1M0S61S8S3U0M1A2M2S62R2A6S5A3S3aS4Se6VXGL;S17S10R5A1A1G0S61G2S6S19A1Sd7S11R5A1A8S5A3S3aS14S88R5PcM3A2S83A3S3aS14S88R6S9eA2S84A3S68S85S16S18R6A1S17S10R9A1A1A3VP0;Vrho0;A1Sb8S7dVrho0;R8A3S2dVFB;R4A2S2eVFF;R5A2S2aVFB;R6RbG0A4S8eRcG0A2S91RdG0A2S29VFF;R9ReS61A4S3cS15S15S3cS2S35Q40A1A1M4G4S3cS70S70VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S28Vrho0;RbA2S8fR11S6aS69RcA1A1A2S3bSdeVCST;Vrho0;VFB;VFF;R12G0S8cS1S1S14S12A2M5S14A2G1S61A3M6R13A8S3bSe0VCST;VXGL;Vrho0;VFB;VFF;R12G0G6S11R15A1A9S3bS3aS12S73R12S88R14G3A2A2S73R12S9S14S12S9G5S14S0G5S14S0S14S12S83Z5A4S84A4M7A3A3A2A3S3aS12S73R12S88R14S9eA2A2S73R12ScG5S14G7A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;Frho;FR;Fs;FE;").
Proof using ALA HXlits.
  intros E s R rho HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr.
    apply (TobjJAT.robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [] frL (Some 0%nat) extraLO R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HR) with (o := o); [| exact Ho | exact Hr].
    intros o' a' _ HE Hr'. exact (extraLO_pclMA CST rho0 FB FF rho [] _ o' a' Hav HP0 HE Hr').
  - apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho _ [] frL (Some 0%nat) [] extraXlo (ax_X E) rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HX).
    intros r' a' _ HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
    + left. exact (xextraLO_pclMA CST rho0 FB FF rho [] _ r' a' Hav HP0 HE Ha).
    + right. apply HXlits. exact (xr_inlits_sound r' rho a' HE Ha).
Qed.

Lemma X_Ee_sf0 : ltac2:(tb__ "0|3|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAFv;S42S4aU1M1A2S4eA2Sb5R3R2A5VFAM;S41S0S1S1SfS24A2M2S3A2S1S12S14A2S0G2S3S0SfS24Sb5S4eA4G1A4S0S12S14ZdbS6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiD3_checks_sf as (CxfA & CwfB & CxfC & CxfD & CwfE & Cent & Cchk & CwfT & _).
  pose proof epiD_chk_sf as (CbaseA & CobjsA & Cdw & ChfA & CnbA & CRA & CeqB & CbaseD & CeqF & CswfF & CRD & CXD & Cta & Cnp & Cnb & C12 & C16 & CRsf & CT0 & Ctidy).
  pose proof epiD_chk_sx as (_ & _ & _ & _ & _ & XeqB & XwfF).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_e) Ee_sf rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 32 64 (ob_cells she) (ob_dflt she)] (vms md tp ms)).
    rewrite <- CeqF.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] frL [] ANone 0%nat 110%positive 5 120%positive Ee_sfD _ tp (tr, mkCfg ms md) eq_refl c5_ok CbaseD XwfF).
    - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      + intros o a Ho Hr. destruct (lo_robjsR0 Ai _ _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRD o a Ho Hr) as [X|X]; [left; exact X | right; left; exact X].
      + exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai _ _ [] _ rho3 tp3 md3 HM HF HN HZ CXD).
    - apply (SPA_axforms segs (JAv nd_e) (xf_merge Ee_sfC) _ Ee_sfC Ee_sfD tp _ CxfD).
      apply (SPA_axforms segs (JAv nd_e) (xf_rebase Ee_sfB) _ Ee_sfB Ee_sfC tp _ CxfC).
      rewrite <- XeqB.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               [] frL [] ANone 0%nat 110%positive 5 120%positive g5 32 64 (ob_cells she) (ob_dflt she) Ee_sfA (objs_butlast Ee_sfA) [] rho tp tr ms md
               eq_refl c5_ok CbaseA CobjsA k32 k32_64 Cdw ChfA eq_refl CnbA).
      + intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (lo_robjsR0 Ai rho _ [] _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRA).
      + exact (SPA_axforms segs (JAv nd_e) (xf_sh Ee_sf0) rho Ee_sf0 Ee_sfA tp _ CxfA Hw). }
  apply TR_exw. intros rho1.
  unfold Pre_sf, L_sf in Cent, Cchk.
  apply (sfree_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           5 Ee_sf (s_sf Ee_sf) Re_sf (ax_X Ee_sf) rho1 tp nd_e 0%nat (vF, 5, vFL) (FAM (efmeasA (Ee_sf0, nd_e, 1%nat, (219, z0)) rho) tp0) CSF c5_ok).
  - intros r H. exact H.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A A' _. exact I.
  - exact (site_sf Ee_sf (s_sf Ee_sf) Re_sf rho1 CRsf CXL_sf C12 C16).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_bd nd_am nd_e remove_nth frL]. unfold Pre_sf, L_sf in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_z) Te_sf rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT3 Te_sf nd_z 1%nat (210, z0) rho' tp'); [right; right; right; right; left; reflexivity | exact I | meas_z0].
Qed.

Hypothesis XOK : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAv;S4bA1Sa3R3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24Sa3S4bA4U1A4S0S12S14Z167S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Hypothesis XPOST : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0VTR;S37S23VJAv;S50A1Sb1R3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24Sb1S50A4U1A4S0S12S14Zd1S6bA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").

Lemma exitsD1_ok : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S59A3VTR;S37S23VJAFv;S42S4aR6A2R7A2R8R4R3A5VFAM;S41S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsD1 In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <- <-.
  - apply X_E_bd0.
  - apply X_L_j1s.
  - apply X_L_fl. exact (proj1 epiD_chk_fl).
  - apply X_L_fl. exact (proj1 (proj2 epiD_chk_fl)).
  - apply X_Lb_j1.
Qed.
Lemma exitsD2_ok : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S5aA3VTR;S37S23VJAFv;S42S4aR6A2R7A2R8R4R3A5VFAM;S41S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsD2 In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <- <- <-.
  - apply TR_JAF. intros _. apply XOK.
  - apply X_X_fa0.
  - apply X_X_A.
  - apply X_L_L1.
  - apply X_E_fd0.
  - apply X_X_fa1.
  - apply X_X_B.
  - apply X_L_L3.
Qed.
Lemma exitsD3_ok : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S5bA3VTR;S37S23VJAFv;S42S4aR6A2R7A2R8R4R3A5VFAM;S41S0G3G0S0G2S3S0SfS24R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsD3 In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <- <-.
  - apply X_E_fa0.
  - apply X_E_ms0.
  - apply X_E_s80.
  - apply X_Ee_sf0.
  - apply TR_JAF. intros _. apply XPOST.
Qed.
End X.

Lemma HamPD_bd : ltac2:(tb__ "0|0|
S85SdbSdbS3aS27S33ScSfS24R1A3A1S32A3Ld;Sc5A3"). Proof. repeat constructor. Qed.
Lemma P0_bd_mono : ltac2:(tb__ "0|2|
S2S1S12S12A2M0A1M1G1S2S1G0S12A2A1S15G0S65G0R1R5A3S65G0R2R5A3F_;Fbn;S87R5R3R2A3S87R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S34S23VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S9fS23S96VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S12S65S12R1S7S12Z0S7S12Zf5S7S12Zf8S6S12A1A3A3A3A3Se9S23S96VAInv;VCST;VXGL;R2A6F_;Fxx;").
Variable FAMQ : list word -> assn.

Hypothesis XOK_T : ltac2:(tb__ "0|1|
S15S2S35Q40A1A1M0G0S6dS23Vok;S37S23VJAv;S4bA1Sa3R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XPOST_T : ltac2:(tb__ "0|1|
S15S2S35Q40A1A1M0G0S6dS23Vok;S37S23VJAv;S50A1Sb1R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CBD_T : ltac2:(tb__ "0|1|
S2S1S12S12A2M0A1S2S1G0S12A2A1S76S15S2S35Q40A1A1S75Z5R3A2S6dS23Vok;S37S23S2cVAInv;VCST;VXGL;VKc;S87R6R5A2R6R5R4S25Sd3ScfSbSd2U0A1A3AaSd1R3R2A5S5dS23Sd0R3R2Sd4VAInv;VCST;VXGL;VKc;S87S25SbdR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_bd.
  eapply (sum_PostsC_k segs AInv CST XGL Kc BDP.P0_bd PTrue BD.Pre_bd (ndh h0 false (BD.ndL 0)) (PDh PD_bd h0 false) BD.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc BDP.P0_bd PTrue BD.Pre_bd (BD.ndL 0) PD_bd BD.NP h0 false h0_ltBD eq_refl HamPD_bd P0_bd_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 _.
  exact (BDP.builder_dispose_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CFREE_T : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1S6dS23Vok;S37S23S9aVAInv;S7eS97R3VKc;A5SbeR2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cSbcS98VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [right; right; left; reflexivity | exact HKc | exact (proj1 Hok) | exact (proj2 Hok)]. Qed.
Lemma CMEMSET_T : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1S6dS23Vok;S37S23S9bVAInv;R3VKc;A3S82R2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cS80S95VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CF8_T : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1S6dS23Vok;S37S23S9cVAInv;R3VKc;A3S81R2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cS7fS95VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSC 248 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CSF_T : ltac2:(tb__ "0|2|
S68S15S2S35Q40A1A1S6dS23Vok;S37S23S9dVAInv;Z5M0R3VKc;A4Sb3R2R1A5S5dS23S72R2R1S7S1SfS5cA2M1S0SfS5cSb2S99VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC 5 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.

Let famS (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6fS3eSf1S23S86S44SefS48VAInv;VCST;VXGL;S7dVKc;Vrho0;VP0;VFB;VFF;VBX;S25S4aAcS86S43S44S46Vcuts;A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S2S1S1S1SfS24A2M0S3A2M1S1S12S14A2M2A2M3A1S2S35Q40A1A1M4SfS24S3G2S15G4S12G4S65G3S0G1G2S0G0S3S0SfS24R8R7A4R6A4R5A4RaA3S42S4aR7R5A3S3bS78Z0S41S0G1G2S0G0S3S0SfS24RaR9A4R8A4R7A4R6A2M5A2S79G5R4A2A2S6dS23Vok;S37S23VJAv;RaA1RbR7R6A5VfamS;RdRcR5R4A4A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD ok (map efdrop cuts) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S2S43A1S2S35Q40A1A1M0S6eS12G0S6dS23Vok;R3VFAMQ;R4A1A4S6dS23Vok;R4VfamS;R6R5R3R2A4A4F_;Ftp0';Fb;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma D3_T : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S53A3S42S4aR6R4A3S6dS23Vok;S37S23VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD3_ok 300%nat cps_ad NP cutsD3 exitsD3 ok (FAMQ tp0) Hok
           ecertD3_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsD3_ok (triple segs ok) (famS cutsD3 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CFREE_T (reenterS cutsD3 tp0) CMEMSET_T CF8_T CSF_T
           (fun rho tp tp0' => rightS cutsD3 tp0 _ _ tp0' (XPOST_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma D2_T : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S52A3S42S4aR6R4A3S6dS23Vok;S37S23VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD2_ok 300%nat cps_ad NP cutsD2 exitsD2 ok (FAMQ tp0) Hok
           ecertD2_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsD2_ok (triple segs ok) (famS cutsD2 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CFREE_T (reenterS cutsD2 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsD2 tp0 _ b tp0' (D3_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp tp0' => rightS cutsD2 tp0 _ _ tp0' (XOK_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma D1_T : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S51A3S42S4aR6R4A3S6dS23Vok;S37S23VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD1_ok 300%nat cps_ad NP cutsD1 exitsD1 ok (FAMQ tp0) Hok
           ecertD1_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsD1_ok (triple segs ok) (famS cutsD1 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CBD_T CFREE_T (reenterS cutsD1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsD1 tp0 _ b tp0' (D2_T T nd k rv rho tp tp0 Hi Hp)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiD_T : ltac2:(tb__ "0|1|
S15S2S35Q40A1A1M0G0S63R3A1S6dS23Vok;S37S23VJAv;S4fA1SbbR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (D1_T K_disp nd_d0 0%nat (390, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sa0S23S96VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S12S65S12R1S7S12Z0S7S12Zf5S7S12Zf8S6S12A1A3A3A3A3SeaS23S96VAInv;VCST;VXGL;R2A6F_;Fxx;").
Variable FAM : ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6eF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S12S12S2S35Q40A1A1S6fS78R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XOK_E : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0S6cS23S37S23VJAv;S4bA1Sa3R3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24Sa3S4bA4U1A4S0S12S14Z167S6bA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPOST_E : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0S6cS23S37S23VJAv;S50A1Sb1R3R2A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24Sb1S50A4U1A4S0S12S14Zd1S6bA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CBD_E : ltac2:(tb__ "0|1|
S2S1S12S12A2M0A1S2S1G0S12A2A1S76S15S2S35Q40A1A1S75Z5R3A2S6cS23S37S23S2cVAInv;VCST;VXGL;VKc;S87R6R5A2R6R5R4S25Sd3ScfSbSd2U0A1A3AaSd1R3R2A5S5dS23Sd0R3R2Sd4VAInv;VCST;VXGL;VKc;S87S25SbdR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_bd.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc BDP.P0_bd PTrue BD.Pre_bd (ndh h0 false (BD.ndL 0)) (PDh PD_bd h0 false) BD.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc BDP.P0_bd PTrue BD.Pre_bd (BD.ndL 0) PD_bd BD.NP h0 false h0_ltBD eq_refl HamPD_bd P0_bd_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 _.
  exact (BDP.builder_dispose_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' rho3 ACX tp3).
Qed.
Lemma CFREE_E : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1S6cS23S37S23S9aVAInv;S7eS97R3VKc;A5SbeR2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cSbcS98VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [right; right; left; reflexivity | exact HKc]. Qed.
Lemma CMEMSET_E : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1S6cS23S37S23S9bVAInv;R3VKc;A3S82R2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cS80S95VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc. Qed.
Lemma CF8_E : ltac2:(tb__ "0|1|
S68S15S2S35Q40A1A1S6cS23S37S23S9cVAInv;R3VKc;A3S81R2R1A5S5dS23S72R2R1S7S1SfS5cA2M0S0SfS5cS7fS95VAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSCX 248 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CSF_E : ltac2:(tb__ "0|2|
S68S15S2S35Q40A1A1S6cS23S37S23S9dVAInv;Z5M0R3VKc;A4Sb3R2R1A5S5dS23S72R2R1S7S1SfS5cA2M1S0SfS5cSb2S99VAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX 5 ltac:(cbn; tauto)). exact HKc. Qed.

Let famE (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S12S2S35Q40A1A1S6fS3eSf0S23S86S43SeeS47VAInv;VCST;VXGL;S7dVKc;Vrho0;VP0;VFB;VFF;VBX;S25S4aAcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S2S1S1S1SfS24A2M0S3A2M1S1S12S14A2M2A2M3A1S2S35Q40A1A1M4SfS24S3G2S15G4S12G4S65G3S0G1G2S0G0S3S0SfS24R8R7A4R6A4R5A4RaA3S42S4aR7R5A3S3bS78Z0S41S0G1G2S0G0S3S0SfS24RaR9A4R8A4R7A4R6A2M5A2S79G5R4A2A2S6cS23S37S23VJAv;RaA1RbR7R6A5VfamE;RdRcR5R4A4A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S2S43A1S2S35Q40A1A1M0S6eS12S12G0S78R3R2A2S6cS23R5VFAM;R4R6A2A3S6cS23R6VfamE;R8R7R4R3A4A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma D3_E : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S53A3S42S4aR6R4A3S6cS23S37S23VJAv;R8A1R9R5R4A5VFAM;S41S0G3G0S0G2S3S0SfS24R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD3_ok 300%nat cps_ad NP cutsD3 exitsD3 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertD3_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsD3_ok (etriple segs) (famE cutsD3 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CFREE_E (reenterE cutsD3 tp0) CMEMSET_E CF8_E CSF_E
           (fun rho tp tp0' => rightE cutsD3 tp0 _ _ _ tp0' (Z.le_refl _) (XPOST_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma D2_E : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S52A3S42S4aR6R4A3S6cS23S37S23VJAv;R8A1R9R5R4A5VFAM;S41S0G3G0S0G2S3S0SfS24R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD2_ok 300%nat cps_ad NP cutsD2 exitsD2 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertD2_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsD2_ok (etriple segs) (famE cutsD2 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CFREE_E (reenterE cutsD2 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsD2 tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (D3_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp tp0' => rightE cutsD2 tp0 _ _ _ tp0' (Z.le_refl _) (XOK_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma D1_E : ltac2:(tb__ "0|4|
SfS24S3S1S12S14A2M0S15S2S35Q40A1A1M1G1S65S1S1S1SfS24A2M2S3A2M3G0A2S0G3G0S0G2S3S0SfS24R7R6A4R5A4R4A4S51A3S42S4aR6R4A3S6cS23S37S23VJAv;R8A1R9R5R4A5VFAM;S41S0G3G0S0G2S3S0SfS24R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads H_ecertD1_ok 300%nat cps_ad NP cutsD1 exitsD1 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertD1_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsD1_ok (etriple segs) (famE cutsD1 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CBD_E CFREE_E (reenterE cutsD1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsD1 tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (D2_E T nd k rv rho tp tp0 Hi Hp)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem epiD_E : ltac2:(tb__ "0|2|
S15S2S35Q40A1A1M0G0S63R3A1S6cS23S37S23VJAv;S4fA1SbbR4R3A5VFAM;S41S0S1S1SfS24A2M1S3A2S1S12S14A2S0G1S3S0SfS24SbbS4fA4U0A4S0S12S14Z186S6bA4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (D1_E K_disp nd_d0 0%nat (390, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Existence.
End Sum.
End Lib_load_obj_epiD_pf.

(* [comment removed for export] *)
Module Lib_load_obj_hv4e.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "nat"; "cons"; "prod"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "nd_op1"; "nd_op0"; "T_op0"; "T_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "mH"; "PhisH"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p"; "nd_p0"; "nd_p1"; "T_p0"; "T_p1"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_hv4e"; "X_l1"; "X_l3"; "X_lok"; "cutsH4"; "exitsH4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w"; "E_o3"; "Lw0"; "Lw1"; "T_w0"; "T_w1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1 Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition X_l1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_op0) pc_latch 0.
Definition X_l3 : axst := Eval vm_compute in leafL (runL 600 cps_v T_p0) pc_latch 0.
Definition X_lok : axst := Eval vm_compute in leafL (runL 600 cps_v T_p1) pc_latch 0.
Definition cutsH4 : list efnode := ltac2:(tb__ "0|9|
S2S3S3S3S7S8A2M0S1A2M1S3SfS10A2M2A2M3S0G1G2S0G0S1S0S7S8ScS9A4U1M4A4SdZfM5Z32A2M6A4S2G3S0G1G2S0G0S1S0S7S8SbSaA4G4A4G6A4S2G3S0G1G2S0G0S1S0S7S8S24S9A4G4A4SdG5Z28A2M7A4S2G3S0G1G2S0G0S1S0S7S8S25S9A4G4A4G7A4S2G3S0G1G2S0G0S1S0S7S8S15S13A4G4A4SdG5Z1eA2M8A4S2G3S0G1G2S0G0S1S0S7S8S14S12A4G4A4G8A4S4G3A1A3A3A3A3A3A3").
Definition exitsH4 : list efnode := ltac2:(tb__ "0|8|
S2S3S3S3S7S8A2M0S1A2M1S3SfS10A2M2A2M3S0G1G2S0G0S1S0S7S8S22S9A4U1M4A4SdZfM5Z2dA2M6A4S2G3S0G1G2S0G0S1S0S7S8S23S9A4G4A4G6A4S2G3S0G1G2S0G0S1S0S7S8S21S9A4G4A4SdG5Z23A2A4S2G3S0G1G2S0G0S1S0S7S8S1cSaA4G4A4S0SfS10S18S19Z1S1aA2A4M7A4S2G3S0G1G2S0G0S1S0S7S8S1dS12A4G4A4G7A4S2G3S0G1G2S0G0S1S0S7S8S1eS13A4G4A4G7A4S4G3A1A3A3A3A3A3A3").
Lemma ecertH4_ok : ltac2:(tb__ "0|0|
S16S5S26S17S11SeU258S1bS11S1fS20A8S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_hv4e.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_st3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "app"; "Some"; "prod"; "fst"; "cons"; "list"; "nil"; "option"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiS_st3"; "E_8"; "R_8"; "E0_8"; "Tf0_8"; "Tf_8"; "Tk0_8"; "Tk_8"; "TfB_8"; "TkB_8"; "qHk_8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "nd0"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_next"; "SLit"; "SPUle"; "valuation"; "SPBranch"; "SPNot"; "sobj"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "kept_ad"; "PDk_ad"; "xfb_ad"; "B32m"; "ENDOWs"; "Xk_ad"; "bd_com"; "cAt"; "dupAt"; "go_fact"; "kAt"; "s_ad"; "xf_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "am_subst"; "NDA"; "amode"; "nd_below"; "ndesc"; "am_eqb"; "nd_am"; "nd_bd"; "nd_tv"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4"; "dup8"; "bd9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs"; "ldef_facts"; "nx500"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition E0_8 : axst := Eval vm_compute in callC B_8.
Definition E_8 : axst := Eval vm_compute in E_ad E0_8 (SVar 418).
Definition R_8 : list sobj := Eval vm_compute in R_ad E_8.
Definition Tk0_8 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_8 (s_ad E_8) R_8 AD.P_ok (Xk_ad E_8 (SVar 418)).
Definition Tf0_8 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_8 (s_ad E_8) R_8 AD.P_fail (Xk_ad E_8 (SVar 418)).
Definition TkB_8 : axst := Eval vm_compute in T_adB Tk0_8.
Definition TfB_8 : axst := Eval vm_compute in T_adB Tf0_8.
Definition Tk_8 : axst := Eval vm_compute in ax_tidy TkB_8.
Definition Tf_8 : axst := Eval vm_compute in ax_tidy TfB_8.
Definition qHk_8 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_8) AD.Pre_ad AD.P_ok E_8) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_8 : ltac2:(tb__ "0|21|
S1S0S3S4fS22S2eS27S18SfA1M0A1A1S4S22S8S22S3fS24P1a2A1M1A1SaS22A1A3M2S26G0A1M3A3A3S2A3S1S0S3S4eS22S25S2cS2bS63S24P1a3A1M4S28Z0M5A1M6A3A1A1G3A3S2A3S1S0S3S4eS22S25S29G4S24P1a4A1M7A2A1G3A3S2A3S1S0S3S4eS22S25S29G7S28S39A1A2A1G3A3S2A3S1S0SbS17A1M8S43S6bG2SfA2S42SfA1A2S5S17SdA2A3S1S0S3S60S3bSdG1A2M9S1aSdA1A2S2A3S1S0SbS9S2dA1MaA1S59SdS1bS41SdA1MbA3S5GaSeA2A3S1S0S3S58SdS1bGbSeS62S6S6S17S49A2McS2aS2aOF_;F_;MdA2MeS17GeS7S17S49S7GcGdR1A3A3Lp;S37A4A5S2A3S1S0S3S6eS50GbA2S2A3S1S0S3S6aGbS5aA2S2A3S1S0S3S6fS50S27S18SdA1MfA1M10A2S2A3S1S0S3S48G10S46S4S6S23S23A2M11S36S8G11S55SaG11A1A3M12A3S33S4S2fS3cS3dU7M13A1S40G13A1A2M14S3eG13A1M15A3M16S44S53S2A2M17A4A2S2A3S1S0S3S30G10S4S2fG14S51A3M18A2S2A3S1S0S3S5cGbG12S4dS1cA1A3S2A3S1S0S3S4aS45GbS4bS1cA1A2G17A2S2A3S1S0S3S61G16G16A2S2A3S1S0S3S61S4S2fG14S4S2fS31GbS4cS1cA1A2M19S51A3M1aA3S4S2fG19G18A3A2S2A3S1S0S3S32G14A1S2A3S1S0S3S6dS26GfA1M1bG6G5G15G1aA5S2A3S1S0S3S4fS6S5eGdA2M1cG1cS5fS1bS5aGbG10S7S5eGdR1A3A5Lp;S37A3S2A3S1S0S3S65G1bS36S33S34SeA5S2A3S1S0S3S67G1bS36S33S66G9A5S2A3S1S0S23S56GbPdA2G1A3S1S0S23S56GbP10A2S64Z80G7A2A3S1S0S3S68G1bA1S2A3S1S0S3S69SdA1S2A3S1S0S17S5dS1bSdGbSeS1eG9A6S12A3S1S0G8S43S12S38S12A1A2S5S17S15A2A3S1S0S17S54S15A1S13A3S1S0S9G11A1M1dS5bS57GbS1bS1eSdA4M1eS1fA2G12A3S1S0S47S45G1eS21A2S44S16S2A2M1fA3S1S0S17S5dS1bSdGbSeS1dG9A6S10A3S1S0G8S43S10S38S10A1A2S5S17S14A2A3S1S0S17S54S14A1S11A3S1S0G1dS5bS57GbS1bS1dSdA4M20S1fA2G12A3S1S0S47S45G20S20A2S44S53ScA2A3S1S0S3S19S13A1S2A3S1S0S3S19S11A1S2A3S1S0S3S48S27S18S13A1A1S46S35S33G18G1fA4A2S2A3S0S3S6cS26S18S11A1A1S4S2fS52S3aA3G18A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS_st3.

