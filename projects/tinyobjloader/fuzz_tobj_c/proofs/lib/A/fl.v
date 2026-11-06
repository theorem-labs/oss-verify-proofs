(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA2.

(* [comment removed for export] *)
Module Asan_memcpy_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "rw"; "ss_facts"; "eval"; "ss_next"; "SLit"; "sprop_below"; "SVar"; "agree_below"; "SAlu"; "SPBranch"; "SPNot"; "soff"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "ACEIL"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "sub"; "lt"; "modulo"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Asan_memcpy"; "FT"; "Posts_mc"; "Pre_mc0"; "E_src"; "E_dst"; "base_mc"; "E_real"; "Pre_mc1"; "Pre_mc2"; "E_Ld_bk"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Asan_memcpy_proof"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "opZ"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "cur"; "F_L"; "xor_facts"; "gs"; "lastd"; "lasts"; "ord1"; "ord2"; "vBd"; "vBs"; "vLd"; "vLs"; "hi_fact"; "lo_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "HSE"; "vN"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "vnodeA"; "withGA"; "vna_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "Posts_memcpyA"; "Pre_memcpyA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Asan_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr AMCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Lemma base_mc_Z : ltac2:(tb__ "0|4|
S1S13S0S2R1A1S37A3S19S4fR2PfP10P11A4S19S4fR2P13P34P35A4S19S19S22Z1S29Q40M0S3R2P12A2A2M1A2S22G1S24Z2M2Z28A2A2A2S19S19S22S23S12Z900A2S29G0S3R2PaA2A2M3A2S22G3S24G2Z3fA2A2A2S1aS50S27G3Z10A2Z0A3A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold base_mc in HF. apply Forall_app in HF as [HD HF]. apply Forall_app in HF as [HS HN].
  pose proof (urange (rw rho 18)) as RN. pose proof (urange (rw rho 10)) as R10.
  have_fact N1 HN (SPUle (SLit 1) vN). have_fact N2 HN (SPUle vN (SLit (2 ^ 40))).
  have_fact N3 HN (SPUle (SLit (ACEIL + 2304)) (SVar 10)). have_fact N4 HN (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact N5 HN (SPAlign 10 4).
  unfold vN in N1, N2. rewrite (U_lit64 rho 1) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia.
  rewrite (U_lit64 rho (ACEIL + 2304)) in N3 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in N4 by lia.
  cbn [eval] in N1, N2, N3, N4. destruct N5 as [_ N5]. change (2 ^ 4) with 16 in N5.
  split; [exact (opnd_Z rho 15 16 17 HD)|]. split; [exact (opnd_Z rho 19 52 53 HS)|]. repeat split; lia.
Qed.

Ltac split_mid HF HX HT :=
  cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Lemma FT_Z : ltac2:(tb__ "0|1|
S1S13S0S2R1A1S32A3S19S4fR2PfP10P11A4S19S4fR2P13P34P35A4S19S22Z1S29Q40S3R2P12A2A2M0A2S22G0S24Z2Z28A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold FT in HF. apply Forall_app in HF as [_ HB].
  destruct (base_mc_Z rho HB) as (ZD & ZS & ZN & _). auto.
Qed.

Lemma opZ_sub : ltac2:(tb__ "0|1|
S1S4cS51S51S51S6aR3S2aA2M0G0G0S1aS15S4dR7S2aA2S17A3S4fR9R7R6R5A4S4fS4bRaR9A2R8R7R6A4F_;F_;F_;F_;F_;Fio;Fil;Fib;Fs;Frho;").
Proof.
  intros rho s ib il io Hb Hl Ho Hid HZ.
  assert (E : forall v, (v < NF)%positive -> rw (rho_sub rho s) v = rw rho v).
  { intros v Hv. rewrite rw_sub, (wsub_get_id s NF v Hid Hv). reflexivity. }
  unfold opZ in *. cbv zeta in *.
  rewrite (E ib Hb), (E il Hl), (E io Ho), (E 18%positive eq_refl). exact HZ.
Qed.

Section Glue.
Variable rho : valuation.

Lemma glue_Ls_in : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS42A1A1A3S13S0S2S4bVrho;S3fA2A1S53S5bS5dS57A3A3F_;").
Proof.
  intros HF. unfold E_Ls_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_in).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 19)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 53)) as R53.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E19, ?E52, ?E53; unfold HSE in *; lia.
Qed.

Lemma glue_Ls_bk : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS41A1A1A3S13S0S2S4bVrho;S3eA2A1S53S5bS5dS57A3A3F_;").
Proof.
  intros HF. unfold E_Ls_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_bk).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ls_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E19, ?E52, ?E53, ?E141; unfold HSE in *; try lia.
Qed.

Lemma glue_Ld_in : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS40A1A1A3S13S0S2S4bVrho;S3dA2A1S53S5aS5cS56A3A3F_;").
Proof.
  intros HF. unfold E_Ld_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_Ld_bk : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS3bA1A1A3S13S0S2S4bVrho;S3cA2A1S53S5aS5cS56A3A3F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_Ls_in : ltac2:(tb__ "0|0|
S1aS28Q40A1S5S4bVrho;S3fA2S52A2S5Vrho;S55A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ls_bk : ltac2:(tb__ "0|0|
S1aS28Q40A1S5S4bVrho;S3eA2S52A2S5Vrho;S63S52S7Z1A1A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_in : ltac2:(tb__ "0|1|
S1aS28Q40A1S5S4bVrho;S3dA2S63S52S7S24Z2Z3eA2A1M0A2A2S5Vrho;S63S55G0A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_bk : ltac2:(tb__ "0|2|
S13S0S2Vrho;A1S4S1eS3bA1A1A3S22S29Q40M0S5Vrho;S63S52S7S23S24Z2Z3eA2M1Z1A2A1A2A2A2S29G0S5S4bVrho;S3cA2S63S52S7G1A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT. apply Forall_app in HX as [HL _].
  have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia.
  change (eval rho cur) with (rw rho 140) in A3. pose proof (urange (rw rho 140)) as R140.
  assert (E1 : bv_unsigned (rw (rho_sub rho s_Ld_bk) 140) = bv_unsigned (rw rho 140) + 1).
  { rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur. apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  unfold add, cur.
  rewrite (U_addc rho (SVar 140) (2 ^ 62 + 1) (bv_unsigned (rw rho 140)) eq_refl) by lia.
  rewrite (U_addc (rho_sub rho s_Ld_bk) (SVar 140) (2 ^ 62) (bv_unsigned (rw rho 140) + 1) E1) by lia.
  lia.
Qed.
End Glue.

Lemma FT_of_E : ltac2:(tb__ "0|0|
S35S20S1S13S0S2R1A1S4S1eS35A1A1A3S13S0S2R2A1S32A3F_;Fr;TE;").
Proof. intros E r HF. cbn [ax_S ss_facts E_src mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst : ltac2:(tb__ "0|0|
S1S13S0S2R1A1S4S1eS36A1A1A3S13S0S2R2A1S32A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_dst mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1S13S0S2R1A1S4S1eS38A1A1A3S13S0S2R2A1S32A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma next_E : ltac2:(tb__ "0|0|
S19S69S2aS6S1eS35A1A1A2S19S69S2aS6S1eS36A1A1A2S69S2aS6S1eS38A1A1A2A2A2").
Proof. repeat split; cbv; congruence. Qed.
Lemma FT_of_E_cls : ltac2:(tb__ "0|0|
S14S0A1S1S13S0S2R1A1S4S1eS6dR2S35A2A1A1A3S13S0S2R2A1S32A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_src mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst_cls : ltac2:(tb__ "0|0|
S14S0A1S1S13S0S2R1A1S4S1eS6dR2S36A2A1A1A3S13S0S2R2A1S32A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_dst mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Definition clsZ (rho : valuation) (ib il : positive) : Prop := ltac2:(tb__ "0|2|
S1bS22S64S29Q40M0S3Vrho;Vib;A2A2M1A2S22S23G1S29G0S3Vrho;Vil;A2A2A2S25S11Z8A2A2A2").
Lemma hi_fact_holds : ltac2:(tb__ "0|0|
S1S51S22S64S29Q40S3R2R1A2A2A2S13S0S2R3A1S16S0S5eS9R2A1A1S18S0A1A3A3F_;Fib;Frho;").
Proof. intros rho ib H. constructor; [|constructor]. unfold hi_fact. cbn [holds]. rewrite (U_lit64 rho HSE) by (unfold HSE; lia). exact H. Qed.
Lemma lo_fact_holds : ltac2:(tb__ "0|1|
S1S51S51S22S23S29Q40M0S3R3R2A2A2S29G0S3R3R1A2A2A2S25S11Z8A2A2S13S0S2R4A1S16S0S5fS9R3A1S9R2A1A2S18S0A1A3A3F_;Fil;Fib;Frho;").
Proof.
  intros rho ib il H. pose proof (urange (rw rho ib)). pose proof (urange (rw rho il)). constructor; [|constructor]. unfold lo_fact, add. cbn [holds].
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl) by (unfold SHB in H; lia).
  rewrite (U_lit64 rho (SHB - 8)) by (unfold SHB; lia). exact H.
Qed.

Lemma FTbT1 : ltac2:(tb__ "0|0|
S1fS66S1fR1S6cA3S1aS15S67S0S8S6S1eS68S49S6bS21R2A1S35S45A5A1A1A1S32A3S17A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 FT_below_T). Qed.
Lemma FTbT2 : ltac2:(tb__ "0|0|
S1fS66S1fR1S6cA3S1aS15S67S0S8S6S1eS68S47S6bS21R2A1S36S43A5A1A1A1S32A3S17A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 (proj2 FT_below_T)). Qed.
Lemma FTbT3 : ltac2:(tb__ "0|0|
S1fS66S1fR1S73A3S1aS15S67S0S8S6S1eS68S48S74S21R2A1S38S44A5A1A1A1S32A3S17A3F_;FL;").
Proof. intros L [<-|[<-|[]]]; [exact (proj1 (proj2 (proj2 FT_below_T))) | exact (proj2 (proj2 (proj2 FT_below_T)))]. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2eS10Vok;VJ;A3").
Hypothesis Hst : stableA segs NF J.

Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_mc_sound : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S20S66S20R1S46A3S1S61S10Vok;S2bS10S6fS1SaS2aR6R1A3Lr;VJ;A2R3R1R4A5S2cS10VJ;S2aR5R4S33A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mc) tp HokG HstG check_mc); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply exit_postA. in_nth 0.
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             cuts_mc _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memcpy_sumA ok' Jq rho1 tp1 Ho Hs).
    + intros L [<-|[<-|[]]]; [in_nth 4 | in_nth 5].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_in CLs_0 (F_L vBs vLs lasts) s_Ls_in tp);
      [in_nth 6 | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_bk CLs_0 (F_L vBs vLs lasts) s_Ls_bk tp);
      [in_nth 6 | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_bk r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_in CLd_0 (F_L vBd vLd lastd) s_Ld_in tp);
      [in_nth 7 | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_bk CLd_0 (F_L vBd vLd lastd) s_Ld_bk tp);
      [in_nth 7 | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_bk r HF)].
Qed.

Theorem asan_memcpy_core_sum1 : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S61S10Vok;S2bS10VJ;S39R2R1A5S2cS10VJ;S2aR2R1S33A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc1). left; reflexivity.
Qed.

Theorem asan_memcpy_core_sum2 : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S61S10Vok;S2bS10VJ;S3aR2R1A5S2cS10VJ;S2aR2R1S33A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc2). right; left; reflexivity.
Qed.
End Sum.

Lemma etriple_SPA_pure' : ltac2:(tb__ "0|2|
S2dS20S1S14S28Q40A1A1M0S62OF_;S14S31A1M1S30R7R5R4R2R1A4S60S10S2bS10S1G0G1S30S19RcR4R3R2R1A4S19S1aG1R2R7A3S1aS30R1R6A3A2A2Lm;Lt;Lp;Lr;R7R6R5A5R4A3F_;Fmd;Ftr;S60S10S2bS10R6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H w [Hsm Hk]. destruct w as [tr [ms md]]. apply (H tr md Hk). split; [exact Hsm|]. cbn. auto.
Qed.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_mc_complete : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S6eS66S6eR1S4aA3S1S60S10S2bS10S6fS1SaS2aR6R1A3Lr;VJ;A2S70R3A1R1R4A5S2cS10VJ;S2aR5R4S33A6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mc) tp HstG); [ | exact echeck_mc | | exact HinT].
  { intros m Hm. unfold vcuts_mc in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_mc Posts_mc (mkVNA P_amc 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_hi 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_lo 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             vcuts_mc _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memcpy_sumA_ex Jq rho1 tp1 Hs).
    + intros L [<-|[<-|[]]].
      * exists (mkVNA T3a 39 (SLit (2 ^ 63 + 8))). split; [in_nth 4|]. split; [reflexivity|]. meas_lit.
      * exists (mkVNA T3b 39 (SLit (2 ^ 63 + 8))). split; [in_nth 5|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_in 151 gs) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_in tp);
      [in_nth 6 | reflexivity | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_bk 151 (add cur (SLit 1))) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_bk tp);
      [in_nth 6 | reflexivity | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_in 101 (add gs (SLit (2 ^ 62)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_in tp);
      [in_nth 7 | reflexivity | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ld_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_bk 101 (add cur (SLit (2 ^ 62 + 1)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_bk tp);
      [in_nth 7 | reflexivity | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_bk r HF) | right; split; [cbn [vna_var]; exact (meas_Ld_bk r HF) | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem asan_memcpy_core_sum1_ex : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S60S10S2bS10VJ;S39R2R1A5S2cS10VJ;S2aR2R1S33A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc1 with (vna_state (mkVNA Pre_mc1 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). left; reflexivity.
Qed.

Theorem asan_memcpy_core_sum2_ex : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S60S10S2bS10VJ;S3aR2R1A5S2cS10VJ;S2aR2R1S33A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc2 with (vna_state (mkVNA Pre_mc2 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). right; left; reflexivity.
Qed.
End SumEx.

Lemma soff_var' : ltac2:(tb__ "0|1|
S1S51S26S29Q40M0S3R2R1A2A2S24Z2Z3fA2A2S1aS50SeR3S9R2A1A2S29G0S3R3R2A2A2A3F_;Fi;Frho;").
Proof.
  intros rho i Hi. unfold soff. cbn [eval]. rewrite bv_signed_U.
  destruct (Zsigned_spec (bv_unsigned (rw rho i))) as [[_ X]|[Y X]]; [exact X|]. pose proof (urange (rw rho i)). lia.
Qed.

Section Public.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre_disjoint : ltac2:(tb__ "0|1|
S14S28Q40A1A1M0S62S1bS2bS10S1G0S14S31A1S30S1cL_;L_;L_;L_;S34Vrho;R2R1A6S1dS2dS2dS2bS10R1S34Vrho;R3R2A6LJ;A2A2S26Vn;S24Z2Z3fA2A2S1bS22S23Va;Vn;A2Vb;A2S1bS22S23Vb;Vn;A2Va;A2S1aS50Vn;Z0A3A2A2F_;F_;Fw;Ftp;").
Proof.
  intros tp w HS Hn.
  assert (Hsm : smatchA segs rho tp Pre_mc0 w) by (destruct HS as [[H _]|[J [H _]]]; exact H).
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre_mc0 mkA objs_mc app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst, O_src in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma pre_Z : ltac2:(tb__ "0|5|
S13S0S2Vrho;A1S37A3S19S1aS50Va;S23S29Q40M0S3Vrho;PfM1A2A2S29G0S3Vrho;P11M2A2A2A2A3S19S1aS50Vb;S23S29G0S3Vrho;P13M3A2A2S29G0S3Vrho;P35M4A2A2A2A3S19S4fVrho;G1P10G2A4S19S4fVrho;G3P34G4A4S19S22Z1Vn;A2S22Vn;S24Z2Z28A2A2A2A2A2A2A2F_;").
Proof.
  intros HF. destruct (base_mc_Z rho HF) as (ZD & ZS & ZN & _).
  split; [exact (V_opd 15 16 17 rho ZD ZN)|]. split; [exact (V_opd 19 52 53 rho ZS ZN)|]. auto.
Qed.

Lemma xor_fact_Z : ltac2:(tb__ "0|0|
SfS50S1aS50S29Q40S5Vrho;R2A2A2R1A3S22S23R2Vn;A2S25S24Z2Z40A2Z1A2A2S2Vrho;SdScS72SbS71R4S7ZffffffffffffffffA1A3S65A3A1A2F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx. cbn [holds branch_taken]. unfold bv_ltu.
  rewrite (U_xor_m1 rho e 18446744073709551615 eq_refl). rewrite He. change (eval rho vN) with (rw rho 18).
  unfold M64v. rewrite Z.ltb_lt. subst n. lia.
Qed.

Lemma facts1 : ltac2:(tb__ "0|1|
S13S0S2Vrho;A1M0S37A3S22S23Va;Vn;A2Vb;A2S13S0G0S16S0S58S54A3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord1, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho dst vN a n eq_refl eq_refl) by (subst a n; lia). fold b. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma facts2 : ltac2:(tb__ "0|1|
S13S0S2Vrho;A1M0S37A3S22S23Vb;Vn;A2Va;A2S13S0G0S16S0S59S54A3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord2, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho src vN b n eq_refl eq_refl) by (subst b n; lia). fold a. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma F1_below : ltac2:(tb__ "0|0|
S1aS15S67S0S8S6S1eS34A1A1A1S16S0S58S54A3A3S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below : ltac2:(tb__ "0|0|
S1aS15S67S0S8S6S1eS34A1A1A1S16S0S59S54A3A3S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_cases : ltac2:(tb__ "0|0|
S2dS14S28Q40A1A1S62S2bS10R3S34Vrho;R2R1A6S1bS2bS10R4S39Vrho;R3R2A6S2bS10R4S3aVrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_mc0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_mc0 mkA] in HF.
  destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre_disjoint tp w (or_intror (ex_intro _ J Hw)) ltac:(lia)) as [H|[H|H]]; [left | right | exfalso; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts1 HF H) | exact F1_below].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts2 HF H) | exact F2_below].
Qed.
End Public.

Theorem asan_memcpy_core_sum : ltac2:(tb__ "0|2|
S62OF_;S2dS1S14S28Q40A1A1M0S2eS10R4R3A3S2fS10S2aR4A3S1G0S14S31A1M1S30R9R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S30RaR4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S61S10R8S2bS10R7S34R6R5A5S2cS10R7S2aR6R5S33A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD HS.
  eapply triple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj; [apply asan_memcpy_core_sum1 | apply asan_memcpy_core_sum2]; assumption.
Qed.

Theorem asan_memcpy_core_sum_ex : ltac2:(tb__ "0|2|
S2dS1S14S28Q40A1A1M0S2fS10S2aR3A3S1G0S14S31A1M1S30R8R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S30R9R4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S60S10S2bS10R6S34R5R4A5S2cS10R6S2aR5R4S33A6A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD HS.
  eapply etriple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj; [apply asan_memcpy_core_sum1_ex | apply asan_memcpy_core_sum2_ex]; assumption.
Qed.
End Asan_memcpy_proof.

(* [comment removed for export] *)
Module Start6States.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "false"; "app"; "bool"; "true"; "list"; "prod"; "Some"; "option"; "length"; "nat"; "pair"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SAlu"; "sobj"; "sprop"; "SVar"; "cell"; "ss_objs"; "SExt"; "mkObj"; "DZero"; "SPUle"; "ss_pc"; "ss_regs"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "swf"; "SPAlign"; "SPEq"; "ss_next"; "c_val"; "mkCell"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16b"; "R16pre"; "SITE16"; "c1"; "F16c"; "O_lowpg"; "O_ss"; "R16m"; "R16r"; "a0_16"; "ES17"; "LOWPG"; "PB"; "PE"; "R16c"; "SSB"; "byte_cells17"; "classes16"; "is_zero_cell16"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "aluop"; "mulop"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "mul"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkAX"; "sym_runA"; "FE"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates"; "S_s15ok"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@Stdlib.Lists.List"; "In"; "filter"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition SITE16 : Z := 0x786ac.
Definition RA16 : Z := 0x680d0.
Definition run15b__R : option (list leafA) := ltac2:(tb__ "0|0|
S52S59U7d0S0S2dS34S1S2dA1A3S5aS5A5").
Local Strategy expand [run15b__R].
Definition R16pre : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 S_s15ok (ro1__)))) run15b__R).
Lemma run15b : ltac2:(tb__ "0|1|
S30S9S6S50A1M0A1S52S59U7d0S0S2dS34S1S2dA1A3S5aS5A5S8G0S0S50S58S33S5eA2S1S50A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run15b__R <: run15b__R = Some [mkLeafA R16pre RsCut]). Qed.
Definition a0_16 : sv := ltac2:(tb__ "0|0|
S10S47S10S45S13P1A1SeZf5fA1A3SeZfffffffffffff000A1A3").
Lemma R16pre_at : ltac2:(tb__ "0|2|
S31S30S2dS1aS4fS33A1M0A1S34A3S31S30S2eS25G0A1P4fA3S31S30SfS5bSfUaS1bG0A1SeZ0A1A4S3bA3S31S30S6S7SfSfA2M1A1S54S33A1S1G1A1A3S31S30SfS55S33A1SeS4eA1A3S30SbSaS11S15G0A1A2U18A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition c1 (t : Z) : Z := 8388608 + 4096 * t.
Definition PB (t : Z) : Z := if t =? 0 then 0x7fff8000 else 0x7fff9000.
Definition PE : Z := 0x800f8000.
Definition LEN16 (t : Z) : Z := if t =? 0 then 1048576 else 1044480.
Definition F16c (t : Z) : list sprop := ltac2:(tb__ "0|9|
S3S12S0S12S23P4fM0ZfA2S0S12S23P50M1ZcA2S1S12A1M2A3A3S3S12S53G1S13G0A1M3A2S0S12S19SeS4aZ7fff7f800000S4bZ1000Vt;A2A2A1G3A2S0S12S19G3SeS4aS4dZ2Z2fA2S35Vt;A1M4A2A1A2S0S12S19S10S45S13P1A1M5SeS4aNa0G4A2A1A3G3A2S0S12S19G3S10S45G5SeS4aZf5fG4A2A1A3A2S0S12S24S10S47S10S45S13G1A1M6SeS3eVt;A1A1A3SeZfffA1M7A3SeZ0A1M8A2S0S12S24S10S47S10S45G6SeS3fA1A3G7A3G8A2G2A3A3A3A3A3A3A3A3").

Definition SSB (t : Z) : sv := ltac2:(tb__ "0|0|
S10S45S13P50A1SeS4cZ7fff8000S4bZ200Vt;A2A2A1A3").
Definition O_ss (t : Z) : sobj := ltac2:(tb__ "0|0|
S17S41Vt;A1SeZ0A1SeZ100000A1S1S14A1S18A5").

Definition LOWPG : Z := 0x800bc000.
Definition O_lowpg : sobj := mkObj (SLit LOWPG) (SLit 0) (SLit 0x4c00) [] DZero.

Definition ES17 : list sv := ltac2:(tb__ "0|2|
S0SfS16S2Q8M0S13P22A1M1A3S0SfS16S2G0S10S46G1SeZ8A1A3A3S0SfS16S2G0S10S46G1SeZ10A1A3A3S0SfS16S2G0S10S46G1SeZ18A1A3A3S0SfS16S2G0S10S46G1SeZ20A1A3A3S0SfS10S46G1SeZ28A1A3S0SfS10S46G1SeZ30A1A3S0SfS10S46G1SeZ38A1A3S1SfA1A3A3A3A3A3A3A3A3").
Fixpoint byte_cells17 (off : Z) (es : list sv) : list cell :=
  match es with [] => [] | e :: r => byte_cells17 (off + 1) r ++ [mkCell (SLit off) 1 e] end.
Definition o21m : sobj := ltac2:(tb__ "0|1|
S17S13P24A1SeZ0A1M0SeZ1000A1S0S14S27G0Z8S13P22A1A3S1S14A1A3S18A5").

Definition R16b : sstate := Eval vm_compute in
  (let St := ax_S R16pre in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 81%positive (ss_lenient St)).

Definition R16r (t : Z) : sstate := ltac2:(tb__ "0|0|
S1cS1aS32A1S5fSfS1bS32A1UaS10S45S13P4fA1SeS35Vt;A1A1A3A4S1fS32A1S1eS32A1S21S32A1S15S32A1S3S12S36Vt;A1S1dS32A1A3P51S20S32A1A9").

Definition R16m (t : Z) : sstate := replace_obj_at (R16r t) 21 o21m.

Definition R16c (t : Z) : axst := ltac2:(tb__ "0|1|
S51S1cS1aS32A1S1bS3aVt;A1M0A1S1fS32A1S1eS32A1S21S32A1S3S11S15S39Vt;A1A1S0S11S37S0S11S38Vt;A1S1S11A1A3A3A3S1dG0A1P51S20S32A1A9S1S7SfSfA2A1SeS4eA1A3").

Definition classes16 : list Z := ltac2:(tb__ "0|0|
S0S2dZ0S0S2dZ1S0S2dZ2S0S2dZ3S0S2dZ4S0S2dZ5S0S2dZ6S0S2dZ7S1S2dA1A3A3A3A3A3A3A3A3").

Definition is_zero_cell16 (c : cell) : bool := ltac2:(tb__ "0|4|
SfS4Lx;S26Vc;A1S2dS2dS4Lz;R1S5S2eS2Lp;M0G0X2dx3Lz;S2eS2Li;S48SfSfS2Lb;La;M1Lop;M2G2S49G1Lop;M3G3S4S2fSfS2La;Lw;Lsgn;S2eSfS2dS2Lk;Li;Ll;Xfx8").
Definition dzc16 (o : sobj) : sobj := ltac2:(tb__ "0|0|
S17S28Vo;A1S2cVo;A1S2bVo;A1S61S14S14SdS44R1A1A1Lc;S29Vo;A1A3S2aVo;A1A5").

Lemma R16b_eq : ltac2:(tb__ "0|1|
S30S57S56S33S1cS1aS4fS33A1M0A1S1bG0A1S1fG0A1S1eG0A1S21G0A1S15G0A1S1dG0A1P51S20G0A1A9A2S51S32S1S7SfSfA2A1SeS4eA1A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma sd16 : ltac2:(tb__ "0|a|
S2dS60S2dR1S43A3S31S30S9S7S6S7SfSfA2M0A1M1S6S12A1M2A2M3A1S5dS32S3aR2A1M4A2S8G3ScG1G2S0G0ScSfSfS3bS10S45S13P4fA1SeS35R2A1A1A3A4S1G0A1A3S36R2A1A4A2A3S31S30S4S22G4A1S5A3S31S30S4S22S39R2A1M5A1S5A3S31S30S4S22S4fS40R2A1A1M6A1S5A3S31S30S9S11A1S62S11S15G4A1U15A3S8S11S17S13P24A1SeZ0M7A1SeZ1000A1S3S14S42G7S3cA2S1S14A1A3S18A5A2A3S31S30S4S5cG4G5A2S5A3S31S30S6S11A1S15G6A1S3S11S3S11S15G5A1M8S0S11S37S1S11A1M9A3A3S0S11S38R2A1G9A3A3A3S31S30S2eS25G5A1P51A3S30SbSaS11G8A2U18A3A2A2A2A2A2A2A2A2F_;Ft;").
Proof.
  intros t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2).
Qed.
End Start6States.

(* [comment removed for export] *)
Module StartNodes2E.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "rw"; "SVar"; "eval"; "rm"; "ss_next"; "ss_pc"; "valuation"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "prod"; "Some"; "list"; "option"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "alloc_top"; "m_vmmaps"; "map_has"; "map_remove"; "region_free"; "vm_init_sp"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2"; "munmap_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA MmapFixedA MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section MunmapE.

Variables (E : axst) (v : positive) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S6S12VE;A1S7S2bA1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S1eS1fA1S32S17SeS11VE;A1A1A2S1cS1fS20A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6S8S11VE;A1Z11A2S7Zd7A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6S8S11VE;A1ZaA2SaVv;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6S8S11VE;A1ZbA2S7VlenZ;A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S34SdS11VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S18S2cVGl;S11VE;A1A2S19A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Local Notation munmap_ok := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2.munmap_ok E nxt) (only parsing).
Local Notation n_valM := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2.n_valM lenZ Hpos Hsmall) (only parsing).
Local Notation mmap_n_lit := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2.mmap_n_lit lenZ Hnl Hpos Hsmall) (only parsing).

Theorem munmap_enode : ltac2:(tb__ "0|8|
SfS1dS5Q40M0A1M1A1S9R2Vv;A2G1S0S10S16S4G0R1A2Z1000A2Z0A3S3S14S13S4G0R2A2M2VlenZ;A2Z10000A2S14Z646000G2A2A2S14S13S4G0R3A2VlenZ;A2S24S25Vm;A1M3A1A2S0S10S4G0S9R6P1A2A2S4G0S29G3A1A2A3S0S18S26S2aG3A1M4R5Vn;A3S19A3G1S23S1bG1G1A2S1aG1G1R7R1A4G4A3S0G1R2Vn;A3F_;Fs;S0S18S28S27G4R7A2R7Vn;A3S19A3S6S10S23S1bS6S10A2S1aS6S10R2R1A4VGl;A3S10S1S14S4G0RcA2M5R1A2S15R1S13G5VlenZ;A2A2A2S2S1S14S4G0SbRfR5A2A2M6R2A2S15R2S13G6R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S2eS17S22S17S21Vm;VB;A2VE;RbRaA5S22S17S21S2fVm;R9Vn;A3VB;A2S2dVE;Vnxt;A2S31RbS30ScRbA1R9Vn;A3A2S33S4G0R9A2M7S13G7VlenZ;A2RaA3A5A3F_;F_;F_;F_;F_;F_;F_;F_;Ta;Ftp;Frho;").
Proof using All.
  intros rho tp a Hal Hlo Hceil Hv1 Hhas Huniq Hfree HG. pose proof (alloc_top_lt (m_vmmaps m)) as CL. pose proof n_valM as Nv.
  destruct mmap_n_lit as [MN MNZ]. change (bv_unsigned n = lenZ) in Nv. change (mmap_n (Z_to_bv 64 lenZ) = n) in MN.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & _).
  rewrite R10 in G0. rewrite R11 in G1. cbn [eval] in G0, G1. change (rw rho v) with a in G0.
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros E0. apply (f_equal bv_unsigned) in E0. rewrite u64_of_lit in E0 by lia. rewrite u64_of_lit in E0 by lia. lia. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE).
  { rewrite G0, G1, MNZ. unfold TASK_SIZE. pose proof (alloc_top_bounds _ Htop) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. lia. }
  assert (Hhas' : map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, G1, MN, Evm. exact Hhas. }
  assert (Hal' : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  exists ([], mkCfg (after_sys_mem ms (Z_to_bv 64 0) (unmap_range (ms_mem ms) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))
                    (munmap_model md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))).
  split; [exact (wstep_munmap_exact_introA segsA ms md _ Hh H215 Hal' Hlen Hwrap Hhas' [] Hp)|].
  rewrite G0, G1, MN.
  set (h' := munmap_vm (m_vmmaps md) a n).
  assert (Emd : munmap_model md a n = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' md)) by reflexivity.
  rewrite Emd. split.
  + unfold munmap_ok. rewrite <- Nv.
    replace (mkAX (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt) [] (SLit SHB)) with (ax_setS E (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt))
      by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
    apply (smatchA_after_munmap segsA rho _ tp E [] ms md [] h' a n (Z_to_bv 64 0) (SLit 0) nxt Hsp).
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * rewrite Evm. exact Huniq.
    * rewrite Evm. exact Hfree.
    * exact Hal.
    * rewrite Nv. exact Hnl.
    * rewrite Nv. unfold two_pow_64 in CL. lia.
    * intros o Ho. rewrite Nv.
      apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear ltac:(lia) ltac:(right; revert Hceil; unfold alloc_top; rewrite stack_max_size_val, <- Hv1; intros Hceil; exact Hceil)); [|exact HG|exact Ho].
      intros x Hx. lia.
    * rewrite HX. intros rr y [].
    * apply agree_below_refl.
    * exact Hnxt.
    * reflexivity.
    * reflexivity.
  + cbn [w_tr w_cfg fst snd cfg_model]. split; [reflexivity|]. split.
    * unfold munmap_model, with_mmap_destroyed. unfold h'. rewrite Evm. apply erase_mat_cong_forget. exact Hem.
    *
      pose proof HMI as (HW & HT & Hmat & Hsub & HpaidMI & Hlc & Hivs & Hlm & Htm).
      pose proof (used_munmap_le md h' a n Hivs ltac:(rewrite Evm; exact Hfree) eq_refl eq_refl) as U1.
      set (md1 := with_vmmaps h' md) in *.
      set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
      assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
      assert (HT' : List.NoDup (tp_forget lo (lo + lenZ) tp)) by (unfold tp_forget; apply List.NoDup_filter; exact HT).
      assert (U2 : (length (unpaid (vm_forget_range lo hi md1) (tp_forget lo (lo + lenZ) tp)) <= length (unpaid md tp))%nat).
      { apply List.NoDup_incl_length; [unfold unpaid; apply List.NoDup_filter; exact HT'|].
        intros p Hpp. assert (Hp' : In p (unpaid (vm_forget_range lo hi md1) tp)).
        { unfold unpaid in Hpp |- *. apply filter_In in Hpp as [Hpp Hb]. apply filter_In. split; [|exact Hb].
          unfold tp_forget in Hpp. apply filter_In in Hpp as [Hpp _]. exact Hpp. }
        pose proof (unpaid_forget_incl md1 lo hi tp p Wl1 Hp') as Hq. unfold md1 in Hq. rewrite (unpaid_ext md (with_vmmaps h' md) tp) in Hq by reflexivity. exact Hq. }
      unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
Qed.
End MunmapE.
End StartNodes2E.

(* [comment removed for export] *)
Module Start5.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "sprop"; "eval"; "rm"; "agree_below"; "holds"; "ss_facts"; "SVar"; "rl"; "sobj"; "DZero"; "SLit"; "SPUle"; "ob_dflt"; "odefault"; "sprop_below"; "sprop_eqb"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "sub"; "mul"; "div"; "of_nat"; "to_nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "vm_limit"; "vm_init_sp"; "alloc_top"; "event"; "region_free"; "Model"; "vm_noaccess"; "lazy_interior"; "m_vm_lazy"; "map_has"; "map_remove"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.Seg5"; "TP12"; "m12"; "vals12"; "B12x"; "rm_same_band"; "G12b"; "Post5"; "m13"; "stackshadow_zero"; "G12"; "m15"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "cons"; "list"; "app"; "bool"; "nil"; "true"; "option"; "Some"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "munmap_model"; "init_sp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.Seg5.S13a.S13"; "m14"; "G13b"; "@Stdlib.Lists.List"; "In"; "existsb"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.Seg5.S13a"; "m13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "TP11"; "B12"; "m8"; "n9"; "Z11"; "ZD11"; "bandav"; "G11c"; "n7"; "m10"; "m11"; "m9"; "priZ"; "spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "agree_vars"; "RMH"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.Seg5.S12b"; "q12"; "n12"; "rm_same_band"; "TP12"; "e12"; "G12b"; "shZ"; "stackshadow_zero"; "B12x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates"; "E_s13g"; "IP12f"; "E_s13"; "R12"; "s12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States"; "L12r"; "L12x"; "C12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "E_k12d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates"; "E_s14"; "E_s15"; "E_s15u"; "S_s15ok"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.Seg5.S13a.S13.S14"; "m15"; "G14b"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget";
"@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pages_rev"; "unknown_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2"; "munmap_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "zero_page_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA SummaryA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement PlacementA Code SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.StartNodes2E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Seg5.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S1S4aS47S6Q40A1M0G0A2A1S2bS29Vm;A1A1S94S1dA1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S1S4aS47S6Q40M0A1M1G1A2M2A1S2aS29Vm;A1A1S49G2S48G1G1Va2;S5G0Z38e000A2A4S49G2S48G1G1Va1;S5G0Z10000A2A4S49G2S48G1G1S5G0Z2008fff7000A2S5G0Zdfff0001000A2A4S49G2S48G1G1S5G0Z8fff7000A2S5G0Z20000000000A2A4S49G2S48G1G1S5G0Z7fff7000A2S5G0Z10000000A2A4S4dG2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S1S4aS47S6Q40M0A1M1G1A2M2A1S32S29Vm;A1A1S49G2S48G1G1S5G0Z8fff7000A2S5G0Z20000000000A2A4S4dG2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S1S4aS47S6Q40M0A1M1G1A2M2A1S34Vm;A1S4bG2S33S5G0Z2008fff7000A2S5G0Zdfff0001000A2A2S4bG2S33S5G0Z8fff7000A2S5G0Z20000000000A2A2S33S5G0Z7fff7000A2S5G0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S0S1fZ646000S7Q40Va1;A2M0A2S0S3S1fS1eG0Z10000A2M1S64A2S1fS63G0A2A2S1fG1S2eS29Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S0S1fZ646000S7Q40Va2;A2M0A2S0S3S1fS1eG0Z38e000A2M1S64A2S1fS63G0A2A2S1fG1S2eS29Vm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S1fS1eVB;Z1000000A2S2cS29Vm;A1A1A2").
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S45S8S4aS6Q40A1A1S4aS2fA1M0S31R5R4R3R2R1A4S1G0R3S4dS2fA1A3F_;Fmd;Ftr;Ftp;Frho;S46S1dVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S45S8S4aS6Q40A1A1S4aS2fA1M0S31R5R4R3R2R1A4S1G0R3S4dS2fA1A3F_;Fmd;Ftr;Ftp;Frho;Sa3S1dVok;R2A3F_;FJ;").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S53S5Q40Z0A2Vm;S6fVP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S53S5Q40Z0A2S69Vm;VP;A2S6aVb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S72Vm;VP;Vb4;A3S5G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S70Vm;VP;Vb4;Vb5;A4S5G0Z10000A2Vb6;A4").

Let mE : Model := ltac2:(tb__ "0|0|
S71Vm;VP;Vb4;Vb5;Vb6;A5").
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation a12_off_P := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.a12_off_P m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation RIw := (RI P) (only parsing).

Lemma OKFx : ltac2:(tb__ "0|0|
S31S27S46S1dVok;S37R2R1A2A3FBB;Fmm;").
Proof using OKF. clear -OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.

Definition vals12 (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S0S1S6Q40M0A1M1S9Vrho;P1bA2Va1;A3S0S1G1S9Vrho;P1cA2Va2;A3S0S1G1S9Vrho;P1dA2VP;A3S0S1G1S9Vrho;P1eA2S74VP;A1M2A3S0S1S27S23Z8S7G0S9Vrho;P1fA2A2A2S7G0G2A2A3S0S1G1S9Vrho;P20A2Vb4;A3S0S1G1S9Vrho;P21A2Vb5;A3S0S1G1S9Vrho;P22A2Vb6;A3S1S27S7G0S9Vrho;P1A2A2S7G0S2dS29Vm;A1A1A2A3A2A2A2A2A2A2A2A2").

Lemma vals12_agree : ltac2:(tb__ "0|0|
S28S8S8Sa4P23R3A2S3aR3A1S28Sa5R1R6A2S1S6Q40A1S9R5R2A2S9R6R2A2A3F_;Fi;S3aR4A1F_;F_;F_;Frho';Frho;Fn;").
Proof.
  clear. intros n rho rho' Hn (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9) A.
  unfold vals12. rewrite !A by lia. repeat split; assumption.
Qed.

Lemma mE_ledger : ltac2:(tb__ "0|7|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29VmE;A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb6;S5G0Z10000A2A4S49G2S48G1G1Vb5;S5G0Z1000A2A4S49G2S48G1G1Vb4;S6aA4M6S49G2S48G1G1VP;S6fA4S2aG5A1A3A3A3A3A3S0S1S27S2cG4A1S2cG5A1A3S0S1G1S2dG4A1S2dG5A1A3S1G3S32G4A1S49G2G6S32S29S69Vm;VP;A2A1A1A3A3A2A2A2A2").
Proof.
  clear. pose proof (m10_ledger m P b4 b5) as (L1 & L2 & L3 & L4 & L5).
  unfold mE, m11, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp vm_noaccess].
  rewrite L1, L2, L3, L4, L5. repeat split; reflexivity.
Qed.
Lemma top_mE : ltac2:(tb__ "0|0|
S1S27S2eS29VmE;A1A1S2eS29Vm;A1A1A3").
Proof. clear. pose proof mE_ledger as (_ & _ & _ & L4 & _). unfold alloc_top. rewrite L4. reflexivity. Qed.
Lemma init_sp_ok_mE : init_sp_ok (m_vmmaps mE).
Proof using Htop. clear -Htop. pose proof mE_ledger as (_ & _ & _ & L4 & _). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_mE : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29VmE;A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof mE_ledger as (L1 & L2 & _). pose proof (m10_ledger m P b4 b5) as (K1 & K2 & _).
  rewrite L1, L2, <- K1, <- K2. apply (band_covered_after_grant (m10 m P b4 b5)). exact (band_m10 m a1 a2 Hmaps P b4 b5). Qed.

Lemma HG11c : ltac2:(tb__ "0|6|
S8S27S3aR2A1S4aS47S6Q40M0A1M1G1A2M2A1M3S2G3G3S1G3R2S4bG2R1S2aS29VmE;A1A1A3A3Ll;A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S6eA3S3S2G1G1S2G1G1S0S5fG2S48G1G1R2R1A4R7A3S0S1fS7G0R2A2M4S7G0ScRaR5A2A2M5A2S1fS1eG5R4A2S1eG4S7G0R1A2A2A2A2A2Ls;A2Lb;A2S1fS1eS7G0ScR8R3A2A2R2A2R7A2A2F_;Fsz;Fe;F_;Fmaps;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6. intros rho LB (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & _) maps [l ->] e sz Hin.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV. pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB. pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof mE_ledger as (_ & L2 & _). rewrite L2, Hmaps. left.
  unfold G11c in Hin.
  destruct Hin as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]; cbn [eval].
  - rewrite H27. exists a1, (Z_to_bv 64 0x10000). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - rewrite H28. exists a2, (Z_to_bv 64 0x38e000). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - exists P, n7. split; [apply in_app_iff; right; cbn [In]; tauto|].
    assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RIw).
    { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
    change (eval rho ri30) with (eval rho ri30). fold ri30. rewrite Eri. unfold n7. rewrite u64_of_lit by lia. lia.
  - exists (Z_to_bv 64 0x2008fff7000), (Z_to_bv 64 0xdfff0001000). split; [apply in_app_iff; right; cbn [In]; tauto|].
    change (eval rho shRI_base) with (pRI rho).
    assert (Up : bv_unsigned (pRI rho) = bv_unsigned (rw rho 31%positive) + 0x47fff8000).
    { unfold pRI, shRI_base. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
    rewrite !u64_of_lit by lia. lia.
  - rewrite H33. exists b5, (Z_to_bv 64 4096). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
  - rewrite H34. exists b6, (Z_to_bv 64 65536). split; [apply in_app_iff; right; cbn [In]; tauto|]. rewrite u64_of_lit by lia. lia.
Qed.

Definition m12 (b7 : word) : Model := eager_model 4096 mE b7.
Definition G12 : list (sv * Z) := G11c.
Lemma clear12 : ltac2:(tb__ "0|0|
S1S4cS77S41S5aS8dA1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg12a : ltac2:(tb__ "0|4|
S8S3aR1A1S58S1dVok;S43S1dS37VmE;S68VB;A1M0A2S8dR2S67R2A1A5S56S2S6Q40M1A1M2G2S0S53S5G1Z0A2VmE;S5G1Z1000M3A2R1A4S44S1dS37S39R1A1S1eG0G3A2A2P25S8cR4P24R1A3S67R4A1S49S59S5bS89S81A2S4dS59A1A3R2A7A2Lb7;A2Lw;A4F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). pose proof mE_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_k12d 4096 mE (B12 B) G12 37%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear12.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_mE.
    + exact band_mE.
    + rewrite M3. unfold B12, B11. lia.
    + apply (HG11c rho _ HV). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA mE (B12 B)) (OKFx _ _) (fun n => stableA_KxA segsA n mE (B12 B)) _ SPIN12 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run12_fail | exact spin12].
  - apply triple_ex; intros b7. apply triple_pure; intros HPL7.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b7; split; [exact HPL7|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_k12d) = 36%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_k12d 4096 37) with S_s12ok. rewrite N.
    eapply sym_run_soundA; [exact run12a | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Section S12b.
Variable b7 : word.
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2VmE;S5G0Z1000A2Vb7;A4").

Definition shZ (rho : valuation) : Z := ltac2:(tb__ "0|0|
S1eS24S7Q40S9Vrho;P1A2A2Z8A2Z7fff8000A2").
Definition q12 (rho : valuation) : Z := ltac2:(tb__ "0|0|
S22S7eVrho;A1Z20000A2S27S22R1S21R1Z1000A2A2Ts;").
Definition e12 (rho : valuation) : Z := ltac2:(tb__ "0|0|
S22S7eVrho;A1Z9A2S27S22R1S21R1Z1000A2A2Ts;").
Definition n12 (rho : valuation) : nat := ltac2:(tb__ "0|0|
S26S1eS24S22S7cVrho;A1S78Vrho;A1A2Z1000A2Z1A2A1").
Definition TP12 (rho : valuation) : list word := ltac2:(tb__ "0|0|
S4bS6Q40A1S9cS78Vrho;A1S79Vrho;A1A2S67Vrho;A1A3").

Definition stackshadow_zero (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S27S0S1fS78Vrho;A1M0R1A2S20R1S1eG0S23Z1000S25S79Vrho;A1A1A2A2A2A2S1S4fS6Q8M1A1M2A1SdVrho;S5Q40R2A2A2S50G2S5G1Z0A2A2A3F_;Fz;").
Definition B12x : Z := ltac2:(tb__ "0|1|
S1eS1eS68VB;A1Z1000M0A2S23G0Z21A2A2").

Lemma q12_ext : ltac2:(tb__ "0|1|
S8S8S1S6Q40A1S9R1P1M0A2S9R2G0A2A3S0S1S27S78R2A1S78R3A1A3S0S1S27S7cR2A1S7cR3A1A3S1S52S79R2A1S79R3A1A3A2A2F_;Frho';Frho;").
Proof. clear. intros rho rho' H. unfold n12, q12, e12, shZ. rewrite H. repeat split; reflexivity. Qed.
Lemma TP12_agree : ltac2:(tb__ "0|0|
S8S8S75P24R2R1A3S1S4aS6Q40A1A1S7bR2A1S7bR3A1A3F_;Frho';Frho;").
Proof.
  clear. intros rho rho' HA. pose proof HA as [A _]. destruct (q12_ext rho rho' (A 1%positive ltac:(lia))) as (E1 & E2 & E3).
  unfold TP12. rewrite E1, E3, (TP11_agree rho rho' HA). reflexivity.
Qed.
Lemma stackshadow_zero_ext : ltac2:(tb__ "0|3|
S8S8S1S6Q40A1M0S9R1P1M1A2S9R2G1A2A3G0S1S4fS6Q8A1A1SdR3R1A2SdR4R1A2A3Fa;S7fR4A1M2G2F_;F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' H Hrm Hz. destruct (q12_ext rho rho' H) as (E1 & E2 & E3). unfold stackshadow_zero. rewrite E1, E3.
  intros z Hzz. rewrite Hrm. apply Hz. exact Hzz.
Qed.

Definition rm_same_band (rho rho' : valuation) : Prop := ltac2:(tb__ "0|2|
S6Q40M0A1S0S1fS64S7G0R1A2M1A2S20G1S63A2A2S1S4fS6Q8A1A1SdVrho';R2A2SdVrho;R2A2A3F_;Fa;").
Lemma rm_same_band_refl : ltac2:(tb__ "0|0|
S8S7aR1R1A2Frho;").
Proof. clear. intros rho a _. reflexivity. Qed.
Lemma rm_same_band_trans : ltac2:(tb__ "0|1|
S8S8S8S7aR3R2A2M0G0S7aR5R3A2F_;F_;Fr3;Fr2;Fr1;").
Proof. clear. intros r1 r2 r3 A1 A2 a Ha. rewrite (A2 a Ha). apply A1. exact Ha. Qed.
Lemma rm_same_band_agree : ltac2:(tb__ "0|0|
S28S8S8SeR3R2R1A3S7aR3R2A2F_;Fr2;Fr1;Fn;").
Proof. clear. intros n r1 r2 (_ & _ & R) a _. symmetry. apply R. Qed.

Lemma lazy_m12 : ltac2:(tb__ "0|2|
S1S4aS47S6Q40A1M0G0A2M1A1S34S39Vb7;A1A1S4bG1S33Vb4;S6aA2S34S69Vm;VP;A2A1A3A3").
Proof. clear. unfold m12, eager_model. rewrite m_vm_lazy_with_vmmaps. apply lazy_m11. Qed.
Lemma noacc_m12 : ltac2:(tb__ "0|2|
S1S4aS47S6Q40A1M0G0A2M1A1S32S29S39Vb7;A1A1A1S49G1S48G0G0Vb4;S6aA4S32S29S69Vm;VP;A2A1A1A3A3").
Proof. clear. unfold m12, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_noaccess]. apply mE_ledger. Qed.
Lemma m12_ledger : ltac2:(tb__ "0|6|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29S39Vb7;A1A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb7;S5G0Z1000A2A4S2aS29VmE;A1A1A3A3S0S1S27S2cG4A1S2cG5A1A3S1G1S2dG4A1S2dG5A1A3A2A2A2").
Proof.
  clear. pose proof mE_ledger as (L1 & L2 & L3 & L4 & L5).
  unfold m12, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. rewrite L1, L3, L4. repeat split; reflexivity.
Qed.
Lemma limit_m12 : ltac2:(tb__ "0|0|
S1S27S2cS29S39Vb7;A1A1A1S2cS29Vm;A1A1A3").
Proof. clear. apply m12_ledger. Qed.
Lemma init_sp_ok_m12 : init_sp_ok (m_vmmaps (m12 b7)).
Proof using Htop. clear -Htop. pose proof m12_ledger as (_ & _ & _ & L4). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m12 : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29S39Vb7;A1A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof m12_ledger as (L1 & L2 & _). pose proof mE_ledger as (K1 & _).
  rewrite L1, L2, <- K1. apply (band_covered_after_grant mE). exact band_mE. Qed.

Lemma b7_facts : ltac2:(tb__ "0|5|
S0S1fZ1000M0S7Q40M1Vb7;A2M2A2S0S6dG2G0A2S0S1fS1eG2G0A2S2eS29Vm;A1A1A2S0S1S27S21G2G0A2Z0A3S1S4cS30S4bS47S6G1A1M3G3A2S2bS29VmE;A1M4A1S2aG4A1A3Vb7;S5G1G0A2A3S4eA3A2A2A2A2").
Proof using HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof mE_ledger as (L1 & L2 & L3 & L4 & L5).
  pose proof (place_LB_A mE 4096 b7 init_sp_ok_mE ltac:(rewrite L1; exact Hres) band_mE ltac:(lia) ltac:(reflexivity) HPL7) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL7 as (Hal & _ & _ & Hfree). rewrite top_mE in Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. split; [exact PLB|]. split; [exact (bandav_intro _ _ Pband)|]. repeat split; assumption.
Qed.

Definition G12b : list (sv * Z) := ltac2:(tb__ "0|1|
S4bS47SaS27A2M0S6eS49G0S48SaS27S11P24A1Z1000A4S4dG0A1A3A3").
Lemma clear_L12u : ltac2:(tb__ "0|0|
S1S4cS77S7dS9dS5aS89A1U0A2A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L12r_len : ltac2:(tb__ "0|4|
S0S99U0M0S51S13S1cS5aS89A1M1A1M2A2A2S0S1S18S17S83S13G0G2Sa1S5Q40Z0A2A1A4A1S14A3S0S1S28S1bG1A1P25A3S1S4aS47SaSaA2M3A1S5cS89A1S4dG3A1A3A2A2A2").
Proof. vm_compute. repeat split; reflexivity || lia. Qed.

Lemma G12b_clear_band : ltac2:(tb__ "0|3|
S8S27S27S3aR3A1S1S6Q40M0A1S9R4P24A2Vb7;A3S1fS64R4A2S1fS1eR5R4A2S63A2S1fZ0R5A2S3S1fS1eR7R6A2S73R8A1M1A2S1fS1eG1Z200A2R7A2A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S7dA3S27S0S1fRcR1A2S20R1S1eRcRbA2A2A2S4S0S1fS7G0ScReR5A2A2M2R2A2S20R2S1eG2R4A2A2A2A1F_;Fx;F_;Fsz;Fe;F_;F_;F_;F_;F_;F_;Fn;Fq;Frho;").
Proof using HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. intros rho q n (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1) H36 Hq0 Hq1 Hn Hqp e sz Hin x Hx.
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof RI_val as RV.
  unfold SHADOW_BAND_HI in PLB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Hq0, Hq1. pose proof (urange P) as UP. unfold alloc_ceiling_hi in Phi.
  pose proof (bandav_intro _ _ (proj1 (proj2 Ha1))) as HA1. pose proof (bandav_intro _ _ (proj1 (proj2 Ha2))) as HA2.
  pose proof b5_facts as (_ & _ & F5b & _). pose proof (bandav_intro _ _ F5b) as F5band. clear F5b.
  pose proof b6_facts as (_ & F6band & _). pose proof b7_facts as (_ & F7band & _).
  clear Ha1 Ha2.
  unfold G12b, G11c in Hin. apply in_app_iff in Hin.
  destruct Hin as [[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]]]|[[= <- <-]|[]]]; cbn [eval].
  - rewrite H27. clear -HA1 Hx Hq0 Hq1. unfold bandav in HA1. lia.
  - rewrite H28. clear -HA2 Hx Hq0 Hq1. unfold bandav in HA2. lia.
  - change (eval rho ri30) with (eval rho ri30).
    assert (Eri : bv_unsigned (eval rho ri30) = bv_unsigned RIw).
    { unfold ri30. cbn [eval]. rewrite H30. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
      change (bv_wrap 64 137438953472) with (2 ^ 37). rewrite RV. apply bv_wrap_small. change (bv_modulus 64) with (2^64).
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)). lia. }
    rewrite Eri. clear -R1 PLB Hx Hq1. lia.
  - change (eval rho shRI_base) with (pRI rho).
    replace (bv_unsigned (pRI rho)) with (priZ rho); [clear -Hqp Hx; lia|].
    unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2^64).
    pose proof (urange (rw rho 31%positive)). pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
    lia.
  - rewrite H33. clear -F5band Hx Hq0 Hq1. unfold bandav in F5band. lia.
  - rewrite H34. clear -F6band Hx Hq0 Hq1. unfold bandav in F6band. lia.
  - rewrite H36. clear -F7band Hx Hq0 Hq1. unfold bandav in F7band. lia.
Qed.

Lemma prep12 : ltac2:(tb__ "0|9|
S8S56S3aR2A1S1S6Q40M0A1M1S9R3P24A2Vb7;A3S43S1dS37S39Vb7;A1M2S1eS68VB;A1Z1000M3A2A2S89R4S67R4A1R3A6S2S8S8S0S28S1G1S9R2R1A2S9R7R1A2A3Fi;S0S28S1S4aS6Q8A1M4A1S12R2R1A2S12R7R1A2A3Fl;S0S7fR1A1S0G1S2G1G1S0S5fG1R1S67R8A1A3S0S1fS7G0R1A2M5S7G0R2A2M6A2S20G6S1eG5G3A2A2A2A2Lp;A2S1S4fG4A1SdR3R2A2SdR8R2A2A3M7F_;Fa;S0G1S1fS63G5A2G7F_;Fa;S0G1S5fG1R1S67R7A1A3M8S1fS1eG6G3A2S78R8A1A2F_;Fp;S0S1fS1eS78R6A1G3A2S63A2S0G1G8S1fS64G6A2F_;Fp;S43S1dS37G2S80A2S8aR1S7bR6A1R5A6A2A2A2A2A2A2A2A2Lrho';A2F_;F_;F_;Fw;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho [tr [ms md]] HV H36 Hsp. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof RI_range as (R1 & R2 & R3).
  pose proof RI_val as RV. pose proof SB_val as SB. pose proof (urange P) as UP. unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB.
  pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB. set (rP := bv_unsigned P mod 65536) in *.
  pose proof b4_facts as (F4lo & F4band' & F4top & F4al & _). pose proof (bandav_intro _ _ F4band') as F4band. clear F4band'.
  pose proof b6_facts as (F6lo & F6band & F6top & F6al & _). pose proof b7_facts as (F7lo & F7band & F7top & F7al & _).
  pose proof Hsp as [Hsm (Htr & Hem & Hpaid)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hem, Hpaid.
  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  destruct L12r_facts1 as (X1 & X2 & X3). destruct L12r_len as (LEN & DZ & NX & XN).
  pose proof (fact_of_state _ _ rho X1 HF) as A1. pose proof (fact_of_state _ _ rho X2 HF) as A2. pose proof (fact_of_state _ _ rho X3 HF) as A3.
  cbn [holds eval] in A1, A2, A3. rewrite Z_to_bv_unsigned in A2, A3.
  change (bv_wrap 64 0x7fff80000000) with 0x7fff80000000 in A2. change (bv_wrap 64 0x7fffffffff20) with 0x7fffffffff20 in A3.
  destruct A1 as [_ A1]. change (2 ^ 4) with 16 in A1.
  pose proof (erase_mat_eq_fields md (m12 b7) Hem) as (Evm & Elz & _).

  assert (Htopv : alloc_top (m_vmmaps m) = bv_unsigned (rw rho 1%positive) - 0x800000).
  { unfold alloc_top. rewrite stack_max_size_val, <- Hv1. reflexivity. }

  set (v1 := bv_unsigned (rw rho 1%positive)) in *.
  apply Z.mod_divide in A1 as [k1 Hk1]; [|lia].
  assert (Hsh : shZ rho = 2 * k1 + 0x7fff8000) by (unfold shZ; fold v1; rewrite Hk1; replace (k1 * 16) with (2 * k1 * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
  pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
  assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
  assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
  assert (Hqal : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  assert (Hrange : q12 rho + 4096 * Z.of_nat (n12 rho) = e12 rho + 4096) by (rewrite Hn; lia).
  assert (Hqlo : 0x2008fff7000 <= q12 rho) by lia.
  assert (Hehi : e12 rho + 4096 <= 0x10007fff8000) by lia.
  assert (Hn33 : Z.of_nat (n12 rho) <= 33) by lia.
  clearbody rP. clear Qm Em.

  set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) => KxA (m12 b7) B12x r (TP12 rho) tr0 md0).
  assert (Hsp1 : SPA segsA J' (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) rho (TP11 rho) (tr, mkCfg ms md)).
  { apply SPA_obj_to_unknown; [exact LEN | exact XN | exact DZ | exact same_L12u |].
    split; [exact Hsm|]. subst J'. cbv beta. unfold KxA. cbn [w_tr w_cfg cfg_model fst snd].
    split; [exact Htr|]. split; [exact Hem|]. unfold TP12, B12x.
    pose proof (paid_app_le md (pages_rev (q12 rho) (n12 rho)) (TP11 rho)) as PL. rewrite length_pages_rev in PL. unfold page_size in PL. lia. }

  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp1) as HF1. cbn [ax_S ax_setS] in HF1.
  assert (V35 : 8 * bv_unsigned (rw rho 35%positive) = bv_unsigned b6 /\ bv_unsigned (rw rho 35%positive) <= 2 ^ 61 - 1).
  { destruct (L12r_facts35) as [Y1 Y2].
    pose proof (fact_of_state _ _ rho Y1 HF) as E1. pose proof (fact_of_state _ _ rho Y2 HF) as E2.
    cbn [holds eval] in E2. rewrite Z_to_bv_unsigned in E2. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in E2.
    cbn [holds] in E1. apply (f_equal bv_unsigned) in E1.
    change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 35%positive) (SLit 3)))) with (SymSoundV.U rho (StepA.g8 35%positive)) in E1.
    rewrite (StepA.U_g8 rho 35%positive) in E1 by (unfold SymSoundV.U; cbn [eval]; exact E2). unfold SymSoundV.U in E1. cbn [eval] in E1. rewrite H34 in E1. split; [exact E1 | exact E2]. }
  assert (Upr : bv_unsigned (pRI rho) = priZ rho).
  { unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). pose proof (urange (rw rho 31%positive)). lia. }
  assert (LOW : forall p, In p (TP11 rho) -> bv_unsigned p + 4096 <= q12 rho).
  { intros p Hp. unfold TP11 in Hp. pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Q1m.
    assert (HS : sbZ rho = bv_unsigned (rw rho 35%positive) + 0x7fff8000) by reflexivity.
    assert (HP : priZ rho = bv_unsigned (rw rho 31%positive) + 0x47fff8000) by reflexivity.
    destruct (q1Z rho =? priZ rho);
      repeat (destruct Hp as [<-|Hp]; [first [rewrite u64_of_lit by (unfold q1Z; lia) | rewrite Upr]; unfold q1Z; lia|]); destruct Hp. }
  assert (LOWB : forall p, In p (TP11 rho) -> SHADOW_BAND_LO <= bv_unsigned p).
  { intros p Hp. unfold TP11 in Hp. pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Q1m. unfold SHADOW_BAND_LO.
    assert (HS : sbZ rho = bv_unsigned (rw rho 35%positive) + 0x7fff8000) by reflexivity.
    assert (HP : priZ rho = bv_unsigned (rw rho 31%positive) + 0x47fff8000) by reflexivity. pose proof (urange (rw rho 35%positive)). pose proof (urange (rw rho 31%positive)).
    destruct (q1Z rho =? priZ rho);
      repeat (destruct Hp as [<-|Hp]; [first [rewrite u64_of_lit by (unfold q1Z; lia) | rewrite Upr]; unfold q1Z; lia|]); destruct Hp. }
  destruct (SPA_prepay_pages_rm J' (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) (q12 rho) (n12 rho) rho (TP11 rho) tr ms md Hsp1)
    as (rho1 & Hsp2 & Hrw1 & Hrl1 & Hz1 & Ho1).
  - intros r r' t t' X; exact X.
  - rewrite Htq. apply Z_mod_mult.
  - lia.
  - lia.
  - intros k Hk. rewrite Elz, lazy_m12, page_in_ranges_app. apply orb_true_intro. right.
    apply (high_shadow_lazy_m8 m a1 a2 Hres Hmaps Hlz Htop P HPL); unfold pageZ; rewrite u64_of_lit by lia; unfold SHADOW_BAND_HI; lia.
  - intros k Hk Hin. pose proof (LOW _ Hin) as X. unfold pageZ in X. rewrite u64_of_lit in X by lia. lia.
  - intros z Hz. rewrite Evm, noacc_m12. unfold covered. cbn [existsb]. apply Bool.orb_false_iff. split.
    + unfold in_iv, ivB, ivS, in_rng, n9. cbn [fst snd]. rewrite u64_of_lit by lia. apply andb_false_iff.
      clear -F4band Hz Hqlo Hehi Hrange. unfold bandav in F4band. destruct F4band as [F|F]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
    + apply (shadow_acc_m8 m a1 a2 Hres Hmaps Hna Hlz Htop P HPL). unfold SHADOW_BAND_HI, SHADOW_BAND_LO, SHADOW_RW_LO_END. lia.
  - destruct Hsp1 as [_ HK]. subst J'. cbv beta in HK. destruct HK as (_ & _ & HP). cbn [w_tr w_cfg cfg_model fst snd] in HP.
    unfold headroom. rewrite Evm, limit_m12. unfold TP12, B12x in HP.
    pose proof (paid_app_ge md (pages_rev (q12 rho) (n12 rho)) (TP11 rho)) as PG. unfold B12, B11, page_size in *. lia.
  - apply Forall_forall. intros o Ho.
    pose proof (objs_clear_e_sound rho G12b (unknown_obj_at (ax_S L12r) 0) (Z_to_bv 64 (q12 rho)) (4096 * Z.of_nat (n12 rho)) HF1 clear_L12u ltac:(lia)
                  ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros x Hx; rewrite u64_of_lit in Hx by lia; lia)) as X.
    rewrite u64_of_lit in X by lia. apply X; [|exact Ho].
    apply (G12b_clear_band rho (q12 rho) (4096 * Z.of_nat (n12 rho)) HV H36); unfold SHADOW_BAND_LO, SHADOW_BAND_HI; try lia.
    right. pose proof (LOW (pRI rho) ltac:(unfold TP11; destruct (q1Z rho =? priZ rho); cbn [In]; tauto)) as LP. rewrite Upr in LP. lia.
  -
    exists rho1. split; [exact Hrw1|]. split; [exact Hrl1|]. split.
    { destruct (q12_ext rho rho1 (Hrw1 1%positive)) as (E1 & E2 & E3). unfold stackshadow_zero. rewrite E1, E3. exact Hz1. }
    split.
    { intros a (p & Hp & Ha). apply Ho1. pose proof (LOW p Hp). lia. }
    split.
    { intros a Ha. apply Ho1. unfold SHADOW_BAND_HI in Ha. rewrite Hrange. lia. }
    split; [exact LOW|]. split; [unfold SHADOW_BAND_HI; lia|]. split; [exact LOWB|].
    rewrite <- L12x_eq.
    change (mkAX (unknown_obj_at (ax_S L12r) 0) [rX12] (SLit SHB)) with (ax_setX (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) (rX12 :: ax_X (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)))).
    pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp2) as HF2. cbn [ax_S ax_setS] in HF2.
    assert (Hsp3 : SPA segsA J' (ax_setX (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)) (rX12 :: ax_X (ax_setS L12r (unknown_obj_at (ax_S L12r) 0)))) rho1 (TP12 rho) (tr, mkCfg ms md)).
    2:{ destruct Hsp3 as [S3 K3]. split; [exact S3 | exact K3]. }
    apply SPA_x_publish; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hsp2].
    cbn [ax_S ax_setS ax_base].
    assert (EB : bv_unsigned (eval rho1 (fst rX12)) = v1 - 1048576).
    { cbn [fst rX12 eval]. unfold alu64, alu. rewrite bv_add_unsigned, (Hrw1 1%positive), Z_to_bv_unsigned. fold v1.
      change (bv_wrap 64 (-1048576)) with 18446744073708503040.
      unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
      replace (v1 + 18446744073708503040) with ((v1 - 1048576) + 1 * 18446744073709551616) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (EL : bv_unsigned (eval rho1 (snd rX12)) = 1048576 - 64) by (cbn [snd rX12 eval]; rewrite u64_of_lit by lia; reflexivity).
    assert (ESH : bv_unsigned (eval rho1 (ax_base L12r)) = 0x7fff8000).
    { replace (ax_base L12r) with (SLit SHB) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). cbn [eval]. rewrite u64_of_lit by (unfold SHB; lia). reflexivity. }
    rewrite ESH.
    apply (xr_ok_of_zero rho1 _ _ rX12 (q12 rho) (q12 rho + 4096 * Z.of_nat (n12 rho))); rewrite ?EB, ?EL.
    + rewrite Hk1. replace (k1 * 16 - 1048576) with ((2 * k1 - 131072) * 8) by lia. apply Z_mod_mult.
    + lia.
    + lia.
    + lia.
    + rewrite Htq. replace (tq * 4096) with (tq * 512 * 8) by lia. apply Z_mod_mult.
    + rewrite Hrange, Hte. replace (te * 4096 + 4096) with ((te + 1) * 512 * 8) by lia. apply Z_mod_mult.
    + intros a Ha. rewrite Hrange.
      pose proof (Z.div_le_mono (v1 - 1048576) a 8 ltac:(lia) ltac:(lia)) as Dlo.
      pose proof (Z.div_le_mono a (v1 - 65) 8 ltac:(lia) ltac:(lia)) as Dhi.
      assert (D1 : (v1 - 1048576) / 8 = 2 * k1 - 131072) by (rewrite Hk1; replace (k1 * 16 - 1048576) with ((2 * k1 - 131072) * 8) by lia; apply Z_div_mult; lia).
      assert (D2 : (v1 - 65) / 8 < 2 * k1 - 8) by (rewrite Hk1; apply Z.div_lt_upper_bound; lia).
      lia.
    + exact Hz1.
    + intros z Hz. apply Forall_forall. intros o Ho.
      assert (R : forall o', obj_range rho1 o' = obj_range rho o').
      { intros o'. unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }
      cbv zeta. rewrite R.
      pose proof (objs_clear_e_sound rho G12b (unknown_obj_at (ax_S L12r) 0) (Z_to_bv 64 (q12 rho)) (4096 * Z.of_nat (n12 rho)) HF1 clear_L12u ltac:(lia)
                    ltac:(rewrite u64_of_lit by lia; lia) ltac:(intros x Hx; rewrite u64_of_lit in Hx by lia; lia)) as X.
      rewrite u64_of_lit in X by lia. rewrite u64_of_lit by lia.
      enough (D : ranges_disjoint (obj_range rho o) (q12 rho, q12 rho + 4096 * Z.of_nat (n12 rho))).
      { unfold ranges_disjoint in D. destruct (obj_range rho o) as [lo' hi']. cbn [fst snd] in D |- *. lia. }
      apply X; [|exact Ho].
      apply (G12b_clear_band rho (q12 rho) (4096 * Z.of_nat (n12 rho)) HV H36); unfold SHADOW_BAND_LO, SHADOW_BAND_HI; try lia.
      right. pose proof (LOW (pRI rho) ltac:(unfold TP11; destruct (q1Z rho =? priZ rho); cbn [In]; tauto)) as LP. rewrite Upr in LP. lia.
Qed.
End S12b.

Section S12c.
Variable b7 : word.
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2VmE;S5G0Z1000A2Vb7;A4").

Lemma holds_all_agree : ltac2:(tb__ "0|1|
S28S8S8S4aSbA1S1S4cS62SbS19R4A1R1A3S4eA3SeR5R4R3A3S82SbSfR5A1M0R3A3S82SbG0R4A3F_;F_;F_;Ffs;Frho';Frho;Fn;").
Proof.
  clear. intros n rho rho' fs Hb Hag HF. apply Forall_forall. intros f Hf.
  apply (proj1 (holds_agree n rho rho' f Hag (proj1 (forallb_forall _ _) Hb f Hf))). exact (proj1 (Forall_forall _ _) HF f Hf).
Qed.

Lemma shape12 : ltac2:(tb__ "0|1|
S8S56S82SbSfR2A1S10S5aS8aA1A1A3S43S1dS37S39Vb7;A1S3bA2M0S8aR3S38R3A1R2A6S43S1dG0S8bR4S38R4A1R3A6F_;F_;Fw;Frho;").
Proof.
  clear. intros rho w HFx Hw.
  replace C12 with (ax_setS (ax_setS L12x C12d) (replace_obj_at C12d 13 o12rtc2b)) by (unfold C12; rewrite <- C12e_eq; reflexivity).
  apply (SPA_add_img_cell (KxA (m12 b7) B12x) rho (ax_setS L12x C12d) 13 o12rtc2a 0xf20e0 0xf20f8 0xf20e8 8 0 (TP12 rho) w o12rtc2a_nth
           eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj2 rtc2_clear) (proj2 rtc2_img)).
  - cbn [ax_S ax_setS]. exact same_C12e.
  - rewrite <- C12d_eq.
    apply (SPA_add_img_cell (KxA (m12 b7) B12x) rho (ax_setS L12x C12c) 13 o12rtc2 0xf20e0 0xf20f8 0xf20f0 8 0 (TP12 rho) w o12rtc2_nth
             eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj1 rtc2_clear) (proj1 rtc2_img)).
    + cbn [ax_S ax_setS]. exact same_C12d.
    + apply (SPA_split_chain segsA (KxA (m12 b7) B12x) rho splits12 L12x C12c (TP12 rho) w split12_ok Hw).
Qed.

Lemma unshape12 : ltac2:(tb__ "0|1|
S8S8S56S82SbSfR3A1S10S5aS8aA1A1A3SeP25R4R3A3S43S1dS37S39Vb7;A1S3bA2M0Sa2S88S9bS9aS8bS87A5R4S38R5A1R3A6S43S1dG0S85R5S38R6A1R4A6F_;F_;F_;Fw;Frho';Frho;").
Proof.
  clear. intros rho rho' w HFx Hag Hw. rewrite IP12_eq in Hw. rewrite <- IP12f_eq. apply SPA_refacts.
  - apply SPA_x_sub; [intros r []| exact Hw].
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros HF'. apply Forall_app. split; [exact HF'|].
    apply (holds_all_agree 37%positive rho rho' _ C12e_facts_below Hag).
    replace (ss_facts C12e) with (ss_facts (ax_S L12x)) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact HFx.
Qed.

Lemma call12 : ltac2:(tb__ "0|1|
S8S3aR1A1S1S6Q40A1S9R2P24A2Vb7;A3S58S1dVok;S43S1dS37S39Vb7;A1S3bA2M0S8aR3S38R3A1A5S56S2S8S8S0SeP25R5R1A3S43S1dG0S85R1S38R5A1R2A6A2Lrho';A2Lw;A4F_;F_;Frho;").
Proof using OKF.
  clear Ha1 Ha2 HBlim HPL HPL4 HPL5 HPL6 HPL7 Htop. intros rho HV H36.
  apply triple_factsA. intros HFx.
  eapply triple_conseq; [intros w Hw; exact (shape12 rho w HFx Hw) | intros w Hw; exact Hw |].
  apply (call_pureA segsA ok C12 Pre_rip Posts_rip s12 R12 (m12 b7) B12x (TP12 rho) rho _ OKF entails12 callcheck12).
  - intros J rho1 tp1 HokJ HstJ. exact (region_sum ok J rho1 tp1 HokJ HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state].
    replace (ss_next (ax_S C12)) with 37%positive in Hag by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply triple_refl].
    exists rho'. split; [exact Hag|]. exact (unshape12 rho rho' w HFx Hag Hw).
Qed.
Lemma ecall12 : ltac2:(tb__ "0|1|
S8S3aR1A1S1S6Q40A1S9R2P24A2Vb7;A3S57S1dS43S1dS37S39Vb7;A1S3bA2M0S8aR3S38R3A1A5S56S2S8S8S0SeP25R5R1A3S43S1dG0S85R1S38R5A1R2A6A2Lrho';A2Lw;A3F_;F_;Frho;").
Proof.
  clear. intros rho HV H36.
  apply etriple_factsA. intros HFx.
  eapply etriple_conseq; [intros w Hw; exact (shape12 rho w HFx Hw) | intros w Hw; exact Hw |].
  apply (ecall_pureA segsA C12 Pre_rip Posts_rip s12 R12 (m12 b7) B12x (TP12 rho) rho _ entails12 callcheck12).
  - intros J rho1 tp1 HstJ. exact (region_sum_ex J rho1 tp1 HstJ).
  - intros L rho' [<-|[]] Hag. cbn [la_state].
    replace (ss_next (ax_S C12)) with 37%positive in Hag by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply etriple_refl].
    exists rho'. split; [exact Hag|]. exact (unshape12 rho rho' w HFx Hag Hw).
Qed.

Lemma E_s13_facts1 : ltac2:(tb__ "0|0|
S1S4cS60SbS1aS16S15Z7fff80000000A1S11P1A1A2A1S10S5aS86A1A1A3S4eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg12d_post : ltac2:(tb__ "0|3|
S8S4aS2fA1M0S97S31S44S1dS37S39Vb7;A1S3bA2M1P4dM2R4S38R4A1S49S59S5bS86S81A2S4dS59A1A3S48G0S92R3S93R2R1A2A4A7S2S8S8S0S75G2R6R1A3S0S3cR6R1A2S0S76R6R1A2S43S1dG1S84R1S38R6A1S48G0S92R5S93R4R3A2A4A6A2A2A2Lrho';A2F_;Fmd;Fms;Ftr;Frho;").
Proof.
  clear. intros rho tr ms md Hw.
  apply (proj1 (LQA1 _ _ _ _ _ _)) in Hw as (rho1 & Hag & Hsp).
  pose proof E_s13g_at as (_ & _ & _ & LENb & LEN & LENe & X13).

  assert (H1 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13a) rho1 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13a_eq. apply SPA_move_last; [rewrite LEN; lia | exact X13 | rewrite T13a_eq; exact same_T13a | exact Hsp]. }
  pose proof (SPA_unobj segsA (KxA (m12 b7) B12x) rho1 (ax_setS E_s13 T13a) (ss_objs T13b) [ostk13] (TP12 rho) tr ms md T13a_split H1 ltac:(intros X; exact X)) as H2.
  cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, T13b_eq in H2.
  set (rho2 := rho_absorb rho1 [ostk13] (vms md (TP12 rho) ms)) in *.

  pose proof (SPA_facts_hold segsA _ _ _ _ _ Hsp) as HF. cbn [ax_S] in HF.
  assert (A2 : 0x7fff80000000 <= bv_unsigned (rw rho1 1%positive)).
  { pose proof (fact_of_state (ax_S E_s13) _ rho1 E_s13_facts1 HF) as A.
    cbn [holds eval] in A. rewrite u64_of_lit in A by lia. exact A. }
  assert (Rng : obj_range rho1 ostk13 = (bv_unsigned (rw rho1 1%positive) - 3104, bv_unsigned (rw rho1 1%positive) - 3024)).
  { unfold obj_range, obj_lo_of, obj_hi_of, soff, ostk13. cbn [ob_base ob_lo ob_hi eval]. unfold alu64, alu.
    rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 (-3024)) with (2 ^ 64 - 3024).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). pose proof (urange (rw rho1 1%positive)).
    replace (bv_unsigned (rw rho1 1%positive) + (2 ^ 64 - 3024)) with ((bv_unsigned (rw rho1 1%positive) - 3024) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia.
    replace (bv_signed (Z_to_bv 64 (-80))) with (-80) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    replace (bv_signed (Z_to_bv 64 0)) with 0 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). f_equal; lia. }
  assert (DEF : forall a, bv_unsigned (rw rho1 1%positive) - 3104 <= a < bv_unsigned (rw rho1 1%positive) - 3024 -> rm rho2 (Z_to_bv 64 a) <> None).
  { intros a Ha. unfold rho2. apply (SPA_released_defined (KxA (m12 b7) B12x) (ax_setS E_s13 T13a) rho1 (TP12 rho) tr ms md (ss_objs T13b) ostk13 T13a_split eq_refl);
      [rewrite Rng; cbn [fst]; lia | exact H1 | rewrite Rng; cbn [fst snd]; exact Ha]. }

  assert (H3 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13c) rho2 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13c_eq.
    apply (SPA_move_last segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13b) 3); [cbn [ax_S ax_setS]; rewrite LENb; lia | exact X13 | cbn [ax_S ax_setS]; rewrite T13c_eq; exact same_T13c | exact H2]. }
  assert (H4 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13d) rho2 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13d_eq.
    apply (SPA_carve_unknown (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13c) (TP12 rho) tr ms md (SVar 1%positive) (-3104) (-3024) (ss_next T13c) H3).
    - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    - cbn [ax_S ax_setS]. lia.
    - lia. - lia. - lia.
    - cbn [eval]. unfold rho2. rewrite rw_absorb. pose proof (urange (rw rho1 1%positive)). lia.
    - cbn [eval]. unfold rho2. rewrite rw_absorb. pose proof (urange (rw rho1 1%positive)). lia.
    -
      cbn [ax_S ax_setS eval].
      replace (bv_unsigned (rw rho2 1%positive)) with (bv_unsigned (rw rho1 1%positive)) by (unfold rho2; rewrite rw_absorb; reflexivity).
      destruct H1 as [Hsm1 _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm1) as S1. unfold virt in S1. cbn [w_tr w_cfg fst snd cfg_ms cfg_model ax_S ax_setS] in S1.
      pose proof (smatch_mm segsA _ _ _ _ _ S1) as (_ & PD & _). rewrite T13a_split in PD.
      apply pairwise_disjoint_app_inv in PD as (_ & _ & CR).
      apply Forall_forall. intros o Ho.
      assert (Ho' : In o (ss_objs T13b)).
      { rewrite <- T13c_eq in Ho. unfold move_obj_last in Ho. cbn [ss_objs set_objs] in Ho.
        rewrite !in_app_iff in Ho. destruct Ho as [Ho|[Ho|Ho]]; [eapply In_firstn_In; exact Ho | eapply In_skipn_In; exact Ho | eapply In_skipn_In; eapply In_firstn_In; exact Ho]. }
      pose proof (CR o ostk13 Ho' (or_introl eq_refl)) as D. rewrite Rng in D.
      replace (obj_range rho2 o) with (obj_range rho1 o) by (unfold obj_range, obj_lo_of, obj_hi_of, soff, rho2; rewrite !eval_absorb; reflexivity).
      unfold ranges_disjoint in D |- *. destruct (obj_range rho1 o) as [lo' hi']. cbn [fst snd] in D |- *. lia.
    - cbn [eval]. replace (bv_unsigned (rw rho2 1%positive)) with (bv_unsigned (rw rho1 1%positive)) by (unfold rho2; rewrite rw_absorb; reflexivity).
      intros a Ha. apply DEF. lia.
    - cbn [ax_X ax_setS]. rewrite X13. intros rr y j []. }
  pose proof (SPA_merge segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13d) 23 T13e (TP12 rho) _ T13e_eq H4) as H5. rewrite ax_setS_ax_setS in H5.
  assert (H6 : SPA segsA (KxA (m12 b7) B12x) (ax_setS E_s13 T13f) rho2 (TP12 rho) (tr, mkCfg ms md)).
  { rewrite <- T13f_eq.
    apply (SPA_move_last segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13e) 3); [cbn [ax_S ax_setS]; rewrite LENe; lia | exact X13 | cbn [ax_S ax_setS]; rewrite T13f_eq; exact same_T13f | exact H5]. }
  pose proof (SPA_merge segsA (KxA (m12 b7) B12x) rho2 (ax_setS E_s13 T13f) 22 T13g (TP12 rho) _ T13g_eq H6) as H7. rewrite ax_setS_ax_setS in H7.
  exists rho2. split; [|split; [|split]].
  - destruct Hag as (V & L & _). unfold rho2. split; [intros i Hi; rewrite rw_absorb; symmetry; apply V; exact Hi | intros l; rewrite rl_absorb; symmetry; apply L].
  - destruct Hag as (_ & _ & R). intros a Ha. unfold rho2. rewrite rm_absorb_outside; [symmetry; apply R|].
    intros (o & [<-|[]] & Hr). rewrite Rng in Hr. cbn [fst snd] in Hr. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha. lia.
  -
    pose proof Hag as (V & _ & _). unfold rho2. apply RMH_absorb; [eapply RMH_below; [apply RMH_refl | exact Hag]|].
    intros a [Ha _] (o & [<-|[]] & Hr). rewrite Rng in Hr. cbn [fst snd] in Hr. rewrite <- (V 1%positive) in Hr by lia. lia.
  - replace E_s13g with (ax_setS E_s13 T13g) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). exact H7.
Qed.

Lemma seg12d : ltac2:(tb__ "0|1|
S8S58S1dVok;S43S1dS37S39Vb7;A1S3bA2M0S85R1S38R1A1A5S56S2S8S8S0S75P4dR3R1A3S0S3cR3R1A2S0S76R3R1A2S43S1dG0S84R1S38R3A1R2A6A2A2A2Lrho';A2Lw;A4Frho;").
Proof using OKF.
  clear Ha1 Ha2 HBlim HPL HPL4 HPL5 HPL6 HPL7 Htop. intros rho.
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply triple1_triple. eapply sym_run_soundA; [exact run12c | apply OKFx | reflexivity | apply stableA_KxA]. }
  intros [tr [ms md]] Hw. replace (ss_next (ax_S IP12f)) with 77%positive in Hw by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  exact (seg12d_post rho tr ms md Hw).
Qed.
Lemma eseg12d : ltac2:(tb__ "0|1|
S8S57S1dS43S1dS37S39Vb7;A1S3bA2M0S85R1S38R1A1A5S56S2S8S8S0S75P4dR3R1A3S0S3cR3R1A2S0S76R3R1A2S43S1dG0S84R1S38R3A1R2A6A2A2A2Lrho';A2Lw;A3Frho;").
Proof.
  clear. intros rho.
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run12c]. }
  intros [tr [ms md]] Hw. replace (ss_next (ax_S IP12f)) with 77%positive in Hw by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  exact (seg12d_post rho tr ms md Hw).
Qed.
End S12c.

Section S13a.
Variable b7 : word.
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2VmE;S5G0Z1000A2Vb7;A4").
Definition m13 (b8 : word) : Model := eager_model 4096 (m12 b7) b8.
Lemma clear13 : ltac2:(tb__ "0|0|
S1S4cS77S3dS5aS84A1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma blocks12b : ltac2:(tb__ "0|6|
S8S27S3aR2A1S1S6Q40M0A1M1S9R3P24A2Vb7;A3S4aS47G1G1A2M2A1M3S2G3G3S1G3R2S4bG2R1S2aS29S39Vb7;A1A1A1A3A3Ll;A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S3dA3S3S2G1G1S2G1G1S0S5fG2S48G1G1R2R1A4R7A3S0S1fS7G0R2A2M4S7G0ScRbR5A2A2M5A2S1fS1eG5R4A2S1eG4S7G0R1A2A2A2A2A2Ls;A2Lb;A2S1fS1eS7G0ScR9R3A2A2R2A2R8A2A2F_;Fsz;Fe;F_;Fmaps;F_;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6 HPL7. intros rho LB HV H36 maps [l ->] e sz Hin.
  pose proof (m12_ledger b7) as (_ & M2 & _).
  unfold G12b in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[[= <- <-]|[]]].
  - apply (HG11c rho LB HV); [|exact Hin]. rewrite M2. exists (l ++ [(b7, Z_to_bv 64 4096)]). rewrite <- app_assoc. reflexivity.
  - left. cbn [eval]. rewrite H36. exists b7, (Z_to_bv 64 4096). split; [apply in_app_iff; right; rewrite M2; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma seg13 : ltac2:(tb__ "0|4|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S58S1dVok;S43S1dS37S39Vb7;A1M2S3bA2S84R3S38R3A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0Z1000M3A2R1A4S44S1dS37S66R1A1S1eS3bG3A2A2P4eS8cR5P4dR1A3S38R5A1S49S59S5bS8eS81A2S4dS59A1A3R2A7A2Lb8;A2Lw;A4F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV H36. pose proof (m12_ledger b7) as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_s13g 4096 (m12 b7) B12x G12b 78%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear13.
    + rewrite M1. exact Hres.
    + exact (init_sp_ok_m12 b7).
    + exact (band_m12 b7).
    + rewrite M3. unfold B12x, B12, B11. lia.
    + apply (blocks12b rho _ HV H36). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m12 b7) B12x) (OKFx _ _) (fun n => stableA_KxA segsA n (m12 b7) B12x) _ SPIN13 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run13_fail | exact spin13].
  - apply triple_ex; intros b8. apply triple_pure; intros HPL8.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b8; split; [exact HPL8|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_s13g) = 77%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_s13g 4096 78) with S_s13ok. rewrite N.
    eapply sym_run_soundA; [exact run13_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hw13 : ltac2:(tb__ "0|2|
S2S6Q40M0A1M1G1S53S5G0Z0A2S39Vb7;A1S5G0Z1000A2R1A4La;A2").
Lemma eseg13 : ltac2:(tb__ "0|4|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S57S1dS43S1dS37S39Vb7;A1M2S3bA2S84R3S38R3A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0Z1000M3A2R1A4S44S1dS37S66R1A1S1eS3bG3A2A2P4eS8cR5P4dR1A3S38R5A1S49S59S5bS8eS81A2S4dS59A1A3R2A7A2Lb8;A2Lw;A3F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 Hmaps Hres Htop Hlz Hw13.
  clear Ha1 Ha2. intros rho HV H36. pose proof (m12_ledger b7) as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply etriple_seq.
  { apply (eager_rw_enode E_s13g 4096 (m12 b7) B12x G12b 78%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear13.
    + rewrite M1. exact Hres.
    + exact (init_sp_ok_m12 b7).
    + exact (band_m12 b7).
    + rewrite M3. unfold B12x, B12, B11. lia.
    + exact Hw13.
    + apply (blocks12b rho _ HV H36). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b8. intros w [HPL8 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_s13g) = 77%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m13 b8) (B12x + 4096)) (eager_ok E_s13g 4096 78) (rho_set_rw rho (ss_next (ax_S E_s13g)) b8) (TP12 rho))
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) (m12 b7) (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m13 b0) (B12x + 4096)) 78 (rho_set_rw rho 77 b0) (TP12 rho) [mkLeafA E_s14 RsCut] w)).
  rewrite N. change (eager_ok E_s13g 4096 78) with S_s13ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b8; split; [exact HPL8|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run13_ok].
Qed.

Section S13.
Variable b8 : word.
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S39Vb7;A1S5G0Z1000A2Vb8;A4").
Definition m14 (b9 : word) : Model := eager_model 4096 (m13 b8) b9.
Definition G13b : list (sv * Z) := ltac2:(tb__ "0|1|
S4bS47SaS27A2M0S3dS49G0S48SaS27S11P4dA1Z1000A4S4dG0A1A3A3").

Lemma m13_ledger : ltac2:(tb__ "0|6|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29S66Vb8;A1A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb8;S5G0Z1000A2A4S2aS29S39Vb7;A1A1A1A3A3S0S1S27S2cG4A1S2cG5A1A3S1G1S2dG4A1S2dG5A1A3A2A2A2").
Proof.
  clear. pose proof (m12_ledger b7) as (L1 & L2 & L3 & L4).
  unfold m13, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. rewrite L1, L3, L4. repeat split; reflexivity.
Qed.
Lemma init_sp_ok_m13 : init_sp_ok (m_vmmaps (m13 b8)).
Proof using Htop. clear -Htop. pose proof m13_ledger as (_ & _ & _ & L4). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m13 : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29S66Vb8;A1A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof m13_ledger as (L1 & L2 & _). pose proof (m12_ledger b7) as (K1 & _).
  rewrite L1, L2, <- K1. apply (band_covered_after_grant (m12 b7)). exact (band_m12 b7). Qed.
Lemma b8_facts : ltac2:(tb__ "0|5|
S0S1fZ1000M0S7Q40M1Vb8;A2M2A2S0S6dG2G0A2S0S1fS1eG2G0A2S2eS29Vm;A1A1A2S0S1S27S21G2G0A2Z0A3S1S4cS30S4bS47S6G1A1M3G3A2S2bS29S39Vb7;A1A1M4A1S2aG4A1A3Vb8;S5G1G0A2A3S4eA3A2A2A2A2").
Proof using HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof (m12_ledger b7) as (L1 & L2 & L3 & L4).
  pose proof (place_LB_A (m12 b7) 4096 b8 (init_sp_ok_m12 b7) ltac:(rewrite L1; exact Hres) (band_m12 b7) ltac:(lia) ltac:(reflexivity) HPL8) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL8 as (Hal & _ & _ & Hfree). revert Ptop. unfold alloc_top. rewrite L4. intros Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. split; [exact PLB|]. split; [exact (bandav_intro _ _ Pband)|]. repeat split; assumption.
Qed.

Lemma blocks13b : ltac2:(tb__ "0|6|
S8S27S3aR2A1S1S6Q40M0A1M1S9R3P24A2Vb7;A3S1G1S9R4P4dA2Vb8;A3S4aS47G1G1A2M2A1M3S2G3G3S1G3R2S4bG2R1S2aS29S66Vb8;A1A1A1A3A3Ll;A2SaS27S5fS47SaS27A2S48SaS27R2R1A4S5eA3S3S2G1G1S2G1G1S0S5fG2S48G1G1R2R1A4R7A3S0S1fS7G0R2A2M4S7G0ScRcR5A2A2M5A2S1fS1eG5R4A2S1eG4S7G0R1A2A2A2A2A2Ls;A2Lb;A2S1fS1eS7G0ScRaR3A2A2R2A2R9A2A2F_;Fsz;Fe;F_;Fmaps;F_;F_;F_;FLB;Frho;").
Proof using HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL4 HPL5 HPL6 HPL7 HPL8. intros rho LB HV H36 H77 maps [l ->] e sz Hin. pose proof m13_ledger as (_ & M2 & _).
  unfold G13b in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[[= <- <-]|[]]].
  - apply (blocks12b rho LB HV H36); [|exact Hin]. rewrite M2. exists (l ++ [(b8, Z_to_bv 64 4096)]). rewrite <- app_assoc. reflexivity.
  - left. cbn [eval]. rewrite H77. exists b8, (Z_to_bv 64 4096). split; [apply in_app_iff; right; rewrite M2; left; reflexivity|]. rewrite u64_of_lit by lia. lia.
Qed.

Lemma clear14 : ltac2:(tb__ "0|0|
S1S4cS77S5eS5aS8eA1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma seg14 : ltac2:(tb__ "0|5|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S1G1S9R3P4dA2Vb8;A3S58S1dVok;S43S1dS37S66Vb8;A1M2S1eS3bZ1000M3A2M4A2S8eR4S38R4A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0G3A2R1A4S44S1dS37S5dR1A1S1eG4G3A2A2P4fS8cR6P4eR1A3S38R6A1S49S59S5bS8fS81A2S4dS59A1A3R2A7A2Lb9;A2Lw;A4F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV H36 H77. pose proof m13_ledger as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply triple_seq.
  { apply triple1_triple.
    apply (eager_rw_node ok OKF OKP E_s14 4096 (m13 b8) (B12x + 4096) G13b 79%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear14.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m13.
    + exact band_m13.
    + rewrite M3. unfold B12x, B12, B11. lia.
    + apply (blocks13b rho _ HV H36 H77). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA (m13 b8) (B12x + 4096)) (OKFx _ _) (fun n => stableA_KxA segsA n (m13 b8) (B12x + 4096)) _ SPIN14 200%nat SPIN_MMAPORDIE);
      [reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact run14_fail | exact spin14].
  - apply triple_ex; intros b9. apply triple_pure; intros HPL9.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b9; split; [exact HPL9|exact Hw] |].
    apply triple1_triple.
    assert (N : ss_next (ax_S E_s14) = 78%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change (eager_ok E_s14 4096 79) with S_s14ok. rewrite N.
    eapply sym_run_soundA; [exact run14_ok | apply OKFx | reflexivity | apply stableA_KxA].
Qed.

Hypothesis Hw14 : ltac2:(tb__ "0|2|
S2S6Q40M0A1M1G1S53S5G0Z0A2S66Vb8;A1S5G0Z1000A2R1A4La;A2").
Lemma eseg14 : ltac2:(tb__ "0|5|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S1G1S9R3P4dA2Vb8;A3S57S1dS43S1dS37S66Vb8;A1M2S1eS3bZ1000M3A2M4A2S8eR4S38R4A1A5S56S2G1G1S0S53S5G0Z0A2G2S5G0G3A2R1A4S44S1dS37S5dR1A1S1eG4G3A2A2P4fS8cR6P4eR1A3S38R6A1S49S59S5bS8fS81A2S4dS59A1A3R2A7A2Lb9;A2Lw;A3F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 Hmaps Hres Htop Hlz Hw14.
  clear Ha1 Ha2. intros rho HV H36 H77. pose proof m13_ledger as (M1 & M2 & M3 & M4). pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  eapply etriple_seq.
  { apply (eager_rw_enode E_s14 4096 (m13 b8) (B12x + 4096) G13b 79%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear14.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_m13.
    + exact band_m13.
    + rewrite M3. unfold B12x, B12, B11. lia.
    + exact Hw14.
    + apply (blocks13b rho _ HV H36 H77). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b9. intros w [HPL9 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_s14) = 78%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) (eager_ok E_s14 4096 79) (rho_set_rw rho (ss_next (ax_S E_s14)) b9) (TP12 rho))
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) (m13 b8) (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m14 b0) (B12x + 4096 + 4096)) 79 (rho_set_rw rho 78 b0) (TP12 rho) [mkLeafA E_s15 RsCut] w)).
  rewrite N. change (eager_ok E_s14 4096 79) with S_s14ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b9; split; [exact HPL9|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run14_ok].
Qed.

Section S14.
Variable b9 : word.
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S53S5Q40M0Z0A2S66Vb8;A1S5G0Z1000A2Vb9;A4").
Definition m15 : Model := ltac2:(tb__ "0|0|
S54S5dVb9;A1Vb9;S5Q40Z1000A2A3").
Definition G14b : list (sv * Z) := ltac2:(tb__ "0|1|
S4bS47SaS27A2M0S5eS49G0S48SaS27S11P4eA1Z1000A4S4dG0A1A3A3").

Lemma m14_ledger : ltac2:(tb__ "0|6|
S0S1S4aS47S6Q40M0A1M1G1A2M2A1M3S2bS29S5dVb9;A1A1M4A1S2bS29Vm;A1M5A1A3S0S1G3S2aG4A1S49G2S48G1G1Vb9;S5G0Z1000A2A4S2aS29S66Vb8;A1A1A1A3A3S0S1S27S2cG4A1S2cG5A1A3S1G1S2dG4A1S2dG5A1A3A2A2A2").
Proof.
  clear. pose proof m13_ledger as (L1 & L2 & L3 & L4).
  unfold m14, eager_model, eager_h. rewrite m_vmmaps_with_vmmaps. cbn [vm_reserved vm_maps vm_limit vm_init_sp]. rewrite L1, L3, L4. repeat split; reflexivity.
Qed.
Lemma init_sp_ok_m14 : ltac2:(tb__ "0|0|
S55S29S5dVb9;A1A1A1").
Proof using Htop. clear -Htop. pose proof m14_ledger as (_ & _ & _ & L4). unfold init_sp_ok in *. rewrite L4. exact Htop. Qed.
Lemma band_m14 : ltac2:(tb__ "0|2|
S65S4bS47S6Q40A1M0G0A2S2bS29S5dVb9;A1A1M1A1S2aG1A1A3S64S63A3").
Proof using Hmaps. clear -Hmaps. pose proof m14_ledger as (L1 & L2 & _). pose proof m13_ledger as (K1 & _).
  rewrite L1, L2, <- K1. apply (band_covered_after_grant (m13 b8)). exact band_m13. Qed.
Lemma b9_facts : ltac2:(tb__ "0|6|
S0S1fZ1000M0S7Q40M1Vb9;A2M2A2S0S3S1fS1eG2G0A2M3Z10000A2S1fZ646000G2A2A2S0S6dG2G0A2S0S1fG3S2eS29Vm;A1A1A2S0S1S27S21G2G0A2Z0A3S1S4cS30S4bS47S6G1A1M4G4A2S2bS29S66Vb8;A1A1M5A1S2aG5A1A3Vb9;S5G1G0A2A3S4eA3A2A2A2A2A2").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof m13_ledger as (L1 & L2 & L3 & L4).
  pose proof (place_LB_A (m13 b8) 4096 b9 init_sp_ok_m13 ltac:(rewrite L1; exact Hres) band_m13 ltac:(lia) ltac:(reflexivity) HPL9) as (PLB & Pimg & Pband & Ptop & _).
  pose proof HPL9 as (Hal & _ & _ & Hfree). revert Ptop. unfold alloc_top. rewrite L4. intros Ptop.
  assert (Hn : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Hn in Hfree.
  change (LB_of 4096) with 0x1000 in PLB. split; [exact PLB|]. split; [exact Pimg|]. split; [exact (bandav_intro _ _ Pband)|]. repeat split; assumption.
Qed.

Lemma clear15 : ltac2:(tb__ "0|0|
S1S4cS77S96S5aS90A1A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma region_free_filter : ltac2:(tb__ "0|2|
S47S6Q40A1M0G0A2M1S4cF_;S4aG1A1G0G0S1S4cS30R3R2R1A3S4eA3S1S4cS30S61G1R5R4A3R3R2A3S4eA3F_;Fk;Fa;Fl;Ff;").
Proof.
  clear. intros f l a k. induction l as [|[b sz] l IH]; cbn; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. destruct (f (b, sz)); cbn; [rewrite H1; cbn|]; apply IH; exact H2.
Qed.
Lemma tp_forget_id : ltac2:(tb__ "0|4|
S27S27S4aS6Q40M0A1M1A1M2G1S5fG1R1R2A3S3S20S7G0R2A2M3R5A2S1fR4G3A2A2F_;Fp;S1G2S98R4R3R2A3R2A3F_;Ftp;Fhi;Flo;").
Proof.
  clear. intros lo hi tp H. unfold tp_forget. induction tp as [|p tp IH]; cbn; [reflexivity|].
  unfold page_outside_range at 1. replace ((lo <=? bv_unsigned p) && (bv_unsigned p <? hi))%bool with false.
  2:{ symmetry. destruct (H p (or_introl eq_refl)) as [X|X]; apply andb_false_iff; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  cbn. rewrite IH; [reflexivity|]. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma TP12_band : ltac2:(tb__ "0|3|
S8S82SbSfR1A1S10S5aS90A1A1A3S3aR2A1S6Q40M0A1M1S5fG1R1S38R4A1A3S0S1fS64S7G0R2A2M2A2S1fS1eG2Z1000A2S63A2A2F_;Fp;F_;F_;Frho;").
Proof using HPL HPL6 HPL4 HPL5 Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim HPL7 HPL8 HPL9.
  intros rho HF HV p Hp. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). destruct E_s15u_facts as (X1 & X2 & X3 & X4).
  pose proof (fact_of_state _ _ rho X1 HF) as A1. pose proof (fact_of_state _ _ rho X2 HF) as A2.
  pose proof (fact_of_state _ _ rho X3 HF) as A3. pose proof (fact_of_state _ _ rho X4 HF) as A4.
  cbn [holds eval] in A1, A3. rewrite Z_to_bv_unsigned in A1, A3.
  change (bv_wrap 64 0x7fffffffff20) with 0x7fffffffff20 in A1. change (bv_wrap 64 (2 ^ 61 - 1)) with (2 ^ 61 - 1) in A3.
  cbn [holds] in A2. apply (f_equal bv_unsigned) in A2.
  change (bv_unsigned (eval rho (SAlu ALU_SLL (SVar 35%positive) (SLit 3)))) with (SymSoundV.U rho (StepA.g8 35%positive)) in A2.
  rewrite (StepA.U_g8 rho 35%positive) in A2 by (unfold SymSoundV.U; cbn [eval]; exact A3). unfold SymSoundV.U in A2. cbn [eval] in A2. rewrite H34 in A2.
  pose proof b6_facts as (F6lo & _ & F6top & _).
  pose proof P_facts as (Pal & Pceil & _ & PLB & Phi). pose proof RI_range as (R1 & R2 & R3). pose proof SB_val as SB.
  unfold alloc_ceiling_hi in Phi. unfold SHADOW_BAND_HI in PLB.
  pose proof (urange P) as UP. pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)) as MB.
  pose proof (urange (rw rho 31%positive)) as U31.
  assert (Htopv : alloc_top (m_vmmaps m) = bv_unsigned (rw rho 1%positive) - 0x800000) by (unfold alloc_top; rewrite stack_max_size_val, <- Hv1; reflexivity).
  assert (Upr : bv_unsigned (pRI rho) = priZ rho).
  { unfold pRI, shRI_base, priZ. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (bv_wrap 64 19327320064) with 19327320064. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  assert (Hpri : 0x2008fff7000 <= priZ rho /\ priZ rho + 12288 <= 0x10007fff8000) by (unfold priZ; lia).
  assert (Hsh : shZ rho <= 0x10007fff7fe4).
  { unfold shZ. pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive)) 0x7fffffffff20 8 ltac:(lia) A1). change (0x7fffffffff20 / 8) with 17592186044388 in H. lia. }
  assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shZ rho).
  { assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive)) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo in Htop; lia).
    unfold shZ. pose proof (Z.div_le_mono 0x7fff80000000 (bv_unsigned (rw rho 1%positive)) 8 ltac:(lia) HX1). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
  pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
  pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as Q1m.
  assert (Eq12 : q12 rho = shZ rho - 131072 - (shZ rho - 131072) mod 4096) by reflexivity.
  assert (Ee12 : e12 rho = shZ rho - 9 - (shZ rho - 9) mod 4096) by reflexivity.
  assert (Eq1 : q1Z rho = sbZ rho - sbZ rho mod 4096) by reflexivity.
  assert (Esb : sbZ rho = bv_unsigned (rw rho 35%positive) + 0x7fff8000) by reflexivity.
  assert (Hsb : 0x7fff8000 + 822272 <= sbZ rho /\ sbZ rho + 8192 <= 0x7fff8000 + (bv_unsigned (rw rho 1%positive) - 0x800000) / 8).
  { rewrite Esb. split; [lia|].
    pose proof (Z.div_le_mono (bv_unsigned b6 + 65536) (bv_unsigned (rw rho 1%positive) - 0x800000) 8 ltac:(lia) ltac:(lia)).
    rewrite <- A2 in H. replace (8 * bv_unsigned (rw rho 35%positive) + 65536) with ((bv_unsigned (rw rho 35%positive) + 8192) * 8) in H by lia.
    rewrite Z.div_mul in H by lia. lia. }
  assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
  assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
  assert (Hqal : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive) - 0x800000) 0x7fffff7fff20 8 ltac:(lia) ltac:(lia)) as DV.
  change (0x7fffff7fff20 / 8) with 17592184995812 in DV.
  unfold TP12, TP11 in Hp. unfold SHADOW_BAND_LO, SHADOW_BAND_HI.
  set (r1 := (shZ rho - 131072) mod 4096) in *. clearbody r1.
  set (r2 := (shZ rho - 9) mod 4096) in *. clearbody r2.
  set (r3 := sbZ rho mod 4096) in *. clearbody r3.
  set (dv := (bv_unsigned (rw rho 1%positive) - 0x800000) / 8) in *. clearbody dv.
  set (sh := shZ rho) in *. clearbody sh. set (sb := sbZ rho) in *. clearbody sb.
  set (q := q12 rho) in *. clearbody q. set (ee := e12 rho) in *. clearbody ee. set (q1 := q1Z rho) in *. clearbody q1.
  set (pr := priZ rho) in *. clearbody pr. pose proof (urange (pRI rho)) as Upr0. rewrite Upr in Upr0.
  clear HF A4 Htopv F6top Pceil SB.
  apply in_app_iff in Hp as [Hp|Hp].
  - apply In_pages_rev in Hp as (k & Hk & ->). unfold pageZ. rewrite !u64_of_lit by lia. lia.
  - destruct (q1 =? pr); cbn [In] in Hp; decompose [or] Hp; subst; try contradiction;
      first [rewrite !Upr | rewrite !u64_of_lit by lia | idtac]; lia.
Qed.

Lemma post15 : ltac2:(tb__ "0|8|
S8S8S56S75P4fM0R3R2A3S3cR4R3A2S76R5R4A2S1S6Q40M1A1S9R5P4eM2A2Vb9;A3S82SbSfR6A1S10S5aS90A1A1A3S3aR7A1S43S1dS37S54S5dVb9;A1S9R8G2A2M3S5G1Z1000M4A2M5A3S1eS1eS3bG4A2G4A2M6A2S9eS90G0A2Sa0R8S9fSdR8A1G3G5A3A2S98S7G1G3A2M7S1eG7G4A2S38R9A1A3R7A6S2S8S8S0S75G0RbR1A3S0S3cRbR1A2S0S76RbR1A2S43S1dS37S95G6A2S91R1S38RbA1R9A6A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Frho1;Frho;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho rho1 w Hag1 RS1 RM1 H78' HF1 HV1 Hw. pose proof Hag1 as [A1 L1]. pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  exists (set_rm rho1 (unmap_range (rm rho1) (rw rho1 78%positive) (Z_to_bv 64 4096))).
  split; [split; [intros i Hi; cbn; apply A1; exact Hi | intros l; cbn; apply L1]|].
  split.
  { intros a Ha. cbn [rm set_rm]. rewrite H78'. rewrite unmap_range_at.
    unfold SysStep.in_range. rewrite u64_of_lit by lia.
    match goal with |- (if ?c then _ else _) = _ => replace c with false end; [apply RS1; exact Ha|].
    symmetry. clear -Ha Kband. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha. unfold bandav in Kband.
    apply andb_false_iff. destruct Kband as [K|K]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
  split.
  { apply RMH_unmap; [exact RM1|]. rewrite H78', u64_of_lit by lia.
    pose proof HV1 as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1). pose proof Hag1 as [A1' _]. rewrite <- (A1' 1%positive) by lia. rewrite Hv1.
    revert K3. unfold alloc_top. rewrite stack_max_size_val. intros K3. lia. }
  rewrite H78' in Hw. rewrite (tp_forget_id) in Hw.
  2:{ intros p Hp. pose proof (TP12_band rho1 HF1 HV1 p) as X.
      rewrite (TP12_agree rho rho1) in X by (split; [intros i Hi; apply A1; lia | exact L1]). specialize (X Hp).
      clear -X Kband. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in X. unfold bandav in Kband. lia. }
  unfold m15. rewrite H78'. exact Hw.
Qed.

Lemma has15 : ltac2:(tb__ "0|0|
S1S4cS35S2aS29S5dVb9;A1A1A1Vb9;S5Q40Z1000A2A3S4eA3").
Proof. clear. pose proof m14_ledger as (_ & M2 & _). rewrite M2. cbn [map_has existsb fst snd]. rewrite !(proj2 (Fs.bv_eqb_eq _ _) eq_refl). reflexivity. Qed.
Lemma uniq15 : ltac2:(tb__ "0|2|
S6Q40M0A1M1S5fS47G1G1A2S48G1G1Vb9;R1A4S2aS29S5dVb9;A1A1A1A3S1G1R2S5G0Z1000A2A3F_;Fsz;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps Ha1 Ha2.
  clear HBlim. pose proof m14_ledger as (M1 & M2 & M3 & M4). pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof P_facts as (Pal & Pceil & Pfree & PLB & Phi). pose proof b4_facts as (F4lo & _). pose proof b5_facts as (F5lo & _).
  pose proof b6_facts as (F6lo & _). pose proof (b7_facts b7 HPL7) as (F7lo & _). pose proof b8_facts as (F8lo & _).
  rewrite M2. intros sz [[= <-]|Hin]; [reflexivity|]. exfalso.
  pose proof (region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ K4) Hin) as OV.
  unfold iv_overlap in OV. apply andb_false_iff in OV. rewrite u64_of_lit in OV by lia.
  pose proof m13_ledger as (_ & N2 & _). pose proof (m12_ledger b7) as (_ & O2 & _). pose proof mE_ledger as (_ & Q2 & _).
  rewrite N2, O2, Q2, Hmaps in Hin. pose proof (urange b9) as U9. clear Ha1 Ha2 Kband Kimg.
  destruct Hin as [[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[[= E1 <-]|[]]]]]]]]]]]];
    try (rewrite u64_of_lit in OV by lia); unfold n9, n7 in OV; try (rewrite u64_of_lit in OV by lia); destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.
Lemma free15 : ltac2:(tb__ "0|0|
S1S4cS30S36S2aS29S5dVb9;A1A1A1Vb9;A2Vb9;S5Q40Z1000A2A3S4eA3").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. pose proof m14_ledger as (_ & M2 & _). pose proof b9_facts as (_ & _ & _ & _ & _ & K4).
  rewrite M2. cbn [map_remove List.filter fst]. rewrite (proj2 (Fs.bv_eqb_eq _ _) eq_refl). cbn [negb].
  apply region_free_filter. exact (region_free_app_r _ _ _ _ K4).
Qed.
Lemma blocks15 : ltac2:(tb__ "0|4|
S8S3aR1A1S1S6Q40M0A1M1S9R2P24A2Vb7;A3S1G1S9R3P4dA2Vb8;A3SaS27S5fS47SaS27A2S48SaS27R2R1A4S5eA3S27S0S1fS7G0Vb9;A2M2R1A2S20R1S1eG2Z1000A2A2A2S4S0S1fS7G0ScR9R5A2A2M3R2A2S20R2S1eG3R4A2A2A2A1F_;Fx;F_;Fsz;Fe;F_;F_;F_;Frho;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho HV H36 H77 e sz Hin x Hx. pose proof b9_facts as (_ & _ & _ & _ & _ & K4).
  destruct (blocks13b rho 0 HV H36 H77 (vm_maps (m_vmmaps (m13 b8))) ltac:(exists []; reflexivity) e sz Hin) as [(b & s' & Hb & Hlo & Hhi)|Hlow].
  - pose proof (region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ K4) Hb) as OV.
    unfold iv_overlap in OV. apply andb_false_iff in OV. rewrite u64_of_lit in OV by lia.
    destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
  - pose proof (urange (eval rho e)). lia.
Qed.

Lemma rel15 : ltac2:(tb__ "0|3|
S8S4aS2fA1M0S97S31S3aR4A1S1S6Q40A1S9R5P4eA2Vb9;A3S43S1dS37S5dVb9;A1S1eS1eS3bZ1000M1A2G1A2A2M2S8fR6S38R6A1S48G0S92R5S93R4R3A2A4A6S2S8S8S0S75P4fR8R1A3S0S3cR8R1A2S0S76R8R1A2S43S1dG2S90R1S38R8A1S48G0S92R7S93R6R5A2A4A6A2A2A2Lrho1;A2F_;F_;F_;Fmd;Fms;Ftr;Frho;").
Proof using HPL9 HPL8 HPL7 HPL6 HPL5 HPL4 HPL Hres Htop Hmaps.
  clear Ha1 Ha2 HBlim. intros rho tr ms md HV H78 Hw. pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof HV as (_ & _ & _ & _ & _ & _ & _ & _ & Hv1).
  exists (rho_absorb rho [last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)] (vms md (TP12 rho) ms)).
  assert (SH : ob_base (last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)) = SVar 78%positive
               /\ ob_lo (last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)) = SLit 0
               /\ ob_hi (last (ss_objs (ax_S E_s15)) (mmap_obj 78%positive 4096)) = SLit 4096) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2).
  destruct SH as (B1 & B2 & B3).
  split; [split; intros; reflexivity|]. split.
  { intros a Ha. apply rm_absorb_outside. intros (o & [<-|[]] & Hr). revert Hr.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite B1, B2, B3. cbn [eval fst snd].
    rewrite H78, !soff_lit_small by lia. clear -Ha Kband. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in Ha. unfold bandav in Kband. lia. }
  split.
  { apply RMH_absorb; [apply RMH_refl|]. intros a [Ha _] (o & [<-|[]] & Hr). revert Hr.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite B1, B2, B3. cbn [eval fst snd].
    rewrite H78, !soff_lit_small by lia. revert K3. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros K3 Hr. lia. }
  rewrite <- E_s15u_eq.
  apply (SPA_unobj segsA (KxA (m14 b9) (B12x + 4096 + 4096)) rho E_s15 (ss_objs (ax_S E_s15u)) _ (TP12 rho) tr ms md E_s15_split Hw). intros X; exact X.
Qed.

Lemma seg15 : ltac2:(tb__ "0|3|
S8S3aR1A1S1S6Q40A1M0S9R2P24A2Vb7;A3S1G0S9R3P4dA2Vb8;A3S1G0S9R4P4eA2Vb9;A3S58S1dVok;S43S1dS37S5dVb9;A1S1eS1eS3bZ1000M1A2G1A2M2A2S8fR5S38R5A1A5S56S2S8S8S0S75P4fR7R1A3S0S3cR7R1A2S0S76R7R1A2S43S1dS37S95G2A2S91R1S38R7A1R2A6A2A2A2Lrho';A2Lw;A4F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hna Hres Htop Hlz OKF OKP.
  intros rho HV H36 H77 H78. pose proof m14_ledger as (M1 & M2 & M3 & M4). pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  apply (@triple_conseq segsA ok (fun w => exists rho1, agree_vars 79%positive rho rho1 /\ rm_same_band rho rho1 /\ RMH rho rho1 /\ SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15u rho1 (TP12 rho) w)
                         (SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15 rho (TP12 rho))
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w)
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w));
    [intros [tr [ms md]] Hw; exact (rel15 rho tr ms md HV H78 Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho1. apply triple_pure; intros Hag1. apply triple_pure; intros RS1. apply triple_pure; intros RM1. pose proof Hag1 as [A1 L1].
  assert (H78' : rw rho1 78%positive = b9) by (rewrite (A1 78%positive) by lia; exact H78).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 79%positive rho rho1); [lia | exact HV | intros i Hi; apply A1; exact Hi]).
  apply triple_factsA. intros HF1.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple;
    apply (munmap_node ok OKF OKP E_s15u 78%positive 4096 (m14 b9) (B12x + 4096 + 4096) G13b 79%positive
             eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
             eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; intros XX; discriminate XX) clear15 init_sp_ok_m14 rho1 (TP12 rho))].
  - cbv beta. intros w Hw. exact (post15 rho rho1 w Hag1 RS1 RM1 H78' HF1 HV1 Hw).
  - rewrite H78'. exact K2.
  - rewrite H78'. exact Kimg.
  - rewrite H78'. revert K3. unfold alloc_top. rewrite M4. intros K3. exact K3.
  - rewrite (A1 1%positive) by lia. rewrite M4. exact Hv1.
  - rewrite H78'. exact has15.
  - rewrite H78'. exact uniq15.
  - rewrite H78'. exact free15.
  - rewrite H78'. exact (blocks15 rho1 HV1 ltac:(rewrite (A1 36%positive) by lia; exact H36) ltac:(rewrite (A1 77%positive) by lia; exact H77)).
Qed.
Lemma eseg15 : ltac2:(tb__ "0|3|
S8S3aR1A1S1S6Q40A1M0S9R2P24A2Vb7;A3S1G0S9R3P4dA2Vb8;A3S1G0S9R4P4eA2Vb9;A3S57S1dS43S1dS37S5dVb9;A1S1eS1eS3bZ1000M1A2G1A2M2A2S8fR5S38R5A1A5S56S2S8S8S0S75P4fR7R1A3S0S3cR7R1A2S0S76R7R1A2S43S1dS37S95G2A2S91R1S38R7A1R2A6A2A2A2Lrho';A2Lw;A3F_;F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hna Hres Htop Hlz.
  intros rho HV H36 H77 H78. pose proof m14_ledger as (M1 & M2 & M3 & M4). pose proof b9_facts as (K1 & Kimg & Kband & K3 & K2 & K4).
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  apply (@etriple_conseq segsA (fun w => exists rho1, agree_vars 79%positive rho rho1 /\ rm_same_band rho rho1 /\ RMH rho rho1 /\ SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15u rho1 (TP12 rho) w)
                         (SPA segsA (KxA (m14 b9) (B12x + 4096 + 4096)) E_s15 rho (TP12 rho))
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w)
                         (fun w => exists rho', agree_vars 79%positive rho rho' /\ rm_same_band rho rho' /\ RMH rho rho' /\ SPA segsA (KxA m15 (B12x + 4096 + 4096)) S_s15ok rho' (TP12 rho) w));
    [intros [tr [ms md]] Hw; exact (rel15 rho tr ms md HV H78 Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho1. apply etriple_pure; intros Hag1. apply etriple_pure; intros RS1. apply etriple_pure; intros RM1. pose proof Hag1 as [A1 L1].
  assert (H78' : rw rho1 78%positive = b9) by (rewrite (A1 78%positive) by lia; exact H78).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 79%positive rho rho1); [lia | exact HV | intros i Hi; apply A1; exact Hi]).
  apply etriple_factsA. intros HF1.
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (munmap_enode E_s15u 78%positive 4096 (m14 b9) (B12x + 4096 + 4096) G13b 79%positive
             eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
             eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; intros XX; discriminate XX) clear15 init_sp_ok_m14 rho1 (TP12 rho))].
  - cbv beta. intros w Hw. exact (post15 rho rho1 w Hag1 RS1 RM1 H78' HF1 HV1 Hw).
  - rewrite H78'. exact K2.
  - rewrite H78'. exact Kimg.
  - rewrite H78'. revert K3. unfold alloc_top. rewrite M4. intros K3. exact K3.
  - rewrite (A1 1%positive) by lia. rewrite M4. exact Hv1.
  - rewrite H78'. exact has15.
  - rewrite H78'. exact uniq15.
  - rewrite H78'. exact free15.
  - rewrite H78'. exact (blocks15 rho1 HV1 ltac:(rewrite (A1 36%positive) by lia; exact H36) ltac:(rewrite (A1 77%positive) by lia; exact H77)).
Qed.
End S14.
End S13.
End S13a.

Lemma stackshadow_zero_band_ext : ltac2:(tb__ "0|4|
S8S8S1S6Q40M0A1S9R1P1M1A2S9R2G1A2A3S0S1fZ7fff80000000S7G0S9R3G1A2A2M2A2S1fG2Z800000000000A2A2S3cR4R3A2S40R5A1M3G3F_;F_;F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' H1 Hx RS Hz. destruct (q12_ext rho rho' H1) as (E1 & E2 & E3). unfold stackshadow_zero. rewrite E1, E3.
  intros z Hzz.
  pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as Qm. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as Em.
  assert (Hsh : shZ rho <= 0x10007fff8000).
  { unfold shZ. pose proof (Z.div_le_mono (bv_unsigned (rw rho 1%positive)) 0x800000000000 8 ltac:(lia) ltac:(lia)). change (0x800000000000 / 8) with 17592186044416 in H. lia. }
  assert (Hsh0 : 0x7fff8000 + 0xFFFF0000000 <= shZ rho).
  { unfold shZ. pose proof (Z.div_le_mono 0x7fff80000000 (bv_unsigned (rw rho 1%positive)) 8 ltac:(lia) ltac:(lia)). change (0x7fff80000000 / 8) with 0xFFFF0000000 in H. lia. }
  assert (Hq : q12 rho <= shZ rho - 131072 < q12 rho + 4096) by (unfold q12; lia).
  assert (He : e12 rho <= shZ rho - 9 < e12 rho + 4096) by (unfold e12; lia).
  assert (Hqal : q12 rho mod 4096 = 0) by (unfold q12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  assert (Heal : e12 rho mod 4096 = 0) by (unfold e12; rewrite Zminus_mod, Z.mod_mod by lia; rewrite Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hqal as [tq Htq]; [|lia]. apply Z.mod_divide in Heal as [te Hte]; [|lia].
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Htq, Hte. replace (te * 4096 - tq * 4096) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  rewrite (RS (Z_to_bv 64 z)) by (rewrite u64_of_lit by lia; unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia). apply Hz. exact Hzz.
Qed.

Definition Post5 (rho : valuation) : assn := ltac2:(tb__ "0|6|
S56S2S6Q40M0A1M1G1S2G1G1S2G1G1S2S8S8S0S53S5G0Z0A2M2VmE;S5G0Z1000M3A2M4R4A4S0S53G2S39R4A1G4R3A4S0S53G2S3fR4R3A2G4R2A4S0S75P24M5Vrho;R1A3S0S1G1S9R1G5A2R4A3S0S1G1S9R1P4dA2R3A3S0S1G1S9R1P4eA2R2A3S0S40R1A1S0S6bR1A1S0S6cR1A1S0S76Vrho;R1A2S43S1dS37S42R4R3R2A3S1eS1eS3bG3A2G3A2A2S91R1S38R1A1R5A6A2A2A2A2A2A2A2A2A2A2A2Lrho';A2Lb9;A2Lb8;A2Lb7;A2Lw;").

Theorem start5_sum_A : ltac2:(tb__ "0|0|
S8S3aR1A1S6bR2A1S6cR3A1S58S1dVok;S43S1dS37VmE;S68VB;A1A2S8dR4S67R4A1A5S3eR4A1A4F_;F_;F_;Frho;").
Proof using All.
  intros rho HV HZ HD. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x800000000000) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo, sp_window_hi in Htop; lia).

  eapply triple_seq; [apply (seg12a rho HV)|].
  apply triple_ex; intros b7. apply triple_pure; intros HPL7.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho1. apply triple_pure; intros Hag1. pose proof Hag1 as (V1 & L1 & R1).
  assert (E1 : forall i, (i < 36)%positive -> rw rho1 i = rw rho i) by (intros i Hi; rewrite <- (V1 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 36%positive rho rho1); [lia | exact HV | exact E1]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite <- (V1 36%positive) by lia; apply rho_set_rw_at).
  assert (AV1 : agree_vars 36 rho rho1) by (split; [exact E1 | intros l; symmetry; apply L1]).
  assert (HZ1 : Z11 rho1) by (apply (Z11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HZ]).
  assert (HD1 : ZD11 rho1) by (apply (ZD11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HD]).
  rewrite <- (TP11_agree rho rho1 AV1).

  eapply triple_conseq; [intros w Hw; exact (prep12 b7 HPL7 rho1 w HV1 H36a Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho2. apply triple_pure; intros Hrw2. apply triple_pure; intros Hrl2. apply triple_pure; intros Hz2.
  apply triple_pure; intros Hrm2. apply triple_pure; intros HI2. apply triple_pure; intros LOW2. apply triple_pure; intros Q12K. apply triple_pure; intros LOWB2.
  assert (HV2 : vals12 rho2) by (eapply (vals12_agree 36%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2]).
  assert (H36b : rw rho2 36%positive = b7) by (rewrite Hrw2; exact H36a).
  assert (AV2 : agree_vars 36 rho1 rho2) by (split; [intros i Hi; apply Hrw2 | exact Hrl2]).
  rewrite <- (TP12_agree rho1 rho2 AV2).

  eapply triple_seq; [apply (call12 b7 rho2 HV2 H36b)|].
  apply triple_ex; intros rho3. apply triple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & R3).
  assert (E3 : forall i, (i < 37)%positive -> rw rho3 i = rw rho2 i) by (intros i Hi; symmetry; apply V3; exact Hi).
  assert (AV3 : agree_vars 36 rho2 rho3) by (split; [intros i Hi; apply E3; lia | intros l; symmetry; apply L3]).
  rewrite <- (TP12_agree rho2 rho3 AV3).

  eapply triple_seq; [apply (seg12d b7 rho3)|].
  apply triple_ex; intros rho4. apply triple_pure; intros AV4. apply triple_pure; intros RS4. apply triple_pure; intros RM4.
  pose proof AV4 as [E4 L4].
  assert (HV4 : vals12 rho4) by (eapply (vals12_agree 37%positive rho2 rho4); [lia | exact HV2 | intros i Hi; rewrite E4 by lia; apply E3; lia]).
  assert (H36d : rw rho4 36%positive = b7) by (rewrite E4 by lia; rewrite E3 by lia; exact H36b).
  assert (AV4' : agree_vars 36 rho3 rho4) by (eapply agree_vars_le; [|exact AV4]; lia).
  rewrite <- (TP12_agree rho3 rho4 AV4').

  eapply triple_seq; [apply (seg13 b7 HPL7 rho4 HV4 H36d)|].
  apply triple_ex; intros b8. apply triple_pure; intros HPL8.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho5. apply triple_pure; intros Hag5. pose proof Hag5 as (V5 & L5 & R5).
  assert (E5 : forall i, (i < 77)%positive -> rw rho5 i = rw rho4 i) by (intros i Hi; rewrite <- (V5 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV5 : vals12 rho5) by (eapply (vals12_agree 77%positive rho4 rho5); [lia | exact HV4 | exact E5]).
  assert (H36e : rw rho5 36%positive = b7) by (rewrite E5 by lia; exact H36d).
  assert (H77e : rw rho5 77%positive = b8) by (rewrite <- (V5 77%positive) by lia; apply rho_set_rw_at).
  assert (AV5 : agree_vars 36 rho4 rho5) by (split; [intros i Hi; apply E5; lia | intros l; rewrite <- (L5 l); reflexivity]).
  rewrite <- (TP12_agree rho4 rho5 AV5).

  eapply triple_seq; [apply (seg14 b7 HPL7 b8 HPL8 rho5 HV5 H36e H77e)|].
  apply triple_ex; intros b9. apply triple_pure; intros HPL9.
  eapply triple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros rho6. apply triple_pure; intros Hag6. pose proof Hag6 as (V6 & L6 & R6).
  assert (E6 : forall i, (i < 78)%positive -> rw rho6 i = rw rho5 i) by (intros i Hi; rewrite <- (V6 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV6 : vals12 rho6) by (eapply (vals12_agree 78%positive rho5 rho6); [lia | exact HV5 | exact E6]).
  assert (H36f : rw rho6 36%positive = b7) by (rewrite E6 by lia; exact H36e).
  assert (H77f : rw rho6 77%positive = b8) by (rewrite E6 by lia; exact H77e).
  assert (H78f : rw rho6 78%positive = b9) by (rewrite <- (V6 78%positive) by lia; apply rho_set_rw_at).
  assert (AV6 : agree_vars 36 rho5 rho6) by (split; [intros i Hi; apply E6; lia | intros l; rewrite <- (L6 l); reflexivity]).
  rewrite <- (TP12_agree rho5 rho6 AV6).

  eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg15 b7 HPL7 b8 HPL8 b9 HPL9 rho6 HV6 H36f H77f H78f)].
  intros w (rho7 & AV7 & RS7 & RM7 & Hsp7). pose proof AV7 as [E7 L7].
  exists b7, b8, b9, rho7. split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|].
  assert (CH : forall i, (i < 36)%positive -> rw rho7 i = rw rho i).
  { intros i Hi. rewrite E7 by lia. rewrite E6, E5, E4, E3 by lia. rewrite Hrw2. apply E1. exact Hi. }
  split.
  { split; [exact CH|]. intros l. rewrite L7, <- (L6 l). cbn. rewrite <- (L5 l). cbn. rewrite L4, <- (L3 l), Hrl2, <- (L1 l). reflexivity. }
  split; [rewrite E7 by lia; exact H36f|]. split; [rewrite E7 by lia; exact H77f|]. split; [rewrite E7 by lia; exact H78f|].
  assert (HX2 : 0x7fff80000000 <= bv_unsigned (rw rho2 1%positive) <= 0x800000000000) by (rewrite Hrw2, E1 by lia; exact HX1).
  split.
  { apply (stackshadow_zero_band_ext rho6 rho7); [apply E7; lia | rewrite E6, E5, E4, E3 by lia; exact HX2 | exact RS7 |].
    apply (stackshadow_zero_ext rho5 rho6); [apply E6; lia | intros a; symmetry; apply R6 |].
    apply (stackshadow_zero_ext rho4 rho5); [apply E5; lia | intros a; symmetry; apply R5 |].
    apply (stackshadow_zero_band_ext rho3 rho4); [apply E4; lia | rewrite E3 by lia; exact HX2 | exact RS4 |].
    apply (stackshadow_zero_ext rho2 rho3); [apply E3; lia | intros a; symmetry; apply R3 | exact Hz2]. }
  split.
  {
    assert (ZBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> Z11 r -> Z11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1 N2.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ, sbZ in N1, N2. rewrite E31 in N1. rewrite E35 in N2.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1 N2).
      -
        rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (Z2 : Z11 rho2).
    { intros a p Hp Ha H64 N1 N2. unfold priZ, sbZ in N1, N2. rewrite !Hrw2 in N1, N2.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HZ1 a p Hp Ha H64 N1 N2). }
    assert (Z3 : Z11 rho3) by (apply (Z11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact Z2]).
    assert (AV13 : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (Z4 : Z11 rho4) by (apply (ZBAND rho3 rho4 AV13); [apply E4; lia | apply E4; lia | exact RS4 | exact Z3]).
    assert (Z5 : Z11 rho5) by (apply (Z11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact Z4]).
    assert (Z6 : Z11 rho6) by (apply (Z11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact Z5]).
    assert (AV16 : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZBAND rho6 rho7 AV16); [apply E7; lia | apply E7; lia | exact RS7 | exact Z6]. }
  split.
  {
    assert (ZDBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> ZD11 r -> ZD11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ in N1. rewrite E31 in N1.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1).
      - rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (ZD2 : ZD11 rho2).
    { intros a p Hp Ha H64 N1. unfold priZ in N1. rewrite !Hrw2 in N1.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HD1 a p Hp Ha H64 N1). }
    assert (ZD3 : ZD11 rho3) by (apply (ZD11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact ZD2]).
    assert (AV13d : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (ZD4 : ZD11 rho4) by (apply (ZDBAND rho3 rho4 AV13d); [apply E4; lia | apply E4; lia | exact RS4 | exact ZD3]).
    assert (ZD5 : ZD11 rho5) by (apply (ZD11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact ZD4]).
    assert (ZD6 : ZD11 rho6) by (apply (ZD11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact ZD5]).
    assert (AV16d : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZDBAND rho6 rho7 AV16d); [apply E7; lia | apply E7; lia | exact RS7 | exact ZD6]. }
  split.
  {
    assert (E6lo : forall i, (i < 7)%positive -> rw rho6 i = rw rho i) by (intros i Hi; rewrite E6, E5, E4, E3 by lia; rewrite Hrw2; apply E1; lia).
    assert (E3lo : forall i, (i < 7)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite E3 by lia; rewrite Hrw2; apply E1; lia).
    eapply RMH_trans; [| exact E6lo | exact RM7].
    intros a Ha. pose proof (proj1 Ha) as HaLo.
    rewrite <- (R6 a). cbn [rho_set_rw rm]. rewrite <- (R5 a). cbn [rho_set_rw rm].
    rewrite (RM4 a) by (apply (proj2 (ARGF_ext rho rho3 a E3lo)); exact Ha).
    rewrite <- (R3 a). rewrite (HI2 a) by (unfold SHADOW_BAND_HI; clear -HaLo HX1; lia).
    rewrite <- (R1 a). reflexivity. }
  rewrite (TP12_agree rho6 rho7) by (eapply agree_vars_le; [|exact AV7]; lia). exact Hsp7.
Qed.

Hypothesis Hwit12 : ltac2:(tb__ "0|2|
S2S6Q40M0A1M1G1S53S5G0Z0A2VmE;S5G0Z1000A2R1A4La;A2").
Hypothesis Hwit13 : ltac2:(tb__ "0|4|
S6Q40M0A1M1S53S5G0Z0A2M2VmE;S5G0Z1000A2M3R1A4S2G1G1S53G2S39R3A1G3R1A4La;A2F_;Fb7;").
Hypothesis Hwit14 : ltac2:(tb__ "0|4|
S6Q40M0A1M1G1S53S5G0Z0A2M2VmE;S5G0Z1000A2M3R2A4S53G2S39R3A1G3R2A4S2G1G1S53G2S3fR5R4A2G3R1A4La;A2F_;F_;Fb8;Fb7;").

Lemma eseg12a : ltac2:(tb__ "0|4|
S8S3aR1A1S57S1dS43S1dS37VmE;S68VB;A1M0A2S8dR2S67R2A1A5S56S2S6Q40M1A1M2G2S0S53S5G1Z0A2VmE;S5G1Z1000M3A2R1A4S44S1dS37S39R1A1S1eG0G3A2A2P25S8cR4P24R1A3S67R4A1S49S59S5bS89S81A2S4dS59A1A3R2A7A2Lb7;A2Lw;A3F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Hmaps Hres Htop Hlz Hwit12.
  clear Ha1 Ha2. intros rho HV. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1). pose proof mE_ledger as (M1 & M2 & M3 & M4 & M5).
  eapply etriple_seq.
  { apply (eager_rw_enode E_k12d 4096 mE (B12 B) G12 37%positive).
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + exact clear12.
    + rewrite M1. exact Hres.
    + exact init_sp_ok_mE.
    + exact band_mE.
    + rewrite M3. unfold B12, B11. lia.
    + exact Hwit12.
    + apply (HG11c rho _ HV). exists []. reflexivity.
    + rewrite M4. exact Hv1. }
  apply etriple_ex; intros b7. intros w [HPL7 Hsp]. revert w Hsp.
  assert (N : ss_next (ax_S E_k12d) = 36%positive) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  change (etriple segsA (SPA segsA (KxA (m12 b7) (B12 B + 4096)) (eager_ok E_k12d 4096 37) (rho_set_rw rho (ss_next (ax_S E_k12d)) b7) (TP11 rho))
           (fun w => exists b0, mmap_place_ok_none (Z_to_bv 64 0) mE (Z_to_bv 64 4096) b0
              /\ LQA segsA (KxA (m12 b0) (B12 B + 4096)) 37 (rho_set_rw rho 36 b0) (TP11 rho) [mkLeafA L12r RsCut] w)).
  rewrite N. change (eager_ok E_k12d 4096 37) with S_s12ok.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exists b7; split; [exact HPL7|exact Hw] |].
  rewrite <- N. eapply sym_run_etripleA; [reflexivity | apply stableA_KxA | exact run12a].
Qed.

Theorem start5_sum_ex_A : ltac2:(tb__ "0|0|
S8S3aR1A1S6bR2A1S6cR3A1S57S1dS43S1dS37VmE;S68VB;A1A2S8dR4S67R4A1A5S3eR4A1A3F_;F_;F_;Frho;").
Proof using HBlim HPL HPL4 HPL5 HPL6 Ha1 Ha2 Hmaps Hna Hres Htop Hlz Hwit12 Hwit13 Hwit14.
  intros rho HV HZ HD. pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  assert (HX1 : 0x7fff80000000 <= bv_unsigned (rw rho 1%positive) <= 0x800000000000) by (rewrite Hv1; unfold init_sp_ok, sp_window_lo, sp_window_hi in Htop; lia).
  eapply etriple_seq; [apply (eseg12a rho HV)|].
  apply etriple_ex; intros b7. apply etriple_pure; intros HPL7.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho1. apply etriple_pure; intros Hag1. pose proof Hag1 as (V1 & L1 & R1).
  assert (E1 : forall i, (i < 36)%positive -> rw rho1 i = rw rho i) by (intros i Hi; rewrite <- (V1 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV1 : vals12 rho1) by (eapply (vals12_agree 36%positive rho rho1); [lia | exact HV | exact E1]).
  assert (H36a : rw rho1 36%positive = b7) by (rewrite <- (V1 36%positive) by lia; apply rho_set_rw_at).
  assert (AV1 : agree_vars 36 rho rho1) by (split; [exact E1 | intros l; symmetry; apply L1]).
  assert (HZ1 : Z11 rho1) by (apply (Z11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HZ]).
  assert (HD1 : ZD11 rho1) by (apply (ZD11_ext rho rho1); [apply E1; lia | apply E1; lia | intros a; symmetry; apply R1 | exact HD]).
  rewrite <- (TP11_agree rho rho1 AV1).
  eapply etriple_conseq; [intros w Hw; exact (prep12 b7 HPL7 rho1 w HV1 H36a Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho2. apply etriple_pure; intros Hrw2. apply etriple_pure; intros Hrl2. apply etriple_pure; intros Hz2.
  apply etriple_pure; intros Hrm2. apply etriple_pure; intros HI2. apply etriple_pure; intros LOW2. apply etriple_pure; intros Q12K. apply etriple_pure; intros LOWB2.
  assert (HV2 : vals12 rho2) by (eapply (vals12_agree 36%positive rho1 rho2); [lia | exact HV1 | intros i Hi; apply Hrw2]).
  assert (H36b : rw rho2 36%positive = b7) by (rewrite Hrw2; exact H36a).
  assert (AV2 : agree_vars 36 rho1 rho2) by (split; [intros i Hi; apply Hrw2 | exact Hrl2]).
  rewrite <- (TP12_agree rho1 rho2 AV2).
  eapply etriple_seq; [apply (ecall12 b7 rho2 HV2 H36b)|].
  apply etriple_ex; intros rho3. apply etriple_pure; intros Hag3. pose proof Hag3 as (V3 & L3 & R3).
  assert (E3 : forall i, (i < 37)%positive -> rw rho3 i = rw rho2 i) by (intros i Hi; symmetry; apply V3; exact Hi).
  assert (AV3 : agree_vars 36 rho2 rho3) by (split; [intros i Hi; apply E3; lia | intros l; symmetry; apply L3]).
  rewrite <- (TP12_agree rho2 rho3 AV3).
  eapply etriple_seq; [apply (eseg12d b7 rho3)|].
  apply etriple_ex; intros rho4. apply etriple_pure; intros AV4. apply etriple_pure; intros RS4. apply etriple_pure; intros RM4.
  pose proof AV4 as [E4 L4].
  assert (HV4 : vals12 rho4) by (eapply (vals12_agree 37%positive rho2 rho4); [lia | exact HV2 | intros i Hi; rewrite E4 by lia; apply E3; lia]).
  assert (H36d : rw rho4 36%positive = b7) by (rewrite E4 by lia; rewrite E3 by lia; exact H36b).
  assert (AV4' : agree_vars 36 rho3 rho4) by (eapply agree_vars_le; [|exact AV4]; lia).
  rewrite <- (TP12_agree rho3 rho4 AV4').
  eapply etriple_seq; [apply (eseg13 b7 HPL7 (Hwit13 b7 HPL7) rho4 HV4 H36d)|].
  apply etriple_ex; intros b8. apply etriple_pure; intros HPL8.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho5. apply etriple_pure; intros Hag5. pose proof Hag5 as (V5 & L5 & R5).
  assert (E5 : forall i, (i < 77)%positive -> rw rho5 i = rw rho4 i) by (intros i Hi; rewrite <- (V5 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV5 : vals12 rho5) by (eapply (vals12_agree 77%positive rho4 rho5); [lia | exact HV4 | exact E5]).
  assert (H36e : rw rho5 36%positive = b7) by (rewrite E5 by lia; exact H36d).
  assert (H77e : rw rho5 77%positive = b8) by (rewrite <- (V5 77%positive) by lia; apply rho_set_rw_at).
  assert (AV5 : agree_vars 36 rho4 rho5) by (split; [intros i Hi; apply E5; lia | intros l; rewrite <- (L5 l); reflexivity]).
  rewrite <- (TP12_agree rho4 rho5 AV5).
  eapply etriple_seq; [apply (eseg14 b7 HPL7 b8 HPL8 (Hwit14 b7 b8 HPL7 HPL8) rho5 HV5 H36e H77e)|].
  apply etriple_ex; intros b9. apply etriple_pure; intros HPL9.
  eapply etriple_conseq; [intros w Hw; exact (proj1 (LQA1 _ _ _ _ _ w) Hw) | intros w Hw; exact Hw |].
  apply etriple_ex; intros rho6. apply etriple_pure; intros Hag6. pose proof Hag6 as (V6 & L6 & R6).
  assert (E6 : forall i, (i < 78)%positive -> rw rho6 i = rw rho5 i) by (intros i Hi; rewrite <- (V6 i) by lia; rewrite rho_set_rw_other by lia; reflexivity).
  assert (HV6 : vals12 rho6) by (eapply (vals12_agree 78%positive rho5 rho6); [lia | exact HV5 | exact E6]).
  assert (H36f : rw rho6 36%positive = b7) by (rewrite E6 by lia; exact H36e).
  assert (H77f : rw rho6 77%positive = b8) by (rewrite E6 by lia; exact H77e).
  assert (H78f : rw rho6 78%positive = b9) by (rewrite <- (V6 78%positive) by lia; apply rho_set_rw_at).
  assert (AV6 : agree_vars 36 rho5 rho6) by (split; [intros i Hi; apply E6; lia | intros l; rewrite <- (L6 l); reflexivity]).
  rewrite <- (TP12_agree rho5 rho6 AV6).
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (eseg15 b7 HPL7 b8 HPL8 b9 HPL9 rho6 HV6 H36f H77f H78f)].
  intros w (rho7 & AV7 & RS7 & RM7 & Hsp7). pose proof AV7 as [E7 L7].
  exists b7, b8, b9, rho7. split; [exact HPL7|]. split; [exact HPL8|]. split; [exact HPL9|].
  assert (CH : forall i, (i < 36)%positive -> rw rho7 i = rw rho i).
  { intros i Hi. rewrite E7 by lia. rewrite E6, E5, E4, E3 by lia. rewrite Hrw2. apply E1. exact Hi. }
  split.
  { split; [exact CH|]. intros l. rewrite L7, <- (L6 l). cbn. rewrite <- (L5 l). cbn. rewrite L4, <- (L3 l), Hrl2, <- (L1 l). reflexivity. }
  split; [rewrite E7 by lia; exact H36f|]. split; [rewrite E7 by lia; exact H77f|]. split; [rewrite E7 by lia; exact H78f|].
  assert (HX2 : 0x7fff80000000 <= bv_unsigned (rw rho2 1%positive) <= 0x800000000000) by (rewrite Hrw2, E1 by lia; exact HX1).
  split.
  { apply (stackshadow_zero_band_ext rho6 rho7); [apply E7; lia | rewrite E6, E5, E4, E3 by lia; exact HX2 | exact RS7 |].
    apply (stackshadow_zero_ext rho5 rho6); [apply E6; lia | intros a; symmetry; apply R6 |].
    apply (stackshadow_zero_ext rho4 rho5); [apply E5; lia | intros a; symmetry; apply R5 |].
    apply (stackshadow_zero_band_ext rho3 rho4); [apply E4; lia | rewrite E3 by lia; exact HX2 | exact RS4 |].
    apply (stackshadow_zero_ext rho2 rho3); [apply E3; lia | intros a; symmetry; apply R3 | exact Hz2]. }
  split.
  { assert (ZBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> Z11 r -> Z11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1 N2.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ, sbZ in N1, N2. rewrite E31 in N1. rewrite E35 in N2.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1 N2).
      - rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (Z2 : Z11 rho2).
    { intros a p Hp Ha H64 N1 N2. unfold priZ, sbZ in N1, N2. rewrite !Hrw2 in N1, N2.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HZ1 a p Hp Ha H64 N1 N2). }
    assert (Z3 : Z11 rho3) by (apply (Z11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact Z2]).
    assert (AV13 : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (Z4 : Z11 rho4) by (apply (ZBAND rho3 rho4 AV13); [apply E4; lia | apply E4; lia | exact RS4 | exact Z3]).
    assert (Z5 : Z11 rho5) by (apply (Z11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact Z4]).
    assert (Z6 : Z11 rho6) by (apply (Z11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact Z5]).
    assert (AV16 : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZBAND rho6 rho7 AV16); [apply E7; lia | apply E7; lia | exact RS7 | exact Z6]. }
  split.
  {
    assert (ZDBAND : forall r (r' : valuation), agree_vars 36 rho1 r -> rw r' 31%positive = rw r 31%positive -> rw r' 35%positive = rw r 35%positive ->
              rm_same_band r r' -> ZD11 r -> ZD11 r').
    { intros r r' AVr E31 E35 RS HZr a p Hp Ha H64 N1.
      assert (ET : TP11 r' = TP11 r) by (unfold TP11, q1Z, sbZ, priZ, pRI, shRI_base; cbn [eval]; rewrite E31, E35; reflexivity).
      rewrite ET in Hp. unfold priZ in N1. rewrite E31 in N1.
      rewrite (RS (Z_to_bv 64 a)).
      - exact (HZr a p Hp Ha H64 N1).
      - rewrite (TP11_agree rho1 r AVr) in Hp. pose proof (LOW2 p Hp). pose proof (LOWB2 p Hp). pose proof (urange p). rewrite u64_of_lit by lia. lia. }
    assert (ZD2 : ZD11 rho2).
    { intros a p Hp Ha H64 N1. unfold priZ in N1. rewrite !Hrw2 in N1.
      rewrite (TP11_agree rho1 rho2 AV2) in Hp. pose proof (urange p).
      rewrite (Hrm2 (Z_to_bv 64 a)) by (exists p; split; [exact Hp | rewrite u64_of_lit by lia; lia]). exact (HD1 a p Hp Ha H64 N1). }
    assert (ZD3 : ZD11 rho3) by (apply (ZD11_ext rho2 rho3); [apply E3; lia | apply E3; lia | intros a; symmetry; apply R3 | exact ZD2]).
    assert (AV13d : agree_vars 36 rho1 rho3) by (split; [intros i Hi; rewrite E3 by lia; apply Hrw2 | intros l; rewrite <- (L3 l); apply Hrl2]).
    assert (ZD4 : ZD11 rho4) by (apply (ZDBAND rho3 rho4 AV13d); [apply E4; lia | apply E4; lia | exact RS4 | exact ZD3]).
    assert (ZD5 : ZD11 rho5) by (apply (ZD11_ext rho4 rho5); [apply E5; lia | apply E5; lia | intros a; symmetry; apply R5 | exact ZD4]).
    assert (ZD6 : ZD11 rho6) by (apply (ZD11_ext rho5 rho6); [apply E6; lia | apply E6; lia | intros a; symmetry; apply R6 | exact ZD5]).
    assert (AV16d : agree_vars 36 rho1 rho6).
    { split; [intros i Hi; rewrite E6, E5, E4, E3 by lia; apply Hrw2 | intros l; rewrite <- (L6 l); cbn; rewrite <- (L5 l); cbn; rewrite L4, <- (L3 l); apply Hrl2]. }
    apply (ZDBAND rho6 rho7 AV16d); [apply E7; lia | apply E7; lia | exact RS7 | exact ZD6]. }
  split.
  { assert (E6lo : forall i, (i < 7)%positive -> rw rho6 i = rw rho i) by (intros i Hi; rewrite E6, E5, E4, E3 by lia; rewrite Hrw2; apply E1; lia).
    assert (E3lo : forall i, (i < 7)%positive -> rw rho3 i = rw rho i) by (intros i Hi; rewrite E3 by lia; rewrite Hrw2; apply E1; lia).
    eapply RMH_trans; [| exact E6lo | exact RM7].
    intros a Ha. pose proof (proj1 Ha) as HaLo.
    rewrite <- (R6 a). cbn [rho_set_rw rm]. rewrite <- (R5 a). cbn [rho_set_rw rm].
    rewrite (RM4 a) by (apply (proj2 (ARGF_ext rho rho3 a E3lo)); exact Ha).
    rewrite <- (R3 a). rewrite (HI2 a) by (unfold SHADOW_BAND_HI; clear -HaLo HX1; lia).
    rewrite <- (R1 a). reflexivity. }
  rewrite (TP12_agree rho6 rho7) by (eapply agree_vars_le; [|exact AV7]; lia). exact Hsp7.
Qed.

End Seg5.
End Start5.

