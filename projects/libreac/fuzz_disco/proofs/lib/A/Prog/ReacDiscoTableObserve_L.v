(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 102 of its 137 lines of code are new or changed and 34 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Definition SegLoopAt (c : tctx) (j : Z) : Prop :=
  forall regs1 m1 md1, tpre B c -> tobs_m B c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 23 = w64 (DTC.n_of (tT c)) ->
  YK11.getr regs1 25 = w64 (48 * j) -> YK11.getr regs1 26 = w64 (48 * DTC.n_of (tT c)) ->
  0 <= j < DTC.n_of (tT c) -> (forall j', 0 <= j' < j -> DTC.mac_of (tT c) j' <> DTC.s_mac (tG c)) ->
  SRr SEGS (tW c) (cfgB 0x5128 regs1 m1 md1) (tpost B c).
Definition SegLoop2At (c : tctx) (j : Z) : Prop :=
  forall regs1 m1 md1 (v : word), tpre B c -> tobs_m B c regs1 m1 md1 (tT c) ->
  YK11.getr regs1 18 = w64 (ts c) -> YK11.getr regs1 19 = w64 (tt c + 48 * j) ->
  YK11.getr regs1 23 = w64 (DTC.n_of (tT c)) ->
  YK11.getr regs1 25 = w64 (48 * j) -> YK11.getr regs1 26 = w64 (48 * DTC.n_of (tT c)) -> YK11.getr regs1 10 = v ->
  (v = w64 0 <-> forall i, 0 <= i < 6 -> nth_error (tT c) (Z.to_nat (48 * j + i)) = nth_error (tG c) (Z.to_nat i)) ->
  0 <= j < DTC.n_of (tT c) -> (forall j', 0 <= j' < j -> DTC.mac_of (tT c) j' <> DTC.s_mac (tG c)) ->
  SRr SEGS (tW c) (cfgB 0x513c regs1 m1 md1) (tpost B c).
Lemma loop_call : forall c j, SegLoop2At c j -> SegLoopAt c j.
Proof.
intros c j HK regs1 m1 md1 HP HM H18 H23 H25 H26 Hj Hmis.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (B8 : base_val (tobs_env c regs1 (tT c) 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 (tT c) 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  apply unsigned_lit_small. lia. }
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (tobs_env c regs1 (tT c) 0) n = YK11.getr regs1 x)
  by (intros n x Hnx; apply tobs_env_reg; exact Hnx).
pose proof (tobs_regs_ok c regs1 (tT c) 0 (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM) (tm_s6 _ _ _ _ _ _ HM)
  (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
pose proof (tobs_env_img c regs1 (tT c) 0) as HEI.
destruct (tobs_enter B c regs1 m1 md1 (tT c) 0x5128 false 0 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(discriminate)) as [HS SHOK].
unfold cfgB.
paj_run_tok RUN HS HJ SHOK TBspan.
{ exact (tobs_awr B c _ false 0 0 HP B8 ltac:(discriminate)). }
pmkst HS.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2. prreg HS (1%bv : bv 5) QRA.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (23%bv : bv 5) P23. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26.
rewrite (EE 18%nat 18%bv eq_refl), H18 in P18. rewrite (EE 23%nat 23%bv eq_refl), H23 in P23.
rewrite (EE 25%nat 25%bv eq_refl), H25 in P25. rewrite (EE 26%nat 26%bv eq_refl), H26 in P26.
rewrite (EE 8%nat 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM), (EE 25%nat 25%bv eq_refl), H25 in P19, QA0.
unfold w64 in P19, QA0. rewrite alu64_add_lit in P19, QA0.
rewrite (EE 18%nat 18%bv eq_refl), H18 in QA1.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
assert (HM2 : tobs_m B c (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) (tT c)).
{ apply (tobs_exit_nostore B LAWS c regs1 m1 md1 (tT c) 0 _ (ms_mem ms) _ (ms_regs ms) HP HM ltac:(left; reflexivity) HFr HG HJ Hreg B8 eq_refl).
  intros q Hq. cbn in Hq.
  repeat (destruct Hq as [<- | Hq];
    [ eapply (tobs_reg_same c regs1 (tT c) 0 _ _ _ _ _ HS HR0);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity] ] |]).
  destruct Hq. }
eapply (tobs_bcmp B LAWS ABCMP c (ms_regs ms) (ms_mem ms) _ (tT c) j 0x513c (tpost B c) HP HM2 ltac:(lia)).
- exact QA0.
- exact QA1.
- exact QA2.
- exact QRA.
- lia.
- reflexivity.
- intros regs2 mem2 md2 v HM3 HP2 Hv Hcmp.
  assert (Pr : forall q : Z, acallee_saved q -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr (ms_regs ms) (Z_to_bv 5 q))
    by (intros q Hq; exact (HP2 q Hq)).
  apply (HK regs2 mem2 md2 v HP HM3).
  + etransitivity; [exact (Pr 18 ltac:(unfold acallee_saved; lia)) | exact P18].
  + etransitivity; [exact (Pr 19 ltac:(unfold acallee_saved; lia)) | exact P19].
  + etransitivity; [exact (Pr 23 ltac:(unfold acallee_saved; lia)) | exact P23].
  + etransitivity; [exact (Pr 25 ltac:(unfold acallee_saved; lia)) | exact P25].
  + etransitivity; [exact (Pr 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + exact Hv.
  + exact Hcmp.
  + exact Hj.
  + exact Hmis.
Qed.
Lemma seg_loop : forall c,
  (forall j, SegLoopAt c (j + 1) -> SegLoop2At c j) -> SegLoop B c.
Proof.
intros c HA.
assert (Hk : forall k : nat, forall j, Z.of_nat k = DTC.n_of (tT c) - j -> SegLoopAt c j).
{ induction k as [|k IH]; intros j Hjk.
  - intros regs1 m1 md1 HP HM H18 H23 H25 H26 Hj Hmis. lia.
  - apply loop_call. apply HA. apply IH. lia. }
intros regs1 m1 md1 j HP HM H18 H23 H25 H26 Hj Hmis.
exact (Hk (Z.to_nat (DTC.n_of (tT c) - j)) j ltac:(lia) regs1 m1 md1 HP HM H18 H23 H25 H26 Hj Hmis).
Qed.
End h.
End f.
End d.
