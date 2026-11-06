(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput on the ASan build:
   the piece of a turn that starts at GA0 (GrantEntrySetDefs.v), slots 0x80b0c .. 0x80c20.

   At GA0 the cell had no byte left, and reac_headamp_tx_set was called at 0x80b08 with
   the cell (0, 0, 0) (fuzz/fuzz_grant.c:201-230 reads 0 for each byte past the end).
   The code keeps the set's answer in s9, sets s8, s2 and s7 (value, channel, parameter)
   and slot 120 (the bytes left) to 0, and at 0x80bfc computes the answer the set must
   give, (s7 < 3 && s8 < 2) - 1, which is 0. The check at 0x80c0c (`bne s9, a0` into the
   error block at 0x81a0c, which calls __asan_handle_no_return and then abort) compares
   the two: the channel 0 is below 48 and the value 0 is legal for the parameter 0
   (legalb 0 0, lib/Prog/HeadampModel.v:58), so the set accepted the cell, s9 is 0 and
   the branch is not taken. Nor is the one at 0x80c10 (`bnez s9`) to the refused end of
   the turn at 0x80c78. The piece ends at the call of reac_headamp_tx_effective at
   0x80c20, which call_e2_stmt carries on to GE2. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC4b YC1g YC1h YC85 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
(* The call of reac_headamp_tx_effective at 0x80c20 after an accepted set lands in GE2. *)
Hypothesis CALLE2 : call_e2_stmt B MT.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The machine state a run left, and a register r the run left as the atom of the entry
   register q (qn = q as a number). *)
Local Ltac ga0_ms HS x :=
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.
Local Ltac ga0_atom HS HE regs r qn q R :=
  prreg HS r R; rewrite HE, Eimg_low in R by (unfold A_TEXT; lia);
  rewrite (ew_Ereg_nat regs _ qn q eq_refl) in R.

(* ---- 0x80b0c: the return of reac_headamp_tx_set for a cell with no byte left ---- *)
(* The seat: the stack slots the turn reads (R_stk, at s1, which lies above the shadow),
   and a0 pinned to 0, the answer of an accepted set. *)
Definition F_ga0 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_ga0a : sstate := mkSS 0x45c sr_atoms [R_stk] None F_ga0.
Definition ss_ga0 : sstate := mkSS 0x45c (sr_set sr_atoms 10%bv (SLit 0)) [R_stk] None F_ga0.

Lemma ge_set_ga0 : seg_ga0_stmt B MT.
Proof.
  intros POST n i HN HE2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & Hlen & HM & R10 & R21).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  (* The cell: no byte is left, so it reads (0, 0, 0) (GrantEntrySetDefs.v gcell_cases,
     from SegSetModel.cell_rd_0), and the set accepts it: 0 < 48 and legalb 0 0. *)
  pose proof (gcell_cases (c_pl cx) i) as HCC. cbv zeta in HCC.
  destruct HCC as [(Hc3 & _) | [(Hc2 & _) | [(Hc1 & _) | (_ & Ecell & EposS)]]]; [lia | lia | lia |].
  assert (Ec : gc (c_pl cx) i = 0) by (unfold gc; rewrite Ecell; reflexivity).
  assert (Eq : gq (c_pl cx) i = 0) by (unfold gq; rewrite Ecell; reflexivity).
  assert (Ev : gv (c_pl cx) i = 0) by (unfold gv; rewrite Ecell; reflexivity).
  assert (HA : gacc (c_pl cx) i = true) by (unfold gacc; rewrite Ec, Eq, Ev; reflexivity).
  rewrite HA in R10. cbv beta iota in R10.
  assert (Ev120 : c_n cx - Z.of_nat (gpos (c_pl cx) i) = 0) by (unfold c_n; rewrite Hlen; lia).
  rewrite Ev120 in HM.
  pose proof HM as (_ & Hsh & _ & _ & Hmid & _ & H120 & _ & HWS & HST).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
  pose proof (R_stk_ok cx fp t ly3 W3 ms3) as RSTK.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [0; gF cx fp + GO_SET; gF cx fp + GO_WAS]))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
      nth j (map (Z_to_bv 64) [0; gF cx fp + GO_SET; gF cx fp + GO_WAS]) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); subst regs; exact G9).
  assert (E32 : ew E 32 = w64 0) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = w64 (gF cx fp + GO_SET)) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = w64 (gF cx fp + GO_WAS)) by exact (EX 2%nat ltac:(lia)).
  assert (HS0 : st_ok_pi SEGS VAL E ss_ga0a (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x45c)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_ga0a. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. subst mem.
      exact (RSTK E 0 HL HSP E9 E32 E33 E34 ltac:(lia) H120 Hmid).
    - split; exact I.
    - unfold F_ga0. split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9. unfold w64.
      rewrite unsigned_lit_small by lia. try change (2 ^ 5) with 32. lia. }
  (* a0 holds the set's answer, 0 (R10). *)
  assert (HS : st_ok_pi SEGS VAL E ss_ga0 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x45c)) mem (seg_rom SEGS)))).
  { apply (st_ok_pi_set_reg E ss_ga0a _ (10%bv : bv 5) (SLit 0) HS0); [discriminate|].
    cbn [ms_regs restrict mkst]. subst regs. rewrite R10. reflexivity. }
  clear HS0.
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) mem)) by constructor.
  subst mem.
  (* 0x80b0c .. 0x80c20: s9 = a0 = 0, the computed answer (s7 < 3 && s8 < 2) - 1 = 0, so
     neither the branch at 0x80c0c to the error block 0x81a0c nor the one at 0x80c10 to
     0x80c78 is taken; the run stops at the call of reac_headamp_tx_effective. *)
  paj_run_tok RUN HS HJ SHOK GBspan.
  - (* the run writes slot 120 only *)
    change (ss_mem ss_ga0) with [R_stk].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia
      | cbn [YP09.r_wlo R_stk]; unfold GE_STK; lia | cbn [YP09.r_whi R_stk]; lia |].
    apply awr_ok_nil.
  - (* at the entry of reac_headamp_tx_effective, from 0x80c20 *)
    ga0_ms HS msF.
    (* the run changed slot 120 only *)
    assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
                   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hw.
      match goal with HFr : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
        apply (frame_wins E _ _ _ _ (fun a => c_sp1 cx + 120 <= a < c_sp1 cx + 128) HFr); [|exact Ha | exact Hw] end.
      intros x (r & Hr & Hx). cbn [ss_mem ss_ga0 In] in Hr.
      destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_stk] in Hx.
      rewrite E9 in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by lia. lia. }
    (* slot 120 holds 0 *)
    lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
      let rr := eval vm_compute in (nth_error (ss_mem ssx) 0) in
      lazymatch rr with Some ?R0 =>
        pose proof (st_ok_region_nth Ex ssx msx 0 R0 HS ltac:(vm_compute; reflexivity)) as FR0 end end.
    cbn [ms_mem restrict] in FR0.
    assert (S120 : gslot cx W3 msF 120 0).
    { unfold gslot. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msF)); [|lia].
      eapply (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 120 8%N (SLit 0) 0 FR0);
        [ first [ rewrite E9 | (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E9) ];
          unfold w64; apply unsigned_lit_small; lia
        | cbn; tauto | reflexivity | cbn; lia | cbn; lia ]. }
    (* the two arrays are kept *)
    assert (NWS : gfarr cx fp W3 msF GO_WAS (gwsi (c_pl cx) i)).
    { unfold gfarr. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msF)); [|exact HWS].
      intros a Ha. rewrite length_map, LW in Ha. apply HWIN; unfold GO_WAS in *; lia. }
    assert (NST : gfarr cx fp W3 msF GO_SET (gsti (c_pl cx) i)).
    { unfold gfarr. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msF)); [|exact HST].
      intros a Ha. rewrite length_map, LS in Ha. apply HWIN; unfold GO_SET in *; lia. }
    assert (GM : gmem cx fp W3 msF t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) 0).
    { apply (gmem_win3 cx fp t ly3 W3 ms3 msF (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) 0
               (gwsi (c_pl cx) i) (gsti (c_pl cx) i) (gF cx fp + 32) (gF cx fp + 240) HL Hn);
        [ intros a Ha Hw; apply HWIN; [exact Ha | intros Hx; apply Hw; left; exact Hx]
        | lia | lia | exact S120 | exact NWS | exact NST | exact HM ]. }
    (* the registers at the callee's entry *)
    pmkst HS.
    rewrite pa_sigma_reac_headamp_tx_effective.
    prreg HS (1%bv : bv 5) Q1.
    ga0_atom HS HE regs (2%bv : bv 5) 2%nat (2%bv : bv 5) Q2. ga0_atom HS HE regs (8%bv : bv 5) 8%nat (8%bv : bv 5) Q8.
    ga0_atom HS HE regs (9%bv : bv 5) 9%nat (9%bv : bv 5) Q9. ga0_atom HS HE regs (3%bv : bv 5) 3%nat (3%bv : bv 5) Q3.
    ga0_atom HS HE regs (4%bv : bv 5) 4%nat (4%bv : bv 5) Q4.
    (* a0 = s4, the table *)
    ga0_atom HS HE regs (10%bv : bv 5) 20%nat (20%bv : bv 5) Q10.
    prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18.
    ga0_atom HS HE regs (19%bv : bv 5) 19%nat (19%bv : bv 5) Q19. ga0_atom HS HE regs (20%bv : bv 5) 20%nat (20%bv : bv 5) Q20.
    ga0_atom HS HE regs (21%bv : bv 5) 21%nat (21%bv : bv 5) Q21. ga0_atom HS HE regs (22%bv : bv 5) 22%nat (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    ga0_atom HS HE regs (27%bv : bv 5) 27%nat (27%bv : bv 5) Q27.
    subst regs.
    apply (CALLE2 POST n i cx fp k acc ly3 S3 W3 (ms_regs msF) (ms_mem msF) _ t HE2 HB HJ HFR HMO
             Hk Hacc Hbl Ht0 Hn Hns HA).
    + exact Q1.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + rewrite Ec. exact Q11.
    + rewrite Eq. exact Q12.
    + rewrite Ec. exact Q18.
    + congruence.
    + congruence.
    + rewrite EposS. congruence.
    + congruence.
    + rewrite Eq. exact Q23.
    + rewrite Ev. exact Q24.
    + congruence.
    + rewrite EposS, Ev120.
      apply (gmem_tr cx fp W3 msF); [intros a; reflexivity | exact GM].
Qed.

End c.
End b.
End a.
