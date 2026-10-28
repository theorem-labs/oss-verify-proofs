(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls H_scanner_get_token H_vfmatch_A H_vfmatch_B H_vfmatch_C H_vfmatch_F.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Section VFG3.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation headst := (headst q S). Notation contst := (contst q S). Notation exitst := (exitst q S).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q cur0).
  Notation F0 := (F0 q cur0). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Notation WF Wx := ((lo, q) :: (S + 8, S + 16) :: Wx)%Z.
  Notation vpost := (vpost q lo S MB A len cap cur0 bs).
  Notation FS := (FS q).

  Notation FMT_CHUNK := 0x1035b%Z.
  Definition fb_chunk : list byte := map (Z_to_bv 8) [37; 120; 37; 76; 37; 99; 0].
  #[using="Type"] Lemma fb_chunk_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_CHUNK fb_chunk.
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m FMT_CHUNK fb_chunk MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Ltac rd_chunk := rdfmt fb_chunk_at constr:(0x1035b%Z).

  Definition R_chunk (P P2 : Z) (tp canary : word) (pv pa pb e : word) (m : mem) : Prop :=
    rw_cells rsegs m P [C4 pv] /\ rw_cells rsegs m P2 [C8 pa; C8 pb] /\ rw_cells rsegs m (bv_unsigned tp - 164) [C4 e]
    /\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].

  Definition X_chunk (P P2 : Z) (tp canary : word) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    exists pv pa pb e, R_chunk P P2 tp canary pv pa pb e m'
      /\ (r = PARSE_OK -> exists v, pv = wz v /\ 0 <= v < 2^31 /\ cur0 + 1 <= cur')%Z.

  #[using="VOK"] Theorem vf_chunk : forall (P P2 : Z) (pv pw1 pw2 errv canary : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m (q + 16) [C8 (wz P)] -> rw_cells rsegs m P [C4 pv] -> (q + 64 <= P /\ P + 4 <= MB)%Z -> (P mod 4 = 0)%Z ->
    rw_cells rsegs m (q + 16 + 8) [C8 (wz P2)] -> rw_cells rsegs m P2 [C8 pw1; C8 pw2] -> (q + 64 <= P2 /\ P2 + 16 <= MB)%Z -> (P2 mod 8 = 0)%Z ->
    (P + 4 <= P2 \/ P2 + 16 <= P)%Z ->
    (lo + 736 <= q)%Z -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    (4096 + 164 <= bv_unsigned tp)%Z -> (bv_unsigned tp mod 4 = 0)%Z -> (bv_unsigned tp - 160 <= lo)%Z -> (ssp_guard + 8 <= lo)%Z -> (got_ssp + 8 <= lo)%Z ->
    (4096 <= A)%Z -> (A + cap + 2^41 < 2^63)%Z -> (cap + 2 <= 2^40)%Z ->
    (bv_unsigned tp - 160 <= A \/ A + Z.of_nat (length bs) <= bv_unsigned tp - 164)%Z ->
    (got_ssp + 8 <= A \/ A + Z.of_nat (length bs) <= got_ssp)%Z -> (ssp_guard + 8 <= A \/ A + Z.of_nat (length bs) <= ssp_guard)%Z ->
    (bv_unsigned tp - 160 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z ->
    (bv_unsigned tp - 160 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (WF [(P, P + 4); (P2, P2 + 16); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z) (X_chunk P P2 tp canary) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CHUNK) (wz (q + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF GC1 PC1 PL1 PA1 GC2 PC2 PL2 PA2 P12 DEEP NULT ERR GOT CAN TP TPAL TPLO GLO GOLO A4 AHI2 CAP40 DA1 DA2 DA3 DG1 DG2. unfx.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof (munch_refl (WF [(P, P + 4); (P2, P2 + 16); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_CHUNK 37 (q + 16) (Z_to_bv 8 37)); try eassumption; try reflexivity; try lia. intros m1 MI1. rd_chunk. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0H. lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. open_FX FXH. unfold FS in FSH.

    Ltac cerr P P2 tp canary :=
      lazymatch goal with PCa : rw_cells rsegs _ P [C4 ?pv], PCb : rw_cells rsegs _ P2 [C8 ?pa; C8 ?pb],
                          PCe : rw_cells rsegs _ (bv_unsigned tp - 164) [C4 ?e] |- _ =>
      eapply evt_mono;
      [ first [ eapply cont_err with (R := R_chunk P P2 tp canary pv pa pb e) (XP := fun r c => r <> PARSE_OK)
              | eapply tail_err with (R := R_chunk P P2 tp canary pv pa pb e) (XP := fun r c => r <> PARSE_OK) ];
        try eassumption; try rd_chunk; try (unfold PARSE_OK in *; lia);
        [ unfold R_chunk; repeat (split; [eassumption|]); eassumption
        | unfold rframe, R_chunk; intros mA mB (Q1 & Q2 & Q3 & Q4 & Q5) MUR WMR;
          split; [rf1 Q1 MUR WMR|]; split; [rf1 Q2 MUR WMR|]; split; [rf1 Q3 MUR WMR|]; split; [rf1 Q4 MUR WMR| rf1 Q5 MUR WMR] ]
      | intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [HRm HXP];
        unfold X_chunk; do 4 eexists; split; [exact HRm|]; let E := fresh in intros E; exfalso; exact (HXP E) ] end.

    rename F0H into F0p1. dcall (dir_x q lo S MB A len cap cur0 bs VOK) r1 c1 X1; [rd_chunk| reflexivity| |].
    2:{ exfalso; exact HXE. }
    try clear ERR; try clear PC1; try clear GOT; try clear CAN.
    unfold XX in X1. destruct X1 as (pv1 & e1 & PC1 & ERR & GOT & CAN & HXX).
    destruct (Z.eq_dec r1 PARSE_OK) as [->|NE]. 2:{ cerr P P2 tp canary. }
    destruct (HXX eq_refl) as (v & l & -> & VR & L1 & -> & C1L).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_chunk| reflexivity| lia| lia|]. open_FX FXH.

    rename F0H into F0p2. dcall (dir_L q lo S MB A len cap cur0 bs VOK) r2 c2 X2; [rd_chunk| reflexivity| |]. 2:{ exfalso; exact HXE. }
    try clear PC2. destruct X2 as (pa & pb & PC2 & -> & HXL).
    destruct (Z.eq_dec r2 PARSE_OK) as [->|NE]. 2:{ cerr P P2 tp canary. }
    destruct (HXL eq_refl) as (l2 & -> & L20 & -> & C2L & CRB).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_chunk| reflexivity| lia| lia|]. open_FX FXH.

    rename F0H into F0p3. dcall (dir_c q lo S MB A len cap cur0 bs VOK) r3 c3 X3; [rd_chunk| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r3 PARSE_OK) as [->|NE]. 2:{ cerr P P2 tp canary. }
    lazymatch goal with ERRh : rw_cells rsegs _ (bv_unsigned tp - 164) [C4 ?e] |- _ =>
    eapply evt_mono;
    [ eapply cont_end with (R := R_chunk P P2 tp canary (wz v) (wz (A + (cur0 + l))) (wz l2) e)
                           (XP := (fun r c => r = PARSE_OK -> cur0 + 1 <= c)%Z);
      try eassumption; try rd_chunk; try reflexivity; try (unfold PARSE_OK in *; lia);
      unfold R_chunk; repeat (split; [eassumption|]); eassumption
    | ] end.
    intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [HRm HXP].
    unfold X_chunk. do 4 eexists; split; [exact HRm|]. intros E. exists v. pose proof (HXP E). use_ok. repeat split; try reflexivity; lia.
  Qed.
End VFG3.
