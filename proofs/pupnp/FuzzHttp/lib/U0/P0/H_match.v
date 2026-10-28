(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_scanner_get_token H_vfmatch_A H_vfmatch_B H_vfmatch_C H_vfmatch_F H_vfmatch_G1 H_vfmatch_G2 H_vfmatch_G3.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition match_entry := 0x14c14%Z.

Section VM.
Context {HCEIL : HasCeiling}.

  Variables (qm lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis MOK : vf_ok (qm + -64) lo S MB A len cap cur0 bs.

  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs).
  Notation WM Wx := ((lo, qm) :: (S + 8, S + 16) :: Wx)%Z.

  Definition mpost (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (W : list ivl) (X : mem -> Z -> Z -> Prop) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (r cur' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo qm
      /\ SCc m' cur' /\ MBc m' /\ BUFc m'
      /\ (0 <= r <= 5)%Z /\ (0 <= cur' <= len)%Z
      /\ (r = PARSE_OK -> cur0 <= cur')%Z /\ (r <> PARSE_OK -> cur' = cur0)
      /\ X m' r cur'.

  #[using="MOK"] Lemma match_shell : forall (Wx : list ivl) (X : mem -> Z -> Z -> Prop) (fmt : Z)
      ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> disjoint_from Wx (qm + -64) 64 ->
    (forall m1,
       stk rsegs m1 lo (qm + -64) -> mem_inv rsegs m1 -> munch [(qm + -64, qm)]%Z m m1 -> wmono rsegs m m1 ->
       rw_cells rsegs m1 (qm + -64) [C8 (wz (qm + -64 + 16)); C8 ra] ->
       rw_cells rsegs m1 (qm + -64 + 16) [C8 a2] -> rw_cells rsegs m1 (qm + -64 + 16 + 8) [C8 a3] ->
       rw_cells rsegs m1 (qm + -64 + 16 + 8 + 8) [C8 a4] -> rw_cells rsegs m1 (qm + -24) [C8 a5; C8 a6; C8 a7] ->
       evt rsegs (vpost (qm + -64) lo S MB A len cap cur0 bs (wz 0x14c40) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    ((lo, qm + -64) :: (S + 8, S + 16) :: Wx)%Z X m1)
         (MS (mkR (wz 0x14c40) (wz (qm + -64)) gp tp t0 t1 t2 s0 s1 (wz S) (wz fmt) (wz (qm + -64 + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz vfmatch_entry) fc None m1 (seg_rom rsegs))) ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM Wx) X m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz fmt) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI DJ BODY. unfold match_entry.
    pose proof (munch_refl (WM Wx) m) as MU. pose proof (munch_refl [(qm + -64, qm)]%Z m) as MU0. pose proof (wmono_refl rsegs m) as WMo.
    assert (E : bv_unsigned (Z_to_bv 64 qm) = qm) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 64%nat ST. rewrite !E in *.
    do 10 sstep. zstep.
    replace (Z_to_bv 64 (qm + -48)) with (Z_to_bv 64 (qm + -64 + 16)) by (f_equal; lia).
    replace (Z_to_bv 64 (qm + -48)) with (Z_to_bv 64 (qm + -64 + 16)) in FR by (f_equal; lia).
    pose proof FR as FRc.
    split_chunk FRc 2%nat FR0 R1. split_chunk R1 1%nat G1 R2. split_chunk R2 1%nat G2 R3. split_chunk R3 1%nat G3 G4.
    replace (qm + -48)%Z with (qm + -64 + 16)%Z in G1 by lia.
    replace (qm + -40)%Z with (qm + -64 + 16 + 8)%Z in G2 by lia.
    replace (qm + -32)%Z with (qm + -64 + 16 + 8 + 8)%Z in G3 by lia.
    eapply evt_cut. { eapply BODY; try eassumption. }
    clear BODY FR0 G1 G2 G3 G4 MU0.
    intros ms' V. unfold vpost in V. destruct V as (r & cur' & V). destruct_exs V.
    destruct V as (E1 & MUc & WMc & MI2 & ST2 & SC2 & MBC2 & BUF2 & HR & HC & HOK & HNOK & HX). subst ms'.
    lazymatch type of MUc with munch _ ?ma ?mb =>
      pose proof (rw_cells_transport rsegs _ ma mb _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; split; [lia| split; [lia| exact DJ]])) as FR';
      assert (MU' : munch (WM Wx) m mb)
        by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc];
            unfold sub_fp; cbn [outside]; intros xo (X1 & X2 & X3); repeat split; try lia; exact X3);
      pose proof (wmono_trans rsegs _ _ _ WMo WMc) as WM'
    end.
    clear FR MU WMo MUc WMc ST MI. rename MU' into MU. rename WM' into WMo.
    replace (ret_pc (Z_to_bv 64 85056)) with (Z_to_bv 64 85056) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep.
    release_frame FR' ST2 qm.
    zstep. apply evt_done. unfold mpost. exists r, cur'. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [assumption|]). exact HX.
  Qed.

  #[using="MOK"] Theorem match_crlf : forall ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM []) (fun m' r cur' => True /\ (r = PARSE_OK -> cur0 + 1 <= cur')%Z) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz 0x102ea) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF. unfx.
    eapply match_shell; [exact ST| exact MI| cbn; exact I|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_crlf (qm + -64) lo S MB A len cap cur0 bs MOK); try eassumption; lia.
  Qed.

  #[using="MOK"] Theorem match_hdr : forall (P1 : Z) (pw1 pw2 : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (qm <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM [(P1, P1 + 16)]%Z) (X_hdr A len cur0 P1) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz 0x102e5) (wz P1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF PC1 PL1 PA1. unfx.
    eapply match_shell; [exact ST| exact MI| cbn; lia|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_hdr (qm + -64) lo S MB A len cap cur0 bs MOK P1); try eassumption; lia.
  Qed.

  #[using="MOK"] Theorem match_resp : forall (P1 : Z) (pw1 pw2 : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (qm <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM [(P1, P1 + 16)]%Z) (X_resp A len cur0 bs P1) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz 0x10646) (wz P1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF PC1 PL1 PA1. unfx.
    eapply match_shell; [exact ST| exact MI| cbn; lia|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_resp (qm + -64) lo S MB A len cap cur0 bs MOK P1); try eassumption; lia.
  Qed.

  #[using="MOK"] Theorem match_req09 : forall (P1 P2 : Z) (pw1 pw2 pw3 pw4 : word) ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (qm <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    rw_cells rsegs m P2 [C8 pw3; C8 pw4] -> (qm <= P2 /\ P2 + 16 <= MB)%Z -> (P2 mod 8 = 0)%Z -> (P1 + 16 <= P2 \/ P2 + 16 <= P1)%Z ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM [(P1, P1 + 16); (P2, P2 + 16)]%Z) (X_req09 A len cur0 P1 P2) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz 0x10331) (wz P1) (wz P2) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF PC1 PL1 PA1 PC2 PL2 PA2 P12. unfx.
    eapply match_shell; [exact ST| exact MI| cbn; lia|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_req09 (qm + -64) lo S MB A len cap cur0 bs MOK P1 P2); try eassumption; lia.
  Qed.

  #[using="MOK"] Theorem match_req : forall (P1 P2 P3 : Z) (pw1 pw2 pw3 pw4 pw5 pw6 : word) ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (qm <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    rw_cells rsegs m P2 [C8 pw3; C8 pw4] -> (qm <= P2 /\ P2 + 16 <= MB)%Z -> (P2 mod 8 = 0)%Z ->
    rw_cells rsegs m P3 [C8 pw5; C8 pw6] -> (qm <= P3 /\ P3 + 16 <= MB)%Z -> (P3 mod 8 = 0)%Z ->
    (P1 + 16 <= P2 \/ P2 + 16 <= P1)%Z -> (P1 + 16 <= P3 \/ P3 + 16 <= P1)%Z -> (P2 + 16 <= P3 \/ P3 + 16 <= P2)%Z ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)]%Z)
                 (X_req A len cur0 bs P1 P2 P3) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz 0x10423) (wz P1) (wz P2) (wz P3) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF PC1 PL1 PA1 PC2 PL2 PA2 PC3 PL3 PA3 P12 P13 P23. unfx.
    eapply match_shell; [exact ST| exact MI| cbn; lia|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_req (qm + -64) lo S MB A len cap cur0 bs MOK P1 P2 P3); try eassumption; lia.
  Qed.

  #[using="MOK"] Theorem match_chunk : forall (P P2 : Z) (pv pw1 pw2 errv canary : word) ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m P [C4 pv] -> (qm <= P /\ P + 4 <= MB)%Z -> (P mod 4 = 0)%Z ->
    rw_cells rsegs m P2 [C8 pw1; C8 pw2] -> (qm <= P2 /\ P2 + 16 <= MB)%Z -> (P2 mod 8 = 0)%Z -> (P + 4 <= P2 \/ P2 + 16 <= P)%Z ->
    (lo + 800 <= qm)%Z -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    (4096 + 164 <= bv_unsigned tp)%Z -> (bv_unsigned tp mod 4 = 0)%Z -> (bv_unsigned tp - 160 <= lo)%Z -> (ssp_guard + 8 <= lo)%Z -> (got_ssp + 8 <= lo)%Z ->
    (4096 <= A)%Z -> (A + cap + 2^41 < 2^63)%Z -> (cap + 2 <= 2^40)%Z ->
    (bv_unsigned tp - 160 <= A \/ A + Z.of_nat (length bs) <= bv_unsigned tp - 164)%Z ->
    (got_ssp + 8 <= A \/ A + Z.of_nat (length bs) <= got_ssp)%Z -> (ssp_guard + 8 <= A \/ A + Z.of_nat (length bs) <= ssp_guard)%Z ->
    (bv_unsigned tp - 160 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z ->
    (bv_unsigned tp - 160 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
    evt rsegs (mpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (WM [(P, P + 4); (P2, P2 + 16); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z) (X_chunk cur0 P P2 tp canary) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz 0x1035b) (wz P) (wz P2) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF PC1 PL1 PA1 PC2 PL2 PA2 P12 DEEP NULT ERR GOT CAN TP TPA TPLO GLO GOLO A4 AHI2 CAP40 DA1 DA2 DA3 DG1 DG2. unfx.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    eapply match_shell; [exact ST| exact MI| cbn; lia|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_chunk (qm + -64) lo S MB A len cap cur0 bs MOK P P2); try eassumption; lia.
  Qed.
End VM.
