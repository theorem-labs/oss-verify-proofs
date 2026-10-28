(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_scanner_get_token H_vfmatch_A H_vfmatch_B H_vfmatch_C H_vfmatch_F H_vfmatch_G1 H_match.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation FMT_CRLF2 := 0x10541%Z.
Definition fb_crlf2 : list byte := map (Z_to_bv 8) [37; 99; 0].
Lemma fb_crlf2_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_CRLF2 fb_crlf2.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m FMT_CRLF2 fb_crlf2 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Ltac rd_crlf2 := rdfmt fb_crlf2_at constr:(0x10541%Z).

Section VFG.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs).
  Notation WF Wx := ((lo, q) :: (S + 8, S + 16) :: Wx)%Z.
  Notation vpost := (vpost q lo S MB A len cap cur0 bs).

  #[using="VOK"] Theorem vf_crlf2 : forall (G : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m -> (q + 16 <= G <= q + 64)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF [])
                 (fun m' r cur' => True /\ (r = PARSE_OK -> cur0 + 1 <= cur')%Z) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CRLF2) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF GR. unfx.
    pose proof (munch_refl (WF []) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_CRLF2 37 G (Z_to_bv 8 37)); try eassumption; try reflexivity; try lia.
      intros m1 MI1. rd_crlf2. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0P. lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. open_FX FXH. clear FR0. destruct F0P as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex. unfold FS in FSH.
    dcall (dir_c q lo S MB A len cap cur0 bs VOK) r1 c1 X1; [rd_crlf2| reflexivity| |].
    -   destruct (Z.eq_dec r1 PARSE_OK) as [->|NE].
      + eapply cont_end with (R := fun _ => True); try eassumption; try rd_crlf2; try reflexivity; try exact I; try (unfold PARSE_OK in *; lia).
      + eapply cont_err with (R := fun _ => True); try eassumption; try rd_crlf2; try exact I; try (unfold PARSE_OK in *; lia).
        unfold rframe; intros; exact I.
    -   exfalso; exact HXE.
  Qed.
End VFG.

Section VM.
Context {HCEIL : HasCeiling}.
  Variables (qm lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis MOK : vf_ok (qm + -64) lo S MB A len cap cur0 bs.
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs).
  Notation WM Wx := ((lo, qm) :: (S + 8, S + 16) :: Wx)%Z.

  #[using="MOK"] Theorem match_crlf2 : forall ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo qm -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    evt rsegs (mpost qm lo S MB A len cap cur0 bs ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WM []) (fun m' r cur' => True /\ (r = PARSE_OK -> cur0 + 1 <= cur')%Z) m)
      (MS (mkR ra (wz qm) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CRLF2) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz match_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof MOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF. unfx.
    eapply (match_shell qm lo S MB A len cap cur0 bs MOK); [exact ST| exact MI| cbn; exact I|].
    intros m1 ST1 MI1 MU1 WM1 FR0 G1 G2 G3 G4.
    transport_after_call rsegs m m1 MU1 WM1.
    eapply (vf_crlf2 (qm + -64) lo S MB A len cap cur0 bs MOK); try eassumption; lia.
  Qed.
End VM.
