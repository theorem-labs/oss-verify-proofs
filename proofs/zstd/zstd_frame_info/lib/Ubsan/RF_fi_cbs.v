(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg RF_fi_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(* [comment removed for export] *)
Definition cbs_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (B : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (r a1' a2' a3' a4' a5' : word) (w0 w1 w2 : list byte) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(B, B + 12)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' B [CB 4 w0; CB 4 w1; CB 4 w2].

Definition cbs_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z) (B : Z) (j0 j1 j2 : list byte),
    buf_at m S bl ->
    rw_cells usegs m B [CB 4 j0; CB 4 j1; CB 4 j2] ->
    S + zlen bl <= B \/ B + 12 <= S ->
    mem_inv usegs m -> 0 < S -> 0 < B -> B mod 4 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) -> a2 = Z_to_bv 64 B ->
    evt usegs (cbs_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PFI_CBS) fc None m (seg_rom usegs)).

Lemma cbs_proof : cbs_stmt.
Proof.
  intros until j2. intros BUF BP SEP MI S0 B0 BA -> -> ->. unfold PFI_CBS.
  pose proof (buf_at_bound _ _ _ BUF) as BB. pose proof (rw_cells_bound _ _ _ _ BP) as PB. cbn [cells_size csize Nat.add] in PB.
  pose proof (munch_refl [(B, B + 12)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00K0>10640767904.4610644848415.4914202106942.5114204194750.4815534906498.6416077671799.4621920002621.4721922089021.5028209084189.6828209084189.6928463071855.5231819521783.6942002707333.6843929283714.6444614246156.5544614246285.5445452174881.65477762999.69  50038540763.6853459164111.6859316643886.6959576979761.5459576979888.5559588178609.6559588178610.6459776615842.6864589843822.6900000300600900<00=00H00K00N00R00V00W00^00b00c00d00e00f00m01401801?01@01A01B01C01J01QS1KS1KS1KS1KFS3SEP2BB2PBS1KS1KS2PBS2PBSS2PB2HBS2PBFSSFS2PB2HBS2PB2HBS2PBS2PB2HBSSSSS2PB2HBS2PB2HB".
if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    zstep. zstep. if_cases U2; zify_cond U2; [exfalso; lia|].
    zstep. if_cases U3; zify_cond U3; [exfalso; lia|].
    zstep. zstep. if_cases U4; zify_cond U4; [exfalso; apply U4; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact BA|].
    pose proof (buf_read m S bl 0 BUF ltac:(lia)) as RD0.
    pose proof (buf_read m S bl 1 BUF ltac:(lia)) as RD1.
    pose proof (buf_read m S bl 2 BUF ltac:(lia)) as RD2.
    destruct (buf_nth m S bl 0 BUF ltac:(lia)) as [_ R0].
    destruct (buf_nth m S bl 1 BUF ltac:(lia)) as [_ R1].
    destruct (buf_nth m S bl 2 BUF ltac:(lia)) as [_ R2].
    replace (wa (S + 0)) with (wa S) in RD0 by (unfold wa; f_equal; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.     (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ ?m1 B [C4 ?a; C4 ?b; C4 ?c] |- _ =>
      apply (rw_cells_reshape m1 B _ [CB 4 (le4 a); CB 4 (le4 b); CB 4 (le4 c)]) in H;
        [| cbn [cells_wf cell_wf]; rewrite !length_le4; repeat split; reflexivity | reflexivity | reflexivity] end.
    zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *) zstep. finish; eassumption.
    + zstep. zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *) zstep. zstep. finish; eassumption.
      * (* [comment removed for export] *) zstep. zstep. finish; eassumption.
  - (* [comment removed for export] *)
    zstep. zstep. finish; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
