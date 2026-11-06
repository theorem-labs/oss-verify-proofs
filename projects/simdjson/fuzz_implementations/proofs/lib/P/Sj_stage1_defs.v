(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Sj_stage1_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition S1_ENTRY : Z := 0x43034.
Definition S1_STACK : Z := 416.
Definition S1_MEMCPY : Z := 0xca58c.
Definition S1_TABLE : Z := 0x1ab19.

Lemma table_image : ro_bytes_b psegs S1_TABLE TABLE_BYTES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_at : forall m, mem_inv psegs m -> bytes_at psegs m S1_TABLE TABLE_BYTES.
Proof. intros m MI. apply table_at_g; [exact table_image| unfold S1_TABLE; lia| unfold S1_TABLE; lia| exact MI]. Qed.

Notation buf_read := (buf_read_g psegs).
Notation tbl_read := (tbl_read_g psegs).
Notation rw_cells_C8_read1 := (rw_cells_C8_read1_g psegs).
Notation memcpy_post := (memcpy_post_g psegs).
Definition memcpy_stmt : Prop := memcpy_stmt_g psegs S1_MEMCPY.
Definition S1_GTOP : Z := 0x10b000.
Notation env_ok := (env_ok_g S1_STACK S1_GTOP).
Notation s1_W := (s1_W_g 416).
Notation s1_post := (s1_post_g psegs 416).

Definition frame_hi (E : s1env) (j280 j300 : list byte) : list cell :=
  [C8 (wz (e_BUF E)); CB 8 j280; C8 (wz (e_THIS E)); C4 (wz (e_len E)); CB 4 j300; C4 (wz 0); C4 (wz 0);
   C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition S1INV (E : s1env) (m1 : mem) (out : list Z) : Prop :=
  (exists j0 j8, rw_cells psegs m1 (bv_unsigned (e_sp E) + -416) [CB 8 j0; CB 8 j8]) /\
  rw_cells psegs m1 (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] /\
  (exists j280 j300, rw_cells psegs m1 (bv_unsigned (e_sp E) + -144) (frame_hi E j280 j300)) /\
  (exists nsi nxt, rw_cells psegs m1 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E)))) /\
  (exists ws, u32arr psegs m1 (e_IDX E) ws /\ length ws = e_cap E /\ firstn (length out) ws = map wz out) /\
  bytes_at psegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
  mem_inv psegs m1 /\ munch (s1_W E) (e_m0 E) m1 /\ wmono psegs (e_m0 E) m1 /\
  stk psegs m1 (e_lo E) (bv_unsigned (e_sp E) + -416).

Notation S1ST E pc xra xt2 xa2 xa5 xa6 xs10 xs11 xt3 xt4 xt5 xt6 m :=
  (MS (mkR xra (Z_to_bv 64 (bv_unsigned (e_sp E) + -416)) (e_gp E) (e_tp E) (Z_to_bv 64 92) (Z_to_bv 64 32) xt2
           (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 (e_IDX E)) xa2
           (Z_to_bv 64 (e_len E + -1)) (Z_to_bv 64 (e_len E + -2)) xa5 xa6 (Z_to_bv 64 34)
           (Z_to_bv 64 0) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 (bv_unsigned (e_sp E) + -400))
           (Z_to_bv 64 160) (Z_to_bv 64 (-64)) (Z_to_bv 64 244) (Z_to_bv 64 240) (Z_to_bv 64 30)
           xs10 xs11 xt3 xt4 xt5 xt6)
      (e_F E) (Z_to_bv 64 pc) (e_fc E) None m (seg_rom psegs)).

Ltac s1_open_inv H :=
  let j0 := fresh "j0" in let j8 := fresh "j8" in let nsi := fresh "nsi" in let nxt := fresh "nxt" in let ws := fresh "ws" in
  let j280 := fresh "j280" in let j300 := fresh "j300" in
  destruct H as ((j0 & j8 & FRlo) & FRtb & (j280 & j300 & FRhi) & (nsi & nxt & PARSER) & (ws & IDXA & IDXL & IDXF) & BUFRO & MI & MU & WM & ST);
  unfold frame_hi in FRhi; unfold parser_cells in PARSER; unfold s1_W_g in MU; cbn [Z.opp] in MU;
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac s1_close_inv :=
  lazymatch goal with
  | |- S1INV _ _ _ =>
      split; [ eapply frlo_forget; [eassumption | reflexivity | reflexivity] | ];
      split; [eassumption|]; split; [eexists _, _; eassumption|];
      split; [eexists _, _; eassumption|];
      split; [eexists; split; [eassumption| split; eassumption]|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Definition s1_postR (E : s1env) (st : s1st) : machine_state -> Prop := s1_post E (s1_code st) (s_out st).

Definition s1_for_stmt (E : s1env) (f : nat) : Prop :=
  forall (st : s1st) xra xt2 xs11 xt3 xt4 xt5 xt6 (m1 : mem),
    S1INV E m1 (s_out st) -> (0 <= s_idx st < e_len E)%Z -> (e_len E - s_idx st <= Z.of_nat f)%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z ->
    evt psegs (s1_postR E (scan_loop (e_bs E) f st))
      (S1ST E 0x430f4 xra xt2 (Z_to_bv 64 (s_err st)) (Z_to_bv 64 (Z.b2z (s_unclosed st)))
            (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) (Z_to_bv 64 (s_idx st)) xs11 xt3 xt4 xt5 xt6 m1).

