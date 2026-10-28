(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Export Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Export Sj_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition A1_ENTRY : Z := 0xba324.
Definition A1_STACK : Z := 432.
Definition A1_MEMCPY_RA : Z := 0xba3c4.
Definition A1_TABLE : Z := 0x2a060.
Definition A1_GTOP : Z := 0x6ca000.
Definition A1_SHB : Z := 2147450880.

Lemma table_image_a : ro_bytes_b asegs A1_TABLE TABLE_BYTES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_at_a : forall m, mem_inv asegs m -> bytes_at asegs m A1_TABLE TABLE_BYTES.
Proof. intros m MI. apply table_at_g; [exact table_image_a| unfold A1_TABLE; lia| unfold A1_TABLE; lia| exact MI]. Qed.

Notation buf_read := (buf_read_g asegs).
Notation tbl_read := (tbl_read_g asegs).
Notation rw_cells_C8_read1 := (rw_cells_C8_read1_g asegs).
Notation env_ok := (env_ok_g A1_STACK A1_GTOP).
Notation a1_W := (s1_W_g 432).
Notation a1_post := (s1_post_g asegs 432).

Definition a1_shz (E : s1env) : Prop :=
  forall m' : mem, munch (a1_W E) (e_m0 E) m' -> wmono asegs (e_m0 E) m' ->
    shz m' (e_THIS E) 96 /\ shz m' (e_IDX E) (4 * (e_len E + 3)) /\ shz m' (e_BUF E) (e_len E + 8).

Definition frame_hi_a (E : s1env) (j296 j316 : list byte) (c320 : cell) : list cell :=
  [C8 (wz (e_BUF E)); CB 8 j296; C8 (wz (e_THIS E)); C4 (wz (e_len E)); CB 4 j316; c320; C4 (wz 0);
   C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition A1INV (E : s1env) (m1 : mem) (out : list Z) : Prop :=
  (exists j0 j8 j16 j24, rw_cells asegs m1 (bv_unsigned (e_sp E) + -432) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]) /\
  rw_cells asegs m1 (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] /\
  (exists j296 j316 j320, rw_cells asegs m1 (bv_unsigned (e_sp E) + -144) (frame_hi_a E j296 j316 (CB 4 j320))) /\
  (exists nsi nxt, rw_cells asegs m1 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E)))) /\
  (exists ws, u32arr asegs m1 (e_IDX E) ws /\ length ws = e_cap E /\ firstn (length out) ws = map wz out) /\
  bytes_at asegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
  mem_inv asegs m1 /\ munch (a1_W E) (e_m0 E) m1 /\ wmono asegs (e_m0 E) m1 /\
  stk asegs m1 (e_lo E) (bv_unsigned (e_sp E) + -432).

Notation A1ST E pc xra xt1 xt2 xa0 xa1 xa2 xa3 xs9 xs10 xs11 xt3 xt4 m :=
  (MS (mkR xra (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) (Z_to_bv 64 32) xt1 xt2
           (Z_to_bv 64 (e_IDX E)) (Z_to_bv 64 0) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_len E))
           (Z_to_bv 64 (bv_unsigned (e_sp E) + -400)) (Z_to_bv 64 34) (Z_to_bv 64 92)
           (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 (-64)) (Z_to_bv 64 244) (Z_to_bv 64 240) (Z_to_bv 64 30)
           xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 224) (Z_to_bv 64 160))
      (e_F E) (Z_to_bv 64 pc) (e_fc E) None m (seg_rom asegs)).

Lemma frlo_forget4 : forall m A c0 c1 c2 c3,
  rw_cells asegs m A [c0; c1; c2; c3] -> csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat ->
  exists j0 j8 j16 j24, rw_cells asegs m A [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24].
Proof.
  intros m A c0 c1 c2 c3 H E0 E1 E2 E3.
  pose proof (rw_cells_merge asegs m A [] [c0] [c1; c2; c3] H) as M. cbn [app cells_size cells_bytes] in M.
  rewrite E0, app_nil_r in M. cbn [Nat.add] in M.
  pose proof (rw_cells_merge asegs m A [CB 8 (cbytes c0)] [c1] [c2; c3] M) as M2. cbn [app cells_size cells_bytes] in M2.
  rewrite E1, app_nil_r in M2. cbn [Nat.add] in M2.
  pose proof (rw_cells_merge asegs m A [CB 8 (cbytes c0); CB 8 (cbytes c1)] [c2] [c3] M2) as M3. cbn [app cells_size cells_bytes] in M3.
  rewrite E2, app_nil_r in M3. cbn [Nat.add] in M3.
  pose proof (rw_cells_merge asegs m A [CB 8 (cbytes c0); CB 8 (cbytes c1); CB 8 (cbytes c2)] [c3] [] M3) as M4. cbn [app cells_size cells_bytes] in M4.
  rewrite E3, app_nil_r in M4. cbn [Nat.add] in M4.
  eexists _, _, _, _. exact M4.
Qed.

Ltac a1_open_inv H :=
  let j0 := fresh "j0" in let j8 := fresh "j8" in let j16 := fresh "j16" in let j24 := fresh "j24" in
  let nsi := fresh "nsi" in let nxt := fresh "nxt" in let ws := fresh "ws" in
  let j296 := fresh "j296" in let j316 := fresh "j316" in let j320 := fresh "j320" in
  destruct H as ((j0 & j8 & j16 & j24 & FRlo) & FRtb & (j296 & j316 & j320 & FRhi) & (nsi & nxt & PARSER) & (ws & IDXA & IDXL & IDXF) & BUFRO & MI & MU & WM & ST);
  unfold frame_hi_a in FRhi; unfold parser_cells in PARSER; unfold s1_W_g in MU; cbn [Z.opp] in MU;
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac a1_close_inv :=
  lazymatch goal with
  | |- A1INV _ _ _ =>
      split; [ eapply frlo_forget4; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity] | ];
      split; [eassumption|]; split; [eexists _, _, _; eassumption|];
      split; [eexists _, _; eassumption|];
      split; [eexists; split; [eassumption| split; eassumption]|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac a1_shz_sel SHZ k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with
      | MU : munch _ ?m0 m, WM : wmono _ ?m0 m |- _ => k (SHZ m MU WM)
      end
  end.
Ltac a1_shz_this SHZ x := a1_shz_sel SHZ ltac:(fun H => let n := fresh "SHRD" in pose proof (proj1 H x ltac:(lia)) as n).
Ltac a1_shz_idx SHZ x := a1_shz_sel SHZ ltac:(fun H => let n := fresh "SHRD" in pose proof (proj1 (proj2 H) x ltac:(lia)) as n).
Ltac a1_shz_buf SHZ x := a1_shz_sel SHZ ltac:(fun H => let n := fresh "SHRD" in pose proof (proj2 (proj2 H) x ltac:(lia)) as n).

Definition a1_postR (E : s1env) (st : s1st) : machine_state -> Prop := a1_post E (s1_code st) (s_out st).

Definition a1_for_stmt (E : s1env) (f : nat) : Prop :=
  forall (st : s1st) xt1 xt2 xa0 xa1 xs11 xt3 xt4 (m1 : mem),
    A1INV E m1 (s_out st) -> (0 <= s_idx st < e_len E)%Z -> (e_len E - s_idx st <= Z.of_nat f)%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z -> err_ok (s_err st) ->
    evt asegs (a1_postR E (scan_loop (e_bs E) f st))
      (A1ST E 0xba430 (Z_to_bv 64 (s_err st)) xt1 xt2 xa0 xa1 (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st))))
            (Z_to_bv 64 (Z.b2z (s_unclosed st))) (Z_to_bv 64 (s_idx st)) (Z_to_bv 64 (e_BUF E)) xs11 xt3 xt4 m1).
