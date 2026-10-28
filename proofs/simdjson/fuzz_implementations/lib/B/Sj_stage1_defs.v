(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Export Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Export Sj_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition B1_ENTRY : Z := 0xc1f1c.
Definition B1_STACK : Z := 448.
Definition B1_MEMCPY_RA : Z := 0xc1fbc.
Definition B1_TABLE : Z := 0x2cde0.
Definition B1_GTOP : Z := 0x6e0000.

Lemma table_image_b : ro_bytes_b bsegs B1_TABLE TABLE_BYTES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_at_b : forall m, mem_inv bsegs m -> bytes_at bsegs m B1_TABLE TABLE_BYTES.
Proof. intros m MI. apply table_at_g; [exact table_image_b| unfold B1_TABLE; lia| unfold B1_TABLE; lia| exact MI]. Qed.

Notation buf_read := (buf_read_g bsegs).
Notation tbl_read := (tbl_read_g bsegs).
Notation rw_cells_C8_read1 := (rw_cells_C8_read1_g bsegs).
Notation b1_W := (s1_W_g 448).
Notation b1_post := (s1_post_g bsegs 448).

Record env_ok_b (E : s1env) : Prop := mkEnvOkB {
  okb_base : env_ok_g B1_STACK B1_GTOP E;
  okb_buf : (0 < e_BUF E)%Z;
  okb_idx : (0 < e_IDX E)%Z;
  okb_align : (e_IDX E mod 4 = 0)%Z
}.

Definition b1_shz (E : s1env) : Prop :=
  forall m' : mem, munch (b1_W E) (e_m0 E) m' -> wmono bsegs (e_m0 E) m' ->
    shz m' (e_THIS E) 96 /\ shz m' (e_IDX E) (4 * (e_len E + 3)) /\ shz m' (e_BUF E) (e_len E + 8).

Definition bframe_hi (E : s1env) (nptr : word) (idxc err : Z) : list cell :=
  [C8 (wz (e_BUF E)); C8 nptr; C8 (wz (e_THIS E)); C4 (wz (e_len E)); C4 (wz idxc); C4 (wz err); C4 (wz 0);
   C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition B1INV (E : s1env) (m1 : mem) (out : list Z) (idxc err : Z) : Prop :=
  (exists j0 j16 j24 j32 j40, rw_cells bsegs m1 (bv_unsigned (e_sp E) + -448) [CB 16 j0; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40]) /\
  rw_cells bsegs m1 (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] /\
  rw_cells bsegs m1 (bv_unsigned (e_sp E) + -144) (bframe_hi E (wz (e_IDX E + 4 * Z.of_nat (length out))) idxc err) /\
  (exists nsi nxt, rw_cells bsegs m1 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E)))) /\
  (exists ws, u32arr bsegs m1 (e_IDX E) ws /\ length ws = e_cap E /\ firstn (length out) ws = map wz out) /\
  bytes_at bsegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
  mem_inv bsegs m1 /\ munch (b1_W E) (e_m0 E) m1 /\ wmono bsegs (e_m0 E) m1 /\
  stk bsegs m1 (e_lo E) (bv_unsigned (e_sp E) + -448).

Notation B1ST E pc xa1 xa2 xa3 xs3 xs5 xs6 xt5 xt6 m :=
  (MS (mkR (Z_to_bv 64 245) (Z_to_bv 64 (bv_unsigned (e_sp E) + -448)) (e_gp E) (e_tp E) (Z_to_bv 64 92) (Z_to_bv 64 31) (Z_to_bv 64 14)
           (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 0) (Z_to_bv 64 (e_IDX E)) xa1 xa2 xa3
           (Z_to_bv 64 (bv_unsigned (e_sp E) + -400)) (Z_to_bv 64 (18446744073709551615 - e_BUF E)) (Z_to_bv 64 34) (Z_to_bv 64 (-4))
           (Z_to_bv 64 (e_THIS E)) xs3 (Z_to_bv 64 2147450880) xs5 xs6
           (Z_to_bv 64 240) (e_s8 E) (Z_to_bv 64 244) (Z_to_bv 64 (18446744073709551615 - (bv_unsigned (e_sp E) + -400))) (Z_to_bv 64 143)
           (Z_to_bv 64 30) (Z_to_bv 64 (-65)) xt5 xt6)
      (e_F E) (Z_to_bv 64 pc) (e_fc E) None m (seg_rom bsegs)).

Lemma frlo_forget5 : forall m A c0 c1 c2 c3 c4,
  rw_cells bsegs m A [c0; c1; c2; c3; c4] -> csize c0 = 16%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat -> csize c4 = 8%nat ->
  exists j0 j16 j24 j32 j40, rw_cells bsegs m A [CB 16 j0; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40].
Proof.
  intros m A c0 c1 c2 c3 c4 H E0 E1 E2 E3 E4.
  pose proof (rw_cells_merge bsegs m A [] [c0] [c1; c2; c3; c4] H) as M. cbn [app cells_size cells_bytes] in M.
  rewrite E0, app_nil_r in M. cbn [Nat.add] in M.
  pose proof (rw_cells_merge bsegs m A [CB 16 (cbytes c0)] [c1] [c2; c3; c4] M) as M2. cbn [app cells_size cells_bytes] in M2.
  rewrite E1, app_nil_r in M2. cbn [Nat.add] in M2.
  pose proof (rw_cells_merge bsegs m A [CB 16 (cbytes c0); CB 8 (cbytes c1)] [c2] [c3; c4] M2) as M3. cbn [app cells_size cells_bytes] in M3.
  rewrite E2, app_nil_r in M3. cbn [Nat.add] in M3.
  pose proof (rw_cells_merge bsegs m A [CB 16 (cbytes c0); CB 8 (cbytes c1); CB 8 (cbytes c2)] [c3] [c4] M3) as M4. cbn [app cells_size cells_bytes] in M4.
  rewrite E3, app_nil_r in M4. cbn [Nat.add] in M4.
  pose proof (rw_cells_merge bsegs m A [CB 16 (cbytes c0); CB 8 (cbytes c1); CB 8 (cbytes c2); CB 8 (cbytes c3)] [c4] [] M4) as M5. cbn [app cells_size cells_bytes] in M5.
  rewrite E4, app_nil_r in M5. cbn [Nat.add] in M5.
  eexists _, _, _, _, _. exact M5.
Qed.

Ltac b1_open_inv H :=
  let j0 := fresh "j0" in let j16 := fresh "j16" in let j24 := fresh "j24" in let j32 := fresh "j32" in let j40 := fresh "j40" in
  let nsi := fresh "nsi" in let nxt := fresh "nxt" in let ws := fresh "ws" in
  destruct H as ((j0 & j16 & j24 & j32 & j40 & FRlo) & FRtb & FRhi & (nsi & nxt & PARSER) & (ws & IDXA & IDXL & IDXF) & BUFRO & MI & MU & WM & ST);
  unfold bframe_hi in FRhi; unfold parser_cells in PARSER; unfold s1_W_g in MU; cbn [Z.opp] in MU;
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac b1_close_inv :=
  lazymatch goal with
  | |- B1INV _ _ _ _ _ =>
      split; [ eapply frlo_forget5; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [eexists _, _; eassumption|];
      split; [eexists; split; [eassumption| split; eassumption]|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac b1_shz_sel SHZ k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with
      | MU : munch _ ?m0 m, WM : wmono _ ?m0 m |- _ => k (SHZ m MU WM)
      end
  end.
Ltac b1_shz_this SHZ x := b1_shz_sel SHZ ltac:(fun H => let n := fresh "SHRD" in pose proof (proj1 H x ltac:(lia)) as n).
Ltac b1_shz_idx SHZ x := b1_shz_sel SHZ ltac:(fun H => let n := fresh "SHRD" in pose proof (proj1 (proj2 H) x ltac:(lia)) as n).
Ltac b1_shz_buf SHZ x := b1_shz_sel SHZ ltac:(fun H => let n := fresh "SHRD" in pose proof (proj2 (proj2 H) x ltac:(lia)) as n).

Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof. intros x H. apply zb_lxor_ones. lia. Qed.

Definition b1_postR (E : s1env) (st : s1st) : machine_state -> Prop := b1_post E (s1_code st) (s_out st).

Lemma align4_ok : forall A n, (A mod 4 = 0)%Z -> (0 <= A + 4 * n)%Z -> Z.land (A + 4 * n) 3 = 0%Z.
Proof.
  intros A n HA H0. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
  rewrite Z.add_mod by lia. rewrite HA. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.
