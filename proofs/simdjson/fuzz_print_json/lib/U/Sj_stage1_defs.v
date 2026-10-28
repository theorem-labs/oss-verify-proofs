(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Export Sj_stage1_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition U1_ENTRY : Z := 0x41870.
Definition U1_STACK : Z := 432.
Definition U1_MEMCPY : Z := 0xcfe78.
Definition U1_TABLE : Z := 0x19da1.
Definition U1_GTOP : Z := 0x110000.

Lemma utable_image : ro_bytes_b usegs U1_TABLE TABLE_BYTES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma utable_at : forall m, mem_inv usegs m -> bytes_at usegs m U1_TABLE TABLE_BYTES.
Proof. intros m MI. apply table_at_g; [exact utable_image| unfold U1_TABLE; lia| unfold U1_TABLE; lia| exact MI]. Qed.

Notation ubuf_read := (buf_read_g usegs).
Notation utbl_read := (tbl_read_g usegs).
Notation urw_cells_C8_read1 := (rw_cells_C8_read1_g usegs).
Definition umemcpy_stmt : Prop := memcpy_stmt_g usegs U1_MEMCPY.
Notation u1_W := (s1_W_g 432).
Notation u1_post := (s1_post_g usegs 432).

Record env_ok_u (E : s1env) : Prop := mkEnvOkU {
  oku_base : env_ok_g U1_STACK U1_GTOP E;
  oku_buf : (0 < e_BUF E)%Z;
  oku_idx : (0 < e_IDX E)%Z;
  oku_align : (e_IDX E mod 4 = 0)%Z
}.

Definition uframe_hi (E : s1env) (nptr : word) (idxc err : Z) : list cell :=
  [C8 (wz (e_BUF E)); C8 nptr; C8 (wz (e_THIS E)); C4 (wz (e_len E)); C4 (wz idxc); C4 (wz err); C4 (wz 0);
   C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition U1INV (E : s1env) (m1 : mem) (out : list Z) (idxc err : Z) : Prop :=
  (exists j0 j8 j16 j24, rw_cells usegs m1 (bv_unsigned (e_sp E) + -432) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]) /\
  rw_cells usegs m1 (bv_unsigned (e_sp E) + -400) [CB 256 TABLE_BYTES] /\
  (exists nptr, rw_cells usegs m1 (bv_unsigned (e_sp E) + -144) (uframe_hi E nptr idxc err)) /\
  (exists nsi nxt, rw_cells usegs m1 (e_THIS E) (parser_cells E nsi nxt (wz (e_BUF E)) (wz (e_len E)))) /\
  (exists ws, u32arr usegs m1 (e_IDX E) ws /\ length ws = e_cap E /\ firstn (length out) ws = map wz out) /\
  bytes_at usegs m1 (e_BUF E) (padded_bytes (e_bs E)) /\
  mem_inv usegs m1 /\ munch (u1_W E) (e_m0 E) m1 /\ wmono usegs (e_m0 E) m1 /\
  stk usegs m1 (e_lo E) (bv_unsigned (e_sp E) + -432).

Notation U1ST E pc xra xa0 xa3 xa5 xs3 xs4 xt3 xt5 xt6 m :=
  (MS (mkR xra (Z_to_bv 64 (bv_unsigned (e_sp E) + -432)) (e_gp E) (e_tp E) (Z_to_bv 64 92) (Z_to_bv 64 31) (Z_to_bv 64 14)
           (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) xa0 (Z_to_bv 64 (e_IDX E))
           (Z_to_bv 64 (18446744073709551615 - (bv_unsigned (e_sp E) + -400))) xa3
           (Z_to_bv 64 (18446744073709551615 - e_BUF E)) xa5 (Z_to_bv 64 34) (Z_to_bv 64 (-4))
           (Z_to_bv 64 0) xs3 xs4 (Z_to_bv 64 (bv_unsigned (e_sp E) + -400))
           (Z_to_bv 64 240) (Z_to_bv 64 144) (Z_to_bv 64 244) (Z_to_bv 64 143) (Z_to_bv 64 245) (Z_to_bv 64 30)
           xt3 (Z_to_bv 64 (-65)) xt5 xt6)
      (e_F E) (Z_to_bv 64 pc) (e_fc E) None m (seg_rom usegs)).

Lemma frlo_forget4 : forall segs m A c0 c1 c2 c3,
  rw_cells segs m A [c0; c1; c2; c3] -> csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat ->
  exists j0 j8 j16 j24, rw_cells segs m A [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24].
Proof.
  intros segs m A c0 c1 c2 c3 H E0 E1 E2 E3.
  pose proof (rw_cells_merge segs m A [] [c0] [c1; c2; c3] H) as M. cbn [app cells_size cells_bytes] in M.
  rewrite E0, app_nil_r in M. cbn [Nat.add] in M.
  pose proof (rw_cells_merge segs m A [CB 8 (cbytes c0)] [c1] [c2; c3] M) as M2. cbn [app cells_size cells_bytes] in M2.
  rewrite E1, app_nil_r in M2. cbn [Nat.add] in M2.
  pose proof (rw_cells_merge segs m A [CB 8 (cbytes c0); CB 8 (cbytes c1)] [c2] [c3] M2) as M3. cbn [app cells_size cells_bytes] in M3.
  rewrite E2, app_nil_r in M3. cbn [Nat.add] in M3.
  pose proof (rw_cells_merge segs m A [CB 8 (cbytes c0); CB 8 (cbytes c1); CB 8 (cbytes c2)] [c3] [] M3) as M4. cbn [app cells_size cells_bytes] in M4.
  rewrite E3, app_nil_r in M4. cbn [Nat.add] in M4.
  eexists _, _, _, _. exact M4.
Qed.

Ltac u1_open_inv H :=
  let j0 := fresh "j0" in let j8 := fresh "j8" in let j16 := fresh "j16" in let j24 := fresh "j24" in
  let nsi := fresh "nsi" in let nxt := fresh "nxt" in let ws := fresh "ws" in let nptr := fresh "nptr" in
  destruct H as ((j0 & j8 & j16 & j24 & FRlo) & FRtb & (nptr & FRhi) & (nsi & nxt & PARSER) & (ws & IDXA & IDXL & IDXF) & BUFRO & MI & MU & WM & ST);
  unfold uframe_hi in FRhi; unfold parser_cells in PARSER; unfold s1_W_g in MU; cbn [Z.opp] in MU;
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac u1_close_inv :=
  lazymatch goal with
  | |- U1INV _ _ _ _ _ =>
      split; [ eapply frlo_forget4; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity] | ];
      split; [eassumption|]; split; [eexists; eassumption|];
      split; [eexists _, _; eassumption|];
      split; [eexists; split; [eassumption| split; eassumption]|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof. intros x H. apply zb_lxor_ones. lia. Qed.

Definition u1_postR (E : s1env) (st : s1st) : machine_state -> Prop := u1_post E (s1_code st) (s_out st).

Definition u1_for_stmt (E : s1env) (f : nat) : Prop :=
  forall (st : s1st) xra xa3 xa5 xt5 xt6 (m1 : mem),
    U1INV E m1 (s_out st) (s_idx st) (s_err st) -> (0 <= s_idx st < e_len E)%Z -> (e_len E - s_idx st <= Z.of_nat f)%Z ->
    (Z.of_nat (length (s_out st)) <= s_idx st)%Z -> err_ok (s_err st) ->
    evt usegs (u1_postR E (scan_loop (e_bs E) f st))
      (U1ST E 0x41968 xra (Z_to_bv 64 (e_IDX E + 4 * Z.of_nat (length (s_out st)))) xa3 xa5
            (Z_to_bv 64 (s_idx st)) (Z_to_bv 64 (e_len E)) (Z_to_bv 64 (Z.b2z (s_unclosed st))) xt5 xt6 m1).

Lemma align4_ok : forall A n, (A mod 4 = 0)%Z -> (0 <= A + 4 * n)%Z -> Z.land (A + 4 * n) 3 = 0%Z.
Proof.
  intros A n HA H0. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
  rewrite Z.add_mod by lia. rewrite HA. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.
