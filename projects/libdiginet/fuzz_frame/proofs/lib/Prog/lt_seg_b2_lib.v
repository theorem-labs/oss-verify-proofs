(* Definitions, facts and tactics for the walk of fuzz_frame's LLVMFuzzerTestOneInput from 0x12d04
   (lt_seg_b2.v): the post of the walk, the cells of the struct spec_frame w at sp while the inlined
   spec_read_frame (fuzz/spec.h:199-223) fills it, the register values of its byte loads and the
   codes of the libdiginet model fr_code.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_parse_c check_parse_refusal_c
  check_parse_fields_c FrameBytes.
Import ListNotations.
Open Scope Z_scope.

(** * The post of the walk *)

Definition b2_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (buf : Z) (b : list byte) (x1 x2 x3 x4 : word) : machine_state -> Prop :=
  fun ms' =>
         (fr_code b = 0 /\
          exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12e58) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' sp a1' a2' a3' a4' a5' a6'
                          a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13058) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            bytes_at rsegs m' buf b /\
            ro_cells rsegs m' (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) /\
            ro_cells rsegs m' (bv_unsigned sp) (spec_cells buf b) /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]) \/
         (exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12e84) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' (Z_to_bv 64 buf) a1' a2' a3'
                          a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x148ac) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]).

(** * The cells of w *)

(* The 80 zero bytes that memset leaves at w, cut at the fields of struct spec_frame. *)
Definition w0_cells : list cell :=
  [ C4 (Z_to_bv 64 0); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
    C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0);
    C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (b8 0); C1 (b8 0); CB 6 (repeat (b8 0) 6);
    C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 6 (repeat (b8 0) 6) ].

(* w after the stores of the fields (0x12ddc-0x12e0c); v is the body_sum cell, stored at 0x12e30. *)
Definition w_cells (buf : Z) (b : list byte) (v : word) : list cell :=
  [ C4 (Z_to_bv 64 0); CB 4 (repeat (b8 0) 4);
    C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (buf + 6));
    C2 (Z_to_bv 64 (fr_ethertype b)); C2 (Z_to_bv 64 (fr_numbytes b));
    C2 (Z_to_bv 64 (fr_sum b)); C2 (Z_to_bv 64 (fr_retry b));
    C4 (Z_to_bv 64 (fr_send b)); C4 (Z_to_bv 64 (fr_ack b));
    C1 (nth 28 b (b8 0)); C1 (nth 29 b (b8 0)); CB 6 (repeat (b8 0) 6);
    C8 (Z_to_bv 64 (buf + 30)); C8 (Z_to_bv 64 (fr_body_len b)); C8 (Z_to_bv 64 (fr_pad_len b));
    C2 v; CB 6 (repeat (b8 0) 6) ].

Lemma w0_shape : forall m A, rw_cells rsegs m A [CB 80 (repeat (b8 0) 80)] -> rw_cells rsegs m A w0_cells.
Proof.
  intros m A [[Hwf Hb] Hw]. split; [split|].
  - vm_compute. repeat split.
  - replace (cells_bytes w0_cells) with (repeat (b8 0) 80) by (vm_compute; reflexivity).
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - exact Hw.
Qed.

Lemma rw_hd : forall m A c cs, rw_cells rsegs m A (c :: cs) -> ro_cells rsegs m A [c].
Proof.
  intros m A c cs [[Hwf Hb] _]. cbn [cells_wf] in Hwf. destruct Hwf as [Hc _]. split.
  - cbn [cells_wf]. split; [exact Hc | exact I].
  - cbn [cells_bytes] in *. rewrite app_nil_r. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma rw_ro : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs H. exact (proj1 H). Qed.

(* The low 16 bits of a word are its two little-endian bytes. *)
Lemma le2_mod16 : forall z, le2 (Z_to_bv 64 z) = le2 (Z_to_bv 64 (z mod 2^16)).
Proof.
  intros z. unfold le2. rewrite !unsigned_lit_wrap.
  rewrite !Z_to_le_bytes_mod by (cbn; lia). reflexivity.
Qed.

(* w with the body sum stored holds the bytes of spec_cells. *)
Lemma spec_of_w : forall m A buf b, rw_cells rsegs m A (w_cells buf b (Z_to_bv 64 (sum_bytes (fr_body b)))) ->
  ro_cells rsegs m A (spec_cells buf b).
Proof.
  intros m A buf b [[_ Hb] _]. split.
  - unfold spec_cells. cbn [cells_wf cell_wf]. repeat split.
  - replace (cells_bytes (spec_cells buf b)) with (cells_bytes (w_cells buf b (Z_to_bv 64 (sum_bytes (fr_body b)))));
      [exact Hb|].
    unfold spec_cells, w_cells. cbn [cells_bytes cbytes].
    rewrite (le2_mod16 (sum_bytes (fr_body b))).
    unfold fr_cmd, fr_ncmds, at8. rewrite !b8_bz. reflexivity.
Qed.

(** * Bytes and register values *)

Lemma b2_rd : forall m a (bs : list byte) (k : Z), bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) 1 = Some [nth (Z.to_nat k) bs (b8 0)].
Proof.
  intros m a bs k H Hk Hl.
  pose proof (rd1 m a bs (Z.to_nat k) H Hl) as R. rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma b2_bytes_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma zxb_u' : forall x : byte, bv_unsigned (zxb x) = bv_unsigned x.
Proof. intros x. unfold zxb. pose proof (byte_range x). apply unsigned_lit. lia. Qed.

(* One more byte of the sum, as the loop adds it. *)
Lemma sum_step : forall (bd : list byte) i, (i < length bd)%nat ->
  sum_bytes (firstn i bd) + bv_unsigned (zxb (nth i bd (Z_to_bv 8 0))) = sum_bytes (firstn (S i) bd).
Proof. intros bd i H. rewrite zxb_u', sum_bytes_firstn_S by exact H. reflexivity. Qed.

(* Z.lor of a shifted value and a smaller one is their sum. *)
Lemma lor_add : forall a c k, 0 <= k -> 0 <= a -> 0 <= c < 2^k -> Z.lor (a * 2^k) c = a * 2^k + c.
Proof.
  intros a c k Hk Ha Hc.
  assert (L : Z.land (a * 2^k) c = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Lt|Ge].
    - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite <- (Z.mod_small c (2^k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- (Z.lxor_lor _ _ L), <- (Z.add_nocarry_lxor _ _ L). reflexivity.
Qed.

Lemma lor_add_r : forall a c k, 0 <= k -> 0 <= a -> 0 <= c < 2^k -> Z.lor c (a * 2^k) = a * 2^k + c.
Proof. intros a c k Hk Ha Hc. rewrite Z.lor_comm. apply lor_add; assumption. Qed.

(* (b[i] << 8) | b[i+1], from two lbu (spec_be16). *)
Lemma be16_reg : forall l i,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (b8 0)))) 8)))
                    (bv_unsigned (zxb (nth (S i) l (b8 0))))) = Z_to_bv 64 (be16 l i).
Proof.
  intros l i. unfold be16, at8, bz. rewrite !zxb_u'.
  pose proof (byte_range (nth i l (b8 0))) as H0. pose proof (byte_range (nth (S i) l (b8 0))) as H1.
  set (x0 := bv_unsigned (nth i l (b8 0))) in *. set (x1 := bv_unsigned (nth (S i) l (b8 0))) in *.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (x0 * 2^8)) by lia.
  rewrite lor_add by lia. reflexivity.
Qed.

(* ((b[i+1] << 16) | (b[i] << 24)) | ((b[i+2] << 8) | b[i+3]), from four lbu (spec_be32). *)
Lemma be32_reg : forall l i,
  Z_to_bv 64 (Z.lor
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth (S i) l (b8 0)))) 16)))
                                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (b8 0)))) 24))))))
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth (S (S i)) l (b8 0)))) 8)))
                                    (bv_unsigned (zxb (nth (S (S (S i))) l (b8 0))))))))
  = Z_to_bv 64 (be32 l i).
Proof.
  intros l i. unfold be32, at8, bz. rewrite !zxb_u'.
  pose proof (byte_range (nth i l (b8 0))) as H0. pose proof (byte_range (nth (S i) l (b8 0))) as H1.
  pose proof (byte_range (nth (S (S i)) l (b8 0))) as H2. pose proof (byte_range (nth (S (S (S i))) l (b8 0))) as H3.
  set (x0 := bv_unsigned (nth i l (b8 0))) in *. set (x1 := bv_unsigned (nth (S i) l (b8 0))) in *.
  set (x2 := bv_unsigned (nth (S (S i)) l (b8 0))) in *. set (x3 := bv_unsigned (nth (S (S (S i))) l (b8 0))) in *.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x1 * 2^16)), (unsigned_lit (x0 * 2^24)), (unsigned_lit (x2 * 2^8)) by lia.
  rewrite (lor_add_r x0 (x1 * 2^16) 24) by lia.
  rewrite (lor_add x2 x3 8) by lia.
  rewrite (unsigned_lit (x0 * 2^24 + x1 * 2^16)), (unsigned_lit (x2 * 2^8 + x3)) by lia.
  replace (x0 * 2^24 + x1 * 2^16) with ((x0 * 2^8 + x1) * 2^16) by ring.
  rewrite lor_add by lia. f_equal. ring.
Qed.

(** * The codes of fr_code *)

Lemma fr_code_short : forall b, (length b < 30)%nat -> fr_code b = -2.
Proof. intros b H. unfold fr_code. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma fr_code_eth : forall b, (30 <= length b)%nat -> fr_ethertype b <> 0x885f -> fr_code b = -3.
Proof.
  intros b H E. unfold fr_code. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

Lemma fr_code_len : forall b, (30 <= length b)%nat -> fr_ethertype b = 0x885f ->
  fr_numbytes b < 16 \/ Z.of_nat (length b) - 14 < fr_numbytes b -> fr_code b = -4.
Proof.
  intros b H E L. unfold fr_code. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E). cbn [negb].
  destruct L as [L|L].
  - rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) L), orb_true_r. reflexivity.
Qed.

Lemma fr_code_zero : forall b, (30 <= length b)%nat -> fr_ethertype b = 0x885f ->
  16 <= fr_numbytes b -> fr_numbytes b <= Z.of_nat (length b) - 14 -> fr_code b = 0.
Proof.
  intros b H E L1 L2. unfold fr_code. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E). cbn [negb].
  rewrite (proj2 (Z.ltb_ge _ _) L1), (proj2 (Z.ltb_ge _ _) L2). reflexivity.
Qed.

(** * Tactics *)

(* The byte k of the bytes at a, for an lbu. *)
Ltac rdb BB k :=
  let HR := fresh "HR" in
  pose proof (b2_rd _ _ _ k BB ltac:(lia) ltac:(lia)) as HR;
  let n := eval vm_compute in (Z.to_nat k) in change (Z.to_nat k) with n in HR.

Ltac b2_uns := rewrite ?unsigned_lit by lia.
Ltac b2_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; b2_uns; solve_cond_rec]
  end.
Ltac b2_curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* A store at sp itself: the step leaves its address as the word sp. *)
Ltac sp_store_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      replace (write_to_mem m a bs) with (write_to_mem m (wa (bv_unsigned a + Z.of_nat 0)) bs)
        by (f_equal; unfold wa; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; apply Z_to_bv_lit_self);
      mem_after_store
  end.

Ltac prem := first [ reflexivity | (symmetry; apply Z_to_bv_lit_self) | eassumption | lia
                   | (eapply rw_ro; eassumption) ].
