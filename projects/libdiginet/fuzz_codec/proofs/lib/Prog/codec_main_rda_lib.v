From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** ---- input bytes ---- *)

(** One input byte at any cut: the input is outside the stack window, so munch keeps it. *)
Lemma data_read1 : forall e m (a : word), env_ok e ->
  munch [(bv_unsigned (e_sp e) - LLVM_CODEC_STACK, bv_unsigned (e_sp e))] (e_m e) m ->
  bv_unsigned (e_p e) <= bv_unsigned a < bv_unsigned (e_p e) + Z.of_nat (length (e_data e)) ->
  ov_read_bytes rsegs m a 1 = Some [nth (Z.to_nat (bv_unsigned a - bv_unsigned (e_p e))) (e_data e) (Z_to_bv 8 0)].
Proof.
  intros e m a HE MU Ha.
  pose proof (data_of_munch e m HE MU) as HD.
  rewrite <- (bytes_at_byte m (bv_unsigned (e_p e)) (e_data e) (bv_unsigned a - bv_unsigned (e_p e)) HD) by lia.
  f_equal. unfold wa. rewrite <- (Z_to_bv_bv_unsigned a) at 1. f_equal. lia.
Qed.

(** The stepper reads an input byte through data_read1 (the address range by lia). *)
Ltac solve_load_data :=
  match goal with
  | |- context [ov_read_bytes rsegs ?m ?a 1] =>
    match goal with
    | HE : env_ok ?e, MU : munch _ (e_m ?e) m |- _ =>
      rewrite (data_read1 e m a HE MU) by (rewrite ?unsigned_lit by lia; lia)
    end
  end; load_post.
Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_data ].

(** ---- the driver of a read chain ---- *)

(** A conditional branch whose outcome the context decides: keep the feasible side. *)
Ltac decide_br :=
  let H := fresh "BR" in if_cases H; zify_cond H; try (exfalso; lia); try clear H.

(** An input byte read into a register becomes a variable with its range. *)
Ltac gen_bytes :=
  repeat match goal with
  | |- context [nth ?k (e_data ?e) ?d] =>
      let b := fresh "b" in let Hb := fresh "Hb" in
      generalize (bv_unsigned_in_range 8 (nth k (e_data e) d)); generalize (nth k (e_data e) d);
      intros b Hb; change (bv_modulus 8) with 256 in Hb
  end.

(** Step to pc stop, deciding every branch on the way. *)
Ltac drive stop :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => decide_br
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; gen_bytes
  end.

(** The bytes left: none, one to three, or a whole u32. *)
Lemma rem_cases : forall rem, 0 <= rem -> rem = 0 \/ rem = 1 \/ rem = 2 \/ rem = 3 \/ 4 <= rem.
Proof. intros. lia. Qed.

(** ---- the frame at a reader cut: k as HEAD leaves it with the fields a, b, c, delta stored, in.p = cur,
    in.n = rem ---- *)

Definition rd_cells (kind pv dv a b c delta cur rem : Z) (tl : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
   C4 (Z_to_bv 64 kind); CB 4 (fz0 4); C8 (Z_to_bv 64 pv); C8 (Z_to_bv 64 dv);
   C4 (Z_to_bv 64 a); C4 (Z_to_bv 64 b); C4 (Z_to_bv 64 c); C4 (Z_to_bv 64 delta);
   CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   CB 32 (fa5 32); CB 32 (fa5 32);
   C4 (Z_to_bv 64 0); CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 rem); CB 80 tl].

(** The record a reader hands to its encoder. *)
Definition k_enc (kind pv dv a b c delta : Z) : kcall :=
  mkKcall kind (fz0 4) pv dv a b c delta (fz0 24) 0 0 (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0.

(** The frame of a reader cut as a body frame, with in.p = cur. *)
Lemma rd_cells_body : forall e m A kind pv dv a b c delta cur rem tl,
  rw_cells rsegs m A (rd_cells kind pv dv a b c delta cur rem tl) ->
  rw_cells rsegs m A (body_cells e (k_enc kind pv dv a b c delta) (cur - bv_unsigned (e_p e)) rem tl).
Proof.
  intros e m A kind pv dv a b c delta cur rem tl H. unfold body_cells.
  replace (bv_unsigned (e_p e) + (cur - bv_unsigned (e_p e))) with cur by lia. exact H.
Qed.

(** ---- the out cell around an encoder call ---- *)

Definition body_pre (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
   C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)].

Definition body_post (e : env) (k : kcall) (c rem : Z) (tl : list byte) : list cell :=
  [C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k));
   C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl].

Definition set_out (k : kcall) (o : list byte) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) o
          (k_want_rc k) (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

Lemma body_cells_eq : forall e k c rem tl,
  body_cells e k c rem tl = body_pre k ++ [CB 32 (k_out k)] ++ body_post e k c rem tl.
Proof. reflexivity. Qed.

Lemma body_out_split : forall m A e k c rem tl,
  rw_cells rsegs m A (body_cells e k c rem tl) ->
  rw_cells rsegs m A (body_pre k) /\ rw_cells rsegs m (A + 124) [CB 32 (k_out k)] /\
  rw_cells rsegs m (A + 156) (body_post e k c rem tl).
Proof.
  intros m A e k c rem tl H. rewrite body_cells_eq in H.
  apply rw_cells_app_split in H. destruct H as [H1 H2].
  apply rw_cells_app_split in H2. destruct H2 as [H2 H3].
  replace (Z.of_nat (cells_size (body_pre k))) with 124 in H2, H3 by reflexivity.
  replace (A + 124 + Z.of_nat (cells_size [CB 32 (k_out k)])) with (A + 156) in H3
    by (cbn [cells_size csize Nat.add]; lia).
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma body_out_join : forall m A e k c rem tl o,
  rw_cells rsegs m A (body_pre k) -> rw_cells rsegs m (A + 124) [CB 32 o] ->
  rw_cells rsegs m (A + 156) (body_post e k c rem tl) ->
  rw_cells rsegs m A (body_cells e (set_out k o) c rem tl).
Proof.
  intros m A e k c rem tl o H1 H2 H3. rewrite body_cells_eq.
  change (body_pre (set_out k o)) with (body_pre k).
  change (body_post e (set_out k o) c rem tl) with (body_post e k c rem tl).
  apply rw_cells_app_join; [exact H1|].
  replace (A + Z.of_nat (cells_size (body_pre k))) with (A + 124) by reflexivity.
  apply rw_cells_app_join; [exact H2|].
  replace (A + 124 + Z.of_nat (cells_size [CB 32 (k_out (set_out k o))])) with (A + 156)
    by (cbn [cells_size csize Nat.add]; lia).
  exact H3.
Qed.

(** Two cell lists with the same bytes describe the same memory. *)
Lemma rw_cells_same : forall m A cs cs',
  cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' Hwf' Hb' Hs' [[Hwf Hb] (Ha & Hl & Hw)].
  split; [split; [exact Hwf' | rewrite Hb'; exact Hb] |].
  rewrite Hs'. split; [exact Ha|]. split; [exact Hl | exact Hw].
Qed.

(** ---- argument forms ---- *)

Lemma s32_range : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= s32 v < 2 ^ 31.
Proof. intros v Hv. unfold s32. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.

(** lw of a u32 field gives its value sign-extended from bit 31. *)
Lemma sx32_s32 : forall v, 0 <= v < 2 ^ 32 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 (s32 v).
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, s32.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (v + 2 ^ 31) (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma arg_u32_sx : forall v, 0 <= v < 2 ^ 32 -> arg_u32 (sx32 (Z_to_bv 64 v)) v.
Proof. intros v Hv. split; [exact Hv | apply sx32_s32; exact Hv]. Qed.

Lemma arg_s32_sx : forall v, 0 <= v < 2 ^ 32 -> arg_s32 (sx32 (Z_to_bv 64 v)) (s32 v).
Proof. intros v Hv. split; [apply s32_range; exact Hv | apply sx32_s32; exact Hv]. Qed.

(** The 4 bytes of the int field holding (int) v are those of v. *)
Lemma le4_s32 : forall v, 0 <= v < 2 ^ 32 -> le4 (Z_to_bv 64 (s32 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v Hv. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (s32 v mod 2 ^ 64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2 ^ 64) 32) by (cbn; lia).
  f_equal. unfold s32. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
  Z.div_mod_to_equations. lia.
Qed.

(** The u32 a read chain composes from two 16-bit halves (lo = b0 | b1 << 8, hi = b2 | b3 << 8). *)
Lemma cmp_range : forall x1 x2 x3 x4, 0 <= x1 < 2 ^ 16 -> 0 <= x2 < 2 ^ 16 -> 0 <= x3 < 2 ^ 16 -> 0 <= x4 < 2 ^ 16 ->
  0 <= Z.lor (Z.lor x2 x1) (Z.shiftl (Z.lor x4 x3) 16 mod 18446744073709551616) < 2 ^ 32.
Proof.
  intros x1 x2 x3 x4 H1 H2 H3 H4.
  pose proof (lor_lt_pow2 x2 x1 16 H2 H1) as L1.
  pose proof (lor_lt_pow2 x4 x3 16 H4 H3) as L2.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  apply lor_lt_pow2; lia.
Qed.

(** ---- the record facts ---- *)

Lemma rdr_zero : forall kind a b c delta,
  0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= delta < 2 ^ 31 ->
  kind <> 5 -> kind <> 10 -> kind <> 11 ->
  reader_ok kind a b c delta (zb (fz0 24)) 0.
Proof.
  intros kind a b c delta Ha Hb Hc Hd H5 H10 H11.
  assert (E : zb (fz0 24) = repeat 0 24) by (vm_compute; reflexivity).
  unfold reader_ok. rewrite E, repeat_length.
  repeat split; try lia.
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma pd_strips : forall pv dv od, pd_ok pv dv od -> forall d, od = Some d -> d_strips d <= 64.
Proof.
  intros pv dv od [(_ & _ & ->) | [(_ & _ & ->) | (_ & _ & ->)]] d Hd; [discriminate | ..];
    injection Hd as <-; cbv; congruence.
Qed.

(** ---- the shared steps of a cut ---- *)

(** The facts every reader cut starts from (the names the finishers use). *)
Ltac rd_setup HE HFR :=
  lazymatch type of HE with env_ok ?e =>
  let HLO := fresh "HLO" in let HPB := fresh "HPB" in
  pose proof HE as (_ & _ & _ & HLO & _ & _ & HPB & _ & _);
  destruct HFR as (SV & ST & MU & WM & HMI);
  unfold LLVM_CODEC_STACK in *;
  let Rsp := fresh "Rsp" in let Rp := fresh "Rp" in let Hlo0 := fresh "Hlo0" in
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp; unfold bv_modulus in Rsp;
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp; unfold bv_modulus in Rp;
  pose proof ST as [Hlo0 _]
  end.

(** The side goals of a cut lemma applied at the end of a chain. *)
Ltac rd_side :=
  first [ eassumption
        | (unfold fr_ok; repeat match goal with |- _ /\ _ => split end; assumption)
        | apply cmp_range; assumption
        | rewrite Z.shiftl_mul_pow2 by lia; lia
        | lia ].
