From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** ---- register forms ---- *)

(** lw of an unsigned field: the register is the field sign-extended from bit 31. *)
Lemma sx32_u : forall a, 0 <= a < 2 ^ 32 ->
  bv_unsigned (sx32 (Z_to_bv 64 a)) = if a <? 2 ^ 31 then a else a + (2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold sx32. rewrite (unsigned_lit a) by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec a (2 ^ 31)).
  - rewrite (Z.mod_small (a + 2 ^ 31) (2 ^ 32)) by lia.
    replace (a + 2 ^ 31 - 2 ^ 31) with a by lia. apply Z.mod_small. lia.
  - replace ((a + 2 ^ 31) mod 2 ^ 32) with (a + 2 ^ 31 - 2 ^ 32)
      by (apply Z.mod_unique with 1; lia).
    symmetry. apply Z.mod_unique with (-1); lia.
Qed.

(** lwu of an unsigned field. *)
Lemma zx32_small : forall b, 0 <= b < 2 ^ 32 -> zx32 (Z_to_bv 64 b) = Z_to_bv 64 b.
Proof. intros b Hb. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(** The low byte of a word, as sb stores it. *)
Lemma b8_lit : forall x, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 x)) = b8 x.
Proof.
  intros x. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite (Z.mod_eq x (bv_modulus 64)) by (cbv; discriminate).
  replace (bv_modulus 64) with (2 ^ 8 * 2 ^ 56) by reflexivity.
  replace (bv_modulus 8) with (2 ^ 8) by reflexivity.
  replace (x - 2 ^ 8 * 2 ^ 56 * (x / (2 ^ 8 * 2 ^ 56))) with (x + (- (2 ^ 56 * (x / (2 ^ 8 * 2 ^ 56)))) * 2 ^ 8) by ring.
  apply Z.mod_add. lia.
Qed.

Lemma bytes_eq_of_unsigned : forall l1 l2 : list byte,
  map (fun b => bv_unsigned b) l1 = map (fun b => bv_unsigned b) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx | apply IH; exact Hl].
Qed.

Lemma b8_u8 : forall x, b8 (u8 x) = b8 x.
Proof.
  intros x. unfold b8, u8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_mod. lia.
Qed.

Lemma u8_unsigned : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_small. exact Hx.
Qed.

(** ---- the desk owe() reads at k.desk ---- *)

Definition desk_cells (d : desk) (np : word) (pad : list byte) : list cell :=
  [C8 np; C1 (Z_to_bv 8 (d_dev d)); C1 (Z_to_bv 8 (d_strips d)); C1 (Z_to_bv 8 (d_chars d));
   C1 (Z_to_bv 8 (d_counter d)); CB 4 pad].

Definition desk_rng (d : desk) : Prop :=
  0 <= d_dev d <= 1 /\ (d_strips d = 24 \/ d_strips d = 8) /\ (d_chars d = 4 \/ d_chars d = 8) /\
  (d_counter d = 0x19 \/ d_counter d = 0x09).

Lemma desk_ro : forall m pv dv d, relro_img m -> pd_ok pv dv (Some d) ->
  (d = c24 \/ d = pc) /\ desk_rng d /\ 0x1f208 <= dv <= 0x1f218 /\
  exists np pad, ro_cells rsegs m dv (desk_cells d np pad).
Proof.
  intros m pv dv d HR [(_ & _ & H) | [(-> & -> & H) | (-> & -> & H)]]; [discriminate | ..];
    injection H as ->.
  - split; [left; reflexivity|]. split; [unfold desk_rng; cbn; repeat split; first [lia | left; reflexivity | right; reflexivity]|].
    split; [lia|]. eexists _, _. exact (codec_SPEC_C24_at m HR).
  - split; [right; reflexivity|]. split; [unfold desk_rng; cbn; repeat split; first [lia | left; reflexivity | right; reflexivity]|].
    split; [lia|]. eexists _, _. exact (codec_SPEC_PC_at m HR).
Qed.

(** ---- the call record after owe() ---- *)

(** k with the five fields owe() writes replaced. *)
Definition set_owe (k : kcall) (wrc : Z) (w : list byte) (wl wk wd : Z) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) (k_out k) wrc w wl wk wd.

(** ---- cutting the flat frame ---- *)

Lemma rw_cells_isolate : forall m A cs i j,
  rw_cells rsegs m A cs ->
  rw_cells rsegs m A (firstn i cs) /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs)))
    [CB (cells_size (firstn j (skipn i cs))) (cells_bytes (firstn j (skipn i cs)))] /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs)) + Z.of_nat (cells_size (firstn j (skipn i cs))))
    (skipn j (skipn i cs)).
Proof.
  intros m A cs i j H.
  rewrite <- (firstn_skipn i cs) in H.
  apply rw_cells_app_split in H. destruct H as [H1 H2].
  rewrite <- (firstn_skipn j (skipn i cs)) in H2.
  apply rw_cells_app_split in H2. destruct H2 as [H2 H3].
  split; [exact H1|]. split; [|exact H3].
  pose proof (rw_cells_merge rsegs m (A + Z.of_nat (cells_size (firstn i cs))) [] (firstn j (skipn i cs)) []) as M.
  rewrite app_nil_r in M. cbn [app] in M. exact (M H2).
Qed.

Lemma rw_cells_join3 : forall m A cs1 n bs cs3,
  rw_cells rsegs m A cs1 ->
  rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) [CB n bs] ->
  rw_cells rsegs m (A + Z.of_nat (cells_size cs1) + Z.of_nat n) cs3 ->
  rw_cells rsegs m A (cs1 ++ CB n bs :: cs3).
Proof.
  intros m A cs1 n bs cs3 H1 H2 H3.
  apply rw_cells_app_join; [exact H1|].
  change (CB n bs :: cs3) with ([CB n bs] ++ cs3).
  apply rw_cells_app_join; [exact H2|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H3.
Qed.

Lemma rw_cells_merge_at : forall m A cs i j,
  rw_cells rsegs m A cs ->
  rw_cells rsegs m A (firstn i cs ++ CB (cells_size (firstn j (skipn i cs))) (cells_bytes (firstn j (skipn i cs)))
                       :: skipn j (skipn i cs)).
Proof.
  intros m A cs i j H.
  apply rw_cells_merge.
  rewrite firstn_skipn. rewrite firstn_skipn. exact H.
Qed.

Lemma rw_cells_bytes_at : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(** Normalize [A + Z.of_nat n] for closed n in a hypothesis. *)
Ltac fix_ofnat H :=
  repeat match type of H with
  | context [Z.of_nat ?n] =>
      let v := eval vm_compute in (Z.of_nat n) in
      lazymatch v with Z.of_nat _ => fail | _ => change (Z.of_nat n) with v in H end
  end.

(** ---- the two exits of owe() into CHK ---- *)

Section Exits.
Variables (e : env) (fuel : nat).
Hypothesis HE : env_ok e.
Hypothesis CHK : chk_ok e fuel.

(** A failed case: want_rc = rc (the store at 0x14804), the want fields still 0. *)
Lemma owe_err_tail : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
    (k : kcall) (od : option desk) (c rem rc : Z) (tl : list byte) (m1 : word -> option byte),
  fuel_ok ops (S fuel) ->
  rec_ok k od -> k_rc k = fst (enc_k k od) ->
  fst (owe_k k od) = rc -> rc <> 0 -> a0' = Z_to_bv 64 rc ->
  k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
  cur_ok e c rem ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  fr_ok e m1 ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
        0x14804 m1).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops k od c rem rc tl m1
         HF HRC HRCk HOW HNZ HA0 HWL HWK HWD HC FR HFR.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  unfold st, body_regs. subst a0'.
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep.
  unfold chk_ok, st, body_regs in CHK.
  eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ops (set_owe k rc (k_want k) 0 0 0) od c rem tl);
    [ exact HF | exact HRC | exact HRCk | | exact HC | | ].
  - unfold owe_want_ok. cbn [set_owe k_want_rc k_want_len k_want_key k_want_display].
    unfold owe_k, set_owe. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
    fold (owe_k k od). rewrite HOW. split; [reflexivity|].
    destruct (Z.eqb_spec rc 0); [contradiction|]. auto.
  - unfold body_cells, set_owe. cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
      k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display].
    rewrite HWL, HWK, HWD in *. eassumption.
  - split; [eassumption|]. split; [eassumption|]. split; [unfold LLVM_CODEC_STACK; eassumption|]. split; eassumption.
Qed.

(** A successful case: the five want fields written, as set_owe k 0 w (length bs) key dp says. *)
Lemma owe_ok_tail : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
    (k : kcall) (od : option desk) (c rem : Z) (tl w : list byte) (bs : list Z) (key dp : Z) (m1 : word -> option byte),
  fuel_ok ops (S fuel) ->
  rec_ok k od -> k_rc k = fst (enc_k k od) ->
  owe_k k od = (0, (bs, key, dp)) -> firstn (length bs) w = bz bs ->
  cur_ok e c rem ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400)
    (body_cells e (set_owe k 0 w (Z.of_nat (length bs)) key dp) c rem tl) ->
  fr_ok e m1 ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
        0x14808 m1).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops k od c rem tl w bs key dp m1
         HF HRC HRCk HOW HW HC FR HFR.
  eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ops (set_owe k 0 w (Z.of_nat (length bs)) key dp) od c rem tl);
    [ exact HF | exact HRC | exact HRCk | | exact HC | exact FR | exact HFR ].
  unfold owe_want_ok. cbn [set_owe k_want_rc k_want_len k_want_key k_want_display k_want].
  unfold owe_k, set_owe. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
  fold (owe_k k od). rewrite HOW. cbn [fst snd Z.eqb]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact HW|]. split; reflexivity.
Qed.

End Exits.
