(* rp_slot_read walk, fuzz_wire plain c8763dfc4e81 0x13790..0x1385c (repace_wire.c:111-124); new.
   rp_slot_width is the named Section hypothesis HSW (its contract, rp_slot_width_c.v). The inlined reac_braid_pos is
   proved against braid_pos (rp_slot_read_c.v) through braid_pos_lin, copied from libreac/fuzz_decode's released
   lib/Prog/reac_decode.v:17 (recipes 25e3d17bdb5, blob d70727b17a36). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes reac_frame_clean_len_c
  reac_frame_clean_len rp_frame_channels_c rp_slot_width_c rp_slot_read_c rp_frame_channels rp_slot_width.
Import ListNotations.
Open Scope Z_scope.

(* Copied from libreac/fuzz_decode lib/Prog/reac_decode.v:17 (released, blob d70727b17a36). *)
Lemma braid_pos_lin : forall s ch nch k, 0 <= k < 3 ->
  braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) +
    (if k =? 0 then 3 + ch mod 2 else if k =? 1 then 5 * (ch mod 2) else 1 + ch mod 2).
Proof.
  intros s ch nch k Hk. unfold braid_pos.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E|E];
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); try rewrite E; lia.
Qed.

Lemma wv : forall (x : word) (e : Z), bv_unsigned x = e -> x = Z_to_bv 64 e.
Proof. intros x e <-. symmetry. apply Z_to_bv_lit_self. Qed.

(* ---- the written bytes ---- *)

Definition out_pref (bs : list byte) (nch slot : Z) (j : nat) : list byte :=
  flat_map (fun s => le4 (Z_to_bv 64 (rp_sample bs nch slot (Z.of_nat s)))) (seq 0 j).

Lemma out_pref_len : forall bs nch slot j, Z.of_nat (length (out_pref bs nch slot j)) = 4 * Z.of_nat j.
Proof.
  intros bs nch slot j. induction j as [|j IH]; [reflexivity|].
  unfold out_pref in *. rewrite seq_S, flat_map_app, app_length. cbn [flat_map app].
  rewrite app_nil_r, length_le4. lia.
Qed.

Lemma out_pref_S : forall bs nch slot j,
  out_pref bs nch slot (S j) = out_pref bs nch slot j ++ le4 (Z_to_bv 64 (rp_sample bs nch slot (Z.of_nat j))).
Proof.
  intros. unfold out_pref. rewrite seq_S, flat_map_app. cbn [flat_map app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma out_pref_full : forall bs nch slot, out_pref bs nch slot 12 = rp_slot_bytes bs nch slot.
Proof. reflexivity. Qed.

(* ---- bit lemmas for the loop body ---- *)

Lemma land_clear_low : forall x k, 0 <= k <= 64 -> 0 <= x < 2^64 ->
  Z.land x (2^64 - 2^k) = x - x mod 2^k.
Proof.
  intros x k Hk Hx.
  assert (E1 : Z.shiftl (Z.ones (64 - k)) k = 2^64 - 2^k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv.
    replace (Z.pred (2 ^ (64 - k))) with (2^(64-k) - 1) by lia.
    rewrite Z.mul_sub_distr_r, Z.mul_1_l, <- Z.pow_add_r by lia.
    replace (64 - k + k) with 64 by lia. reflexivity. }
  assert (E2 : x - x mod 2^k = Z.shiftl (x / 2^k) k)
    by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (L : Z.log2 x < 64)
    by (destruct (Z.eq_dec x 0) as [->|Hx0]; [vm_compute; reflexivity | apply Z.log2_lt_pow2; lia]).
  rewrite <- E1, E2. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i k) as [H|H].
  - rewrite (Z.testbit_neg_r (Z.ones (64 - k)) (i - k)) by lia.
    rewrite (Z.testbit_neg_r (x / 2^k) (i - k)) by lia. apply andb_false_r.
  - destruct (Z.lt_ge_cases (i - k) (64 - k)) as [H2|H2].
    + rewrite Z.ones_spec_low by lia. rewrite andb_true_r.
      rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      rewrite Z.div_pow2_bits by lia. apply Z.bits_above_log2; lia.
Qed.

Lemma land_m2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551614 = x - x mod 2.
Proof.
  intros x Hx. replace 18446744073709551614 with (2^64 - 2^1) by (vm_compute; reflexivity).
  rewrite land_clear_low by lia. reflexivity.
Qed.

Lemma land_1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x Hx. replace 1 with (2^1 - 1) by reflexivity. apply zb_land_mask. lia. Qed.

Lemma sb_val : forall b : byte, bv_signed b = (if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256).
Proof.
  intros b. pose proof (byte_range b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  destruct (Z.ltb_spec (bv_unsigned b) 128); Z.div_mod_to_equations; lia.
Qed.

Lemma hi_lo : forall b : byte, Z.land (bv_signed b mod 2^64) 255 = bv_unsigned b.
Proof.
  intros b. pose proof (byte_range b) as R. rewrite sb_val.
  destruct (Z.ltb_spec (bv_unsigned b) 128) as [H|H].
  - rewrite Z.mod_small by lia. replace 255 with (2^8 - 1) by reflexivity.
    rewrite zb_land_mask by lia. apply Z.mod_small. lia.
  - replace ((bv_unsigned b - 256) mod 2^64) with (bv_unsigned b + 18446744073709551360).
    2: { rewrite <- (Z.mod_add (bv_unsigned b - 256) 1 (2^64)) by lia.
         rewrite Z.mod_small by lia. lia. }
    replace 255 with (2^8 - 1) by reflexivity. rewrite zb_land_mask by lia.
    replace (bv_unsigned b + 18446744073709551360) with (bv_unsigned b + 72057594037927935 * 2^8) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi_mask : forall b : byte,
  Z.land (bv_signed b mod 2^64) 18446744073692774400
  = (if bv_unsigned b <? 128 then 0 else 18446744073692774400).
Proof.
  intros b. pose proof (byte_range b) as R.
  replace 18446744073692774400 with (2^64 - 2^24) by (vm_compute; reflexivity).
  rewrite sb_val. destruct (Z.ltb_spec (bv_unsigned b) 128) as [H|H].
  - rewrite Z.mod_small by lia. rewrite land_clear_low by lia.
    rewrite (Z.mod_small (bv_unsigned b) (2^24)) by lia. lia.
  - replace ((bv_unsigned b - 256) mod 2^64) with (bv_unsigned b + 18446744073709551360).
    2: { rewrite <- (Z.mod_add (bv_unsigned b - 256) 1 (2^64)) by lia.
         rewrite Z.mod_small by lia. lia. }
    rewrite land_clear_low by lia.
    replace ((bv_unsigned b + 18446744073709551360) mod 2^24) with (bv_unsigned b + 16777216 - 256).
    2: { replace (bv_unsigned b + 18446744073709551360)
           with ((bv_unsigned b + 16777216 - 256) + 1099511627775 * 2^24) by (change (2^24) with 16777216; lia).
         rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. change (2^24) with 16777216. lia. }
    lia.
Qed.

Lemma mod64_32 : forall y, (y mod 2^64) mod 2^32 = y mod 2^32.
Proof.
  intros y. rewrite (Z.mod_eq y (2^64)) by lia.
  replace (y - 2^64 * (y / 2^64)) with (y + - (4294967296 * (y / 2^64)) * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma le4_eqm : forall x y : word, bv_unsigned x mod 2^32 = bv_unsigned y mod 2^32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by lia.
  rewrite H. reflexivity.
Qed.

(* The three loaded bytes combined by 0x13810..0x13828, modulo 2^32: the sign-extended 24-bit sample. *)
Lemma sample_val : forall b0 b1 b2 : byte,
  Z.lor (Z.lor (bv_unsigned b1 * 2^8) (bv_unsigned b0))
        (Z.lor (bv_unsigned b2 * 2^16)
               (if bv_unsigned b2 <? 128 then 0 else 18446744073692774400)) mod 2^32
  = (if bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 <? 2^23
     then bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2
     else bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 - 2^24) mod 2^32.
Proof.
  intros b0 b1 b2. pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  pose proof (byte_range b2) as R2.
  assert (A : Z.lor (bv_unsigned b1 * 2^8) (bv_unsigned b0) = bv_unsigned b0 + 256 * bv_unsigned b1).
  { rewrite Z.lor_comm. rewrite (lor_low 8 (bv_unsigned b0) (bv_unsigned b1)) by lia. lia. }
  rewrite A.
  destruct (Z.ltb_spec (bv_unsigned b2) 128) as [H|H].
  - rewrite Z.lor_0_r.
    rewrite (lor_low 16 (bv_unsigned b0 + 256 * bv_unsigned b1) (bv_unsigned b2)) by lia.
    rewrite (proj2 (Z.ltb_lt _ (2^23))) by lia. f_equal. lia.
  - assert (B : Z.lor (bv_unsigned b2 * 2^16) 18446744073692774400
               = 18446744073692774400 + bv_unsigned b2 * 2^16).
    { replace 18446744073692774400 with (1099511627775 * 2^24) by (vm_compute; reflexivity).
      rewrite (lor_low 24 (bv_unsigned b2 * 2^16) 1099511627775) by lia. lia. }
    rewrite B.
    assert (C : Z.lor (bv_unsigned b0 + 256 * bv_unsigned b1) (18446744073692774400 + bv_unsigned b2 * 2^16)
                = 18446744073692774400 + bv_unsigned b2 * 2^16 + (bv_unsigned b0 + 256 * bv_unsigned b1)).
    { replace (18446744073692774400 + bv_unsigned b2 * 2^16)
        with ((281474976710400 + bv_unsigned b2) * 2^16) by lia.
      rewrite (lor_low 16 (bv_unsigned b0 + 256 * bv_unsigned b1) (281474976710400 + bv_unsigned b2))
        by lia. lia. }
    rewrite C.
    rewrite (proj2 (Z.ltb_ge _ (2^23))) by lia.
    replace (18446744073692774400 + bv_unsigned b2 * 2^16 + (bv_unsigned b0 + 256 * bv_unsigned b1))
      with ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 - 2^24)
            + 4294967296 * 2^32) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* ---- geometry of a successful width ---- *)

Lemma fc_geom : forall len, 0 <= rp_frame_channels_model len ->
  2 <= rp_frame_channels_model len <= 40 /\ rp_frame_channels_model len mod 2 = 0 /\
  52 + 36 * rp_frame_channels_model len <= len.
Proof.
  intros len. unfold rp_frame_channels_model. cbv zeta.
  destruct (Z.ltb_spec len 0) as [HL|HL]; [lia|].
  pose proof (clean_range len HL) as RC.
  destruct ((reac_frame_clean_len_model len <? 52)
            || negb ((reac_frame_clean_len_model len - 52) mod 36 =? 0)) eqn:EG; [lia|].
  apply orb_false_iff in EG. destruct EG as [EG1 EG2]. apply Z.ltb_ge in EG1.
  apply negb_false_iff, Z.eqb_eq in EG2.
  set (c := reac_frame_clean_len_model len) in *.
  assert (EQ : c - 52 = 36 * ((c - 52) / 36)) by (Z.div_mod_to_equations; lia).
  set (q := (c - 52) / 36) in *.
  assert (Rq : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  destruct (Z.ltb_spec (bv_swrap 32 q) 2) as [H2|H2]; [cbn [orb]; lia|].
  destruct (Z.ltb_spec 40 (bv_swrap 32 q)) as [H3|H3]; [cbn [orb]; lia|].
  destruct (Z.odd (bv_swrap 32 q)) eqn:EO; [cbn [orb]; lia|].
  cbn [orb]. intros _.
  assert (Hqv : q >= bv_swrap 32 q).
  { revert H2 H3. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
    intros. Z.div_mod_to_equations. lia. }
  rewrite odd_mod2 in EO. apply Z.eqb_neq in EO.
  pose proof (Z.mod_pos_bound (bv_swrap 32 q) 2 ltac:(lia)).
  split; [lia|]. split; [lia|]. lia.
Qed.

Lemma sw_model_range : forall n bs slot,
  rp_slot_width_model n bs slot = -1 \/ 2 <= rp_slot_width_model n bs slot <= 40.
Proof.
  intros n bs slot. unfold rp_slot_width_model. cbv zeta.
  destruct ((n <? 50) || negb (slot_byte bs 16 =? 0) || negb (slot_byte bs 17 =? 0)); [left; reflexivity|].
  destruct ((rp_frame_channels_model (bv_swrap 64 n) <? 0) || (slot <? 0)
            || (rp_frame_channels_model (bv_swrap 64 n) <=? slot)); [left; reflexivity|].
  apply fc_model_range.
Qed.

Lemma sw_geom : forall n bs slot, 0 <= n < 2^64 -> 0 <= rp_slot_width_model n bs slot ->
  (let nch := rp_slot_width_model n bs slot in
   2 <= nch <= 40 /\ nch mod 2 = 0 /\ 0 <= slot < nch /\ 52 + 36 * nch <= n).
Proof.
  intros n bs slot Hn H. cbv zeta. revert H. unfold rp_slot_width_model. cbv zeta.
  destruct ((n <? 50) || negb (slot_byte bs 16 =? 0) || negb (slot_byte bs 17 =? 0)); [lia|].
  assert (SW : bv_swrap 64 n <= n).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63).
    Z.div_mod_to_equations. lia. }
  destruct (Z.ltb_spec (rp_frame_channels_model (bv_swrap 64 n)) 0) as [G1|G1]; [cbn [orb]; lia|].
  destruct (Z.ltb_spec slot 0) as [G2|G2]; [cbn [orb]; lia|].
  destruct (Z.leb_spec (rp_frame_channels_model (bv_swrap 64 n)) slot) as [G3|G3]; [cbn [orb]; lia|].
  cbn [orb]. intros _. destruct (fc_geom (bv_swrap 64 n) G1) as (F1 & F2 & F3).
  split; [lia|]. split; [lia|]. lia.
Qed.

(* seqz a7, s1; addi a7, a7, -1; andi a6, a7, 5: 5 when the slot is odd, 0 when it is even. *)
Lemma seqz5 : forall z, 0 <= z <= 1 ->
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64
    (bv_unsigned (v_sltiu (Z_to_bv 64 z) 1) + -1))) 5)) = 5 * z.
Proof.
  intros z Hz. destruct (Z.eq_dec z 0) as [->|Hz0]; [| assert (Ez : z = 1) by lia; subst z];
    vm_compute; reflexivity.
Qed.

(* Rewrite bv_unsigned (Z_to_bv 64 z) to z, innermost first, where lia proves z in range. *)
Ltac rw_inner_lit :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (unsigned_lit z) by lia
      end
  end.

Section SR.
Hypothesis HSW : rp_slot_width_contract.

Section Loop.
Variables (ra sp gp tp S0 S1 S2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
Variables (f v nch slot lo : Z).

Local Notation SP := (bv_unsigned sp).

Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hslot : 0 <= slot < nch.
Hypothesis Hlen : 50 + 36 * nch <= Z.of_nat (length bs).
Hypothesis Hf : 0 <= f.
Hypothesis Hfb : f + Z.of_nat (length bs) <= 2^64.
Hypothesis HDJf : f + Z.of_nat (length bs) <= SP - 64 \/ SP <= f.
Hypothesis Hv : 0 <= v.
Hypothesis Hv48 : v + 48 <= 2^64.
Hypothesis HDJv : v + 48 <= SP - 64 \/ SP <= v.
Hypothesis HDJfv : v + 48 <= f \/ f + Z.of_nat (length bs) <= v.
Hypothesis Hlo0 : 0 <= lo.
Hypothesis HSPlo : lo + 64 <= SP.

Definition PostOK : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' S0 S1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                  S2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP /\
    munch [(SP - 64, SP); (v, v + 48)] m m' /\ bytes_at rsegs m' v (rp_slot_bytes bs nch slot).

Definition INVR (mk : word -> option byte) (j : nat) : Prop :=
  bytes_at rsegs mk f bs /\ rw_cells rsegs mk (SP + -32) [C8 S2; C8 S1; C8 S0; C8 ra] /\
  stk rsegs mk lo (SP + -32) /\ wr_at rsegs mk v 48 /\ mem_inv rsegs mk /\
  munch [(SP - 64, SP); (v, v + 48)] m mk /\ wmono rsegs m mk /\
  bytes_at rsegs mk v (out_pref bs nch slot j).

Local Notation STATE pc mk y5 y6 y7 x8 x15 x9 x10 x11 x12 x13 x14 x16 x17 x18 :=
  (MS (mkR (Z_to_bv 64 79796) (Z_to_bv 64 (SP + -32)) gp tp y5 y6 y7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
        x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

Lemma sr_exit : forall (mk : word -> option byte) (y5 y6 y7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : word),
  INVR mk 12 -> evt rsegs PostOK (STATE 79932 mk y5 y6 y7 x8 x15 x9 x10 x11 x12 x13 x14 x16 x17 x18).
Proof.
  intros mk y5 y6 y7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (HBB & FR & ST & HW & MI & MU & WM & HOUT).
  pose proof (u64_range sp) as Rsp.
  do 8 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold PostOK. do 11 eexists. split; [reflexivity|].
  split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact MU|].
  rewrite <- out_pref_full. exact HOUT.
Qed.

Lemma sr_loop : forall (x9 x10 x11 x12 x13 x14 x16 x17 x18 : word),
  bv_unsigned x9 = slot mod 2 -> bv_unsigned x10 = 3 * nch -> bv_unsigned x11 = f + 50 ->
  x12 = Z_to_bv 64 (v + 48) -> bv_unsigned x13 = f + 50 + slot mod 2 + 3 ->
  bv_unsigned x14 = f + 50 + slot mod 2 + 1 -> bv_unsigned x16 = 5 * (slot mod 2) ->
  bv_unsigned x17 = 18446744073692774400 ->
  forall (K : nat) (s : Z) (mk : word -> option byte) (y5 y6 y7 x8 x15 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x8 = v + 4 * s -> bv_unsigned x15 = 3 * (s * nch + (slot - slot mod 2)) ->
  INVR mk (Z.to_nat s) ->
  evt rsegs PostOK (STATE 79860 mk y5 y6 y7 x8 x15 x9 x10 x11 x12 x13 x14 x16 x17 x18).
Proof.
  intros x9 x10 x11 x12 x13 x14 x16 x17 x18 H9 H10 H11 H12 H13 H14 H16 H17 K.
  induction K as [K IH] using lt_wf_ind.
  intros s mk y5 y6 y7 x8 x15 HK Hs H8 H15 INV.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound slot 2 ltac:(lia)) as Rmod.
  assert (Hsl2 : slot - slot mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hsn0 : 0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hsn : s * nch <= 11 * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  destruct INV as (HBB & FR & ST & HW & MI & MU & WM & HOUT).
  (* the three braid bytes *)
  assert (RD : forall k, 0 <= k < 3 ->
    ov_read_bytes rsegs mk (wa (f + (50 + (3 * (s * nch + (slot - slot mod 2)) +
      (if k =? 0 then 3 + slot mod 2 else if k =? 1 then 5 * (slot mod 2) else 1 + slot mod 2))))) 1
    = Some [nth (Z.to_nat (50 + braid_pos s slot nch k)) bs (Z_to_bv 8 0)]).
  { intros k Hk. rewrite <- braid_pos_lin by lia.
    pose proof (rd1 mk f bs (Z.to_nat (50 + braid_pos s slot nch k)) HBB) as R.
    rewrite Z2Nat.id in R by (rewrite braid_pos_lin by lia;
      destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); lia).
    apply R. rewrite braid_pos_lin by lia.
    destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); lia. }
  pose proof (RD 0 ltac:(lia)) as R0. pose proof (RD 1 ltac:(lia)) as R1.
  pose proof (RD 2 ltac:(lia)) as R2. cbn [Z.eqb Pos.eqb] in R0, R1, R2. clear RD.
  remember (nth (Z.to_nat (50 + braid_pos s slot nch 0)) bs (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth (Z.to_nat (50 + braid_pos s slot nch 1)) bs (Z_to_bv 8 0)) as b1 eqn:E1.
  remember (nth (Z.to_nat (50 + braid_pos s slot nch 2)) bs (Z_to_bv 8 0)) as b2 eqn:E2.
  pose proof (wr_at_store_ok rsegs mk v 48 (4 * s) 4%nat HW ltac:(lia) ltac:(cbn; lia)) as HS.
  apply wv in H8, H9, H10, H11, H13, H14, H15, H16, H17.
  subst x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.
  step. zsimp. step. zsimp. step. zsimp. step. step. step. zsimp. step.
  step. step. step. step. step. step. step. step.
  (* the store: the stored word is the sample, modulo 2^32 *)
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?W)) _) =>
    replace (le4 W) with (le4 (Z_to_bv 64 (rp_sample bs nch slot s))) end.
  2: { symmetry. apply le4_eqm.
       cbv delta [sxb]. rewrite !unsigned_lit_wrap, !mod64_32.
       rewrite !hi_lo, !hi_mask. rewrite !Z.shiftl_mul_pow2 by lia.
       pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
       repeat rewrite (Z.mod_small _ (2^64)) by zrange.
       unfold rp_sample. cbv beta zeta. rewrite <- E0, <- E1, <- E2.
       apply sample_val. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mk0 ?aa ?wb) _) =>
    assert (INV2 : INVR (write_to_mem mk0 aa wb) (S (Z.to_nat s)));
    [ unfold INVR; split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]
    | set (mk2 := write_to_mem mk0 aa wb) in *; clearbody mk2 ]
  end.
  { apply bytes_at_write_other; [exact HBB | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  { apply rw_cells_frame;
      [exact FR | lia | rewrite length_le4; lia | cbn [cells_size csize Nat.add]; rewrite length_le4; lia]. }
  { apply stk_write; [exact ST | lia | rewrite length_le4; lia]. }
  { apply wr_at_write. exact HW. }
  { apply mem_inv_store; [exact MI | rewrite length_le4; exact HS]. }
  { apply munch_write; [exact MU | lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; lia]. }
  { apply wmono_write. exact WM. }
  { rewrite out_pref_S. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split.
    - apply bytes_at_write_other;
        [exact HOUT | lia | rewrite length_le4; lia | rewrite out_pref_len, length_le4; lia].
    - rewrite out_pref_len, (Z2Nat.id s) by lia.
      apply bytes_at_write_same; [lia | rewrite length_le4; lia]. }
  clear HBB FR ST HW MI MU WM HOUT HS.
  step. step. step. if_cases HE.
  - (* another sample *)
    zify_cond HE. try rewrite !unsigned_lit in HE by lia.
    eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1) mk2);
      [ reflexivity | lia
      | repeat (rewrite unsigned_lit by lia); lia
      | repeat (rewrite unsigned_lit by lia);
        replace ((s + 1) * nch) with (s * nch + nch) by ring; lia
      | replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia; exact INV2 ].
  - (* the twelfth sample is written: leave the loop *)
    zify_cond HE. try rewrite !unsigned_lit in HE by lia.
    apply sr_exit. replace 12%nat with (S (Z.to_nat s)) by lia. exact INV2.
Qed.

End Loop.

Theorem rp_slot_read_holds : rp_slot_read_contract.
Proof.
  unfold rp_slot_read_contract, RP_SLOT_READ. unfold rp_slot_width_contract, RP_SLOT_WIDTH in HSW.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    MI ST LO HB HV.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof (u64_range a3) as Ra3.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 9 step.
  lazymatch goal with
  | FR : rw_cells _ ?m1 _ _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _, MI : mem_inv _ _ |- _ =>
    eapply evt_cut;
    [ eapply HSW with (lo := lo) (bs := bs);
      [ exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
      | intros HN50; destruct (HB HN50) as (HLEN & BB & DJ);
        split; [lia|]; split;
        [ eapply bytes_at_transport; [exact BB | exact MU | cbn [disjoint_from]; split; [lia | exact I]]
        | rewrite unsigned_lit by lia; lia ] ] |];
    intros ms' (a1' & a2' & a3' & m2 & -> & MU2 & WM2 & MI2 & ST2)
  end.
  rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU2, ST2 by lia.
  replace (ret_pc (Z_to_bv 64 79796)) with (Z_to_bv 64 79796) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (sw_model_range (bv_unsigned a1) bs (bv_signed a2)) as RNG.
  (* the facts about the caller's memory that both exits need *)
  assert (MU3 : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m2).
  { eapply munch_trans; [exact MU|].
    apply (munch_weaken [(bv_unsigned sp + -32 - 32, bv_unsigned sp + -32)]); [|exact MU2].
    intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | exact I]. }
  assert (WM3 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR2.
  clear FR MU WM MI.
  step. if_cases HOK.
  - (* the width is -1: nothing is read, nothing is written *)
    zify_cond HOK.
    assert (HNEG : rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) = -1)
      by (destruct RNG as [E|E]; [exact E | lia]).
    do 7 step.
    replace (rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)) with 0
      by (unfold rp_slot_read_model; rewrite HNEG; reflexivity).
    rewrite HNEG. cbn [Z.leb].
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. do 11 eexists. split; [reflexivity|].
    split; [exact WM3|]. split; [exact MI2|]. split; [exact ST2|]. exact MU3.
  - (* the width is a channel count: twelve samples are read and written *)
    zify_cond HOK.
    assert (HM0 : 2 <= rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) <= 40)
      by (destruct RNG as [E|E]; [rewrite E in HOK; lia | lia]).
    destruct (sw_geom (bv_unsigned a1) bs (bv_signed a2) ltac:(lia) ltac:(lia)) as (G1 & G2 & G3 & G4).
    assert (HN50 : 50 <= bv_unsigned a1) by lia.
    destruct (HB HN50) as (HLEN & BB & DJ).
    destruct (HV ltac:(lia)) as (HW & DJV & DJFV).
    pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
    pose proof HW as HWc. destruct HWc as (HW1 & HW2 & _).
    assert (Ea2 : bv_unsigned a2 = bv_signed a2).
    { pose proof (u64_range a2) as R2. pose proof G3 as G3'.
      unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in G3' |- *.
      change (2 ^ Z.of_N 64) with (2^64) in G3' |- *.
      revert G3'. Z.div_mod_to_equations. lia. }
    assert (L1 : Z.land (bv_unsigned a2) 1 = bv_signed a2 mod 2)
      by (rewrite land_1 by lia; rewrite Ea2; reflexivity).
    assert (L2 : Z.land (bv_unsigned a2) 18446744073709551614 = bv_signed a2 - bv_signed a2 mod 2)
      by (rewrite land_m2 by lia; rewrite Ea2; reflexivity).
    pose proof (Z.mod_pos_bound (bv_signed a2) 2 ltac:(lia)) as Rm2.
    do 15 step. 
    rewrite ?L1, ?L2. rewrite ?Z.shiftl_mul_pow2 by lia.
    eapply evt_mono.
    + eapply sr_loop with (m := m) (bs := bs) (f := bv_unsigned a0) (v := bv_unsigned a3)
        (nch := rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (slot := bv_signed a2)
        (lo := lo) (K := 12%nat) (s := 0).
      
      all: try lia.
      all: try (solve [ lazymatch goal with |- @eq Z (bv_unsigned _) _ => idtac end;
                        rw_inner_lit; lia ]).
      all: try (solve [ apply seqz5; lia ]).
      all: try reflexivity.
      
      (* the loop invariant at the first sample *)
      unfold INVR. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      * eapply bytes_at_transport; [exact BB | exact MU3 | cbn [disjoint_from]; split; [lia | exact I]].
      * exact FR2.
      * exact ST2.
      * eapply wr_at_transport; [exact HW | exact WM3].
      * exact MI2.
      * eapply munch_weaken; [| exact MU3].
        intros x Hx; cbn [outside] in *; split; [apply (proj1 Hx) | exact I].
      * exact WM3.
      * cbn [out_pref flat_map seq]. apply bytes_at_nil. lia.
    + intros ms' (t0' & t1' & t2' & b1' & b2' & b3' & b4' & b5' & b6' & b7' & m' & -> & W' & I' & S' & U' & B').
      replace (rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)) with 1
        by (unfold rp_slot_read_model; rewrite (proj2 (Z.ltb_ge _ 0)) by lia; reflexivity).
      rewrite (proj2 (Z.leb_le 0 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)))) by lia.
      do 11 eexists. split; [reflexivity|].
      split; [exact W'|]. split; [exact I'|]. split; [exact S'|]. split; [exact U' | exact B'].
Qed.

End SR.
