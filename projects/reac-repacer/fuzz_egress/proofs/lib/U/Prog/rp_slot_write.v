(* rp_slot_write (fuzz_egress ubsan 44f6a3ebc228 at 0x1346c, statement rp_slot_write_c.v) given rp_slot_width_contract.
   The UBSan build keeps an 80-byte frame (ra, s0..s4 at sp+32 .. sp+72; the pos[3] array of the inlined
   reac_braid_pos at sp+8 / sp+16 / sp+24) and calls rp_slot_width (32 bytes more below its sp): 112 in all.
   Every check branches to the `unimp` at 0x135dc and is shown not taken from the statement's premises:
     0x1349c  f == NULL                         (0 < f)
     0x134a4  f + 50 overflows                  (f + n <= 2^64 and 124 <= n when the width is >= 0)
     0x134f0  s * nch  wraps in 32 bits         (s <= 11, nch <= 40)
     0x13500  s * nch + (slot & ~1) wraps       (<= 478)
     0x1351c, 0x13524, 0x1353c, 0x13548         &pos[j] overflows (the frame is below sp <= 2^64)
     0x13558  v + 4 s < v                       (v + 48 <= 2^64)
     0x13564  v and v + 4 s disagree on NULL    (0 < v, so both are non-null)
     0x13568  v is NULL or is not 4-aligned     (0 < v and v mod 4 = 0)
     0x1356c, 0x1357c, 0x1358c  f + 50 + pos[j] overflows  (braid_at + 1 <= 50 + 36 nch <= n)
   The memory model of the result is the plain build's: EgressFrame.slot_write_upto. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame EgressBraid.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import
  reac_frame_clean_len_c rp_frame_channels_c rp_slot_width_c rp_slot_write_c.
Import ListNotations.
Open Scope Z_scope.

Ltac sw_bools :=
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  repeat match goal with
   | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E]
   | E : (_ || _) = false |- _ => apply orb_false_iff in E; destruct E
   | E : (_ && _) = true |- _ => apply andb_true_iff in E; destruct E
   | E : (_ && _) = false |- _ => apply andb_false_iff in E; destruct E as [E|E]
   | E : negb _ = true |- _ => apply negb_true_iff in E
   | E : negb _ = false |- _ => apply negb_false_iff in E
   | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E
   | E : (_ =? _) = false |- _ => apply Z.eqb_neq in E
   | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
   | E : (_ <=? _) = false |- _ => apply Z.leb_gt in E
   | E : (_ <? _) = true |- _ => apply Z.ltb_lt in E
   | E : (_ <? _) = false |- _ => apply Z.ltb_ge in E
   | E : Z.odd _ = true |- _ => rewrite Zodd_mod in E; apply Z.eqb_eq in E
   | E : Z.odd _ = false |- _ => rewrite Zodd_mod in E; apply Z.eqb_neq in E
   end.

Lemma sw_range : forall n bs slot, -1 <= rp_slot_width_model n bs slot <= 40.
Proof.
  intros n bs slot.
  unfold rp_slot_width_model, rp_frame_channels_model. sw_bools; lia.
Qed.

(* What a non-negative width tells: the width, the slot and the frame's length. *)
Lemma sw_facts : forall n bs slot, 0 <= n < 2^64 -> 0 <= rp_slot_width_model n bs slot ->
  let nch := rp_slot_width_model n bs slot in
  2 <= nch <= 40 /\ nch mod 2 = 0 /\ 52 + 36 * nch <= n /\ 0 <= slot < nch.
Proof.
  intros n bs slot Hn Hm. cbv zeta. revert Hm.
  unfold rp_slot_width_model, rp_frame_channels_model, reac_frame_clean_len_model.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  sw_bools; intros Hm; try lia.
  all: Z.div_mod_to_equations; nia.
Qed.

Lemma sw_firstn1_skipn : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof. induction bs as [|b bs IH]; intros [|k] d H; cbn in *; try lia; auto. apply IH; lia. Qed.



Lemma sw_land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.

Lemma sw_land_3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. exact (Z.land_ones x 2 ltac:(lia)). Qed.

Lemma sw_unsigned_signed : forall x : word, 0 <= bv_signed x -> bv_unsigned x = bv_signed x.
Proof.
  intros x H. unfold bv_signed in *. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 64) with (2^63) in *. change (bv_modulus 64) with (2^64) in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sw_pair_le : forall nch slot, nch mod 2 = 0 -> 0 <= slot < nch -> slot - slot mod 2 <= nch - 2.
Proof. intros nch slot H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma sw_pair_ge : forall slot, 0 <= slot -> 0 <= slot - slot mod 2.
Proof. intros slot H. Z.div_mod_to_equations. lia. Qed.

Lemma sw_braid_bound : forall nch slot s j, 2 <= nch <= 40 -> nch mod 2 = 0 -> 0 <= slot < nch ->
  0 <= s <= 11 -> 50 <= braid_at nch slot s j /\ braid_at nch slot s j + 1 <= 50 + 36 * nch.
Proof.
  intros nch slot s j Hn He Hs Hs'. pose proof (sw_pair_le nch slot He Hs) as P.
  assert (Q : 0 <= slot - slot mod 2) by (Z.div_mod_to_equations; lia).
  unfold braid_at. destruct (slot mod 2 =? 0); destruct (j =? 0); try destruct (j =? 1); split; nia.
Qed.

Lemma sw_par' : forall z, z mod 2 = 0 \/ z mod 2 = 1.
Proof. intros z. pose proof (Z.mod_pos_bound z 2 ltac:(lia)). lia. Qed.

Lemma sw_upd_app : forall (a c bs : list byte) k, (k + length bs <= length a)%nat ->
  upd_bytes (a ++ c) k bs = upd_bytes a k bs ++ c.
Proof.
  intros a c bs k H. unfold upd_bytes.
  rewrite firstn_app, skipn_app.
  replace (k - length a)%nat with 0%nat by lia. replace (k + length bs - length a)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

(* A store inside the frame's junk cell keeps the cell list's shape. *)
Lemma sw_frame_store : forall m A sz fj rest (k : Z) (bs : list byte),
  rw_cells rsegs m A (CB sz fj :: rest) -> length bs = 8%nat -> 0 <= k -> (Z.to_nat k + 8 <= sz)%nat ->
  rw_cells rsegs (write_to_mem m (wa (A + k)) bs) A (CB sz (upd_bytes fj (Z.to_nat k) bs) :: rest).
Proof.
  intros m A sz fj rest k bs [[Hwf Hb] Hw] Hl Hk Hk8.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hfj Hrest].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length; lia | exact Hrest].
  - cbn [cells_bytes cbytes] in *.
    apply (bytes_at_write_inside rsegs m A (fj ++ cells_bytes rest) k bs) in Hb;
      [| lia | rewrite app_length; lia].
    rewrite sw_upd_app in Hb by lia. exact Hb.
  - cbn [cells_size csize] in *. apply wr_at_write. exact Hw.
Qed.

Ltac sw_reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end)
  end.
Ltac sw_setreg r v' tac :=
  let v := sw_reg_val r in first [ constr_eq v v' | replace v with v' by tac ].

(* The normal form of an arithmetic register value. *)
Ltac sw_val :=
  f_equal; rewrite ?unsigned_lit by lia;
  rewrite ?bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia);
  rewrite ?unsigned_lit by lia;
  rewrite ?Z.shiftl_mul_pow2 by lia;
  first [ reflexivity | ring | lia ].

Lemma sw_upto_S : forall nch slot vbs bs t, 0 <= t ->
  slot_write_upto nch slot vbs bs (Z.to_nat (t + 1)) =
  upd_bytes (upd_bytes (upd_bytes (slot_write_upto nch slot vbs bs (Z.to_nat t))
      (Z.to_nat (braid_at nch slot t 0)) [nth (Z.to_nat (4 * t + 0)) vbs (Z_to_bv 8 0)])
      (Z.to_nat (braid_at nch slot t 1)) [nth (Z.to_nat (4 * t + 1)) vbs (Z_to_bv 8 0)])
      (Z.to_nat (braid_at nch slot t 2)) [nth (Z.to_nat (4 * t + 2)) vbs (Z_to_bv 8 0)].
Proof.
  intros nch slot vbs bs t Ht. rewrite Z2Nat.inj_add by lia. replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.add_1_r. cbn [slot_write_upto]. rewrite Z2Nat.id by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Section Loop.
Variables (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs vbs : list byte) (lo nch : Z).
Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hlen : 52 + 36 * nch <= bv_unsigned a1.
Hypothesis Hslot : 0 <= bv_signed a2 < nch.
Hypothesis Hw : rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) = nch.
Hypothesis HL' : Z.of_nat (length bs) = bv_unsigned a1.
Hypothesis HVL' : Z.of_nat (length vbs) = 48.
Hypothesis HFB : bv_unsigned a0 + bv_unsigned a1 <= 2^64.
Hypothesis Ha0 : 0 < bv_unsigned a0.
Hypothesis HVB : 0 < bv_unsigned a3 /\ bv_unsigned a3 + 48 <= 2^64.
Hypothesis DF : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0.
Hypothesis DV : bv_unsigned a3 + 48 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a3.
Hypothesis DFV : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned a3 \/ bv_unsigned a3 + 48 <= bv_unsigned a0.
Hypothesis Rsp : 112 <= bv_unsigned sp < 2^64.
Hypothesis HLO : lo + 112 <= bv_unsigned sp.
Hypothesis Hlo0 : 0 <= lo.

Notation f := (bv_unsigned a0).
Notation n := (bv_unsigned a1).
Notation v := (bv_unsigned a3).
Notation slot := (bv_signed a2).
Notation p := (bv_signed a2 mod 2).
Notation W := [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)].

Notation POST := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) <? 0 then 0 else 1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0) (rp_slot_write_bytes (bv_unsigned a1) bs (bv_signed a2) vbs)).

Definition sw_mem (mm : word -> option byte) (L : list byte) : Prop :=
  bytes_at rsegs mm f L /\ length L = length bs /\ wr_at rsegs mm f n /\ mem_inv rsegs mm /\
  munch W m mm /\ wmono rsegs m mm /\ bytes_at rsegs mm v vbs /\
  (exists fj, rw_cells rsegs mm (bv_unsigned sp + -80)
     [CB 32 fj; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
  stk rsegs mm lo (bv_unsigned sp + -80).

Lemma sw_par : p = 0 \/ p = 1.
Proof. pose proof (Z.mod_pos_bound slot 2 ltac:(lia)). lia. Qed.

Lemma sw_sp0 : 0 <= slot - p.
Proof. apply sw_pair_ge. lia. Qed.

Lemma sw_sp1 : slot - p <= nch - 2.
Proof. apply sw_pair_le; [exact Hev | lia]. Qed.

Lemma sw_bnd : forall t j, 0 <= t <= 11 -> 50 <= braid_at nch slot t j /\ braid_at nch slot t j + 1 <= n.
Proof. intros t j Ht. pose proof (sw_braid_bound nch slot t j Hnch Hev Hslot Ht). lia. Qed.

Lemma sw_store_ok : forall mm L k, sw_mem mm L -> 0 <= k -> k + 1 <= n ->
  store_ok rsegs mm (Z_to_bv 64 (f + k)) 1 = true.
Proof.
  intros mm L k (_ & _ & HW & _) Hk Hk1. change (Z_to_bv 64 (f + k)) with (wa (f + k)).
  apply (wr_at_store_ok rsegs mm f n k 1 HW); cbn; lia.
Qed.

Lemma sw_pos_ok : forall mm L (d : Z), sw_mem mm L -> -80 <= d -> d <= -56 ->
  store_ok rsegs mm (Z_to_bv 64 (bv_unsigned sp + d)) 8 = true.
Proof.
  intros mm L d (_ & _ & _ & _ & _ & _ & _ & (fj & _ & HW) & _) Hd1 Hd2.
  cbn [cells_size csize Nat.add] in HW.
  change (Z_to_bv 64 (bv_unsigned sp + d)) with (wa (bv_unsigned sp + d)).
  replace (bv_unsigned sp + d) with (bv_unsigned sp + -80 + (d + 80)) by lia.
  apply (wr_at_store_ok rsegs mm (bv_unsigned sp + -80) (Z.of_nat 80) (d + 80) 8); [exact HW | lia | lia].
Qed.

Lemma sw_mem_store : forall mm L k b, sw_mem mm L -> 0 <= k -> k + 1 <= n ->
  sw_mem (write_to_mem mm (Z_to_bv 64 (f + k)) [b]) (upd_bytes L (Z.to_nat k) [b]).
Proof.
  intros mm L k b H Hk Hk1. pose proof (sw_store_ok mm L k H Hk Hk1) as HS.
  change (Z_to_bv 64 (f + k)) with (wa (f + k)) in HS |- *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (fj & H8) & H9).
  assert (HLn : Z.of_nat (length L) = n) by lia.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply bytes_at_write_inside; [exact H1 | lia | cbn [length]; lia].
  - rewrite upd_bytes_length; cbn [length]; lia.
  - apply wr_at_write. exact H3.
  - apply mem_inv_store; [exact H4 | exact HS].
  - apply munch_write; [exact H5 | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; right; left; lia].
  - apply wmono_write. exact H6.
  - apply bytes_at_write_other; [exact H7 | lia | cbn [length Z.of_nat]; lia | rewrite HVL'; cbn [length Z.of_nat]; lia].
  - exists fj. apply rw_cells_frame; [exact H8 | lia | cbn [length Z.of_nat]; lia |].
    change (Z.of_nat (cells_size [CB 32 fj; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) with 80.
    cbn [length Z.of_nat]. lia.
  - apply stk_write; [exact H9 | lia | cbn [length Z.of_nat]; lia].
Qed.

Lemma sw_mem_pos : forall mm L (x : word) (d : Z), sw_mem mm L -> -80 <= d -> d <= -56 ->
  sw_mem (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + d)) (le8 x)) L.
Proof.
  intros mm L x d H Hd1 Hd2. pose proof (sw_pos_ok mm L d H Hd1 Hd2) as HS.
  change (Z_to_bv 64 (bv_unsigned sp + d)) with (wa (bv_unsigned sp + d)) in HS |- *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (fj & H8) & H9).
  assert (HLn : Z.of_nat (length L) = n) by lia.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply bytes_at_write_other; [exact H1 | lia | rewrite length_le8 | rewrite length_le8]; cbn [Z.of_nat]; lia.
  - exact H2.
  - apply wr_at_write. exact H3.
  - apply mem_inv_store; [exact H4 | rewrite length_le8; exact HS].
  - apply munch_write; [exact H5 | lia | rewrite length_le8; cbn [Z.of_nat]; lia |].
    rewrite length_le8. cbn [inside Z.of_nat]. left. lia.
  - apply wmono_write. exact H6.
  - apply bytes_at_write_other; [exact H7 | lia | rewrite length_le8; cbn [Z.of_nat]; lia |].
    rewrite length_le8, HVL'. cbn [Z.of_nat]. lia.
  - exists (upd_bytes fj (Z.to_nat (d + 80)) (le8 x)).
    replace (bv_unsigned sp + d) with (bv_unsigned sp + -80 + (d + 80)) by lia.
    apply sw_frame_store; [exact H8 | apply length_le8 | lia | lia].
  - apply stk_write; [exact H9 | lia | rewrite length_le8; cbn [Z.of_nat]; lia].
Qed.

Lemma sw_read : forall mm L a k, sw_mem mm L -> a = v + k -> 0 <= k < 48 ->
  ov_read_bytes rsegs mm (wa a) 1 = Some [nth (Z.to_nat k) vbs (Z_to_bv 8 0)].
Proof.
  intros mm L a k (_ & _ & _ & _ & _ & _ & HV & _) -> Hk.
  rewrite (bytes_at_read rsegs mm _ vbs k 1 HV) by lia. f_equal. apply sw_firstn1_skipn. lia.
Qed.

(* A check whose trap branch the premises rule out. *)
Ltac sw_trapgoal H := first [ lia | cbv delta [wa] in H; zsimp_in H; lia ].
Ltac sw_notaken := let H := fresh "HT" in if_cases H; zify_cond H; [exfalso; sw_trapgoal H | ].
Ltac sw_taken := let H := fresh "HT" in if_cases H; zify_cond H; [ | exfalso; sw_trapgoal H ].

Ltac sw_eqlia := f_equal; lia.
Ltac sw_braid E :=
  f_equal; try unfold braid_at; rewrite ?E; cbv [Z.eqb Pos.eqb]; first [ ring | lia ].

Ltac sw_ld t k :=
  match goal with HM : sw_mem ?mm ?L |- _ =>
    let R := fresh "RV" in
    assert (R := sw_read mm L (v + 4 * t + k) (4 * t + k) HM ltac:(ring) ltac:(lia))
  end; step.

Ltac sw_st t j :=
  match goal with HM : sw_mem ?mm ?L |- _ =>
    let HS := fresh "HS" in
    assert (HS := sw_store_ok mm L (braid_at nch slot t j) HM ltac:(lia) ltac:(lia));
    step; rewrite ?le1_zxb;
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm _ [?b]) _) =>
      let HM' := fresh "HM" in
      assert (HM' := sw_mem_store mm L (braid_at nch slot t j) b HM ltac:(lia) ltac:(lia));
      clear HM HS;
      let mm' := fresh "mm" in
      remember (write_to_mem mm (Z_to_bv 64 (f + braid_at nch slot t j)) [b]) as mm' eqn:Emm; clear Emm
    end
  end.

Ltac sw_pos d :=
  match goal with HM : sw_mem ?mm ?L |- _ =>
    let HS := fresh "HS" in
    assert (HS := sw_pos_ok mm L d HM ltac:(lia) ltac:(lia));
    step;
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm _ (le8 ?x)) _) =>
      let HM' := fresh "HM" in
      assert (HM' := sw_mem_pos mm L x d HM ltac:(lia) ltac:(lia));
      clear HM HS;
      let mm' := fresh "mm" in
      remember (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + d)) (le8 x)) as mm' eqn:Emm; clear Emm
    end
  end.

(* 0x134e8 .. 0x135ac: one sample. Leaves the loop's back branch undecided. *)
Ltac sw_body t :=
  pose proof (sw_bnd t 0 ltac:(lia)) as B0;
  pose proof (sw_bnd t 1 ltac:(lia)) as B1;
  pose proof (sw_bnd t 2 ltac:(lia)) as B2;
  assert (HX : 0 <= t * nch <= 440) by nia;
  (* 0x134e8 mul t6, a1, a0 *)
  step; sw_setreg 31 (Z_to_bv 64 (t * nch)) ltac:(sw_val);
  (* 0x134ec mulw s2, a1, a0 ; 0x134f0 bne *)
  step; sw_setreg 18 (Z_to_bv 64 (t * nch)) ltac:(sw_val);
  step; rewrite bv_eqb_refl; cbn [negb];
  (* 0x134f4 sext.w s2, t6 *)
  step; sw_setreg 18 (Z_to_bv 64 (t * nch)) ltac:(sw_val);
  (* 0x134f8 add t6, s2, a3 ; 0x134fc addw s2, s2, a3 ; 0x13500 bne *)
  step; sw_setreg 31 (Z_to_bv 64 (t * nch + (slot - p))) ltac:(sw_val);
  step; sw_setreg 18 (Z_to_bv 64 (t * nch + (slot - p))) ltac:(sw_val);
  step; rewrite bv_eqb_refl; cbn [negb];
  (* 0x13504 sext.w t6, t6 *)
  step; sw_setreg 31 (Z_to_bv 64 (t * nch + (slot - p))) ltac:(sw_val);
  (* 0x13508 slli s3, t6, 1 ; 0x1350c add s3, s3, t6 *)
  step; sw_setreg 19 (Z_to_bv 64 (2 * (t * nch + (slot - p)))) ltac:(sw_val);
  step; sw_setreg 19 (Z_to_bv 64 (3 * (t * nch + (slot - p)))) ltac:(sw_val);
  (* 0x13510 bnez s1: the slot's parity *)
  step;
  destruct sw_par as [Ep|Ep];
  [ (* even: 0x13514 .. 0x13530; s2 keeps 3 X and s4 keeps 1, the join normalises both *)
    sw_notaken;
    step; sw_setreg 31 (Z_to_bv 64 (braid_at nch slot t 0 - 50)) ltac:(sw_braid Ep);
    sw_pos (-72);                   (* 0x13518 pos[0] = 3 X + 3 *)
    step; sw_notaken;               (* 0x1351c *)
    sw_pos (-64);                   (* 0x13520 pos[1] = 3 X *)
    step; sw_notaken;               (* 0x13524 *)
    step; step; step                (* 0x13528 s4 = 1 ; 0x1352c s2 = s3 ; 0x13530 j *)
  | (* odd: 0x13534 .. 0x1354c *)
    sw_taken;
    step; sw_setreg 31 (Z_to_bv 64 (braid_at nch slot t 0 - 50)) ltac:(sw_braid Ep);
    sw_pos (-72);                   (* 0x13538 pos[0] = 3 X + 4 *)
    step; sw_notaken;               (* 0x1353c *)
    step;                           (* 0x13540 s2 = 3 X + 5 *)
    sw_pos (-64);                   (* 0x13544 pos[1] *)
    step; sw_notaken;               (* 0x13548 *)
    step                            (* 0x1354c s4 = 2 *)
  ];
  (* 0x13550 add s3, s3, s4 ; 0x13554 sd s3, 0x18(sp) *)
  step; sw_setreg 19 (Z_to_bv 64 (braid_at nch slot t 2 - 50)) ltac:(sw_braid Ep);
  sw_setreg 18 (Z_to_bv 64 (braid_at nch slot t 1 - 50)) ltac:(sw_braid Ep);
  sw_pos (-56);
  (* 0x13558 bltu t5, s0 (v + 4 s >= v) *)
  step; sw_notaken;
  (* 0x1355c seqz s4, t5 ; 0x13560 xor s4, a4, s4 ; 0x13564 beqz s4 ; 0x13568 beqz t2 *)
  step; sw_setreg 20 (Z_to_bv 64 0)
    ltac:(unfold v_sltiu; replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity);
          rewrite unsigned_lit by lia;
          replace (v + 4 * t <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity);
  step; sw_setreg 20 (Z_to_bv 64 1) ltac:(first [ reflexivity | apply bv_eq; vm_compute; reflexivity ]);
  step; if_false;
  step; if_false;
  (* 0x1356c bltu t1, t6 ; 0x13570 lbu ; 0x13574 add t6, a2, t6 ; 0x13578 sb *)
  step; sw_notaken; sw_ld t 0;
  step; sw_setreg 31 (Z_to_bv 64 (f + braid_at nch slot t 0)) ltac:(sw_eqlia); sw_st t 0;
  (* 0x1357c bltu t1, s2 ; 0x13580 lbu ; 0x13584 add s2, a2, s2 ; 0x13588 sb *)
  step; sw_notaken; sw_ld t 1;
  step; sw_setreg 18 (Z_to_bv 64 (f + braid_at nch slot t 1)) ltac:(sw_eqlia); sw_st t 1;
  (* 0x1358c bltu t1, s3 ; 0x13590 add s3, a2, s3 ; 0x13594 lbu *)
  step; sw_notaken;
  step; sw_setreg 19 (Z_to_bv 64 (f + braid_at nch slot t 2)) ltac:(sw_eqlia); sw_ld t 2;
  (* 0x13598 addiw a1 ; 0x1359c addi t5 ; 0x135a0 addi a5 ; 0x135a4 sb ; 0x135a8 addi t4 ; 0x135ac bnez *)
  step; step; step; sw_st t 2; step; step.

(* the last sample's back branch is not taken: restore and return 1 *)
Ltac sw_exit t :=
  let HC := fresh "HC" in
  let HB := fresh "HB" in let HLL := fresh "HLL" in let HWx := fresh "HWx" in
  let HIx := fresh "HIx" in let MU := fresh "MU" in let WM := fresh "WM" in
  let HVx := fresh "HVx" in let FR := fresh "FR" in let ST := fresh "ST" in
  let fj := fresh "fj" in
  if_cases HC; zify_cond HC; [exfalso; lia |];
  (* 0x135b0 addi a0, zero, 1 ; 0x135b4 j ; the epilogue *)
  step; step;
  match goal with HMx : sw_mem _ _ |- _ =>
    destruct HMx as (HB & HLL & HWx & HIx & MU & WM & HVx & FR & ST) end;
  destruct FR as [fj FR];
  do 8 step;
  release_frame FR ST (bv_unsigned sp);
  apply evt_done; do 15 eexists; split;
  [ rewrite Hw; rewrite (proj2 (Z.ltb_ge nch 0)) by lia; reflexivity
  | split; [exact MU|]; split; [exact WM|]; split; [exact HIx|]; split; [exact ST|];
    unfold rp_slot_write_bytes; rewrite Hw, (proj2 (Z.ltb_ge nch 0)) by lia;
    replace 12%nat with (Z.to_nat (t + 1)) by lia;
    rewrite sw_upto_S by lia; exact HB ].

(* the back branch is taken: the next sample *)
Ltac sw_next t IH :=
  let HC := fresh "HC" in
  if_cases HC; zify_cond HC; [| exfalso; lia];
  eapply (IH (t + 1));
  [ lia | lia
  | rewrite sw_upto_S by lia; eassumption
  | f_equal; rewrite unsigned_lit by lia;
    rewrite bv_swrap_small; [lia | change (bv_half_modulus 32) with (2^31); lia]
  | f_equal; lia | f_equal; lia | f_equal; lia ].
Lemma sw_loop : forall (i : nat) (t : Z) (x11 x15 x18 x19 x20 x29 x30 x31 : word) (mm : word -> option byte),
  t = 11 - Z.of_nat i -> 0 <= t ->
  sw_mem mm (slot_write_upto nch slot vbs bs (Z.to_nat t)) ->
  x11 = Z_to_bv 64 t -> x15 = Z_to_bv 64 (12 - t) ->
  x29 = Z_to_bv 64 (v + 4 * t) -> x30 = Z_to_bv 64 (v + 4 * t) ->
  evt rsegs POST
    (MS (mkR (Z_to_bv 64 0x13498) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp
             (Z_to_bv 64 (-17)) (Z_to_bv 64 (18446744073709551615 - (f + 50))) (Z_to_bv 64 1)
             a3 (Z_to_bv 64 p) (Z_to_bv 64 nch) x11 (Z_to_bv 64 (f + 50)) (Z_to_bv 64 (slot - p))
             (Z_to_bv 64 1) x15 (Z_to_bv 64 (-8)) (Z_to_bv 64 (bv_unsigned sp + -72))
             x18 x19 x20 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 (-9)) x29 x30 x31)
        F (Z_to_bv 64 0x134e8) fc None mm (seg_rom rsegs)).
Proof.
  pose proof sw_sp0 as SP0. pose proof sw_sp1 as SP1.
  pose proof HVB as [HV0 HV1].
  induction i as [|i IH]; intros t x11 x15 x18 x19 x20 x29 x30 x31 mm Et Ht HM -> -> -> ->.
  - (* the last sample: leave the loop *)
    assert (Ht11 : t = 11) by lia.
    sw_body t; sw_exit t.
  - assert (Ht11 : t <= 10) by lia.
    sw_body t; sw_next t IH.
Qed.

End Loop.

Section SW.
Variable SWC : rp_slot_width_contract.

Theorem rp_slot_write_holds : rp_slot_write_contract.
Proof.
  unfold rp_slot_write_contract, RP_SLOT_WRITE, RP_SLOT_WRITE_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs vbs lo
    HI ST HLO Ha0 HB HL HW HV HVL Hv0 Hv4 DF DV DFV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. change (bv_modulus 64) with (2^64) in Ra1.
  assert (HL' : Z.of_nat (length bs) = bv_unsigned a1) by (rewrite HL; lia).
  assert (HVL' : Z.of_nat (length vbs) = 48) by (rewrite HVL; reflexivity).
  assert (Hlo0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  eapply evt_cut; [eapply (SWC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs lo) |].
  all: rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by lia.
  { assumption. }
  { exact ST. }
  { lia. }
  { intros H50. split; [lia|]. split; [lia|]. split; [exact HB|]. rewrite HL'. lia. }
  intros ms' (a1' & a2' & a3' & mB & -> & MU1 & WM1 & MI1 & ST1).
  replace (ret_pc (Z_to_bv 64 0x13498)) with (Z_to_bv 64 0x13498) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  clear ST HI. rename ST1 into ST. rename MI1 into HI.
  transport_after_call rsegs mA mB MU1 WM1.
  step.
  pose proof (sw_range (bv_unsigned a1) bs (bv_signed a2)) as RG.
  set (w := rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) in *.
  if_cases HC; zify_cond HC.
  - (* rp_slot_width < 0: return 0 *)
    assert (Hwn : w < 0).
    { destruct (Z.ltb_spec w 0); [assumption|]. rewrite Z.mod_small in HC by lia. lia. }
    do 9 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 14 eexists. exists mB. split.
    + rewrite (proj2 (Z.ltb_lt w 0)) by exact Hwn. reflexivity.
    + split; [exact MU|]. split; [exact WM|]. split; [exact HI|]. split; [exact ST|].
      unfold rp_slot_write_bytes. fold w. rewrite (proj2 (Z.ltb_lt w 0)) by exact Hwn. exact HB.
  - assert (Hwp : 0 <= w).
    { destruct (Z.ltb_spec w 0); [|assumption]. replace (w mod 2^64) with (w + 2^64) in HC by
        (symmetry; rewrite <- (Z.mod_add w 1 (2^64)) by lia; rewrite Z.mod_small by lia; ring). lia. }
    pose proof (sw_facts (bv_unsigned a1) bs (bv_signed a2) Ra1 Hwp) as SF. cbv zeta in SF. fold w in SF.
    destruct SF as (Hnch & Hev & Hlen & Hslot).
    assert (Hun : bv_unsigned a2 = bv_signed a2) by (apply sw_unsigned_signed; lia).
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. change (bv_modulus 64) with (2^64) in Ra2.
    pose proof (bytes_at_bound rsegs mB _ _ HB) as HBb. rewrite HL' in HBb.
    pose proof (bytes_at_bound rsegs mB _ _ HV) as HVb. rewrite HVL' in HVb.
    pose proof (Z.mod_pos_bound (bv_signed a2) 2 ltac:(lia)) as Rp.
    (* 0x1349c beqz s2 (f <> 0) ; 0x134a0 ; 0x134a4 bltu a1, s2 (f + 50 does not overflow) *)
    step. if_false.
    step.
    step. if_false.
    do 16 step.
    sw_setreg 9 (Z_to_bv 64 (bv_signed a2 mod 2))
      ltac:(f_equal; rewrite sw_land_1; rewrite Hun; reflexivity).
    sw_setreg 13 (Z_to_bv 64 (bv_signed a2 - bv_signed a2 mod 2))
      ltac:(f_equal; rewrite land_m2 by lia; rewrite Hun; reflexivity).
    sw_setreg 14 (Z_to_bv 64 1)
      ltac:(unfold v_sltu, c_ltu, bv_ltu; rewrite unsigned_lit by lia;
            replace (0 <? bv_unsigned a3) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    sw_setreg 7 (Z_to_bv 64 1)
      ltac:(unfold v_sltiu; replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity);
            rewrite unsigned_lit by (rewrite sw_land_3; lia); rewrite sw_land_3;
            replace (bv_unsigned a3 mod 4 <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    sw_setreg 6 (Z_to_bv 64 (18446744073709551615 - (bv_unsigned a0 + 50)))
      ltac:(f_equal; rewrite unsigned_lit by lia; symmetry; apply zb_lxor_ones; lia).
    eapply sw_loop with (i := 11%nat) (t := 0).
    all: try lia.
    all: try reflexivity.
    all: try (rewrite Z.mul_0_r, Z_to_bv_plus0; reflexivity).
    (* what is left: the frame's cells and the memory facts *)
    unfold sw_mem. cbn [slot_write_upto Z.to_nat].
    split; [exact HB|]. split; [reflexivity|]. split; [exact HW|]. split; [exact HI|].
    split; [exact MU|]. split; [exact WM|]. split; [exact HV|].
    split; [eexists; exact FR|]. exact ST.
Qed.

End SW.
