From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0 EgressFrame EgressBraid.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import
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

Lemma sw_unsigned_signed : forall x : word, 0 <= bv_signed x -> bv_unsigned x = bv_signed x.
Proof.
  intros x H. unfold bv_signed in *. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 64) with (2^63) in *. change (bv_modulus 64) with (2^64) in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sw_pair_le : forall nch slot, nch mod 2 = 0 -> 0 <= slot < nch -> slot - slot mod 2 <= nch - 2.
Proof. intros nch slot H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma sw_braid_bound : forall nch slot s j, 2 <= nch <= 40 -> nch mod 2 = 0 -> 0 <= slot < nch ->
  0 <= s <= 11 -> 50 <= braid_at nch slot s j /\ braid_at nch slot s j + 1 <= 50 + 36 * nch.
Proof.
  intros nch slot s j Hn He Hs Hs'. pose proof (sw_pair_le nch slot He Hs) as P.
  assert (Q : 0 <= slot - slot mod 2) by (Z.div_mod_to_equations; lia).
  unfold braid_at. destruct (slot mod 2 =? 0); destruct (j =? 0); try destruct (j =? 1); split; nia.
Qed.

Lemma sw_upto_length : forall nch slot vbs bs t, 2 <= nch <= 40 -> nch mod 2 = 0 -> 0 <= slot < nch ->
  (t <= 12)%nat -> 50 + 36 * nch <= Z.of_nat (length bs) ->
  length (slot_write_upto nch slot vbs bs t) = length bs.
Proof.
  intros nch slot vbs bs t Hn He Hs. induction t as [|t IH]; intros Ht HL; [reflexivity|].
  cbn [slot_write_upto].
  pose proof (sw_braid_bound nch slot (Z.of_nat t) 0 Hn He Hs ltac:(lia)) as B0.
  pose proof (sw_braid_bound nch slot (Z.of_nat t) 1 Hn He Hs ltac:(lia)) as B1.
  pose proof (sw_braid_bound nch slot (Z.of_nat t) 2 Hn He Hs ltac:(lia)) as B2.
  specialize (IH ltac:(lia) HL).
  set (L := slot_write_upto nch slot vbs bs t) in *.
  set (L1 := upd_bytes L (Z.to_nat (braid_at nch slot (Z.of_nat t) 0)) [nth (Z.to_nat (4 * Z.of_nat t)) vbs (Z_to_bv 8 0)]).
  assert (E1 : length L1 = length bs) by (unfold L1; rewrite upd_bytes_length; cbn [length]; lia).
  set (L2 := upd_bytes L1 (Z.to_nat (braid_at nch slot (Z.of_nat t) 1)) [nth (Z.to_nat (4 * Z.of_nat t + 1)) vbs (Z_to_bv 8 0)]).
  assert (E2 : length L2 = length bs) by (unfold L2; rewrite upd_bytes_length; cbn [length]; lia).
  rewrite upd_bytes_length; cbn [length]; lia.
Qed.

Ltac sw_reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end)
  end.
Ltac sw_setreg r v' tac := let v := sw_reg_val r in replace v with v' by tac.

Lemma sw_par' : forall z, z mod 2 = 0 \/ z mod 2 = 1.
Proof. intros z. pose proof (Z.mod_pos_bound z 2 ltac:(lia)). lia. Qed.

Section Loop.
Variables (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
Hypothesis HVB : 0 <= bv_unsigned a3 /\ bv_unsigned a3 + 48 <= 2^64.
Hypothesis DF : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0.
Hypothesis DV : bv_unsigned a3 + 48 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a3.
Hypothesis DFV : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned a3 \/ bv_unsigned a3 + 48 <= bv_unsigned a0.
Hypothesis Rsp : 64 <= bv_unsigned sp < 2^64.
Hypothesis HLO : lo + 64 <= bv_unsigned sp.
Hypothesis Hlo0 : 0 <= lo.

Notation f := (bv_unsigned a0).
Notation n := (bv_unsigned a1).
Notation v := (bv_unsigned a3).
Notation slot := (bv_signed a2).
Notation p := (bv_signed a2 mod 2).
Notation W := [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)].

Notation POST := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) <? 0 then 0 else 1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0) (rp_slot_write_bytes (bv_unsigned a1) bs (bv_signed a2) vbs)).

Definition sw_mem (mm : word -> option byte) (L : list byte) : Prop :=
  bytes_at rsegs mm f L /\ length L = length bs /\ wr_at rsegs mm f n /\ mem_inv rsegs mm /\
  munch W m mm /\ wmono rsegs m mm /\ bytes_at rsegs mm v vbs /\
  rw_cells rsegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\ stk rsegs mm lo (bv_unsigned sp + -32).

Lemma sw_store_ok : forall mm L k, sw_mem mm L -> 0 <= k -> k + 1 <= n -> store_ok rsegs mm (wa (f + k)) 1 = true.
Proof. intros mm L k (_ & _ & HW & _) Hk Hk1. apply (wr_at_store_ok rsegs mm f n k 1 HW); cbn; lia. Qed.

Lemma sw_mem_store : forall mm L k b, sw_mem mm L -> 0 <= k -> k + 1 <= n ->
  sw_mem (write_to_mem mm (wa (f + k)) [b]) (upd_bytes L (Z.to_nat k) [b]).
Proof.
  intros mm L k b H Hk Hk1. pose proof (sw_store_ok mm L k H Hk Hk1) as HS.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  assert (HLn : Z.of_nat (length L) = n) by lia.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply bytes_at_write_inside; [exact H1 | lia | cbn [length]; lia].
  - rewrite upd_bytes_length; cbn [length]; lia.
  - apply wr_at_write. exact H3.
  - apply mem_inv_store; [exact H4 | exact HS].
  - apply munch_write; [exact H5 | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; right; left; lia].
  - apply wmono_write. exact H6.
  - apply bytes_at_write_other; [exact H7 | lia | cbn [length Z.of_nat]; lia | rewrite HVL'; cbn [length Z.of_nat]; lia].
  - apply rw_cells_frame; [exact H8 | lia | cbn [length Z.of_nat]; lia |].
    change (Z.of_nat (cells_size [C8 s2; C8 s1; C8 s0; C8 ra])) with 32. cbn [length Z.of_nat]. lia.
  - apply stk_write; [exact H9 | lia | cbn [length Z.of_nat]; lia].
Qed.

Lemma sw_read : forall mm L a k, sw_mem mm L -> a = v + k -> 0 <= k < 48 ->
  ov_read_bytes rsegs mm (wa a) 1 = Some [nth (Z.to_nat k) vbs (Z_to_bv 8 0)].
Proof.
  intros mm L a k (_ & _ & _ & _ & _ & _ & HV & _) -> Hk.
  rewrite (bytes_at_read rsegs mm _ vbs k 1 HV) by lia. f_equal. apply sw_firstn1_skipn. lia.
Qed.

Lemma sw_par : p = 0 \/ p = 1.
Proof. pose proof (Z.mod_pos_bound slot 2 ltac:(lia)). lia. Qed.

Lemma sw_bnd : forall t j, 0 <= t <= 11 -> 0 <= braid_at nch slot t j /\ braid_at nch slot t j + 1 <= n.
Proof. intros t j Ht. pose proof (sw_braid_bound nch slot t j Hnch Hev Hslot Ht). lia. Qed.

Ltac sw_addr :=
  f_equal; unfold braid_at; destruct sw_par as [E|E]; rewrite E; cbv [Z.eqb Pos.eqb];
  rewrite ?unsigned_lit by (destruct sw_par as [E'|E']; rewrite E'; cbn; lia); ring.

Ltac sw_ld t k :=
  match goal with HM : sw_mem ?mm ?L |- _ =>
    let R := fresh "RV" in
    assert (R := sw_read mm L (v + 4 * t + k) (4 * t + k) HM ltac:(ring) ltac:(lia))
  end; step.

Ltac sw_st t j :=
  sw_setreg 5 (Z_to_bv 64 (f + braid_at nch slot t j)) sw_addr;
  match goal with HM : sw_mem ?mm ?L |- _ =>
    let HS := fresh "HS" in
    assert (HS := sw_store_ok mm L (braid_at nch slot t j) HM ltac:(apply sw_bnd; lia) ltac:(apply sw_bnd; lia));
    step; rewrite ?le1_zxb;
    change (Z_to_bv 64 (f + braid_at nch slot t j)) with (wa (f + braid_at nch slot t j));
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm _ [?b]) _) =>
      let HM' := fresh "HM" in
      assert (HM' := sw_mem_store mm L (braid_at nch slot t j) b HM ltac:(apply sw_bnd; lia) ltac:(apply sw_bnd; lia));
      clear HM HS;
      let mm' := fresh "mm" in
      remember (write_to_mem mm (wa (f + braid_at nch slot t j)) [b]) as mm' eqn:Emm; clear Emm
    end
  end.

Lemma sw_upto_S : forall t, 0 <= t ->
  slot_write_upto nch slot vbs bs (Z.to_nat (t + 1)) =
  upd_bytes (upd_bytes (upd_bytes (slot_write_upto nch slot vbs bs (Z.to_nat t))
      (Z.to_nat (braid_at nch slot t 0)) [nth (Z.to_nat (4 * t + 0)) vbs (Z_to_bv 8 0)])
      (Z.to_nat (braid_at nch slot t 1)) [nth (Z.to_nat (4 * t + 1)) vbs (Z_to_bv 8 0)])
      (Z.to_nat (braid_at nch slot t 2)) [nth (Z.to_nat (4 * t + 2)) vbs (Z_to_bv 8 0)].
Proof.
  intros t Ht. rewrite Z2Nat.inj_add by lia. replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.add_1_r. cbn [slot_write_upto]. rewrite Z2Nat.id by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma sw_loop : forall (i : nat) (t : Z) (x5 x8 x13 x17 : word) (mm : word -> option byte),
  t = 11 - Z.of_nat i -> 0 <= t ->
  sw_mem mm (slot_write_upto nch slot vbs bs (Z.to_nat t)) ->
  x8 = Z_to_bv 64 (v + 4 * t) -> x13 = Z_to_bv 64 (3 * (slot - p) + 3 * nch * t) ->
  evt rsegs POST
    (MS (mkR (Z_to_bv 64 0x13354) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 t1 t2 x8 (Z_to_bv 64 p)
             (Z_to_bv 64 (3 * nch)) (Z_to_bv 64 (f + 50)) (Z_to_bv 64 (v + 48)) x13
             (Z_to_bv 64 (f + 50 + p + 3)) (Z_to_bv 64 (f + 50 + p + 1)) (Z_to_bv 64 (if p =? 0 then 0 else 5)) x17
             a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13390) fc None mm (seg_rom rsegs)).
Proof.
  induction i as [|i IH]; intros t x5 x8 x13 x17 mm Et Ht HM -> ->.
  - cbn [Z.of_nat] in Et. subst t.
    set (L := slot_write_upto nch slot vbs bs (Z.to_nat (11 - 0))) in *.
    sw_ld (11 - Z.of_nat 0) 0. step. sw_st (11 - Z.of_nat 0) 0.
    sw_ld (11 - Z.of_nat 0) 1. step. step. sw_st (11 - Z.of_nat 0) 1.
    sw_ld (11 - Z.of_nat 0) 2. step. step. sw_st (11 - Z.of_nat 0) 2.
    step. step.
    replace (v + 4 * (11 - Z.of_nat 0) + 4) with (v + 48) by lia. rewrite bv_eqb_refl. cbn [negb].
    match goal with HM : sw_mem ?mm _ |- _ => destruct HM as (HB & HLL & HW & HI & MU & WM & HV & FR & ST) end.
    do 8 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 15 eexists. split.
    { rewrite Hw. rewrite (proj2 (Z.ltb_ge nch 0)) by lia. reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact HI|]. split; [exact ST|].
    unfold rp_slot_write_bytes. rewrite Hw, (proj2 (Z.ltb_ge nch 0)) by lia.
    replace 12%nat with (Z.to_nat ((11 - Z.of_nat 0) + 1)) by reflexivity.
    rewrite sw_upto_S by lia. exact HB.
  - assert (Ht11 : t <= 10) by lia.
    sw_ld t 0. step. sw_st t 0.
    sw_ld t 1. step. step. sw_st t 1.
    sw_ld t 2. step. step. sw_st t 2.
    step. step.
    let HC := fresh "HC" in
    if_cases HC; zify_cond HC; [| exfalso; Z.div_mod_to_equations; lia].
    eapply (IH (t + 1)); [lia | lia | | |].
    + rewrite sw_upto_S by lia. eassumption.
    + f_equal. ring.
    + f_equal. ring.
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
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 9 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  eapply evt_cut; [eapply (SWC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs lo) |].
  all: rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
  { assumption. }
  { exact ST. }
  { lia. }
  { intros H50. split; [lia|]. split; [exact HB|]. rewrite HL'. lia. }
  intros ms' (a1' & a2' & a3' & mB & -> & MU1 & WM1 & MI1 & ST1).
  replace (ret_pc (Z_to_bv 64 0x13354)) with (Z_to_bv 64 0x13354) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  clear ST HI. rename ST1 into ST. rename MI1 into HI.
  transport_after_call rsegs mA mB MU1 WM1.
  step.
  pose proof (sw_range (bv_unsigned a1) bs (bv_signed a2)) as RG.
  set (w := rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) in *.
  if_cases HC; zify_cond HC.
  - (* rp_slot_width < 0: return 0 *)
    assert (Hw : w < 0).
    { destruct (Z.ltb_spec w 0); [assumption|]. rewrite Z.mod_small in HC by lia. lia. }
    do 7 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 14 eexists. exists mB. split.
    + rewrite (proj2 (Z.ltb_lt w 0)) by exact Hw. reflexivity.
    + split; [exact MU|]. split; [exact WM|]. split; [exact HI|]. split; [exact ST|].
      unfold rp_slot_write_bytes. fold w. rewrite (proj2 (Z.ltb_lt w 0)) by exact Hw. exact HB.
  - assert (Hw : 0 <= w).
    { destruct (Z.ltb_spec w 0); [|assumption]. replace (w mod 2^64) with (w + 2^64) in HC by
        (symmetry; rewrite <- (Z.mod_add w 1 (2^64)) by lia; rewrite Z.mod_small by lia; ring). lia. }
    pose proof (sw_facts (bv_unsigned a1) bs (bv_signed a2) Ra1 Hw) as SF. cbv zeta in SF. fold w in SF.
    destruct SF as (Hnch & Hev & Hlen & Hslot).
    do 14 step.
    assert (Hun : bv_unsigned a2 = bv_signed a2) by (apply sw_unsigned_signed; lia).
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. change (bv_modulus 64) with (2^64) in Ra2.
    rewrite !sw_land_1, !land_m2 by lia. rewrite !Hun.
    pose proof (bytes_at_bound rsegs mB _ _ HB) as HBb. rewrite HL' in HBb.
    pose proof (bytes_at_bound rsegs mB _ _ HV) as HVb. rewrite HVL' in HVb.
    pose proof (Z.mod_pos_bound (bv_signed a2) 2 ltac:(lia)) as Rp.
    pose proof (sw_pair_le w (bv_signed a2) Hev Hslot) as Pl.
    sw_setreg 10 (Z_to_bv 64 (3 * w)) ltac:(f_equal; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
    sw_setreg 13 (Z_to_bv 64 (3 * (bv_signed a2 - bv_signed a2 mod 2) + 3 * w * 0))
      ltac:(f_equal; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
    sw_setreg 14 (Z_to_bv 64 (bv_unsigned a0 + 50 + bv_signed a2 mod 2 + 3)) ltac:(f_equal; lia).
    sw_setreg 15 (Z_to_bv 64 (bv_unsigned a0 + 50 + bv_signed a2 mod 2 + 1)) ltac:(f_equal; lia).
    sw_setreg 16 (Z_to_bv 64 (if bv_signed a2 mod 2 =? 0 then 0 else 5))
      ltac:(destruct (sw_par' (bv_signed a2)) as [E|E]; rewrite E; apply bv_eq; vm_compute; reflexivity).
    eapply (sw_loop ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs vbs lo w
              Hnch Hev Hlen Hslot eq_refl HL' HVL' ltac:(lia) Ha0 ltac:(lia) DF DV DFV ltac:(lia) HLO Hlo0 11%nat 0).
    all: try reflexivity. all: try lia.
    all: first [ (rewrite Z.mul_0_r, Z_to_bv_plus0; reflexivity)
               | exact (conj HB (conj eq_refl (conj HW (conj HI (conj MU (conj WM (conj HV (conj FR ST)))))))) ].
Qed.

End SW.
