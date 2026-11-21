(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit Z_infl_iface Z_infl_c_pure Z_infl_c_tab Z_infl_t_iface Zg_infl_t_iface Zg_infl_c_kit Z_itab_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1 RefInflateA_LENLENS2 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma rod_order : forall m, mem_inv usegs m -> bytes_at usegs m Z_ORDER (u16s (av16 order_a 19)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_ORDER; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma order_rd : forall m i a, mem_inv usegs m -> 0 <= i < 19 -> a = wa (Z_ORDER + 2 * i) ->
  ov_read_bytes usegs m a 2 = Some (le2 (wz (arr_get order_a i))).
Proof.
  intros m i a MI Hi ->. eapply u16ro_read; [exact (rod_order m MI)| apply av16_nth; exact Hi| lia| reflexivity].
Qed.
Lemma ll_arm_entry : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_LENLENS x26 x12 ms -> 0 <= is_have s <= 19 ->
  evt usegs (fun ms' => exists q, ILOOPh X (mkW s c r) PC_LENLENS_E q ms' /\ h17 q = wz (is_have s) /\ h14 q = wz (il_NI (ix_L X) + ir_next r)
                                  /\ h12 q = wz (ir_have r) /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
                                  /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)) ms.
Proof.
  intros X s c r x26 x12 ms HL RH.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_LENLENS. do 4 zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|]. hred. repeat split; reflexivity.
Qed.
Definition PC_LL1_H : Z := 0x1fae8.
Definition PC_LL1_B : Z := 0x1fb20.
Definition PC_LL2 : Z := 0x1fb88.
Definition ll1_Q (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h10 q = wz Z_ORDER /\ h11 q = wz (is_ncode s) /\ h13 q = wz 18446744073709551597 /\ h15 q = wz (is_have s + 1) /\ h16 q = wz (18446744073709551616 - is_ncode s)
  /\ h17 q = wz (2 * is_have s) /\ h14 q = wz (il_NI (ix_L X) + ir_next r) /\ h12 q = wz (ir_have r)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).
Lemma zext32_x2 : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 31 = 2 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^31) with 2147483648. Z.div_mod_to_equations. lia.
Qed.
Lemma ll_entry : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LENLENS_E q ms ->
  h17 q = wz (is_have s) -> h14 q = wz (il_NI (ix_L X) + ir_next r) -> h12 q = wz (ir_have r) ->
  h9 q = wz (il_NO (ix_L X) + ir_put r) -> h18 q = wz (ir_bits r) -> h22 q = wz (ir_hold r) ->
  0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r) PC_LL1_H q' ms' /\ ll1_Q X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL E17 E14 E12 E9 E18 E22 RH RN.
  destruct HL as (m & -> & HMEM). hred_in E17. hred_in E14. hred_in E12. hred_in E9. hred_in E18. hred_in E22. subst x17 x14 x12 x9 x18 x22.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_LENLENS_E.
  do 4 zs. br_false. do 3 zs. br_false. do 6 zs.
  rewrite unsigned_lit by lia. rewrite zext32_x2 by lia.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity; exact HMEM|].
  unfold ll1_Q. hred. unfold Z_ORDER. repeat split; ireg.
Qed.
Definition PC_LL1_DRY : Z := 0x21758.
Lemma ll1_head : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGSg c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATG X (mkW s c r) ->
  evt usegs (NBJq X s c r 3 PC_LL1_B (fun r1 q1 => ll1_Q X s r1 q1)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO DR Rin HP.
  unfold ll1_Q in HQ. hred_in HQ. destruct HQ as (E10 & E11 & E13 & E15 & E16 & E17 & E14 & E12 & E9 & E18 & E22). subst x10 x11 x13 x15 x16 x17 x14 x12 x9 x18 x22.
  destruct HL as (m & -> & HMEM). hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct DR as (Rn & [Rh HAV] & Rnh & RB & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_LL1_H. ix_open XO.
  do 2 zs. br_cases K.
  -
    apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; try reflexivity. exact HMEM.
    + unfold ll1_Q. hred. repeat split; reflexivity.
  - zs. br_cases K2.
    +
      assert (H1 : 0 < ir_have r) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. zs. zs. br_cases KG; [| exfalso; lia].
      zs. zs. zs. clear RD. zs. zs. zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nbG_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * unfold hide in RH. eapply ILOOPh_intro; try reflexivity. exact HMEM.
      * unfold ll1_Q. hred. pullr_rw c r. repeat split; ireg.
    +
      do 7 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.
Ltac st16 ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.
Lemma swrap32_negadd : forall k x c, c = 18446744073709551616 - k -> - 2^31 <= x - k < 2^31 -> bv_swrap 32 (c + x) = x - k.
Proof. intros k x c -> H. rewrite Z.add_comm. apply swrap32_sub; [reflexivity| exact H]. Qed.
Lemma land64_np : forall x, - 4294967296 <= x <= 0 -> Z.land x 18446744073709551615 = 1 -> False.
Proof.
  intros x Hx K. destruct (Z.eq_dec x 0) as [E|NE]; [rewrite E in K; discriminate K|].
  rewrite land_ones64_neg in K by lia. lia.
Qed.
Definition LL2Q (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h17 q = wz (is_have s) /\ h14 q = wz (il_NI (ix_L X) + ir_next r) /\ h12 q = wz (ir_have r) /\ h10 q = wz Z_ORDER
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).
Local Ltac close_ll j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; rewrite ?EV; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma ll1_body : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL1_B q ms -> ll1_Q X s r q -> ix_ok X -> PATG X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  3 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     if is_ncode s - is_have s - 1 =? 0
     then ILOOPh X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL2 q' ms' /\ LL2Q X (ll_s s (ir_hold r)) (ll_r r) q'
     else ILOOPh X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL1_H q' ms' /\ ll1_Q X (ll_s s (ir_hold r)) (ll_r r) q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL RHV RNC RB RH RPUT.
  unfold ll1_Q in HQ. hred_in HQ. destruct HQ as (E10 & E11 & E13 & E15 & E16 & E17 & E14 & E12 & E9 & E18 & E22).
  iarm_openh HL. subst x10 x11 x13 x15 x16 x17 x14 x12 x9 x18 x22.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL1_B, Z_ORDER.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  pose proof (order_lt19 (is_have s) ltac:(lia)) as ROR. set (od := arr_get order_a (is_have s)) in *.
  assert (EV : wrap16 (BITSv (ir_hold r) 3) = Z.land (ir_hold r) 7) by (rewrite wrap16_bits3 by lia; rewrite land7_mod; reflexivity).
  pose proof (land7_range (ir_hold r)) as R7. set (v := Z.land (ir_hold r) 7) in *.
  zs. rewrite (swrap32_negadd 19) by lia. zs. zs. itr_groups MUf WMf. clear MUf WMf.
  zstep. if_cases K; br_norm K; [clear K | exfalso; eapply land64_np; [|exact K]; lia].
  zs. change (Z.lxor 75196 18446744073709551615) with 18446744073709476419. gT.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv usegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl usegs m1) as WMf;
    pose proof (order_rd m1 (is_have s) (wa (Z_ORDER + 2 * is_have s)) MI' ltac:(lia) eq_refl) as RD end.
  fold od in RD. unfold Z_ORDER in RD. zs. zs. rewrite (zx16_small od) by lia. clear RD.
  zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zs.
  zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  do 6 zs.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od v ltac:(reflexivity).
  zs. rewrite (swrap32_negadd (is_ncode s)) by lia. zs. zs.
  destruct (Z.eqb_spec (is_ncode s - is_have s - 1) 0) as [E0|NE0].
  -
    replace (is_have s + 2 - is_ncode s) with 1 by lia. zstep. br_false. zs. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold ll_s, ll_r; ired; try reflexivity|].
    + close_ll j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
    + unfold LL2Q, ll_s, ll_r. hred. ired. rewrite (wrap32_id (is_have s + 1)) by lia. repeat split; ireg.
  - zstep. if_cases K; br_norm K; [clear K | exfalso; eapply land64_np; [|exact K]; lia]. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold ll_s, ll_r; ired; try reflexivity|].
    + close_ll j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
    + unfold ll1_Q, ll_s, ll_r. hred. ired. rewrite (wrap32_id (is_have s + 1)) by lia. unfold Z_ORDER. repeat split; ireg.
Qed.
Definition LL1POST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' => (exists q, ILOOPh X w1 PC_LL2 q ms' /\ LL2Q X (w_s w1) (w_r w1) q)
                            /\ PATG X w1 /\ 0 <= is_have (w_s w1) <= 19 /\ is_mode (w_s w1) = LENLENS
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATG X w'
  | ARet _ _ => fun _ => False
  end.
Lemma ll1_loop : forall k X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGSg c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATG X (mkW s c r) -> is_mode s = LENLENS ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> is_ncode s - is_have s <= Z.of_nat k ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (LL1POST X (lenlens_while1 k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HQ XO DR Rin HP HM LL RHV RNC RK RPUT; [cbn [Z.of_nat] in RK; lia|].
  rewrite lenlens_while1_S. replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (ll1_head X s c r q ms HL HQ XO DR Rin HP)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ1)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite EN. cbn [LL1POST]. apply evt_done. split; [exact HLV|].
      destruct HR1 as [->| ->]; [exact HP| eapply PATG_regs; [exact HP| reflexivity..]]. }
  rewrite EN.
  destruct (DREGSg_nb c r r1 3 DR Rin ltac:(lia) HR1) as (DR1 & RB3 & EI & EO & ER & EP & EL).
  assert (HP1 : PATG X (mkW s c r1)) by (eapply PATG_regs; [exact HP| assumption..]).
  pose proof (DREGSg_hold64 c r1 DR1) as RH1. pose proof DR1 as (_ & _ & _ & RB1 & _).
  assert (HP2 : PATG X (mkW (ll_s s (ir_hold r1)) c (ll_r r1))).
  { eapply PATG_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold ll_s; cbn [is_mode iset_have iset_lens]; rewrite HM; unfold LENLENS, FLAGS, HCRC; lia
                      | reflexivity..| |exact Pisr| bk_keep].
    unfold ll_s, ll_r. cbn [is_mode iset_have iset_lens ir_put irset_bits irset_hold]. rewrite HM. reflexivity. }
  eapply evt_cut; [exact (ll1_body X s c r1 q1 ms1 (ILOOPh_regs X s c r r1 _ q1 ms1 HJ EI EO ER EP EL) HQ1 XO HP1 LL RHV RNC ltac:(lia) RH1 ltac:(lia))|].
  intros ms2 (q2 & H2).
  assert (EH' : is_have (ll_s s (ir_hold r1)) = is_have s + 1) by (unfold ll_s; cbn [is_have iset_have]; apply wrap32_id; lia).
  assert (EN' : is_ncode (ll_s s (ir_hold r1)) = is_ncode s) by reflexivity.
  destruct (Z.eqb_spec (is_ncode s - is_have s - 1) 0) as [E0|NE0].
  -
    destruct H2 as (H2 & HQ2).
    rewrite lenlens_while1_stop by (rewrite EH', EN'; lia). cbn [LL1POST w_s w_r].
    apply evt_done. split; [exists q2; split; [exact H2| exact HQ2]|].
    split; [exact HP2|]. split; [rewrite EH'; lia| unfold ll_s; cbn [is_mode iset_have iset_lens]; exact HM].
  - destruct H2 as (H2 & HQ2).
    refine (IH X _ c _ q2 ms2 H2 HQ2 XO (DREGSg_drop c r1 3 DR1 ltac:(lia)) Rin HP2 _ _ _ _ _ _).
    + unfold ll_s; cbn [is_mode iset_have iset_lens]; exact HM.
    + unfold ll_s. cbn [is_lens iset_have iset_lens]. rewrite arr_len_set. exact LL.
    + rewrite EH', EN'. lia.
    + rewrite EN'. exact RNC.
    + rewrite EH', EN'. lia.
    + unfold ll_r. cbn [ir_put irset_bits irset_hold]. lia.
Qed.
