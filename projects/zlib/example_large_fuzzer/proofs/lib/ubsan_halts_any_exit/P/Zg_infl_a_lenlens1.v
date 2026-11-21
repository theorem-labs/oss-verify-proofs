(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Z_infl_t_iface Zg_infl_t_iface Zg_infl_c_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1 RefInflateA_LENLENS2 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rod_order : forall m, mem_inv psegs m -> bytes_at psegs m Z_ORDER (u16s (av16 order_a 19)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_ORDER; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma order_rd : forall m i a, mem_inv psegs m -> 0 <= i < 19 -> a = wa (Z_ORDER + 2 * i) ->
  ov_read_bytes psegs m a 2 = Some (le2 (wz (arr_get order_a i))).
Proof.
  intros m i a MI Hi ->. pose proof (rod_order m MI) as Hb.
  pose proof (av16_nth order_a 19 i Hi) as Hn.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m Z_ORDER _ (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Ltac st16 ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
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

Definition PC_LL1_H : Z := 0x1d924.
Definition PC_LL1_B : Z := 0x1d8f4.
Definition PC_LL2 : Z := 0x1d954.

Definition ll1_Q (X : ictx) (s : inflate_state) (r : iregs) (q : iscr) : Prop :=
  sc12 q = wz (is_ncode s) /\ sc13 q = wz (Z_ORDER + 2 * is_have s) /\ sc14 q = wz (is_ncode s - is_have s)
  /\ sc15 q = wz (is_have s + 1) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r).

Lemma ll1_head : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGSg c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATG X (mkW s c r) ->
  evt psegs (NBJg X s c r 3 PC_LL1_B (fun r1 q1 => ll1_Q X s r1 q1)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E13 & E14 & E15 & E26) XO HREGS Rin HP.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x12 x13 x14 x15 x26.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & [Rh HAV] & Rnh & RB & RH).
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
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + unfold ll1_Q. cbn [sc12 sc13 sc14 sc15 sc26]. repeat split; reflexivity.
  - zs. br_cases K2.
    +
      assert (H1 : 0 < ir_have r) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 6 zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nbG_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * unfold hide in RH. eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
      * unfold ll1_Q. cbn [sc12 sc13 sc14 sc15 sc26]. pullr_rw c r. repeat split; ireg.
    +
      do 2 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_ll jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; rewrite ?EV; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll1_body : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL1_B q ms -> ll1_Q X s r q -> ix_ok X -> PATG X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  3 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q',
     if is_ncode s - is_have s - 1 =? 0
     then ILOOPg X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL2 q' ms' /\ sc15 q' = wz (is_ncode s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)
     else ILOOPg X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL1_H q' ms' /\ ll1_Q X (ll_s s (ir_hold r)) (ll_r r) q') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E13 & E14 & E15 & E26) XO HP LL RHV RNC RB RH RPUT.
  iarm_openg HL. subst x12 x13 x14 x15 x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL1_B.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  pose proof (order_lt19 (is_have s) ltac:(lia)) as ROR. set (od := arr_get order_a (is_have s)) in *.
  assert (EV : wrap16 (BITSv (ir_hold r) 3) = Z.land (ir_hold r) 7) by (rewrite wrap16_bits3 by lia; rewrite land7_mod; reflexivity).
  pose proof (land7_range (ir_hold r)) as R7. set (v := Z.land (ir_hold r) 7) in *.
  do 2 zs. itr_groups MUf WMf. clear MUf WMf.

  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv psegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl psegs m1) as WMf;
    pose proof (order_rd m1 (is_have s) (wa (Z_ORDER + 2 * is_have s)) MI' ltac:(lia) eq_refl) as RD end.
  fold od in RD. zs. rewrite (zx16_small od) by lia. clear RD.
  do 5 zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zs.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od v ltac:(reflexivity).
  do 2 zs. itr_groups MUf WMf. br_cases K.
  - replace (is_ncode s - is_have s - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    zs. apply evt_done. eexists. (split; [eapply ILOOPg_intro; unfold ll_s, ll_r; ired; [ireg .. |]| cbn [sc15 sc26]; split; reflexivity]).
    close_ll jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
  - replace (is_ncode s - is_have s - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold ll_s, ll_r; ired; [ireg .. |]|].
    + close_ll jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
    + unfold ll1_Q, ll_s, ll_r. cbn [sc12 sc13 sc14 sc15 sc26]. ired. rewrite (wrap32_id (is_have s + 1)) by lia. repeat split; ireg.
Qed.

Definition LL1POST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' => (exists q, ILOOPg X w1 PC_LL2 q ms' /\ sc15 q = wz (is_have (w_s w1)) /\ sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w1)))
                            /\ PATG X w1 /\ 0 <= is_have (w_s w1) <= 19 /\ is_mode (w_s w1) = LENLENS
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATG X w'
  | ARet _ _ => fun _ => False
  end.

Lemma ll1_loop : forall k X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGSg c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATG X (mkW s c r) -> is_mode s = LENLENS ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> is_ncode s - is_have s <= Z.of_nat k ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (LL1POST X (lenlens_while1 k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HQ XO DR Rin HP HM LL RHV RNC RK RPUT; [cbn [Z.of_nat] in RK; lia|].
  rewrite lenlens_while1_S. replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
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
                      | reflexivity..| |exact Pisr].
    unfold ll_s, ll_r. cbn [is_mode iset_have iset_lens ir_put irset_bits irset_hold]. rewrite HM. reflexivity. }
  eapply evt_cut; [exact (ll1_body X s c r1 q1 ms1 HJ HQ1 XO HP1 LL RHV RNC ltac:(lia) RH1 ltac:(lia))|].
  intros ms2 (q2 & H2).
  assert (EH' : is_have (ll_s s (ir_hold r1)) = is_have s + 1) by (unfold ll_s; cbn [is_have iset_have]; apply wrap32_id; lia).
  assert (EN' : is_ncode (ll_s s (ir_hold r1)) = is_ncode s) by reflexivity.
  destruct (Z.eqb_spec (is_ncode s - is_have s - 1) 0) as [E0|NE0].
  -
    destruct H2 as (H2 & E15 & E26).
    rewrite lenlens_while1_stop by (rewrite EH', EN'; lia). cbn [LL1POST w_s w_r].
    apply evt_done. split; [exists q2; split; [exact H2| split; [rewrite EH'; rewrite E15; f_equal; lia| exact E26]]|].
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
