(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Zg_defl_iface Zg_sto_model Zg_sto_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel RefDeflStored2 RefDeflStored5 RefDeflStored6 RefDeflStored7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_EMIT : Z := 0x17f9c.

Section PURE.
Variable X : deflate_state.
Let v := ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X).
Let have := cs_avail_out (ds_strm X) - sb_hdr X.

Lemma sb_left_eq' : 0 <= ds_block_start X <= ds_strstart X -> ds_strstart X <= 65536 -> sb_left X = ds_strstart X - ds_block_start X.
Proof using have v. intros H1 H2. unfold sb_left. rewrite wrap32_mod. apply Z.mod_small. lia. Qed.

Lemma sb_len1_mach : 0 <= ds_block_start X <= ds_strstart X -> ds_strstart X <= 65536 -> 0 <= cs_avail_in (ds_strm X) < 2^31 ->
  sb_len1 X = (if v <? 65535 then v else 65535).
Proof using have.
  intros H1 H2 H3. unfold sb_len1. rewrite sb_left_eq' by assumption. subst v.
  destruct (Z.ltb_spec (ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X)) 65535); [|reflexivity].
  rewrite wrap32_mod. apply Z.mod_small. lia.
Qed.

Lemma sb_len_mach : sb_len X = (if have <? sb_len1 X then have else sb_len1 X).
Proof using. reflexivity. Qed.
End PURE.

Lemma swrap32_big : forall v, 2^31 <= v < 2^32 -> wz (bv_swrap 32 v) = wz (v + 2^64 - 2^32).
Proof.
  intros v Hv. apply Z_to_bv_eqm. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div]. change (4294967296 / 2) with 2147483648.
  change (2^31) with 2147483648 in Hv. change (2^32) with 4294967296 in Hv.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_swrap32 : forall a v, 0 <= a < 2^31 -> 0 <= v < 2^32 -> bv_eqb (wz a) (wz (bv_swrap 32 v)) = (a =? v).
Proof.
  intros a v Ha Hv. unfold bv_eqb.
  destruct (Z_lt_le_dec v (2^31)).
  - rewrite bv_swrap32_id by lia. rewrite !unsigned_lit by lia. reflexivity.
  - rewrite swrap32_big by lia. rewrite !unsigned_lit by lia.
    destruct (Z.eqb_spec a (v + 2^64 - 2^32)); destruct (Z.eqb_spec a v); first [reflexivity| exfalso; lia].
Qed.

Lemma hdr_srlw : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 3) = Z.shiftr x 3.
Proof.
  intros x Hx. assert (E : bv_wrap 32 x = x) by (unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
  rewrite E. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= x / 2^3 <= x) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). apply bv_swrap32_id. lia.
Qed.


Lemma land_brk : forall (b1 b2 b3 : bool) (e : Z), (e = 0 \/ e = 1) ->
  Z.land (Z.land (if b1 then 0 else 1) (Z.lor (if b2 then 1 else 0) (Z.b2z b3))) e = if negb b1 && (b2 || b3) && (e =? 1) then 1 else 0.
Proof. intros b1 b2 b3 e H. destruct b1, b2, b3; destruct H as [-> | ->]; reflexivity. Qed.

Lemma brk_bool : forall (f len w : Z), 0 <= len ->
  ((len =? 0) && negb (f =? 4) || (f =? 0) || negb (len =? w)) =
  negb (negb (f =? 0) && ((f =? 4) || (0 <? len)) && ((if len =? w then 1 else 0) =? 1)).
Proof.
  intros f len w H. destruct (f =? 0), (f =? 4), (len =? w); destruct (Z.eqb_spec len 0); destruct (Z.ltb_spec 0 len); cbn; try reflexivity; lia.
Qed.

Lemma lxor_b2z : forall a b, 0 <= a -> 0 <= b -> Z.b2z (Z.lxor a b <? 1) = if a =? b then 1 else 0.
Proof.
  intros a b Ha Hb. pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)) as N.
  destruct (Z.eqb_spec a b) as [E|NE].
  - subst. rewrite Z.lxor_nilpotent. reflexivity.
  - destruct (Z.eq_dec (Z.lxor a b) 0) as [Z0|Z0].
    + exfalso. apply NE. apply (proj1 (Z.lxor_eq_0_iff a b)). exact Z0.
    + replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Section HEAD.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.

Definition KEMIT (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 1 rest0 lo r me X m' ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz (sb_len X)) y10 y11 y12 y13 y14 y15 y16 y17 (wz (sb_lastv X flush)) y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31)
                    F (wz Z_STO_EMIT) fc None m' (seg_rom psegs)).

Variables (Q : machine_state -> Prop) (X : deflate_state).
Hypothesis RBV : 0 <= ds_bi_valid X <= 16.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X) < 2^31.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X) < 2^31.
Hypothesis RBS : 0 <= ds_block_start X <= ds_strstart X.
Hypothesis RSTR : ds_strstart X <= 65536.
Hypothesis KB : sb_broke X flush 32768 = true -> TK10 L flush ai0 1 rest0 lo r F fc me Q Z_STO_BREAK (dl_S L) X.
Hypothesis KB2 : sb_broke X flush 32768 = true -> TK10 L flush ai0 1 rest0 lo r F fc me Q Z_STO_BREAK2 (dl_S L) X.
Hypothesis KE : sb_broke X flush 32768 = false -> KEMIT Q X.

Let v := ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X).
Let have := cs_avail_out (ds_strm X) - sb_hdr X.

Lemma sto_head : TK L flush ai0 1 rest0 lo r F fc me Q Z_STO_HEAD X.
Proof using have v KE KB KB2 RSTR RBS RAI RAO RBV HFL CTX inp.
  unfold TK. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_HEAD, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL.
  open_DST ST. open_A GA. open_D GD. open_zs ZS.
  pose proof (sb_hdr_eq X RBV) as [EH RH].
  zs. zs. zs. zs. zs.
  rewrite hdr_srlw by lia. change (Z.shiftr (ds_bi_valid X + 42) 3) with (sb_hdr X).
  zstep. br_cases K.
  { unfold TK10 in KB. eapply KB; [| exact INV]. rewrite sb_broke_eq. replace (cs_avail_out (ds_strm X) <? sb_hdr X) with true by (symmetry; apply Z.ltb_lt; exact K). reflexivity. }
  assert (HH : sb_hdr X <= cs_avail_out (ds_strm X)) by lia.
  pose proof (sb_len_range X ltac:(lia) HH) as (RL1 & RL2 & RL3).
  pose proof (sb_len1_mach X RBS RSTR RAI) as EL1. pose proof (sb_len_mach X) as EL. fold v in EL1. fold have in EL.
  assert (EBROKE : sb_broke X flush 32768 = sb_brk X flush 32768).
  { rewrite sb_broke_eq. replace (cs_avail_out (ds_strm X) <? sb_hdr X) with false by (symmetry; apply Z.ltb_ge; exact HH). reflexivity. }
  set (eqv := if sb_len X =? v then 1 else 0).
  assert (ELV : sb_lastv X flush = Z.land (if flush =? 4 then 1 else 0) eqv).
  { unfold sb_lastv, Z_FINISH, eqv. rewrite (sb_left_eq' X RBS RSTR). subst v. rewrite wrap32_mod, Z.mod_small by lia.
    destruct (flush =? 4), (sb_len X =? _); reflexivity. }
  assert (K20 : forall (a2v a3v a4v : word), sb_brk X flush 32768 = false ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz (sb_len X)) (wz (dl_S L)) (wz eqv) a2v a3v a4v y15 y16 y17 y18 y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31) F (wz 0x17f94) fc None m' (seg_rom psegs))).
  { intros a2v a3v a4v NB. unfold stoR, stoR7. zs. zs. rewrite <- ELV.
    unfold KEMIT in KE. eapply KE; solve [exact INV | rewrite EBROKE; exact NB]. }
  assert (EBRK : sb_len X < 32768 ->
    sb_brk X flush 32768 = negb (negb (flush =? 0) && ((flush =? 4) || (0 <? sb_len X)) && (eqv =? 1))).
  { intros HLT. unfold sb_brk, Z_FINISH, Z_NO_FLUSH. rewrite (sb_left_eq' X RBS RSTR), wrap32_mod, Z.mod_small by lia.
    replace (sb_len X <? 32768) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    rewrite brk_bool by lia. reflexivity. }
  assert (K04 : forall (a2v a3v a4v : word), sb_len X < 32768 ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz (sb_len X)) (wz (dl_S L)) (wz eqv) a2v a3v a4v y15 y16 y17 y18 y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31) F (wz 0x17f78) fc None m' (seg_rom psegs))).
  { intros a2v a3v a4v HLT. unfold stoR, stoR7. zs. zs. zs. zs. zs. zs.
    rewrite (land_brk (flush =? 0) (flush =? 4) (0 <? sb_len X) eqv) by (unfold eqv; destruct (sb_len X =? v); [right|left]; reflexivity).
    pose proof (EBRK HLT) as EB.
    remember (negb (flush =? 0) && ((flush =? 4) || (0 <? sb_len X)) && (eqv =? 1)) as c eqn:EC.
    zstep. br_cases K4; destruct c; rewrite ?unsigned_lit in K4 by lia; try (exfalso; lia).
    - unfold TK10 in KB2. eapply KB2; [| exact INV]. rewrite EBROKE, EB. reflexivity.
    - eapply K20. rewrite EB. reflexivity. }
  assert (KCC : forall (a1v a2v a3v a4v : word), ds_strstart X - ds_block_start X <= sb_len X ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz (sb_len X)) (wz (dl_S L)) a1v a2v a3v a4v y15 y16 y17 y18 y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31) F (wz 0x17f40) fc None m' (seg_rom psegs))).
  { intros a1v a2v a3v a4v HGE. unfold stoR, stoR7. zs. zs. zs. zs.
    rewrite lxor_b2z by lia.
    replace (if sb_len X - (ds_strstart X - ds_block_start X) =? cs_avail_in (ds_strm X) then 1 else 0) with eqv
      by (unfold eqv; subst v; destruct (Z.eqb_spec (sb_len X - (ds_strstart X - ds_block_start X)) (cs_avail_in (ds_strm X)));
          destruct (Z.eqb_spec (sb_len X) (ds_strstart X - ds_block_start X + cs_avail_in (ds_strm X))); lia).
    zs. zstep. br_cases K5.
    - eapply K20. unfold sb_brk. replace (sb_len X <? 32768) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - zstep. eapply K04. lia. }
  assert (KF8 : forall (a1v a2v a3v a4v : word), sb_len X < ds_strstart X - ds_block_start X ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz (sb_len X)) (wz (dl_S L)) a1v a2v a3v a4v y15 y16 y17 y18 y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31) F (wz 0x17f6c) fc None m' (seg_rom psegs))).
  { intros a1v a2v a3v a4v HLT. unfold stoR, stoR7. zs.
    replace (wz 0) with (wz eqv) by (f_equal; unfold eqv; replace (sb_len X =? v) with false by (symmetry; apply Z.eqb_neq; subst v; lia); reflexivity).
    zs. zstep. br_cases K5.
    - eapply K20. unfold sb_brk. replace (sb_len X <? 32768) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - eapply K04. lia. }
  assert (KJ1 : forall (s1v a3v a4v : word), sb_len X = have ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 s1v (wz (dl_S L)) (wz (cs_avail_out (ds_strm X) - sb_hdr X)) (wz (sb_hdr X)) a3v a4v y15 y16 y17 y18 y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31) F (wz 0x17f38) fc None m' (seg_rom psegs))).
  { intros s1v a3v a4v ELEN. unfold stoR, stoR7. zs.
    replace (wz (cs_avail_out (ds_strm X) - sb_hdr X)) with (wz (sb_len X)) by (f_equal; rewrite ELEN; reflexivity).
    zstep. br_cases K6.
    - eapply KF8. lia.
    - eapply KCC. lia. }
  assert (KJ2 : forall (s1v a3v a4v : word), s1v = wz (sb_len X) ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 s1v (wz (dl_S L)) (wz (cs_avail_out (ds_strm X) - sb_hdr X)) (wz (sb_hdr X)) a3v a4v y15 y16 y17 y18 y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) (wz (ds_block_start X)) y28 y29 y30 y31) F (wz 0x17f68) fc None m' (seg_rom psegs))).
  { intros s1v a3v a4v ->. unfold stoR, stoR7.
    zstep. br_cases K6.
    - eapply KCC. lia.
    - eapply KF8. lia. }
  rd_lo4 GA 152%nat. zs. zs. zs. zs. zstep. br_cases K1.
  - assert (EL1' : sb_len1 X = 65535) by (rewrite EL1; destruct (Z.ltb_spec v 65535); subst v; lia).
    zs. zstep. br_cases K2.
    + eapply KJ2. f_equal. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
    + eapply KJ1. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
  - zs. zs. zstep. br_cases K2.
    + assert (EL1' : sb_len1 X = v) by (rewrite EL1; destruct (Z.ltb_spec v 65535); subst v; lia).
      zs. zs. zstep. br_cases K3.
      * eapply KJ1. rewrite EL, EL1'. destruct (Z.ltb_spec have v); subst have v; lia.
      * eapply KJ2. f_equal. rewrite EL, EL1'. destruct (Z.ltb_spec have v); subst have v; lia.
    + assert (EL1' : sb_len1 X = 65535) by (rewrite EL1; destruct (Z.ltb_spec v 65535); subst v; lia).
      zs. zs. zstep. br_cases K3.
      * eapply KJ2. f_equal. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
      * zstep. eapply KJ1. rewrite EL, EL1'. destruct (Z.ltb_spec have 65535); subst have; lia.
Qed.


End HEAD.
