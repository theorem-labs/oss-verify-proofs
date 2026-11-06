(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec3 SymExec3Sound SymRun3 LibAtomic.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibAmo SymExecA.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S. Import SXA.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module SXAS.

Lemma fetch_dec_inv : forall segs p i,
  fetch_dec segs p = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 p) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Proof.
  intros segs p i H. unfold fetch_dec in H.
  destruct (fetch_word segs (Z_to_bv 64 p)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  exists w. split; [first [reflexivity | exact Hf]|]. split; [first [reflexivity | exact He]|].
  destruct sz as [|q|q]; try discriminate.
  repeat (destruct q; try discriminate). injection H as ->. first [reflexivity | exact Hd].
Qed.

Lemma reg_eqb_eq : forall a b, reg_eqb a b = true -> a = b.
Proof. intros a b H. unfold reg_eqb, bv_eqb in H. apply bv_eq. apply Z.eqb_eq. exact H. Qed.
Lemma reg_eqb_neq : forall a b, reg_eqb a b = false -> a <> b.
Proof. intros a b H E. subst. unfold reg_eqb, bv_eqb in H. rewrite Z.eqb_refl in H. discriminate. Qed.

Lemma vdecode_inv : forall segs p vi,
  vdecode segs p = Some vi ->
  match vi with
  | VReal i => exists w, fetch_word segs (Z_to_bv 64 p) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z)
  | VCas rd rt rd2 rs1 rs2 =>
      exists w0 w1 w2 aq rl aq' rl' imm1,
        fetch_word segs (Z_to_bv 64 p) = Some w0 /\ is_ecall w0 = false /\ decode_any w0 = Some (Lr AW aq rl rd rs1, 4%Z)
        /\ fetch_word segs (Z_to_bv 64 (p + 4)) = Some w1 /\ is_ecall w1 = false
        /\ decode_any w1 = Some (Branch BC_NE rd rt imm1, 4%Z)
        /\ fetch_word segs (Z_to_bv 64 (p + 8)) = Some w2 /\ is_ecall w2 = false
        /\ decode_any w2 = Some (Sc AW aq' rl' rd2 rs1 rs2, 4%Z)
        /\ rd <> rs1 /\ rd <> 0%bv
  | VAmo op wd rd rs1 rs2 =>
      (op = AMO_ADD \/ op = AMO_SWAP) /\
      exists w aq rl, fetch_word segs (Z_to_bv 64 p) = Some w /\ is_ecall w = false
                      /\ decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z)
  end.
Proof.
  intros segs p vi H. unfold vdecode in H.
  destruct (fetch_dec segs p) as [i|] eqn:H0; [|discriminate].
  pose proof (fetch_dec_inv _ _ _ H0) as (w0 & F0 & E0 & D0).
  destruct i; try (injection H as <-; exists w0; auto; fail).
  all: try (injection H as <-; exists w0; split; [exact F0|split; [exact E0|exact D0]]).
  -
    destruct w; [|discriminate].
    destruct (fetch_dec segs (p + 4)) as [i1|] eqn:H1; [|discriminate].
    destruct i1; try discriminate. destruct c; try discriminate.
    destruct (fetch_dec segs (p + 8)) as [i2|] eqn:H2; [|discriminate].
    destruct i2; try discriminate. destruct w; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection H as <-.
    apply andb_prop in Hc as [Hc Hd0]. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [Ha Hb].
    apply reg_eqb_eq in Ha. apply reg_eqb_eq in Hb. subst.
    apply Bool.negb_true_iff in Hcs. apply Bool.negb_true_iff in Hd0.
    pose proof (fetch_dec_inv _ _ _ H1) as (w1 & F1 & E1 & D1).
    pose proof (fetch_dec_inv _ _ _ H2) as (w2 & F2 & E2 & D2).
    exists w0, w1, w2, aq, rl, aq0, rl0, imm.
    repeat (split; [eassumption|]).
    split; [apply reg_eqb_neq; exact Hcs | apply reg_eqb_neq; exact Hd0].
  -
    discriminate.
  -
    destruct op; try discriminate; injection H as <-; (split; [auto | do 3 eexists; eauto]).
Qed.

Section Resolve.
Variable segs : list Segment.

Lemma lookup1_sound : forall E base fk ss rb rk n sx hints acc v scs hints',
  know_ok segs E base fk -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (1 <= n)%nat -> (n <= 8)%nat ->
  lookup1 segs fk ss rb rk n sx hints acc = R1Hit v scs hints' ->
  scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
  (exists pre, scs = pre ++ acc) /\
  exists bs, rdn segs (mem_denot E base (s_log ss)) (adenot E (SA rb rk)) n = Some bs
             /\ length bs = n /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v.
Proof.
  intros E base fk ss rb rk n sx hints acc v scs hints' Hfk Hlf Hkn Hn1 Hn8 HL Hsc Hfl.
  unfold lookup1 in HL.
  pose proof (log_lookup_sound segs E base fk (s_log ss) rb rk n sx hints acc Hfk Hlf Hn1 Hn8) as HLS.
  pose proof (log_lookup_acc fk (s_log ss) rb rk n sx hints acc) as HLA.
  destruct (log_lookup fk (s_log ss) rb rk n sx hints acc) as [v0 scs0 h0|scs0 h0|] eqn:Hll; [ | | discriminate].
  - injection HL as <- <- <-. split; [exact HLA|]. exact (HLS Hsc Hfl).
  - pose proof (know_lookupA_sound segs E base fk base (s_know ss) rb rk n sx h0 scs0 Hfk Hkn Hn1 Hn8) as HKS.
    pose proof (know_lookupA_acc fk segs (s_know ss) rb rk n sx h0 scs0) as HKA.
    destruct (know_lookupA fk segs (s_know ss) rb rk n sx h0 scs0) as [v1 scs1 h1|scs1 h1|] eqn:Hkl; try discriminate.
    injection HL as <- <- <-.
    destruct HKA as [pre1 ->]. destruct HLA as [pre0 ->].
    split; [exists (pre1 ++ pre0); rewrite app_assoc; reflexivity|].
    assert (Hsc0 : scs_denot segs base E (pre0 ++ acc)) by (apply scs_denot_app in Hsc as [_ H]; exact H).
    destruct (HKS Hsc Hfl) as (bs & Hrd & Hlen & Hval).
    exists bs. split; [|split; [exact Hlen | exact Hval]].
    rewrite (HLS Hsc0 Hfl). exact Hrd.
Qed.

Lemma flat_first1 : forall E rb rk k,
  flat E (SA rb rk) (Z.of_nat (S k)) -> flat E (SA rb rk) 1.
Proof.
  intros E rb rk k (H1 & H2 & H3 & H4). unfold flat, estart in *. cbn [a_base a_off] in *.
  rewrite Nat2Z.inj_succ in *. repeat split; lia.
Qed.

Lemma flat_rest : forall E rb rk k,
  flat E (SA rb rk) (Z.of_nat (S k)) -> (1 <= k)%nat -> flat E (SA rb (rk + 1)) (Z.of_nat k).
Proof.
  intros E rb rk k (H1 & H2 & H3 & H4) Hk. unfold flat, estart in *. cbn [a_base a_off] in *.
  rewrite Nat2Z.inj_succ in *. repeat split; lia.
Qed.

Lemma adenot_shift1 : forall E rb rk,
  flat E (SA rb rk) 1 -> adenot E (SA rb (rk + 1)) = adenot E (SA rb rk) + nat_to_word 1.
Proof.
  intros E rb rk Hfl. rewrite w_add_nat. rewrite (flat_u E _ _ Hfl).
  unfold adenot, v_addi, estart. cbn [a_base a_off Z.of_nat]. f_equal. lia.
Qed.

Lemma byte_val : forall (b : byte) z,
  Z_to_bv 64 (extz false 1 (bytes_le_to_Z [b])) = Z_to_bv 64 z -> bv_unsigned b = (z mod 256)%Z.
Proof.
  intros b z H. cbn [bytes_le_to_Z extz] in H.
  apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  rewrite Z.shiftl_0_l, Z.lor_0_r in H. unfold bv_wrap, bv_modulus in H.
  rewrite Z.mod_small in H by (cbn in Hb |- *; lia).
  rewrite H in Hb |- *.
  rewrite <- (Z.mod_mod_divide z (2 ^ Z.of_N 64) 256) by (exists (2 ^ 56)%Z; reflexivity).
  symmetry. apply Z.mod_small. cbn in Hb |- *.
  pose proof (Z.mod_pos_bound z 18446744073709551616 ltac:(lia)). lia.
Qed.

Lemma zbytes_le_eq : forall (bs : list byte) (zs : list Z),
  length bs = length zs ->
  (forall j, (j < length zs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) = nth j zs 0%Z) ->
  bytes_le_to_Z bs = zbytes_le zs.
Proof.
  induction bs as [|b bs IH]; intros [|z zs] Hlen Hnth; cbn in Hlen |- *; try reflexivity; try lia.
  pose proof (Hnth 0%nat ltac:(cbn; lia)) as H0. cbn in H0.
  rewrite (IH zs); [| lia | intros j Hj; apply (Hnth (S j)); cbn; lia].
  rewrite <- H0. reflexivity.
Qed.

Lemma gather_sound : forall E base fk ss k rb rk hints acc zs scs hints',
  know_ok segs E base fk -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  gather segs fk ss rb rk k hints acc = Some (zs, scs, hints') ->
  scs_denot segs base E scs ->
  (1 <= k)%nat -> flat E (SA rb rk) (Z.of_nat k) ->
  (exists pre, scs = pre ++ acc) /\
  exists bs, rdn segs (mem_denot E base (s_log ss)) (adenot E (SA rb rk)) k = Some bs
             /\ length bs = k /\ length zs = k
             /\ (forall j, (j < k)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) = nth j zs 0%Z)
             /\ (forall j, (j < k)%nat -> 0 <= nth j zs 0 < 256)%Z.
Proof.
  intros E base fk ss k. induction k as [|k IH]; intros rb rk hints acc zs scs hints' Hfk Hlf Hkn HG Hsc Hk Hfl; [lia|].
  cbn [gather] in HG.
  destruct (lookup1 segs fk ss rb rk 1 false hints acc) as [v acc1 h1|] eqn:HL; [|discriminate].
  pose proof (conc_expr_sound segs E base fk v Hfk) as Hcv.
  destruct (conc_expr fk v) as [b| | | | | | |] eqn:Hce; try discriminate.
  destruct (gather segs fk ss rb (rk + 1) k h1 acc1) as [[[zs' acc2] h2]|] eqn:HG2; [|discriminate].
  injection HG as <- <- <-.
  pose proof (flat_first1 E rb rk k Hfl) as Hfl1.
  destruct k as [|k'].
  -
    cbn [gather] in HG2. injection HG2 as <- <- <-.
    destruct (lookup1_sound E base fk ss rb rk 1 false hints acc v acc1 h1 Hfk Hlf Hkn ltac:(lia) ltac:(lia) HL Hsc Hfl1)
      as [Hpre (bs & Hrd & Hlen & Hval)].
    split; [exact Hpre|]. exists bs.
    destruct bs as [|b0 [|]]; cbn in Hlen; try lia.
    rewrite <- Hcv in Hval. cbn [edenot] in Hval.
    pose proof (byte_val b0 b Hval) as Hb0.
    split; [exact Hrd|]. split; [reflexivity|]. split; [reflexivity|]. split.
    + intros j Hj. destruct j; [cbn; exact Hb0 | lia].
    + intros j Hj. destruct j; [cbn | lia]. pose proof (Z.mod_pos_bound b 256 ltac:(lia)). lia.
  -
    assert (Hk' : (1 <= S k')%nat) by lia.
    pose proof (flat_rest E rb rk (S k') Hfl Hk') as Hfl2.

    destruct (IH rb (rk + 1)%Z h1 acc1 zs' acc2 h2 Hfk Hlf Hkn HG2 Hsc Hk' Hfl2)
      as [[pre2 Hacc2] (bs2 & Hrd2 & Hlen2 & Hlenz2 & Hnth2 & Hrng2)]. subst acc2.
    assert (Hsc1 : scs_denot segs base E acc1) by (apply scs_denot_app in Hsc as [_ H]; exact H).
    destruct (lookup1_sound E base fk ss rb rk 1 false hints acc v acc1 h1 Hfk Hlf Hkn ltac:(lia) ltac:(lia) HL Hsc1 Hfl1)
      as [[pre1 ->] (bs1 & Hrd1 & Hlen1 & Hval1)].
    split; [exists (pre2 ++ pre1); rewrite app_assoc; reflexivity|].
    destruct bs1 as [|b0 [|]]; cbn in Hlen1; try lia.
    rewrite <- Hcv in Hval1. cbn [edenot] in Hval1.
    pose proof (byte_val b0 b Hval1) as Hb0.
    exists (b0 :: bs2).
    split.
    { change (S (S k')) with (1 + S k')%nat. apply (rdn_app segs _ 1 (S k') _ [b0] bs2 Hrd1).
      rewrite <- (adenot_shift1 E rb rk Hfl1). exact Hrd2. }
    split; [cbn; lia|]. split; [cbn; lia|]. split.
    + intros j Hj. destruct j; [cbn; exact Hb0 | cbn; apply Hnth2; lia].
    + intros j Hj. destruct j; [cbn; pose proof (Z.mod_pos_bound b 256 ltac:(lia)); lia | cbn; apply Hrng2; lia].
Qed.

Lemma resolve_load_sound : forall E base fk ss a n sx scr v scs scr',
  know_ok segs E base fk -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (1 <= n)%nat -> (n <= 8)%nat ->
  resolve_load segs fk ss a n sx scr = ROk v scs scr' ->
  scs_denot segs base E scs ->
  flat E a (Z.of_nat n) /\
  exists bs, rdn segs (mem_denot E base (s_log ss)) (adenot E a) n = Some bs
             /\ length bs = n /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v.
Proof.
  intros E base fk ss a n sx scr v scs scr' Hfk Hlf Hkn Hn1 Hn8 HR Hsc.
  unfold resolve_load in HR. destruct a as [rb rk]. cbn [a_base a_off] in HR.
  destruct (lookup1 segs fk ss rb rk n sx (sc_hints scr) []) as [v1 scs1 h1|] eqn:HL.
  - injection HR as <- <- <-.
    apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
    split; [exact Hfl|].
    destruct (lookup1_sound E base fk ss rb rk n sx _ [] v1 scs1 h1 Hfk Hlf Hkn Hn1 Hn8 HL Hsc Hfl)
      as [_ (bs & Hrd & Hlen & Hval)].
    exists bs. split; [exact Hrd|]. split; [exact Hlen|]. rewrite (extK_denot segs E base fk v1 Hfk). exact Hval.
  - destruct (gather segs fk ss rb rk n (sc_hints scr) []) as [[[zs scs2] h2]|] eqn:HG; [|discriminate].
    injection HR as <- <- <-.
    apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
    split; [exact Hfl|].
    destruct (gather_sound E base fk ss n rb rk _ [] zs scs2 h2 Hfk Hlf Hkn HG Hsc Hn1 Hfl)
      as [_ (bs & Hrd & Hlen & Hlenz & Hnth & Hrng)].
    exists bs. split; [exact Hrd|]. split; [exact Hlen|].
    cbn [edenot]. rewrite Z_to_bv_bv_unsigned. unfold extz, extz'.
    rewrite (zbytes_le_eq bs zs ltac:(lia) ltac:(rewrite Hlenz; exact Hnth)). reflexivity.
Qed.

Lemma storeok_sound : forall E base fk a n rest,
  know_ok segs E base fk -> (n <= 8)%nat ->
  flat E a (Z.of_nat n) ->
  scs_denot segs base E (storeok_sc fk a n ++ rest) ->
  RiscvSemantics.store_ok segs base (adenot E a) n = true /\ scs_denot segs base E rest.
Proof.
  intros E base fk a n rest Hfk Hn8 Hfl Hsc.
  unfold storeok_sc in Hsc.
  destruct (wr_covered fk fk a n) eqn:Hw.
  - split; [|exact Hsc]. clear Hsc. revert Hw. pose proof Hfk as Hall. generalize Hfk. generalize fk at 1 3 as kn. intros kn Hkn0 Hw.
    induction kn as [|K rest' IH]; cbn [wr_covered] in Hw; [discriminate|].
    apply Forall_cons_iff in Hkn0 as [HK Hrest].
    destruct K as [| | | | | |[kb kk] len|]; try (apply IH; assumption).
    cbn [kentry_ok] in HK. destruct HK as [Hflk Hs0]. unfold elenZ in Hflk, Hs0.
    match type of Hw with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
    { destruct (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool eqn:H12; [|discriminate].
      apply andb_prop in H12 as [H1 H2].
      apply expr_eqb_eq in H1. apply Z.leb_le in H2.
      destruct (xlo fk len) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hc. rename Hc into H3.
      pose proof (xlo_sound segs E base fk len l Hall Hxl) as Hl.
      replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (a_off a - kk))).
      + apply Hs0; lia.
      + apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite <- H1.
        destruct Hfl as (?&?&?&?). unfold estart in *. rewrite u_small by lia. lia. }
    match type of Hw with (if ?c then _ else _) = _ => destruct c eqn:Hxi; [|apply IH; assumption] end.
    destruct (xinside_sound segs E base fk _ _ _ _ _ _ Hall Hxi) as [I1 I2].
    replace (SA (a_base a) (a_off a)) with a in I1, I2 by (destruct a; reflexivity).
    unfold elenZ in I2. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
    replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (estart E a - estart E (SA kb kk)))).
    + apply Hs0; lia.
    + apply bv_eq. rewrite (flat_u E _ _ Hfl).
      destruct Hfl as (?&?&?&?). rewrite u_small by lia. lia.
  - apply scs_denot_cons in Hsc as [Hok Hrest]. cbn [sc_denot] in Hok. split; [exact Hok | exact Hrest].
Qed.

Lemma kalign_of_sound : forall E base fk e,
  know_ok segs E base fk -> (0 < kalign_of fk e)%Z ->
  (bv_unsigned (edenot E e) mod kalign_of fk e = 0)%Z.
Proof.
  intros E base fk e Hfk. induction fk as [|K rest IH]; cbn [kalign_of]; intros Hk.
  - apply Z.mod_1_r.
  - apply Forall_cons_iff in Hfk as [HK Hrest].
    destruct K as [| | | |e' m| | |]; try (apply IH; assumption).
    destruct (expr_eqb e e') eqn:Heq; [|apply IH; assumption].
    apply expr_eqb_eq in Heq. subst e'. cbn [kentry_ok] in HK. destruct HK as [_ H]. exact H.
Qed.

Lemma mod_of_multiple : forall x k m, (0 < m)%Z -> (0 < k)%Z -> (k mod m = 0)%Z -> (x mod k = 0)%Z -> (x mod m = 0)%Z.
Proof.
  intros x k m Hm Hk Hkm Hx.
  apply Z.mod_divide in Hkm; [|lia]. apply Z.mod_divide in Hx; [|lia].
  apply Z.mod_divide; [lia|]. eapply Z.divide_trans; eassumption.
Qed.

Lemma aligned_dec_sound : forall E base fk a m len,
  know_ok segs E base fk -> flat E a len ->
  (m = 4 \/ m = 8)%Z ->
  aligned_dec fk a m = true ->
  (bv_unsigned (adenot E a) mod m = 0)%Z.
Proof.
  intros E base fk a m len Hfk Hfl Hm Had.
  assert (Hm0 : (0 < m)%Z) by lia.
  assert (Hdiv : (m | 2 ^ 64)%Z).
  { destruct Hm as [-> | ->]; [exists (2 ^ 62)%Z | exists (2 ^ 61)%Z]; reflexivity. }
  rewrite (flat_u E a len Hfl). unfold aligned_dec in Had. unfold estart.
  destruct a as [b off]. cbn [a_base a_off] in *.
  destruct b as [z| | | | | | |];
  [
    cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    apply Z.eqb_eq in Had;
    rewrite Zplus_mod, (Z.mod_mod_divide z (2 ^ Z.of_N 64) m Hdiv), <- Zplus_mod; exact Had
  | .. ].
  all: apply andb_prop in Had as [Had Hoff]; apply andb_prop in Had as [Hk0 Hkm];
       apply Z.ltb_lt in Hk0; apply Z.eqb_eq in Hkm; apply Z.eqb_eq in Hoff;
       rewrite Zplus_mod, Hoff, Z.add_0_r, Z.mod_mod by lia;
       eapply mod_of_multiple; [exact Hm0 | exact Hk0 | exact Hkm | eapply kalign_of_sound; eassumption].
Qed.

End Resolve.

Section StepSound.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma getr_regupd_other : forall regs (rd r : reg) v, r <> rd -> getr (regupd regs rd v) r = getr regs r.
Proof.
  intros regs rd r v H. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact H.
Qed.

Lemma vload_sound : forall E base rom ss regs sz sx rd rs imm v scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
  resolve_load segs (facts_of (s_know ss)) ss
     (to_saddrK (facts_of (s_know ss)) (sr_get (s_regs ss) rs) (bv_signed imm))
     (msize_bytes sz) (match sz with SZ8 => false | _ => sx end) scr = ROk v scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom) = MachineOk ms'
              /\ st_ok segs E base rom (sset ss rd v (s_pc ss + 4)) ms'.
Proof.
  intros E base rom ss regs sz sx rd rs imm v scs scr scr' w Hf He Hd HR Hsc Hregs Hlf Hkn.
  set (mem := mem_denot E base (s_log ss)) in *.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  pose proof (msize_bytes_range sz) as [Hn1 Hn8].
  destruct (resolve_load_sound segs E base fk ss _ _ _ scr v scs scr' Hfk Hlf Hkn Hn1 Hn8 HR Hsc)
    as (Hfl & bs & Hrd & Hlen & Hval).
  rewrite (to_saddrK_denot segs E base fk _ _ Hfk), <- (Hregs rs) in Hrd.
  eexists; split; [exact (step_load segs regs _ mem rom w sz sx rd rs imm bs Hf He Hd Hrd)|].
  eexists; split; [f_equal; cbn [s_pc sset]; apply v_addi_lit|].
  cbn [s_regs s_log s_know sset]. split; [|split; [exact Hlf | exact Hkn]].
  apply regs_ok_upd; [exact Hregs|].
  rewrite load_result_val by exact Hlen. symmetry. destruct sz; exact Hval.
Qed.

Lemma swrap32_roundtrip : forall u, (0 <= u < 2^32)%Z ->
 (((((u + 2 ^ 32 / 2) mod 2 ^ 32 - 2 ^ 32 / 2) mod 2 ^ 64) mod 2 ^ 32) = u)%Z.
Proof.
  intros u Hu.
  rewrite (Z.mod_mod_divide _ (2^64) (2^32)) by (exists (2^32)%Z; reflexivity).
  change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  destruct (Z_lt_le_dec u (2^31)).
  - rewrite (Z.mod_small (u + 2^31)) by lia. replace (u + 2^31 - 2^31)%Z with u by lia. apply Z.mod_small. lia.
  - replace ((u + 2 ^ 31) mod 2 ^ 32)%Z with (u + 2^31 - 2^32)%Z.
    + replace (u + 2 ^ 31 - 2 ^ 32 - 2 ^ 31)%Z with (u - 2^32)%Z by lia.
      rewrite <- Z.mod_add with (b := 1%Z) by lia. replace (u - 2^32 + 1 * 2^32)%Z with u by lia. apply Z.mod_small; lia.
    + symmetry. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma low32_sext64 : forall z : bv 32, low32 (sext 64 z) = z.
Proof.
  intros z. apply bv_eq. rewrite low32_unsigned, sext64_lit, Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 32 z) as Hz.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  cbn -[Z.add Z.sub Z.mul Z.modulo Z.pow Z.div bv_unsigned] in *.
  apply swrap32_roundtrip. exact Hz.
Qed.

Lemma amo_bytes_w : forall E op v s we (old : bv 32) (src : word),
  amo_store_expr op AW v s = Some we ->
  edenot E v = sext 64 old -> edenot E s = src ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val op old (low32 src))) = Z_to_le_bytes 4 (bv_unsigned (edenot E we)).
Proof.
  intros E op v s we old src Hwe Hv Hs.
  destruct op; cbn [amo_store_expr] in Hwe; try discriminate; injection Hwe as <-; cbn [amo_val].
  -   rewrite <- Hs. apply store_bytes_low32.
  -   rewrite mkAluw_denot, Hv, Hs, low32_sext64.
    change (alu32 ALU_ADD old (low32 src)) with (old + low32 src).
    rewrite <- (low32_sext64 (old + low32 src)) at 1.
    apply store_bytes_low32.
Qed.

Lemma amo_bytes_d : forall E op v s we (old src : word),
  amo_store_expr op AD v s = Some we ->
  edenot E v = old -> edenot E s = src ->
  Z_to_le_bytes 8 (bv_unsigned (amo_val op old src)) = Z_to_le_bytes 8 (bv_unsigned (edenot E we)).
Proof.
  intros E op v s we old src Hwe Hv Hs.
  destruct op; cbn [amo_store_expr] in Hwe; try discriminate; injection Hwe as <-; cbn [amo_val].
  - rewrite Hs. reflexivity.
  - rewrite mkAlu_denot, Hv, Hs. reflexivity.
Qed.

Lemma vstep_sound : forall E base rom ss ms vi ss' scs scr scr',
  vdecode segs (s_pc ss) = Some vi ->
  vstep segs vi ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof.
  intros E base rom ss ms vi ss' scs scr scr' Hvd Hs Hsc Hst.
  pose proof (vdecode_inv segs (s_pc ss) vi Hvd) as Hinv.
  destruct Hst as (regs & Hms & Hregs & Hlf & Hkn).
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk.
  destruct vi as [i | rd rt rd2 rs1 rs2 | op wd rd rs1 rs2]; cbn [vstep] in Hs.
  -
    destruct Hinv as (w & Hf & He & Hd).
    destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:Hss.
    + injection Hs as <- <- <-.
      destruct (sym_step_sound segs E base rom ss ms i ss1 scs1 scr scr1 w Hf He Hd Hss Hsc
                  ltac:(exists regs; auto)) as (ms' & Hstep & Hst').
      exists ms'. split; [|exact Hst'].
      eapply mst_step; [subst ms; reflexivity | exact Hstep | apply mst_refl].
    + destruct i; try discriminate.
      match type of Hs with (match ?r with ROk _ _ _ => _ | RStop => _ end) = _ => destruct r as [v scs2 scr2|] eqn:HR; [|discriminate] end.
      injection Hs as <- <- <-. subst ms.
      match type of Hd with _ = Some (Load ?sz ?sx ?rd ?rs ?imm, _) =>
      destruct (vload_sound E base rom ss regs sz sx rd rs imm v scs2 scr scr2 w Hf He Hd HR Hsc Hregs Hlf Hkn)
        as (ms' & Hstep & Hst') end.
      exists ms'. split; [|exact Hst'].
      eapply mst_step; [reflexivity | exact Hstep | apply mst_refl].
  -
    destruct Hinv as (w0 & w1 & w2 & aq & rl & aq' & rl' & imm1 & F0 & E0 & D0 & F1 & E1 & D1 & F2 & E2 & D2 & Hne & Hrd0).
    set (fk := facts_of (s_know ss)) in *.
    set (a := to_saddrK fk (sr_get (s_regs ss) rs1) 0) in *.
    destruct (aligned_dec fk a 4) eqn:Hal; [|discriminate]. cbn [negb] in Hs.
    destruct (resolve_load segs fk ss a 4 true scr) as [v scs1 scr1|] eqn:HR; [|discriminate].
    set (sr1 := sr_upd (s_regs ss) (ridx rd) v) in *.
    destruct (decide_branch fk BC_NE (sr_get sr1 rd) (sr_get sr1 rt)) as [[|]|] eqn:Hdb; try discriminate.
    injection Hs as <- <- <-.
    apply scs_denot_app in Hsc as [Hsc1 Hsc3].
    destruct (resolve_load_sound segs E base fk ss a 4 true scr v scs1 scr1 Hfk Hlf Hkn ltac:(lia) ltac:(lia) HR Hsc1)
      as (Hfl & bs & Hrd & Hlen & Hval).
    destruct (storeok_sound segs E base fk a 4 [] Hfk ltac:(lia) Hfl ltac:(rewrite app_nil_r; exact Hsc3)) as [Hok _].
    assert (Hadr : adenot E a = getr regs rs1).
    { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), <- (Hregs rs1). apply v_addi_0. }
    rewrite Hadr in Hrd, Hok.
    pose proof (aligned_dec_sound segs E base fk a 4 _ Hfk Hfl ltac:(left; reflexivity) Hal) as Hal4.
    rewrite Hadr in Hal4.
    set (regs1 := regupd regs rd (load_result SZ4 true bs)).
    assert (Hregs1 : regs_ok E sr1 regs1).
    { subst sr1 regs1.
      pose proof (regs_ok_upd E (s_regs ss) regs rd (load_result SZ4 true bs) v Hregs) as X.
      assert (Hb : bv_eqb rd 0 = false) by (unfold bv_eqb; apply Z.eqb_neq; intros C; apply Hrd0; apply bv_eq; exact C).
      rewrite Hb in X. apply X. rewrite load_result_val by exact Hlen. symmetry. exact Hval. }
    assert (Hrs1 : getr regs1 rs1 = getr regs rs1) by (subst regs1; apply getr_regupd_other; congruence).
    assert (Heq : c_eq (getr regs1 rd) (getr regs1 rt) = true).
    { pose proof (decide_branch_sound segs E base fk BC_NE _ _ false Hfk Hdb) as Hbt.
      cbn [branch_taken] in Hbt. rewrite <- (Hregs1 rd), <- (Hregs1 rt) in Hbt.
      unfold c_eq. destruct (bv_eqb (getr regs1 rd) (getr regs1 rt)); [reflexivity | discriminate]. }
    assert (Hok' : RiscvSemantics.store_ok segs (mem_denot E base (s_log ss)) (getr regs rs1) 4 = true).
    { eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
    eexists. split.
    + subst ms.
      pose proof (msteps_cas_w segs regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                    w0 w1 w2 aq rl aq' rl' rd rt rd2 rs1 rs2 imm1 bs F0 E0 D0) as X.
      rewrite !v_addi_lit in X.
      replace (s_pc ss + 4 + 4 + 4)%Z with (s_pc ss + 12)%Z in X by lia.
      replace (s_pc ss + 4 + 4)%Z with (s_pc ss + 8)%Z in X by lia.
      specialize (X F1 E1 D1 F2 E2 D2 Hal4 Hrd Hok').
      assert (Hb : bv_eqb rd 0 = false) by (unfold bv_eqb; apply Z.eqb_neq; intros C; apply Hrd0; apply bv_eq; exact C).
      rewrite Hb in X. exact (X Hrs1 Heq).
    + exists (if bv_eqb rd2 0 then regs1 else regupd regs1 rd2 (Z_to_bv 64 0)).
      split; [|split; [|split]].
      * f_equal; try (f_equal; lia). cbn [s_log mem_denot]. rewrite Hadr. subst regs1. rewrite (Hregs1 rs2). reflexivity.
      * cbn [s_regs]. apply regs_ok_upd; [exact Hregs1 | reflexivity].
      * cbn [s_log log_flat]. split; [lia|]. split; [exact Hfl | exact Hlf].
      * exact Hkn.
  -
    destruct Hinv as (Hop & w & aq & rl & Hf & He & Hd).
    set (fk := facts_of (s_know ss)) in *.
    set (a := to_saddrK fk (sr_get (s_regs ss) rs1) 0) in *.
    set (n := awidth_bytes wd) in *.
    set (sx := match wd with AW => true | AD => false end) in *.
    destruct (aligned_dec fk a (Z.of_nat n)) eqn:Hal; [|discriminate]. cbn [negb] in Hs.
    destruct (resolve_load segs fk ss a n sx scr) as [v scs1 scr1|] eqn:HR; [|discriminate].
    destruct (amo_store_expr op wd v (sr_get (s_regs ss) rs2)) as [we|] eqn:Hwe; [|discriminate].
    injection Hs as <- <- <-.
    apply scs_denot_app in Hsc as [Hsc1 Hsc3].
    assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (subst n; destruct wd; cbn; lia). destruct Hn18 as [Hn1 Hn8].
    destruct (resolve_load_sound segs E base fk ss a n sx scr v scs1 scr1 Hfk Hlf Hkn Hn1 Hn8 HR Hsc1)
      as (Hfl & bs & Hrd & Hlen & Hval).
    destruct (storeok_sound segs E base fk a n [] Hfk Hn8 Hfl ltac:(rewrite app_nil_r; exact Hsc3)) as [Hok _].
    assert (Hadr : adenot E a = getr regs rs1).
    { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), <- (Hregs rs1). apply v_addi_0. }
    rewrite Hadr in Hrd, Hok.
    assert (Hm : (Z.of_nat n = 4 \/ Z.of_nat n = 8)%Z) by (subst n; destruct wd; cbn; lia).
    pose proof (aligned_dec_sound segs E base fk a (Z.of_nat n) _ Hfk Hfl Hm Hal) as Haln.
    rewrite Hadr in Haln.
    assert (Hok' : RiscvSemantics.store_ok segs (mem_denot E base (s_log ss)) (getr regs rs1) n = true).
    { eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
    subst ms.

    assert (Hv : edenot E v = load_result (match wd with AW => SZ4 | AD => SZ8 end) true bs).
    { rewrite load_result_val by (destruct wd; exact Hlen). symmetry. subst n sx. destruct wd; exact Hval. }
    destruct wd.
    +
      eexists. split.
      * eapply mst_step; [reflexivity | | apply mst_refl].
        exact (step_amo_w segs regs _ _ rom w op aq rl rd rs1 rs2 bs Hf He Hd Haln Hrd Hok').
      * eexists. split; [|split; [|split; [|exact Hkn]]].
        -- f_equal; try (f_equal; lia); try apply v_addi_lit.
           cbn [s_log mem_denot]. rewrite Hadr. f_equal.
           unfold word_to_le_bytes. subst n. cbn [awidth_bytes].
           apply (amo_bytes_w E op v (sr_get (s_regs ss) rs2) we _ (getr regs rs2) Hwe);
             [rewrite Hv; reflexivity | symmetry; apply Hregs].
        -- cbn [s_regs]. apply regs_ok_upd; [exact Hregs | exact Hv].
        -- cbn [s_log log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
    +
      eexists. split.
      * eapply mst_step; [reflexivity | | apply mst_refl].
        exact (step_amo_d segs regs _ _ rom w op aq rl rd rs1 rs2 bs Hf He Hd Haln Hrd Hok').
      * eexists. split; [|split; [|split; [|exact Hkn]]].
        -- f_equal; try (f_equal; lia); try apply v_addi_lit.
           cbn [s_log mem_denot]. rewrite Hadr. f_equal.
           unfold word_to_le_bytes. subst n. cbn [awidth_bytes].
           apply (amo_bytes_d E op v (sr_get (s_regs ss) rs2) we _ (getr regs rs2) Hwe);
             [rewrite Hv; reflexivity | symmetry; apply Hregs].
        -- cbn [s_regs]. apply regs_ok_upd; [exact Hregs | exact Hv].
        -- cbn [s_log log_flat]. split; [exact Hn8|]. split; [exact Hfl | exact Hlf].
Qed.

Lemma sym_execA_acc : forall fuel first stops scr ss acc E base,
  match sym_execA segs fuel first stops scr ss acc with
  | (ss', scs, scr') => scs_denot segs base E scs -> scs_denot segs base E acc
  end.
Proof.
  induction fuel as [|f IH]; intros first stops scr ss acc E base; cbn [sym_execA].
  - intros H; exact H.
  - destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [intros H; exact H|].
    destruct (vdecode segs (s_pc ss)) as [vi|]; [|intros H; exact H].
    destruct (vstep segs vi ss scr) as [ss2 scs2 scr2|]; [|intros H; exact H].
    specialize (IH false stops scr2 ss2 (sc_add scs2 acc) E base).
    destruct (sym_execA segs f false stops scr2 ss2 (sc_add scs2 acc)) as [[ss' scs] scr'].
    intros H. apply IH in H. apply sc_add_denot in H as [_ H]. exact H.
Qed.

Theorem sym_execA_sound : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_execA segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof.
  induction fuel as [|f IH]; intros first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
  { cbn in Hex. injection Hex as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
  assert (Hstop : (ss, acc, scr) = (ss', scs, scr') ->
                  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms').
  { intro HX. injection HX as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
  cbn [sym_execA] in Hex.
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (Hstop Hex)|].
  destruct (vdecode segs (s_pc ss)) as [vi|] eqn:Hvd; [|exact (Hstop Hex)].
  destruct (vstep segs vi ss scr) as [ss2 scs2 scr2|] eqn:Hstep; [|exact (Hstop Hex)].
  pose proof (sym_execA_acc f false stops scr2 ss2 (sc_add scs2 acc) E base) as Hacc.
  rewrite Hex in Hacc. specialize (Hacc Hsc). apply sc_add_denot in Hacc as [Hsc2 _].
  destruct (vstep_sound E base rom ss ms vi ss2 scs2 scr scr2 Hvd Hstep Hsc2 Hst) as (msA & HmsA & HstA).
  destruct (IH false stops scr2 ss2 (sc_add scs2 acc) ss' scs scr' E base rom msA Hex Hsc HstA)
    as (msB & HmsB & HstB).
  exists msB. split; [|exact HstB]. eapply msteps_trans; [exact HmsA | exact HmsB].
Qed.

Theorem sym_execA_ex : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_execA segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
  destruct (sym_execA_sound fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
    as (ms' & Hms & (R & Heq & Hregs & Hlf & Hkn)).
  exists R. split; [exact Hregs|]. split; [exact Hlf|]. rewrite <- Heq. exact Hms.
Qed.

Theorem runA_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
  sym_execA segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_execA_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

End StepSound.
End SXAS.
