(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsM DefsW.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX MemFX CopyFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM PlanS CtrLib CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module CopyFXW.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.
Local Abbreviation keyof := CopyFX.keyof.
Local Abbreviation zone := (CopyFX.zone segs).
Local Abbreviation zoneW := (CopyFX.zoneW segs).
Local Abbreviation same_ranges := CopyFX.same_ranges.

Lemma ov_read_bytes_nth : forall m n A bs, 0 <= A -> A + Z.of_nat n <= two64 ->
  ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m n. induction n as [|n IH]; intros A bs HA HB H.
  - cbn in H. injection H as <-. split; [reflexivity| intros i Hi; lia].
  - cbn [ov_read_bytes] in H.
    destruct (match m (Z_to_bv 64 A) with Some b0 => Some b0 | None => match memory_read segs (Z_to_bv 64 A) 1 with Some (b0 :: _) => Some b0 | _ => None end end) as [b|] eqn:B0; [|discriminate H].
    rewrite Z_to_bv_succ in H. destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:R; [|discriminate H]. cbn in H. injection H as <-.
    destruct (IH (A + 1) bs' ltac:(lia) ltac:(lia) R) as [L P]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|NZ].
    + rewrite Z.add_0_r, rb_unfold. cbn [Z.to_nat nth_error]. exact B0.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite (P (i - 1)) by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma loadw_where : forall E st ms mo a w v k o,
  St.st_ok segs OPS E st ms mo -> wok w -> addr_of a = Some (k, o) ->
  do_load segs st a w false = inl (Some v) ->
  let A := bv_unsigned (den E a) in
  exists key bs, Mem.okey o = Some key /\ A = bv_unsigned (ev E k) + keyZ key
    /\ length bs = Z.to_nat (to_Z w) /\ store_bytes w (den E v) = bs
    /\ forall t, 0 <= t < to_Z w ->
         zone (s_regs st) (s_priv st) E k (A + t) /\ A + t + 1 < two64 /\ rb segs (ms_mem ms) (A + t) = nth_error bs (Z.to_nat t).
Proof.
  intros E st ms mo a w v k o HS Hw Ha H. cbv zeta.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  destruct (do_load_sound segs OPS E st ms mo a w false v HS Hw H) as (bs & Len & OV & Dv).
  unfold do_load in H. rewrite Ha in H.
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (Mem.okey o) as [key|] eqn:Hk; [|discriminate].
  destruct (can_read segs (s_facts st) (s_priv st) k r key w) eqn:CR; [|discriminate].
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
  pose proof (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfs Hz RO Hw CR) as (RA & RAw & _ & RNG & ABS).
  cbv zeta in RA, RAw.
  pose proof (access_addr E a k o key (addrZ E k key) Hz Ha Hk eq_refl RA ltac:(lia)) as DA.
  assert (EA : bv_unsigned (den E a) = addrZ E k key).
  { rewrite DA, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
  rewrite <- (Z_to_bv_bv_unsigned (den E a)) in OV. rewrite EA in OV.
  destruct (ov_read_bytes_nth (ms_mem ms) (Z.to_nat (to_Z w)) (addrZ E k key) bs RA ltac:(rewrite Z2Nat.id by lia; exact RAw) OV) as [_ NTH].
  rewrite Z2Nat.id in NTH by lia.
  exists key, bs. split; [reflexivity|]. rewrite EA. split; [reflexivity|]. split; [exact Len|]. split.
  -
    rewrite Dv. unfold store_bytes.
    rewrite <- (bytes_val_ext_word false (to_Z w) bs Len ltac:(lia)). unfold bytes_val.
    pose proof (bytes_le_to_Z_bound bs) as B. rewrite Len, Z2Nat.id in B by lia.
    assert (HP : 2 ^ (8 * to_Z w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite (ext_Z_small_id false (to_Z w) (bytes_le_to_Z bs)); [| lia| unfold two64; lia| rewrite Z.sub_0_r; lia].
    rewrite (Z_to_bv_small (bytes_le_to_Z bs)) by (unfold two64; lia). rewrite <- Len. apply MemFX.Z_to_le_bytes_to_Z.
  - intros t Ht. split; [| split; [| exact (NTH t Ht)]].
    + unfold CopyFX.zone. destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
      * destruct (ABS eq_refl t Ht) as ([bs' MR] & NP).
        assert (A0 : addrZ E k key = keyZ key).
        { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
        rewrite A0 in *. split; [| exact NP]. apply (memory_read_find_segment segs (keyZ key + t) bs'); [| exact MR].
        unfold two64 in *. lia.
      * exists r. split; [exact Hr|]. pose proof (RNG eq_refl t Ht) as X. unfold addrZ. lia.
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
      * assert (A0 : addrZ E k key = keyZ key).
        { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
        rewrite A0. pose proof (keyZ_range key). unfold two64 in *. lia.
      * pose proof (RNG eq_refl t Ht) as X. pose proof (ro_range _ _ _ _ _ _ RO K0) as [_ RH]. unfold addrZ. lia.
Qed.

Lemma storew_where : forall E st (R F : bvmap 5 word) pc fc m rom mo a w v st',
  St.st_ok segs OPS E st (MS R F pc fc None m rom) mo -> s_resv st = RNone -> wok w ->
  do_store segs st a w v = inl st' ->
  let A := bv_unsigned (den E a) in
  St.st_ok segs OPS E st' (MS R F pc fc None (write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v))) rom) mo
  /\ st' = SS (s_pc st) (s_rf st) (s_ff st) RNone (s_regs st') (s_facts st) (s_ops st) (s_priv st) (s_next st)
  /\ same_ranges (s_regs st) (s_regs st')
  /\ exists k o key, addr_of a = Some (k, o) /\ Mem.okey o = Some key /\ A = bv_unsigned (ev E k) + keyZ key
       /\ forall t, 0 <= t < to_Z w ->
            zoneW (s_regs st) (s_priv st) E k (A + t) /\ A + t + 1 < two64 /\ wb segs m (A + t) = true /\ rb segs m (A + t) <> None.
Proof.
  intros E st R F pc fc m rom mo a w v st' HS RV Hw H. cbv zeta.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_bst _ _ _ _ _ _ HS) as HB.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  unfold do_store in H.
  destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (Mem.okey o) as [key|] eqn:Hk; [|discriminate].
  destruct (can_write segs (s_facts st) (s_priv st) k r key w) eqn:CW; [|discriminate].
  apply inl_inj in H. subst st'. rewrite RV. cbn [resv_after_store s_regs].
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
  destruct (can_write_sound segs (s_priv st) E m (s_facts st) k r key w Hfs Hz RO Hw CW) as (CR & WB & SEGW).
  pose proof (can_read_sound segs (s_priv st) E m (s_facts st) k r key w Hfs Hz RO Hw CR) as (RA & RAw & RBk & RNG & ABS).
  cbv zeta in RA, RAw.
  pose proof (access_addr E a k o key (addrZ E k key) Hz Ha Hk eq_refl RA ltac:(lia)) as DA.
  assert (EA : bv_unsigned (den E a) = addrZ E k key).
  { rewrite DA, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
  rewrite EA.
  destruct (store_sound segs OPS E st (MS R F pc fc None m rom) mo a k o r key w v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
  cbn [ms_mem MS core_of with_resv ms_upd ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_rom c_regs c_fregs c_pc c_fcsr c_resv] in ST.
  rewrite DA in ST.
  destruct (region_store_sound segs (s_priv st) E m (s_facts st) k r key w v Hfs Hz RO Hw CW) as (_ & _ & Flo & Fhi & Fw & Fbg & _).
  split; [exact ST|]. split; [reflexivity|]. split.
  - intros k1. split.
    + intros r' H'. destruct (Uint63.eqb k k1) eqn:Q.
      * apply Uint63.eqb_correct in Q. subst k1. rewrite IMap.find_add_same in H' by exact HB. injection H' as <-.
        exists r. rewrite Flo, Fhi, Fw. auto.
      * apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H' by (exact HB || exact Q). exists r'. auto.
    + intros r1 H1. destruct (Uint63.eqb k k1) eqn:Q.
      * apply Uint63.eqb_correct in Q. subst k1. eexists. rewrite IMap.find_add_same by exact HB. reflexivity.
      * apply Uint63.eqb_false_spec in Q. exists r1. rewrite IMap.find_add_other by (exact HB || exact Q). exact H1.
  - exists k, o, key. split; [reflexivity|]. split; [first [exact Hk | reflexivity]|]. split; [reflexivity|].
    intros t Ht. split; [| split; [| split; [exact (WB t Ht)| exact (RBk t Ht)]]].
    + split.
      * unfold CopyFX.zone. destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
        -- destruct (ABS eq_refl t Ht) as ([bs' MR] & NP).
           assert (A0 : addrZ E k key = keyZ key).
           { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
           rewrite A0 in *. split; [| exact NP]. apply (memory_read_find_segment segs (keyZ key + t) bs'); [| exact MR].
           unfold two64 in *. lia.
        -- exists r. split; [exact Hr|]. pose proof (RNG eq_refl t Ht) as X. unfold addrZ. lia.
      * intros K0. exists r. split; [exact Hr|]. unfold can_write in CW. rewrite K0 in CW. apply andb_prop in CW as [W _]. exact W.
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
      * assert (A0 : addrZ E k key = keyZ key).
        { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
        rewrite A0. pose proof (keyZ_range key). unfold two64 in *. lia.
      * pose proof (RNG eq_refl t Ht) as X. pose proof (ro_range _ _ _ _ _ _ RO K0) as [_ RH]. unfold addrZ. lia.
Qed.

Lemma wadd_lit0 : forall o, wadd o (wlit (of_Z 0)) = o.
Proof. intros o. apply w2Z_inj. rewrite wadd_ok, wlit_ok. change (to_Z (of_Z 0)) with 0. rewrite Z.add_0_r. apply Z.mod_small. apply w2Z_range. Qed.

Section COPYW.
Variables (E : env) (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rom : word -> option byte) (mo : Model).
Variables (src dst : sv) (st0 : sstate) (m0 : word -> option byte).
Hypothesis RV0 : s_resv st0 = RNone.
Variables (ks kd : int) (os od : w64).
Hypothesis ASRC : addr_of src = Some (ks, os).
Hypothesis ADST : addr_of dst = Some (kd, od).
Local Abbreviation saddr := (CopyFX.saddr E src).
Local Abbreviation daddr := (CopyFX.daddr E dst).

Record CINVW (i : Z) (sti : sstate) (mi : word -> option byte) (bs : list byte) : Prop := MKCW {
  cw_ok : St.st_ok segs OPS E sti (MS R F pc fc None mi rom) mo;
  cw_shape : sti = SS (s_pc st0) (s_rf st0) (s_ff st0) RNone (s_regs sti) (s_facts st0) (s_ops st0) (s_priv st0) (s_next st0);
  cw_ranges : same_ranges (s_regs st0) (s_regs sti);
  cw_len : length bs = Z.to_nat i;
  cw_frame : forall x, (forall j, 0 <= j < i -> x <> daddr j) -> mi x = m0 x;
  cw_written : forall j, 0 <= j < i -> mi (daddr j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0));
  cw_read : forall j, 0 <= j < i -> (forall j', 0 <= j' < j -> saddr j <> daddr j') ->
              rb segs m0 (bv_unsigned (saddr j)) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0));
  cw_src : forall j, 0 <= j < i -> zone (s_regs st0) (s_priv st0) E ks (bv_unsigned (saddr j)) /\ bv_unsigned (saddr j) + 1 < two64;
  cw_src0 : 0 < i -> exists key, Mem.okey os = Some key /\ bv_unsigned (saddr 0) = bv_unsigned (ev E ks) + keyZ key;
  cw_dst : forall j, 0 <= j < i -> zoneW (s_regs st0) (s_priv st0) E kd (bv_unsigned (daddr j)) /\ bv_unsigned (daddr j) + 1 < two64
              /\ wb segs m0 (bv_unsigned (daddr j)) = true /\ rb segs m0 (bv_unsigned (daddr j)) <> None;
  cw_dst0 : 0 < i -> exists key, Mem.okey od = Some key /\ bv_unsigned (daddr 0) = bv_unsigned (ev E kd) + keyZ key }.

Lemma CINVW0 : St.st_ok segs OPS E st0 (MS R F pc fc None m0 rom) mo -> CINVW 0 st0 m0 [].
Proof.
  intros HS. constructor; try (intros; lia).
  - exact HS.
  - destruct st0; cbn in RV0 |- *. subst. reflexivity.
  - apply CopyFX.same_ranges_refl.
  - reflexivity.
  - intros x _. reflexivity.
Qed.

Lemma addr_in_access : forall (W : word) i t, 0 <= t -> bv_unsigned (W + Z_to_bv 64 i)%bv + t < two64 ->
  bv_unsigned (W + Z_to_bv 64 (i + t))%bv = bv_unsigned (W + Z_to_bv 64 i)%bv + t.
Proof.
  intros W i t Ht B. rewrite !CopyFX.unsigned_add_lit in *. rewrite Z.add_assoc.
  rewrite <- (Z.add_mod_idemp_l (bv_unsigned W + i) t) by (unfold two64; lia). apply Z.mod_small.
  pose proof (Z.mod_pos_bound (bv_unsigned W + i) two64 ltac:(unfold two64; lia)). lia.
Qed.

Lemma copy_wstep : forall i (iw : int) sti mi bs v st',
  0 <= i -> i + 8 <= 4096 -> to_Z iw = i -> CINVW i sti mi bs ->
  do_load segs sti (sv_alu ALU_ADD src (VL (wlit iw))) 8%uint63 false = inl (Some v) ->
  do_store segs sti (sv_alu ALU_ADD dst (VL (wlit iw))) 8%uint63 v = inl st' ->
  exists b8, length b8 = 8%nat /\ CINVW (i + 8) st' (write_to_mem mi (daddr i) b8) (bs ++ b8).
Proof.
  intros i iw sti mi bs v st' Hi Hi8 Hiw CI HL HST.
  destruct CI as [OK SH SR LEN FR WR RD SRC SRC0 DST DST0].
  assert (RVi : s_resv sti = RNone) by (rewrite SH; reflexivity).
  assert (PRIVi : s_priv sti = s_priv st0) by (rewrite SH; reflexivity).
  assert (W8 : wok 8%uint63) by (right; right; right; reflexivity).
  pose proof (CopyFX.addr_of_add_lit src ks os (wlit iw) ASRC) as AS_i.
  destruct (loadw_where E sti _ mo _ 8%uint63 v ks _ OK W8 AS_i HL) as (key & b8 & OKs & XAs & L8 & SB & PT).
  destruct (storew_where E sti R F pc fc mi rom mo _ 8%uint63 v st' OK RVi W8 HST) as (OK' & SH' & SR' & kd' & od' & keyd & AD & OKd & XD & PD).
  rewrite (CopyFX.addr_of_add_lit dst kd od (wlit iw) ADST) in AD. injection AD as <- <-.
  cbn [ms_mem MS] in PT. change (to_Z 8%uint63) with 8 in *. change (Z.to_nat 8) with 8%nat in L8.
  rewrite !CopyFX.den_add_lit, !Hiw in *. fold (saddr i) in XAs, PT. fold (daddr i) in OK', XD, PD.
  set (Si := bv_unsigned (saddr i)) in *. set (Di := bv_unsigned (daddr i)) in *.
  assert (ES : forall t, 0 <= t < 8 -> bv_unsigned (saddr (i + t)) = Si + t).
  { intros t Ht. unfold CopyFX.saddr. apply addr_in_access; [lia|]. destruct (PT t Ht) as (_ & B & _). fold (saddr i). fold Si. lia. }
  assert (ED : forall t, 0 <= t < 8 -> bv_unsigned (daddr (i + t)) = Di + t).
  { intros t Ht. unfold CopyFX.daddr. apply addr_in_access; [lia|]. destruct (PD t Ht) as (_ & B & _). fold (daddr i). fold Di. lia. }
  rewrite SB in OK'. replace (Z_to_bv 64 Di) with (daddr i) in OK' by (unfold Di; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 (daddr i)) as RDi. rewrite bv_modulus_64 in RDi. fold Di in RDi.
  assert (D8 : Di + 8 <= two64) by (destruct (PD 7 ltac:(lia)) as (_ & B & _); lia).
  assert (WSPEC : forall x, write_to_mem mi (daddr i) b8 x =
            if (Z.leb Di (bv_unsigned x) && Z.ltb (bv_unsigned x) (Di + 8))%bool then nth_error b8 (Z.to_nat (bv_unsigned x - Di)) else mi x).
  { intros x. replace (daddr i) with (Lib.Mem.wa Di) by (unfold Lib.Mem.wa, Di; apply Z_to_bv_bv_unsigned).
    rewrite (Lib.Mem.write_to_mem_spec b8 mi Di x ltac:(lia) ltac:(rewrite L8; unfold two64 in D8; lia)). rewrite L8. reflexivity. }
  assert (INJ : forall j j', 0 <= j < 4096 -> 0 <= j' < 4096 -> daddr j = daddr j' -> j = j').
  { intros j j' Hj Hj' X. apply (CopyFX.word_add_inj (den E dst)); unfold two64; try lia. exact X. }
  assert (INW : forall x, (Z.leb Di (bv_unsigned x) && Z.ltb (bv_unsigned x) (Di + 8))%bool = true -> exists t, 0 <= t < 8 /\ x = daddr (i + t) /\ bv_unsigned x - Di = t).
  { intros x C. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. exists (bv_unsigned x - Di). split; [lia|]. split; [| reflexivity].
    apply bv_eq. rewrite (ED (bv_unsigned x - Di)) by lia. lia. }
  exists b8. split; [exact L8|]. constructor.
  - exact OK'.
  - rewrite SH' at 1. rewrite SH. reflexivity.
  - eapply CopyFX.same_ranges_trans; [exact SR| exact SR'].
  - rewrite length_app, LEN, L8. lia.
  - intros x Hx. rewrite WSPEC. destruct (Z.leb Di (bv_unsigned x) && Z.ltb (bv_unsigned x) (Di + 8))%bool eqn:C.
    + exfalso. destruct (INW x C) as (t & Ht & -> & _). exact (Hx (i + t) ltac:(lia) eq_refl).
    + apply FR. intros j Hj. apply Hx. lia.
  - intros j Hj. rewrite WSPEC. destruct (Z.leb Di (bv_unsigned (daddr j)) && Z.ltb (bv_unsigned (daddr j)) (Di + 8))%bool eqn:C.
    + destruct (INW _ C) as (t & Ht & EQ & ET). apply INJ in EQ; [| lia| lia]. subst j. rewrite ET.
      rewrite app_nth2 by (rewrite LEN; lia). rewrite LEN. replace (Z.to_nat (i + t) - Z.to_nat i)%nat with (Z.to_nat t) by lia.
      apply nth_error_nth'. rewrite L8. lia.
    + assert (JI : j < i).
      { destruct (Z_lt_le_dec j i) as [L|G]; [exact L| exfalso]. rewrite (ED (j - i) ltac:(lia)) in C || (replace j with (i + (j - i)) in C by lia; rewrite (ED (j - i) ltac:(lia)) in C).
        apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C| apply Z.ltb_ge in C]; lia. }
      rewrite WR by lia. rewrite app_nth1 by (rewrite LEN; lia). reflexivity.
  - intros j Hj SEP. destruct (Z_lt_le_dec j i) as [JI|JI].
    + rewrite RD by (try lia; intros j' Hj'; apply SEP; lia). rewrite app_nth1 by (rewrite LEN; lia). reflexivity.
    + replace j with (i + (j - i)) in * by lia. set (t := j - i) in *. assert (Ht : 0 <= t < 8) by lia.
      rewrite app_nth2 by (rewrite LEN; lia). rewrite LEN. replace (Z.to_nat (i + t) - Z.to_nat i)%nat with (Z.to_nat t) by lia.
      destruct (PT t Ht) as (_ & _ & RBt). rewrite (nth_error_nth' b8 (Z_to_bv 8 0)) in RBt by (rewrite L8; lia).
      rewrite <- RBt. rewrite (ES t Ht). unfold rb. rewrite <- (ES t Ht), Z_to_bv_bv_unsigned.
      rewrite (FR (saddr (i + t))); [reflexivity|]. intros j' Hj'. apply SEP. lia.
  - intros j Hj. destruct (Z_lt_le_dec j i) as [JI|JI]; [apply SRC; lia|].
    replace j with (i + (j - i)) by lia. rewrite (ES (j - i) ltac:(lia)). destruct (PT (j - i) ltac:(lia)) as (ZO & B & _).
    split; [| lia]. rewrite <- PRIVi. exact (CopyFX.zone_same_ranges segs _ _ _ _ _ _ SR ZO).
  - intros _. destruct (Z.eq_dec i 0) as [I0|I0]; [| apply SRC0; lia].
    exists key. assert (IW0 : iw = of_Z 0) by (apply Uint63.to_Z_inj; rewrite Hiw, I0; reflexivity).
    rewrite IW0, wadd_lit0 in OKs. split; [exact OKs|]. rewrite <- I0. exact XAs.
  - intros j Hj. destruct (Z_lt_le_dec j i) as [JI|JI]; [apply DST; lia|].
    replace j with (i + (j - i)) by lia. rewrite (ED (j - i) ltac:(lia)). destruct (PD (j - i) ltac:(lia)) as (ZW & B & WB & RB).
    split; [rewrite <- PRIVi; exact (CopyFX.zoneW_same_ranges segs _ _ _ _ _ _ SR ZW)|]. split; [lia|].
    assert (MI : mi (Z_to_bv 64 (Di + (j - i))) = m0 (Z_to_bv 64 (Di + (j - i)))).
    { apply FR. intros j' Hj' X. apply (f_equal bv_unsigned) in X. rewrite Z_to_bv_unsigned in X. rewrite bv_wrap_small in X by (rewrite bv_modulus_64; lia).
      rewrite <- (ED (j - i) ltac:(lia)) in X. apply bv_eq in X. apply INJ in X; lia. }
    unfold wb, rb in *. unfold wview in WB |- *. rewrite <- MI. split; [exact WB| exact RB].
  - intros _. destruct (Z.eq_dec i 0) as [I0|I0]; [| apply DST0; lia].
    exists keyd. assert (IW0 : iw = of_Z 0) by (apply Uint63.to_Z_inj; rewrite Hiw, I0; reflexivity).
    rewrite IW0, wadd_lit0 in OKd. split; [exact OKd|]. rewrite <- I0. exact XD.
Qed.

Lemma copy_words_ind : forall cnt i (iw : int) sti mi bs stn,
  0 <= i -> i + 8 * Z.of_nat cnt <= 4096 -> to_Z iw = i -> CINVW i sti mi bs ->
  CtrW.copy_words segs cnt iw src dst sti = Some stn ->
  exists mn bsn, CINVW (i + 8 * Z.of_nat cnt) stn mn bsn.
Proof.
  induction cnt as [|cnt IH]; intros i iw sti mi bs stn Hi Hc Hiw CI H.
  - cbn in H. injection H as <-. exists mi, bs. rewrite Z.mul_0_r, Z.add_0_r. exact CI.
  - cbn [CtrW.copy_words] in H.
    destruct (do_load segs sti (sv_alu ALU_ADD src (VL (wlit iw))) 8%uint63 false) as [[v|]|] eqn:HL; try discriminate.
    destruct (do_store segs sti (sv_alu ALU_ADD dst (VL (wlit iw))) 8%uint63 v) as [st'|] eqn:HST; [|discriminate].
    destruct (copy_wstep i iw sti mi bs v st' Hi ltac:(lia) Hiw CI HL HST) as (b8 & _ & CI').
    assert (Hiw1 : to_Z (PrimInt63.add iw 8%uint63) = i + 8).
    { rewrite add_Z; [| change (to_Z 8%uint63) with 8; rewrite wB_two63, two63_eq; pose proof (int_range iw); lia]. change (to_Z 8%uint63) with 8. lia. }
    destruct (IH (i + 8) (PrimInt63.add iw 8%uint63) st' _ _ stn ltac:(lia) ltac:(lia) Hiw1 CI' H) as (mn & bsn & CIn).
    exists mn, bsn. replace (i + 8 * Z.of_nat (S cnt)) with (i + 8 + 8 * Z.of_nat cnt) by lia. exact CIn.
Qed.

End COPYW.
End WithSegs.
End CopyFXW.
