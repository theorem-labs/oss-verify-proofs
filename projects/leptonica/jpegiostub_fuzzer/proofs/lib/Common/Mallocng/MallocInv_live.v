(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


Definition round16 (n : Z) : Z := 16 * ((n + 15) / 16).

Lemma round16_ge : forall n, n <= round16 n.
Proof using Type. pu_keep tt. intros n. unfold round16. pose proof (Z.div_mod (n + 15) 16 ltac:(llia)). pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(llia)). llia. Qed.

Lemma round16_le_mult : forall n m, 0 <= n -> n <= 16 * m -> round16 n <= 16 * m.
Proof using Type. pu_keep tt.
  intros n m Hn Hle. unfold round16.
  assert ((n + 15) / 16 < m + 1) by (apply Z.div_lt_upper_bound; llia). llia.
Qed.

Section Live.
  Variable A : astate.
  Hypothesis HW : WF A.

  (* [comment removed for export] *)
  Lemma live_geom : forall ma mt aib slots i off n,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i ->
    nth_error slots (Z.to_nat i) = Some (SLive off n) ->
    let p := slot_start mt i + 16 * off in
    exists q, mt_stride mt = 16 * q /\
      0 <= n /\ 0 <= off /\ 16 * off + n <= mt_stride mt - 4 /\
      mt_mem mt mod 16 = 0 /\ p mod 16 = 0 /\
      gext_lo mt + 16 <= slot_start mt i /\ slot_start mt i <= p /\
      p + round16 n <= slot_start mt i + mt_stride mt /\ slot_start mt i + mt_stride mt <= gext_hi mt + 4 /\
      0x1000 <= gext_lo mt /\ gext_hi mt + 4 <= alloc_ceiling /\ (gext_hi mt + 4 <= IMG_LO \/ IMG_HI <= gext_lo mt).
  Proof using HW. pu_keep (HW).
    intros ma mt aib slots i off n Hma Hr Hi0 Hi p.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS.
    pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hfit2 & _).
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
    destruct (stride_16 mt) as [q Hq].
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & _).
    destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpgr).
    destruct (Hpgr Hml) as [_ (R1 & R2 & R3 & R4)].
    exists q. unfold gext_lo, gext_hi, slot_start, slot_start_g in *. subst p.
    assert (0 <= i * mt_stride mt /\ i * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by lnia.
    assert (round16 n <= mt_stride mt - 16 * off).
    { replace (mt_stride mt - 16 * off) with (16 * (q - off)) by llia. apply round16_le_mult; llia. }
    repeat split; try llia.
    all: rewrite Hq; replace (mt_mem mt + 16 + i * (16 * q) + 16 * off) with (16 * (1 + i * q + off) + mt_mem mt) by llia;
         rewrite Z.add_mod, Z.mul_comm, Z.mod_mul, Hal16 by llia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma live_clear : forall ma mt aib slots i off n,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i ->
    nth_error slots (Z.to_nat i) = Some (SLive off n) ->
    let p := slot_start mt i + 16 * off in
    forall f, has A f -> f_a f + f_n f <= p \/ p + n <= f_a f.
  Proof using HW MLok. pu_keep (HW, MLok).
    intros ma mt aib slots i off n Hma Hr Hi0 Hi p f Hf.
    destruct (live_geom ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & Hq & Hn & Ho & Hfit & Hal & Hpal & G1 & G2 & G3 & G4 & G5 & G6 & G7).
    fold p in Hpal, G2, G3. pose proof (round16_ge n) as Hr16. unfold gext_lo, gext_hi in G1, G4, G5, G6, G7.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & _).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hrlo & Hrhi & _).
    pose proof (has_addr A HW f Hf) as (Hfn & Hf1 & Hf2 & Hfw).
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpgr).
      destruct (Hpgr Hml) as [_ Hheap]. pose proof (has_ctx_where A f Hc) as (C1 & C2 & C3).
      destruct Hc as (k & Hk & ->). cbn in *.
      destruct (heap_avoids_ctx _ _ Hheap k Hk); unfold gext_lo, gext_hi in *; llia.
    - destruct Har as (pg & Hpga & ->). cbn in *.
      destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
    - destruct Hm as (ma' & mt' & fl & Hma' & ->). cbn in *. pose proof (mfield_range fl).
      destruct (proj1 (wf_meta_dom A HW ma') ltac:(rewrite Hma'; discriminate)) as (pg & k & Hpga & Hk & ->).
      pose proof (meta_addr_range pg k Hk).
      destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
    - destruct Hg as (ma' & mt' & aib' & slots' & Hma' & Hr' & Hin).
      destruct (Z.eq_dec ma' ma) as [-> | Hne].
      + rewrite Hma in Hma'. injection Hma' as <-. rewrite Hr in Hr'. injection Hr' as <- <-.
        destruct Hin as [Hin | (i' & st' & Hi' & Hin)].
        * destruct Hin as [<- | [<- | []]]; cbn; unfold gext_lo in *; llia.
        * destruct (Nat.eq_dec i' (Z.to_nat i)) as [-> | Hne'].
          -- rewrite Hi in Hi'. injection Hi' as <-. rewrite Z2Nat.id in Hin by llia.
             unfold slot_fields, slot_fields_g in Hin.
             change (slot_start_g (mt_mem mt) (mt_stride mt) i) with (slot_start mt i) in Hin.
             unfold slot_end_g in Hin. unfold slot_start, slot_start_g in *.
             set (P0 := mt_mem mt + 16 + i * mt_stride mt) in *.
             repeat (apply in_app_iff in Hin; destruct Hin as [Hin | Hin]).
             ++ destruct Hin as [<- | [<- | []]]; cbn; llia.
             ++ destruct (off =? 0) eqn:E; [destruct Hin|]. apply Z.eqb_neq in E.
                destruct Hin as [<- | [<- | [<- | []]]]; cbn; llia.
             ++ destruct Hin as [<- | [<- | []]]; cbn; llia.
             ++ destruct (_ <? 5) eqn:E; [destruct Hin|]. apply Z.ltb_ge in E.
                destruct Hin as [<- | [<- | []]]; cbn; llia.
             ++ destruct (_ =? 0) eqn:E; [destruct Hin|]. destruct Hin as [<- | []]; cbn; llia.
          -- pose proof (slot_fact_bounds A HW ma mt aib slots i' st' f Hma Hr Hi' Hin) as (B1 & B2).
             unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
             assert (Hi'lt : (i' < length slots)%nat) by (apply (proj1 (nth_error_Some slots i')); rewrite Hi'; discriminate).
             destruct (Nat.lt_ge_cases i' (Z.to_nat i)) as [Hlt | Hge].
             ++ left. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) (Z.of_nat i') i HS ltac:(llia) Hi0 ltac:(llia)). llia.
             ++ right. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i (Z.of_nat i') HS Hi0 ltac:(llia) ltac:(llia)). llia.
      + assert (Hfin : gext_lo mt' <= f_a f /\ f_a f + f_n f <= gext_hi mt' + 1).
        { destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as (Hw32' & _ & Hsc' & Hlen' & _).
          pose proof (stride_ge16 mt' ltac:(llia) Hsc') as HS'.
          destruct Hin as [Hin | (i' & st' & Hi' & Hin)].
          - unfold gext_lo, gext_hi. assert (0 <= mt_cnt mt' * mt_stride mt') by lnia.
            destruct Hin as [<- | [<- | []]]; cbn; llia.
          - pose proof (slot_fields_where A HW ma' mt' aib' slots' i' st' f Hma' Hr' Hi' Hin). llia. }
        destruct (wf_laminar A HW ma mt aib slots ma' mt' aib' slots' Hma Hr Hma' Hr' ltac:(congruence))
          as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
        * unfold gext_lo, gext_hi in *. llia.
        * unfold gext_lo, gext_hi in *. llia.
        * assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; discriminate).
          unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
          destruct (Z.lt_ge_cases j i) as [Hlt | Hge].
          -- left. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) j i HS Hj0 Hi0 Hlt). llia.
          -- right. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i j HS Hi0 Hj0 ltac:(llia)). llia.
        * destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as (Hw32' & _ & Hsc' & Hlen' & _).
          pose proof (stride_ge16 mt' ltac:(llia) Hsc') as HS'.
          unfold gext_lo, gext_hi in Hjlo, Hjhi.
          destruct Hin as [Hin | (i' & st' & Hi' & Hin)].
          -- left. unfold slot_start, slot_start_g in Hjlo. assert (0 <= j * mt_stride mt') by lnia.
             destruct Hin as [<- | [<- | []]]; cbn; llia.
          -- pose proof (slot_fact_bounds A HW ma' mt' aib' slots' i' st' f Hma' Hr' Hi' Hin) as (B1 & B2).
             unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
             destruct (Z.lt_total (Z.of_nat i') j) as [Hlt | [Heq | Hgt]].
             ++ left. pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') (Z.of_nat i') j HS' ltac:(llia) Hj0 Hlt). llia.
             ++ rewrite <- Heq, Nat2Z.id in Hj. rewrite Hj in Hi'. injection Hi' as <-.
                unfold slot_fields, slot_fields_g in Hin. apply in_app_iff in Hin.
                destruct Hin as [[<- | [<- | []]] | [<- | [<- | []]]]; cbn [f_a f_n]; unfold slot_start_g, slot_end_g; llia.
             ++ right. pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') j (Z.of_nat i') HS' Hj0 ltac:(llia) Hgt). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_disjoint : forall ma mt aib slots i off n ma' mt' aib' slots' i' off' n',
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i -> nth_error slots (Z.to_nat i) = Some (SLive off n) ->
    a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> 0 <= i' -> nth_error slots' (Z.to_nat i') = Some (SLive off' n') ->
    (ma <> ma' \/ i <> i') ->
    let p := slot_start mt i + 16 * off in
    let p' := slot_start mt' i' + 16 * off' in
    p + round16 n <= p' \/ p' + round16 n' <= p.
  Proof using HW. pu_keep (HW).
    intros ma mt aib slots i off n ma' mt' aib' slots' i' off' n' Hma Hr Hi0 Hi Hma' Hr' Hi0' Hi' Hdiff p p'.
    destruct (live_geom ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & Hq & Hn & Ho & Hfit & Hal & Hpal & G1 & G2 & G3 & G4 & G5 & G6 & G7).
    destruct (live_geom ma' mt' aib' slots' i' off' n' Hma' Hr' Hi0' Hi') as (q' & Hq' & Hn' & Ho' & Hfit' & Hal' & Hpal' & G1' & G2' & G3' & G4' & G5' & G6' & G7').
    fold p in Hpal, G2, G3. fold p' in Hpal', G2', G3'.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32 & _ & Hsc & Hlen & _).
    destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as (Hw32' & _ & Hsc' & Hlen' & _).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS. pose proof (stride_ge16 mt' ltac:(llia) Hsc') as HS'.
    destruct (Z.eq_dec ma ma') as [<- | Hne].
    - rewrite Hma in Hma'. injection Hma' as <-. rewrite Hr in Hr'. injection Hr' as <- <-.
      assert (Hii : i <> i') by (destruct Hdiff as [H|H]; [exfalso; apply H; reflexivity | exact H]).
      unfold slot_start, slot_start_g in *.
      destruct (Z.lt_total i i') as [Hlt | [-> | Hgt]]; [| exfalso; apply Hii; reflexivity |].
      + left. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i i' HS Hi0 Hi0' Hlt). llia.
      + right. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i' i HS Hi0' Hi0 Hgt). llia.
    - destruct (wf_laminar A HW ma mt aib slots ma' mt' aib' slots' Hma Hr Hma' Hr' Hne)
        as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
      + left. llia.
      + right. llia.
      + (* [comment removed for export] *)
        assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; discriminate).
        unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
        destruct (Z.lt_ge_cases j i) as [Hlt | Hge].
        * right. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) j i HS Hj0 Hi0 Hlt). llia.
        * left. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i j HS Hi0 Hj0 ltac:(llia)). llia.
      + assert (Hji : j <> i') by (intros ->; rewrite Hi' in Hj; discriminate).
        unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
        destruct (Z.lt_ge_cases j i') as [Hlt | Hge].
        * left. pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') j i' HS' Hj0 Hi0' Hlt). llia.
        * right. pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') i' j HS' Hi0' Hj0 ltac:(llia)). llia.
  Qed.
End Live.

End WithLayout.
