(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngWk MngImage.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_efz MngMalloc.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz.AXF_efa2z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition ef_tail (g : sptr) (idx n : Z) (s : astate) : itree astate (option sptr * astate) :=
  ibind (enframe g idx n (st_mmap_counter s) FUser s) (fun '(p, s') => IRet (Some p, s')).

(* [comment removed for export] *)
Definition mw_sc (s : astate) (n : Z) : Z :=
  let sc0 := size_to_class n in
  let g0 := nth (Z.to_nat sc0) (st_active s) None in
  if (osptr_eqb g0 None) && (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of s sc0 =? 0)
  then
    let u := usage_of s (sc0 + 1) in
    let head_full :=
      match nth (Z.to_nat (sc0 + 1)) (st_active s) None with
      | None => true
      | Some h => match mlookup (st_metas s) h with
                  | Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
                  | _ => true
                  end
      end in
    let u := if head_full then u + 3 else u in
    if u <=? 12 then sc0 + 1 else sc0
  else sc0.

(* [comment removed for export] *)
Definition k_slow (sc n : Z) : Z * astate -> itree astate (option sptr * astate) :=
  fun '(idx, s1) => if idx <? 0 then IRet (None, s1)
                    else match active_hd s1 sc with
                         | Some gm => ef_tail gm idx n s1
                         | None => IFail (FModel 9)
                         end.

Lemma malloc_fast_eq : forall n s g am, 1 <= n < MMAP_THRESHOLD ->
  active_hd s (mw_sc s n) = Some g -> MT s g = Some (MUsed am) -> am_avail am <> 0 ->
  malloc n s = ef_tail g (mf_idx am) n (set_meta s g (MUsed (mf_am1 am))).
Proof.
  intros n s g am Hn Hact HMT Hav.
  unfold malloc. replace (size_overflows n) with false by (unfold size_overflows; symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
  replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold bind, get, ret. cbn [ibind]. fold (mw_sc s n).
  unfold active_hd in Hact. rewrite Hact.
  unfold getm, bind, get, ret. cbn [ibind]. unfold MT in HMT. rewrite HMT. cbn [ibind].
  replace (am_avail am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hav).
  unfold setm, modify. cbn [ibind set_metas st_mmap_counter st_metas].
  unfold ef_tail, bind, get, ret. cbn [ibind st_mmap_counter]. unfold set_meta. reflexivity.
Qed.

Section WKJ.
Context {fx : FPState}.
Variables (segs : list Segment) (FORB : list (Z * Z)) (HTOP : Z) (rom : word -> option byte).

#[using="Type"] Lemma wk_junk : forall {R : Type} L regs pc m b s (k : Z -> itree astate R) (Q : @wpost R) z,
  0 <= z < 256 -> wk segs FORB HTOP rom L regs pc m (k z) Q -> wk segs FORB HTOP rom L regs pc m (IAsk (KJunk b) s k) Q.
Proof. LiaFast.lf_pins LiaFast.u0. intros R L regs pc m b s k Q z Hz H. cbn. exists z. split; [exact Hz | exact H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_slow_wk : forall n s L regs pc m (Q : @wpost (option sptr * astate)) (P : @wpost (Z * astate)),
  1 <= n < MMAP_THRESHOLD ->
  (forall g, active_hd s (mw_sc s n) = Some g -> exists am, MT s g = Some (MUsed am) /\ am_avail am = 0) ->
  wk segs FORB HTOP rom L regs pc m (alloc_slot NEST_FUEL (mw_sc s n) n s) P ->
  (forall L' idx s1 R pc' m', P L' (idx, s1) R pc' m' -> wk segs FORB HTOP rom L' R pc' m' (k_slow (mw_sc s n) n (idx, s1)) Q) ->
  wk segs FORB HTOP rom L regs pc m (malloc n s) Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n s L regs pc m Q P Hn Hsl W K.
  unfold malloc. replace (size_overflows n) with false by (unfold size_overflows; symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
  replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold bind, get, ret. cbn [ibind]. fold (mw_sc s n).
  assert (K' : forall L' (a : Z * astate) R pc' m', P L' a R pc' m' -> wk segs FORB HTOP rom L' R pc' m' (k_slow (mw_sc s n) n a) Q).
  { intros L' [idx s1] R pc' m' HP. exact (K L' idx s1 R pc' m' HP). }
  clear K.
  destruct (nth (Z.to_nat (mw_sc s n)) (st_active s) None) as [g|] eqn:Eg.
  { destruct (Hsl g Eg) as (am & HMT & Hav). unfold getm, bind, get, ret. cbn [ibind]. unfold MT in HMT. rewrite HMT. cbn [ibind].
    rewrite Hav. cbn [Z.eqb ibind]. clear Hsl.
    apply wk_ibind. apply wk_ibind. eapply wk_mono; [|exact W].
    intros L' [idx s1] R pc' m' HP. pose proof (K' L' (idx, s1) R pc' m' HP) as W'. unfold k_slow in W'.
    destruct (idx <? 0) eqn:Ei.
    - cbn [ibind]. apply wk_ret. cbn in W' |- *. exact W'.
    - unfold get_head, bind, get, ret. cbn [ibind]. unfold active_hd in W'.
      destruct (nth (Z.to_nat (mw_sc s n)) (st_active s1) None) as [gm|]; [|exact I].
      cbn [ibind]. apply wk_ret. unfold ef_tail in W'. cbn [ibind]. exact W'. }
  cbn [ibind]. unfold bind. cbn [ibind].
  apply wk_ibind. apply wk_ibind. eapply wk_mono; [|exact W].
  intros L' [idx s1] R pc' m' HP. pose proof (K' L' (idx, s1) R pc' m' HP) as W'. unfold k_slow in W'.
  destruct (idx <? 0) eqn:Ei.
  - cbn [ibind]. apply wk_ret. cbn in W' |- *. exact W'.
  - unfold get_head, bind, get, ret. cbn [ibind]. unfold active_hd in W'.
    destruct (nth (Z.to_nat (mw_sc s n)) (st_active s1) None) as [gm|]; [|exact I].
    cbn [ibind]. apply wk_ret. unfold ef_tail in W'. cbn [ibind]. exact W'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma enframe_wk : forall {R : Type} L regs pc m g idx n ctr s am off0 (k : sptr * astate -> itree astate R) (Q : @wpost R)
    (QM : sptr * astate -> Prop),
  itok (enframe g idx n ctr FUser s) QM ->
  MT s g = Some (MUsed am) -> 0 <= idx <= am_last am -> 0 <= ef_slackm am n -> 0 <= off0 < 256 ->
  (forall h3 h16, ss_hdr (nth_slot am idx) = Some (h3, h16) -> ef_slackm am n <> 0 -> off0 = Z.land (if h3 =? 0 then ctr else h16 + 1) 255) ->
  (QM (ef_ptr am idx (ef_offm am n off0), set_meta s g (MUsed (ef_am am idx n (ef_offm am n off0)))) ->
   wk segs FORB HTOP rom L regs pc m (k (ef_ptr am idx (ef_offm am n off0), set_meta s g (MUsed (ef_am am idx n (ef_offm am n off0))))) Q) ->
  wk segs FORB HTOP rom L regs pc m (ibind (enframe g idx n ctr FUser s) k) Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R L regs pc m g idx n ctr s am off0 k Q QM OK HMT Hidx Sl0 Hoff0 Hhdr W.
  revert OK.
  unfold enframe, getm, bind, get, ret, mcheck. cbn [ibind]. unfold MT in HMT. rewrite HMT. cbn [ibind].
  replace ((0 <=? idx) && (idx <=? am_last am)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  cbn [ibind]. change ((stride_of am - IB - n) / UNIT) with (ef_slackm am n).
  destruct (ef_slackm am n =? 0) eqn:ES; [|destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:EH].
  - cbn [ibind]. rewrite ef_off_model. unfold massert. apply Z.eqb_eq in ES. rewrite ES.
    rewrite (ef_off_zero_slack 0) by lia. cbn -[set_metas mupdate enframe]. intros OK.
    replace (ef_offm am n off0) with 0 in W by (unfold ef_offm; rewrite ES; symmetry; apply ef_off_zero_slack; lia).
    unfold set_meta, ef_ptr, ef_am, ef_hdrm, ef_rsvm in W. exact (W OK).
  - apply Z.eqb_neq in ES. rewrite <- (Hhdr h3 h16 eq_refl ES). cbn [ibind]. rewrite ef_off_model. unfold massert.
    pose proof (ef_off_rng (ef_slackm am n) off0 Sl0 ltac:(lia)) as (OR1 & OR2).
    replace (ef_off (ef_slackm am n) off0 <=? ef_slackm am n) with true by (symmetry; apply Z.leb_le; lia).
    cbn -[set_metas mupdate]. intros OK.
    change (ef_off (ef_slackm am n) off0) with (ef_offm am n off0) in OK |- *.
    unfold set_meta, ef_ptr, ef_am, ef_hdrm, ef_rsvm in W. exact (W OK).
  - unfold askz. cbn [ibind]. intros OK. apply (wk_junk L regs pc m _ s _ Q off0 Hoff0).
    destruct OK as (_ & OK). specialize (OK off0 ltac:(cbn; lia)). revert OK.
    rewrite (Z.mod_small off0 256) by lia. cbn [ibind]. rewrite ef_off_model. unfold massert.
    pose proof (ef_off_rng (ef_slackm am n) off0 Sl0 ltac:(lia)) as (OR1 & OR2).
    replace (ef_off (ef_slackm am n) off0 <=? ef_slackm am n) with true by (symmetry; apply Z.leb_le; lia).
    cbn -[set_metas mupdate]. intros OK.
    change (ef_off (ef_slackm am n) off0) with (ef_offm am n off0) in OK |- *.
    unfold set_meta, ef_ptr, ef_am, ef_hdrm, ef_rsvm in W. exact (W OK).
Qed.
End WKJ.
