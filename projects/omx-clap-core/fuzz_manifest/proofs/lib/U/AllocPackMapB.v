From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO16 YL01 YK1j YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocMallocPath AllocFreePath AllocBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocPack AllocPackRoom AllocPackFree AllocReallocOK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocPackMalloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract AllocCut AllocForm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocPackGSF.
Import ListNotations.
Local Open Scope Z_scope.

(* map_bytes_pack (AllocPackRoom.v) with the weights of MAPB: the same injection from live mapped regions to the
   targets pk_tgt s nestF, where a small-class group of class c weighs GLEN c (GSF, PKS clause 3 and mapped_ok
   bound its mapped length) and a band-48 block of n bytes weighs 3 * PGSZ + n (GS clause 2). *)

Lemma mb_cs_nonneg c : 0 <= c < 48 -> 0 <= class_size c.
Proof.
  intros Hc. assert (T : forallb (fun c => 0 <=? class_size c) (zseq 0 48) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in T. specialize (T c (proj2 (In_zseq 0 48 c) ltac:(lia))). apply Z.leb_le in T. exact T.
Qed.

Lemma mb_GLEN_nonneg c : 0 <= c < 48 -> 0 <= GLEN c.
Proof.
  intros Hc. pose proof (mb_cs_nonneg c Hc) as Hcs. pose proof (FC_pos c Hc) as Hfc. unfold GLEN.
  assert (Hx : 0 <= class_size c * FC c + UNIT) by (unfold UNIT; nia).
  pose proof (page_round_ge (class_size c * FC c + UNIT)). lia.
Qed.

(* A mapped group of a small class maps at most GLEN of its class. *)
Lemma mb_glen s g ag : WF s -> GSF s -> PKS [] s -> usedX [] s g ag -> 0 < am_maplen ag -> 0 <= am_sc ag < 48 ->
  am_maplen ag * PGSZ <= GLEN (am_sc ag).
Proof.
  intros HW HF HP U Mpos Hsc.
  pose proof (inv_groups HW g ag U) as ((L0 & _) & _ & _ & _ & Gmp & _).
  destruct (Gmp Mpos) as (r & rg & _ & _ & _ & _ & _ & _ & B0).
  pose proof HP as (_ & _ & P3 & _). pose proof (P3 g ag U ltac:(lia)) as Hl.
  pose proof (mb_cs_nonneg (am_sc ag) Hsc) as Hcs. pose proof (FC_pos (am_sc ag) Hsc) as Hfc.
  unfold GLEN.
  destruct (Z.eq_dec (am_last ag) 0) as [E0|Ne].
  - eapply Z.le_trans; [exact (B0 E0 ltac:(lia))|]. apply page_round_mono. nia.
  - eapply Z.le_trans; [exact (HF g ag U Mpos ltac:(lia) ltac:(lia))|]. apply page_round_mono. nia.
Qed.

Definition mb_sw (s : astate) (g : sptr) : Z :=
  match MTX [] s g with Some (MUsed am) => GLEN (am_sc am) | _ => 0 end.

Definition mb_w (s : astate) (x : sptr * option Z) : Z :=
  match snd x with None => mb_sw s (fst x) | Some n => 3 * PGSZ + n end.

Lemma mb_sw_key s c f g : In g (pk_gkeys s f) -> (forall am, f am = true -> am_sc am = c) -> mb_sw s g = GLEN c.
Proof.
  intros Hg Hf. unfold pk_gkeys in Hg. apply filter_In in Hg as [_ Hg]. cbv beta in Hg. unfold mb_sw.
  destruct (MTX [] s g) as [[pr nx| |am]|]; try discriminate. rewrite (Hf am Hg). reflexivity.
Qed.

Lemma mb_gfull_sc c am : gfull c am = true -> am_sc am = c.
Proof. unfold gfull. intros H. apply andb_true_iff in H as [H _]. apply Z.eqb_eq. exact H. Qed.

Lemma mb_gred_sc c am : gred c am = true -> am_sc am = c.
Proof. unfold gred. intros H. apply andb_true_iff in H as [H _]. apply Z.eqb_eq. exact H. Qed.

Lemma mb_sw_cls s c g : In g (pk_gkeys s (gfull c) ++ pk_gkeys s (gred c)) -> mb_sw s g = GLEN c.
Proof.
  intros Hg. apply in_app_iff in Hg as [Hg|Hg].
  - exact (mb_sw_key s c (gfull c) g Hg (mb_gfull_sc c)).
  - exact (mb_sw_key s c (gred c) g Hg (mb_gred_sc c)).
Qed.

Lemma mb_sw_small s skip g : In g (pk_small s skip) -> exists c, 0 <= c < 48 /\ mb_sw s g = GLEN c.
Proof.
  unfold pk_small. intros Hg. apply in_flat_map in Hg as (c & Hc & Hg). apply In_zseq in Hc.
  destruct (skip c); [cbn in Hg; contradiction|]. exists c. split; [lia|]. exact (mb_sw_cls s c g Hg).
Qed.

Lemma mb_zsum_flat {A} (f : A -> Z) (h : Z -> list A) l : zsum f (flat_map h l) = zsumZ (fun c => zsum f (h c)) l.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [flat_map]. rewrite zsum_app, IH. reflexivity. Qed.

Lemma mb_zsum_const {A} (f : A -> Z) k l : (forall x, In x l -> f x = k) -> zsum f l = k * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; intros H; [rewrite zsum_nil; cbn [length Z.of_nat]; ring|].
  rewrite zsum_cons, (H x (or_introl eq_refl)), IH by (intros y Hy; apply H; right; exact Hy).
  cbn [length]. rewrite Nat2Z.inj_succ. unfold Z.succ. ring.
Qed.

Lemma mb_wsum s caps : PKC [] caps s ->
  zsum (mb_w s) (pk_tgt s nestF) <=
  zsumZ (fun c => if nestF c then 0 else (znth c (NF caps) + RED) * GLEN c) (zseq 0 48) +
  3 * PGSZ * bcount s 48 + zsum snd (pk_ub48 s).
Proof.
  intros HC. unfold pk_tgt. rewrite zsum_app.
  assert (A1 : forall l : list sptr, zsum (mb_w s) (map (fun g => (g, None)) l) = zsum (mb_sw s) l).
  { induction l as [|g l IH]; [reflexivity|]. cbn [map]. rewrite !zsum_cons, IH. reflexivity. }
  assert (A2 : forall l : list (sptr * Z),
    zsum (mb_w s) (map (fun b => (fst b, Some (snd b))) l) = 3 * PGSZ * Z.of_nat (length l) + zsum snd l).
  { induction l as [|b l IH]; cbn [map length]; [rewrite !zsum_nil; lia|].
    rewrite !zsum_cons, IH. unfold mb_w at 1. cbn [fst snd]. unfold PGSZ. lia. }
  rewrite A1, A2.
  assert (A3 : zsum (mb_sw s) (pk_small s nestF) <=
    zsumZ (fun c => if nestF c then 0 else (znth c (NF caps) + RED) * GLEN c) (zseq 0 48)).
  { unfold pk_small. rewrite mb_zsum_flat. apply zsumZ_le. intros c Hc. apply In_zseq in Hc. cbv beta.
    destruct (nestF c); cbv iota; [rewrite zsum_nil; lia|].
    rewrite (mb_zsum_const (mb_sw s) (GLEN c)) by (intros g Hg; exact (mb_sw_cls s c g Hg)).
    rewrite length_app, Nat2Z.inj_add. destruct (HC c ltac:(lia)) as [H1 H2].
    change (gcountX [] s (gfull c)) with (Z.of_nat (length (pk_gkeys s (gfull c)))) in H1.
    change (gcountX [] s (gred c)) with (Z.of_nat (length (pk_gkeys s (gred c)))) in H2.
    pose proof (mb_GLEN_nonneg c ltac:(lia)) as G. nia. }
  assert (Eb : bcount s 48 = Z.of_nat (length (pk_ub48 s))) by reflexivity.
  rewrite Eb. lia.
Qed.

Theorem map_bytes_cf : forall s caps L, WF s -> SI s -> GS s -> GSF s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  map_bytes s <= MAPB caps + ubytes s.
Proof.
  intros s caps L HW HS HG HF HP HC HU _ _ HB. unfold map_bytes. rewrite rsum_idx.
  match goal with |- zsum ?c ?l <= _ => assert (Hl : zsum c l <= zsum (mb_w s) (pk_tgt s nestF)) end.
  { apply (ac_wsum pk_tdec (pk_RR s)).
    - apply seq_NoDup.
    - intros x Hx. unfold pk_tgt in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_map_iff in Hx as (y & <- & Hy);
        unfold mb_w; cbn [fst snd].
      + destruct (mb_sw_small s nestF y Hy) as (c & Hc & ->). exact (mb_GLEN_nonneg c Hc).
      + unfold pk_ub48 in Hy. apply filter_In in Hy as [Hy _]. pose proof (ub_nonneg s HW y Hy). unfold PGSZ. lia.
    - intros k _. cbv beta.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; cbv beta iota; [|left; lia].
      unfold f_mapb. destruct (rg_live rg && is_map rg) eqn:E; cbv beta iota; [right|left; lia].
      apply andb_true_iff in E as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof (inv_groups HW g ag U) as (_ & _ & _ & _ & Gmp & _).
      destruct (Gmp Mpos) as (r & rg' & Em & Hr' & _ & _ & Len & _).
      rewrite Em in Pk. cbn in Pk. subst r. unfold region_of in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
      rewrite Len.
      pose proof HP as (_ & _ & _ & P4).
      destruct (pk_tgt_ex s nestF g ag HW HP U (fun Hc => P4 g ag U (proj2 Hc) Mpos)) as (x & Hx & Rx).
      exists x. split; [exact Hx|]. split; [exists g, ag; split; [exact U|]; split; [rewrite Em; reflexivity | exact Rx]|].
      destruct Rx as (a & Ua & Hm). rewrite (usedX_fun _ _ _ _ _ Ua U) in Hm.
      destruct (HG g ag U Mpos) as [_ G63].
      unfold mb_w. destruct x as [p [n|]]; cbn [fst snd] in Hm |- *.
      + destruct Hm as (E63 & _ & fr & F & ->). pose proof (G63 E63 fr F). unfold PGSZ in *. lia.
      + destruct Hm as (Ep & C). subst p. unfold mb_sw.
        assert (EM : MTX [] s g = Some (MUsed ag)) by exact U. rewrite EM.
        exact (mb_glen s g ag HW HF HP U Mpos C).
    - intros k k' x _ _ (g & a & U & Pk & R1) (g' & a' & U' & Pk' & R2).
      pose proof (pk_RT_inj s g g' x R1 R2) as <-. rewrite (usedX_fun _ _ _ _ _ U U') in Pk. congruence. }
  pose proof (mb_wsum s caps HC) as Hw.
  assert (Hsub : zsum snd (pk_ub48 s) <= ubytes s).
  { change (ubytes s) with (zsum snd (user_blocks s)). unfold pk_ub48. apply pk_zsum_filter.
    intros b Hb. exact (ub_nonneg s HW b Hb). }
  pose proof (pk_b48 s caps L HU HB) as Hb.
  unfold MAPB. unfold PGSZ in *. lia.
Qed.
