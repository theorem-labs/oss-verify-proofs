From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0q YO15 YO0u YO10.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import AllocSI AllocGS AllocCount.
Import ListNotations.
Local Open Scope Z_scope.

Lemma stride_nested am : am_maplen am = 0 -> stride_of am = class_size (am_sc am).
Proof. intros M. unfold stride_of. rewrite M. destruct (am_last am =? 0); reflexivity. Qed.

Lemma wpar_link s (HW : WF s) c ac g ag : wpar s c g -> usedX [] s c ac -> usedX [] s g ag ->
  am_maplen ac = 0 /\ 16 + class_size (am_sc ac) * (am_last ac + 1) <= stride_of ag /\
  am_sc ac < am_sc ag /\ am_sc ag < 48.
Proof.
  intros (ac' & i & Uc & M0 & H) Hc Hg. rewrite (usedX_fun _ _ _ _ _ Uc Hc) in M0, H.
  pose proof (inv_groups HW c ac Hc) as (_ & _ & _ & _ & _ & Gn).
  destruct (Gn M0) as (_ & g' & am' & i' & fr' & U' & Hi' & F' & K' & Mem & Sc & N63 & Fit).
  destruct (fgroup_frame [] None U0 s HW g' am' i' fr' U' Hi' F' K') as [Fn Off].
  pose proof (find_frame_in_spec [] None U0 s HW g' am' i' fr' U' Hi' F') as Hf.
  unfold frame_ptr in Hf. rewrite Off, Z.mul_0_r, ac_padd0, <- Mem, H in Hf.
  injection Hf as Eg _. subst g. rewrite (usedX_fun _ _ _ _ _ Hg U').
  destruct (sc_range s HW g' am' U') as [E|E]; [contradiction|].
  unfold UNIT, IB in *. split; [exact M0|]. split; [lia|]. split; [exact Sc|lia].
Qed.

Lemma depth_size s (HW : WF s) (HN : NL s) b n : forall g ag, witn s b n g -> usedX [] s g ag -> am_maplen ag = 0 ->
  16 * (2 ^ (Z.of_nat n + 1) - 1) <= class_size (am_sc ag).
Proof.
  induction n as [|n IH]; intros g ag W Ug M0.
  - pose proof (inv_groups HW g ag Ug) as (_ & _ & _ & _ & _ & Gn). destruct (Gn M0) as (N63 & _).
    destruct (sc_range s HW g ag Ug) as [E|E]; [contradiction|].
    pose proof (class_size_ge16 (am_sc ag) E). cbn. lia.
  - cbn [witn] in W. destruct W as (c & Wc & P).
    destruct (witn_used s HW b n c Wc) as (ac & Uc).
    destruct (wpar_link s HW c ac g ag P Uc Ug) as (Mc & Lk & _ & _).
    pose proof (IH c ac Wc Uc Mc) as Hc. pose proof (HN c ac Uc Mc) as Hl.
    rewrite (stride_nested ag M0) in Lk.
    replace (Z.of_nat (S n) + 1) with (Z.succ (Z.of_nat n + 1)) by lia.
    rewrite Z.pow_succ_r by lia.
    assert (Hm : 2 * class_size (am_sc ac) <= class_size (am_sc ac) * (am_last ac + 1)) by nia.
    lia.
Qed.

Theorem depth_bound : forall s b j g, WF s -> NL s -> witn s b j g -> (j <= 12)%nat.
Proof.
  intros s b j g HW HN W. destruct j as [|n]; [lia|].
  destruct (witn_used s HW b (S n) g W) as (ag & Ug).
  cbn [witn] in W. destruct W as (c & Wc & P).
  destruct (witn_used s HW b n c Wc) as (ac & Uc).
  destruct (wpar_link s HW c ac g ag P Uc Ug) as (Mc & _ & Sc & S48).
  pose proof (depth_size s HW HN b n c ac Wc Uc Mc) as Hs.
  assert (C0 : 0 <= am_sc ac) by (destruct (sc_range s HW c ac Uc); lia).
  pose proof (class_size_mono (am_sc ac) 46 C0 ltac:(lia) ltac:(lia)) as Hm.
  assert (E46 : class_size 46 = 104832) by reflexivity.
  destruct (Nat.le_gt_cases n 11) as [L|L]; [lia|exfalso].
  pose proof (Z.pow_le_mono_r 2 13 (Z.of_nat n + 1) ltac:(lia) ltac:(lia)) as Hp.
  change (2 ^ 13) with 8192 in Hp. lia.
Qed.

Definition mD (bl : list sptr) : list (Z * option sptr) :=
  map (fun c => (c, None)) (zseq 0 48) ++ flat_map (fun d => map (fun b => (d, Some b)) bl) (zseq 0 13).

Definition RD (s : astate) (g : sptr) (x : Z * option sptr) : Prop :=
  exists ag, usedX [] s g ag /\
  match snd x with None => frameless ag /\ am_sc ag = fst x | Some b => witn s b (Z.to_nat (fst x)) g end.

Theorem nused_bound_depth : forall s, WF s -> SI s -> NL s -> nused s <= 13 * nblocks s + 48.
Proof.
  intros s HW HS HN. unfold nused, nblocks.
  assert (L : (length (map fst (used_metas s)) <= length (mD (map fst (user_blocks s))))%nat).
  { apply (ac_count ac_kdec (RD s)).
    - apply NoDup_used_metas_keys. exact (proj1 (inv_keys HW)).
    - intros g Hg. apply in_map_iff in Hg as ([g' ag] & E & Hin). cbn [fst] in E. subst g'.
      apply (used_metas_usedX s g ag HW) in Hin.
      destruct (frameless_dec ag) as [FL | Hx].
      + pose proof HS as (_ & EO & _). destruct (EO g ag Hin FL (ac_unres g)) as [_ C].
        exists (am_sc ag, None). split.
        * unfold mD. apply in_app_iff. left. apply in_map_iff. exists (am_sc ag). split; [reflexivity | apply In_zseq; lia].
        * exists ag. split; [exact Hin|]. cbn [fst snd]. split; [exact FL|reflexivity].
      + destruct (wit_ex s HW HS g ag Hin Hx) as (b & n & Hb & W).
        pose proof (depth_bound s b n g HW HN W) as Hd.
        exists (Z.of_nat n, Some b). split.
        * unfold mD. apply in_app_iff. right. apply in_flat_map. exists (Z.of_nat n). split.
          -- apply In_zseq. lia.
          -- apply in_map_iff. exists b. split; [reflexivity | exact Hb].
        * exists ag. split; [exact Hin|]. cbn [fst snd]. rewrite Nat2Z.id. exact W.
    - intros g g' [d o] _ _ (a & U & H) (a' & U' & H').
      destruct o as [b|]; cbn [fst snd] in H, H'.
      + exact (witn_fun s b (Z.to_nat d) g g' H H').
      + destruct H as (FL & E), H' as (FL' & E'). pose proof HS as (_ & _ & EU & _).
        exact (EU g a g' a' U U' FL FL' (ac_unres g) (ac_unres g') ltac:(lia)). }
  unfold mD in L. rewrite length_map, length_app, length_map, flat_len, zseq48, length_map in L.
  assert (Z13 : length (zseq 0 13) = 13%nat) by reflexivity. rewrite Z13 in L. lia.
Qed.
