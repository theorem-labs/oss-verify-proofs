(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, program part: g_live is below alloc_ceiling. Lane BCrs of h-rw-pre-5.
   rule 24: proves no function (kind: segment lemma - a pure interval-sum fact and its ledger corollary).
   WHY: a caller that holds `live = fuzz_alloc_live ()` (= Ledger.lsum Lam) in s0 across a program call meets
   YCbqGcall.v aj_call_x's frame-chain premise `achain lyc rd (sp0 + o) (s0Z regs) ch1` (YCbq.v:218) only through its
   first arm, s0 < alloc_ceiling with the empty chain (check_reject_clean keeps live in s0 across fuzz_alloc_live).
   The texts state no bound on lsum Lam; this file derives it from the allocator relation's block law
   (AR_laws_x alx_blocks: each block in [4096, alloc_ceiling), the blocks pairwise disjoint) and the ledger
   (PRH_Base.v prh_ledger: each harness block (a, k) is the allocator block (a - cf_head, k + cf_head), the bases
   distinct). Generic: any listing (PAImg L), any ARx with its laws; no address.
   - iv_sum_le: pairwise disjoint intervals of positive length inside [lo, hi) have total length at most hi - lo
     (induction on the list, removing the interval with the largest start);
   - prh_lsum_lt_ceiling: 0 <= lsum Lam <= alloc_ceiling - 4096.
   Rule-24 search for the interval fact (2026-10-29, worktree + engine branch): S1Ledger.v prh_lsum_room bounds
   lsum Lam by blocks_bytes S, which is bounded only under ARcf's Wf (wf_live), not under a generic ARx; no
   disjoint-interval sum lemma found in lib/Reusable (YA09 sum_sizes is over sorted interval sets).
   Numerals: 4096 (LENGTH: the zero page, alx_blocks' lower bound). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Definition iv_sum (l : list (Z * Z)) : Z := fold_right (fun u s => snd u + s) 0 l.

Lemma iv_sum_app : forall l1 l2, iv_sum (l1 ++ l2) = iv_sum l1 + iv_sum l2.
Proof.
  intros l1 l2. induction l1 as [|u l1 IH].
  - unfold iv_sum. cbn [app fold_right]. first [reflexivity | lia].
  - cbn [app]. unfold iv_sum in *. cbn [fold_right]. rewrite IH. lia.
Qed.

Lemma iv_max : forall (l : list (Z * Z)), l <> [] -> exists m, In m l /\ forall v, In v l -> fst v <= fst m.
Proof.
  induction l as [|u l IH]; intros Hne; [congruence|].
  destruct l as [|w l].
  - exists u. split; [left; reflexivity|]. intros v [<-|[]]. lia.
  - destruct (IH ltac:(discriminate)) as (m & Hm & Hmax).
    destruct (Z_le_gt_dec (fst u) (fst m)) as [Hle|Hgt].
    + exists m. split; [right; exact Hm|]. intros v [<-|Hv]; [exact Hle | exact (Hmax v Hv)].
    + exists u. split; [left; reflexivity|]. intros v [<-|Hv]; [lia|]. specialize (Hmax v Hv). lia.
Qed.

(* positive-length intervals inside [lo, hi), any two distinct ones disjoint: total length <= hi - lo *)
Lemma iv_sum_le : forall n (l : list (Z * Z)) lo hi, length l = n -> lo <= hi -> List.NoDup l ->
  (forall u, In u l -> lo <= fst u /\ 0 < snd u /\ fst u + snd u <= hi) ->
  (forall u v, In u l -> In v l -> u <> v -> zdisjoint u v) ->
  iv_sum l <= hi - lo.
Proof.
  induction n as [|n IH]; intros l lo hi Hlen Hlh Hnd Hin Hdj.
  - destruct l; [cbn; lia | discriminate].
  - assert (Hne : l <> []) by (intros ->; discriminate Hlen).
    destruct (iv_max l Hne) as (m & Hm & Hmax).
    destruct (in_split m l Hm) as (l1 & l2 & E12).
    assert (Hnd' : List.NoDup (l1 ++ l2)) by (rewrite E12 in Hnd; exact (NoDup_remove_1 l1 l2 m Hnd)).
    assert (Hnm : ~ In m (l1 ++ l2)) by (rewrite E12 in Hnd; exact (NoDup_remove_2 l1 l2 m Hnd)).
    assert (Hsub : forall v, In v (l1 ++ l2) -> In v l /\ v <> m).
    { intros v Hv. split; [rewrite E12; apply in_app_or in Hv as [Hv|Hv]; apply in_or_app; [left|right; right]; exact Hv|].
      intros ->. exact (Hnm Hv). }
    destruct (Hin m Hm) as (Hm1 & Hm2 & Hm3).
    assert (Hrest : iv_sum (l1 ++ l2) <= fst m - lo).
    { apply (IH (l1 ++ l2) lo (fst m)).
      - rewrite E12, !length_app in Hlen. cbn [length] in Hlen. rewrite length_app. lia.
      - exact Hm1.
      - exact Hnd'.
      - intros v Hv. destruct (Hsub v Hv) as [Hvl Hvm]. destruct (Hin v Hvl) as (H1 & H2 & H3). split; [exact H1|].
        split; [exact H2|]. destruct (Hdj v m Hvl Hm Hvm) as [D|D]; [exact D|].
        specialize (Hmax v Hvl). unfold zdisjoint in D. lia.
      - intros u v Hu Hv Huv. exact (Hdj u v (proj1 (Hsub u Hu)) (proj1 (Hsub v Hv)) Huv). }
    rewrite E12, iv_sum_app. cbn [iv_sum fold_right]. rewrite iv_sum_app in Hrest. unfold iv_sum in *. lia.
Qed.

Lemma iv_pairwise_mem : forall (l : list (Z * Z)) u v, pairwise zdisjoint l -> In u l -> In v l -> u <> v ->
  zdisjoint u v.
Proof.
  induction l as [|w l IH]; intros u v Hp Hu Hv Huv; [destruct Hu|]. destruct Hp as [HF Hp].
  rewrite Forall_forall in HF.
  destruct Hu as [<-|Hu]; destruct Hv as [<-|Hv].
  - congruence.
  - exact (HF v Hv).
  - pose proof (HF u Hu) as D. unfold zdisjoint in *. lia.
  - exact (IH u v Hp Hu Hv Huv).
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

Definition prh_ivs (Lam : list (Z * Z)) : list (Z * Z) :=
  map (fun ak => (fst ak - cf_head, req_size (snd ak + cf_head))) Lam.

Lemma prh_ivs_sum : forall Lam, Forall (fun ak => 0 <= snd ak) Lam -> Ledger.lsum Lam <= iv_sum (prh_ivs Lam).
Proof.
  induction Lam as [|[a k] Lam IH]; intros HF.
  - apply Z.le_refl.
  - inversion HF as [|? ? Hk HF']; subst. specialize (IH HF'). cbn [snd] in Hk.
    change (k + Ledger.lsum Lam <= snd (a - cf_head, req_size (k + cf_head)) + iv_sum (prh_ivs Lam)).
    cbn [snd]. pose proof cf_head_nonneg as C.
    destruct (req_size_pos (k + cf_head) (Z.add_nonneg_nonneg _ _ Hk C)) as [R1 R2].
    clear -IH R2 C. lia.
Qed.

Lemma prh_ivs_nodup : forall Lam, List.NoDup (map fst Lam) -> List.NoDup (prh_ivs Lam).
Proof.
  induction Lam as [|[a k] Lam IH]; intros Hnd.
  - constructor.
  - change (List.NoDup ((a - cf_head, req_size (k + cf_head)) :: prh_ivs Lam)).
    change (List.NoDup (a :: map fst Lam)) in Hnd.
    inversion Hnd as [|? ? Hna Hnd']; subst. constructor; [|exact (IH Hnd')].
    intros Hin. apply Hna. unfold prh_ivs in Hin. apply in_map_iff in Hin as ([a' k'] & E & Hin'). cbn [fst snd] in E.
    injection E as E1 _. apply in_map_iff. exists (a', k'). split; [cbn [fst]; clear -E1; lia | exact Hin'].
Qed.

(* g_live is the sum of the harness blocks' user sizes, which lie in disjoint allocator blocks below alloc_ceiling *)
Lemma prh_lsum_lt_ceiling : forall ly S Hp W mem md Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  0 <= Ledger.lsum Lam <= alloc_ceiling - 4096.
Proof.
  intros ly S Hp W mem md Lam peak cnt fail ran most own HAR (_ & Hnd & HF & _).
  apply NoDup_ListNoDup in Hnd.
  rewrite Forall_forall in HF.
  assert (Hk : Forall (fun ak => 0 <= snd ak) Lam) by (apply Forall_forall; intros ak Hak; exact (proj1 (HF ak Hak))).
  assert (Hsum0 : 0 <= Ledger.lsum Lam).
  { clear -Hk. induction Lam as [|[a k] Lam IH].
    - apply Z.le_refl.
    - inversion Hk as [|? ? Hk1 Hk2]; subst. change (0 <= k + Ledger.lsum Lam). cbn [snd] in Hk1.
      specialize (IH Hk2). clear -IH Hk1. lia. }
  split; [exact Hsum0|].
  (* every interval is an allocator block's (base, req_size) *)
  assert (Hblk : forall u, In u (prh_ivs Lam) ->
    In u (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\
    4096 <= fst u /\ 0 < snd u /\ fst u + snd u <= alloc_ceiling).
  { intros u Hu. unfold prh_ivs in Hu. apply in_map_iff in Hu as ([a k] & <- & Hin).
    destruct (HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in *.
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
    pose proof cf_head_nonneg as C. destruct (req_size_pos (k + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 C)) as [R1 _].
    split; [apply in_map_iff; exists (a - cf_head, k + cf_head); split; [reflexivity | exact Hab]|]. cbn [fst snd].
    clear -H4096 R1 Hc. lia. }
  assert (C1 : 4096 <= alloc_ceiling)
    by exact (Z.le_trans _ _ _ (proj1 (Z.leb_le 4096 140735332483072) eq_refl) (proj1 (proj1 (@alloc_ceiling_val rc)))).
  assert (Hdj : forall u v, In u (prh_ivs Lam) -> In v (prh_ivs Lam) -> u <> v -> zdisjoint u v).
  { intros u v Hu Hv Huv. destruct (Hblk u Hu) as (Hu' & _). destruct (Hblk v Hv) as (Hv' & _).
    pose proof Hu' as Hu''. apply in_map_iff in Hu'' as ([p n] & _ & Hpn).
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md p n HAR Hpn) as (_ & _ & _ & _ & _ & Hpw).
    exact (iv_pairwise_mem _ u v Hpw Hu' Hv' Huv). }
  pose proof (iv_sum_le (length (prh_ivs Lam)) (prh_ivs Lam) 4096 alloc_ceiling eq_refl C1
    (prh_ivs_nodup Lam Hnd) (fun u Hu => proj2 (Hblk u Hu)) Hdj) as Hle.
  pose proof (prh_ivs_sum Lam Hk) as Hs. clear -Hle Hs. lia.
Qed.
End c.
