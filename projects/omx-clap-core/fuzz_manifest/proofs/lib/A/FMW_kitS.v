(* Shared walk kit, strings part (G5; the rest of the kit is lib/A/FMW_kit.v, G6): a C string a caller keeps across a
   program call. cstr_ok_kept carries cstr_ok and its block home over the callee's ajournal; cstr_kept_kept carries the
   home in both arms. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP09 YI04 YI00 YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the rule's answer is 0 or 1 *)
Lemma scan_01 : forall t u fuel i d, ManifestModel.scan t u i d fuel = 0 \/ ManifestModel.scan t u i d fuel = 1.
Proof.
intros t u fuel. induction fuel as [|f IH]; intros i d; cbn [ManifestModel.scan]; [left; reflexivity|].
destruct (length t <=? i)%nat; [left; reflexivity|].
destruct (ManifestModel.decl t i) as [| |name nl ns nl2 close]; [apply IH | left; reflexivity |].
destruct (ManifestModel.matches t u ns nl2); [|apply IH].
destruct (16 <? S d)%nat; [right; reflexivity|].
destruct (ManifestModel.token _ _ _); [right; reflexivity | apply IH].
Qed.
Lemma names_01 : forall t u, ManifestModel.names t u = 0 \/ ManifestModel.names t u = 1.
Proof.
intros t u. unfold ManifestModel.names. destruct (length u =? 0)%nat; [left; reflexivity|].
destruct (ManifestModel.whole t u); [right; reflexivity | apply scan_01].
Qed.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma shadow_hull_vis_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.
(* the 8-byte word end is monotone *)
Lemma word_end_mono : forall x y, x <= y -> x - x mod 8 + 8 <= y - y mod 8 + 8.
Proof.
intros x y H. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a string in a live block: cstr_ok carried over a journal that keeps the block and leaves the string's bytes out of
   its footprint *)
Lemma cstr_ok_kept_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (shadow_hull_vis_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (block_word_tail_vis B LAWS ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

(* a suffix of a C string is a C string with the same NUL *)
Lemma cstr_ok_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
split; [split|].
- rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (garr8_app tfibsegs) in Hg as [_ Hg].
  rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
- rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [intros x Hx; apply Hra; lia|].
  split; [apply (shadow_hull_vis_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
  intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.

(* a C string the caller keeps (FMH_Fn.v cstr_kept) after a program call: the block arm by cstr_ok_kept_blk (a footprint
   of image bytes, as FM_PSTAT_FP, misses every block), the read-only arms (suffixes of fm's listed strings) by
   fm_img_facts at the new state *)
Lemma cstr_ok_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l,
  fm_img_facts tfibsegs B ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  (forall a, inFP FP a -> in_img tfibsegs a) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem') ->
  cstr_kept B ly S p l -> cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l IMG HJ Hinc HFP HRO' Hk Hc.
pose proof HJ as (HAR' & _).
destruct Hk as [(b & m & Hin & Hb & Hbm) | (p0 & l0 & kk & Hsrc & Hkl & -> & ->)].
- apply (cstr_ok_kept_blk STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin (Hinc _ Hin) Hb Hbm); [|exact Hc].
  intros a Ha Hf. apply (blk_img tfibsegs B LAWS ly' S' W' mem' md' b m a HAR' (Hinc _ Hin)); [|exact (HFP a Hf)].
  assert (req_size m = m) as -> by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- apply (cstr_ok_suffix W' mem' p0 l0 kk Hkl).
  destruct Hsrc as [Hro | (ps & Hf & ->)].
  + destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & HS & _).
    exact (proj1 (proj1 (Forall_forall _ _) HS (p0, l0) Hro)).
  + destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & _ & HF). exact (proj1 (HF p0 ps Hf)).
Qed.

(* the home itself: the block arm through a kept block, the read-only arms are constant *)
Lemma cstr_kept_kept : forall ly S ly' S' p l,
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  cstr_kept B ly S p l -> cstr_kept B ly' S' p l.
Proof.
intros ly S ly' S' p l Hinc [(b & m & Hin & H1 & H2) | Himg].
- left. exists b, m. split; [exact (Hinc _ Hin) | split; assumption].
- right. exact Himg.
Qed.

(* fm's statics footprint is image bytes *)
Lemma pstat_img : forall a, inFP FM_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) && (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs) FM_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply existsb_exists in H as (s & Hs & Hss).
apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
Lemma nil_img : forall a, inFP [] a -> in_img tfibsegs a.
Proof. intros a Ha. exfalso. exact (inFP_nil a Ha). Qed.
(* a reader call with no allocation set to fail answers the rule and counts its one allocation (FMH_Fn.v names_res) *)
Lemma names_res_quiet : forall (W : world tfibsegs) mem tb ub live peak cnt fail res,
  names_res tfibsegs tb ub live peak cnt fail res W mem -> quiet cnt fail 1 ->
  res = ManifestModel.names tb ub /\
  fm_glob tfibsegs W mem live (rt_peak ub live peak) (if (length ub =? 0)%nat then cnt else cnt + 1) SIZE_MAXZ.
Proof.
intros W mem tb ub live peak cnt fail res HN (Hf & Hc0 & Hc1).
destruct HN as [(-> & -> & HG) | [(_ & Hcf & _) | (Hne & _ & -> & HG)]].
- split; [reflexivity|]. rewrite Hf in HG. exact HG.
- exfalso. rewrite Hf in Hcf. unfold SIZE_MAXZ in Hcf. lia.
- split; [reflexivity|]. rewrite Hf in HG. destruct ub as [|c ub']; [exfalso; exact (Hne eq_refl)|]. exact HG.
Qed.
(* a reader call whose one allocation is set to fail (fail = cnt): it fails, holds nothing, counts the allocation and
   g_fail_at goes back to SIZE_MAX; without a URI nothing happens *)
Lemma names_res_starved : forall (W : world tfibsegs) mem tb ub live peak cnt res,
  names_res tfibsegs tb ub live peak cnt cnt res W mem ->
  fm_glob tfibsegs W mem live peak (if (length ub =? 0)%nat then cnt else cnt + 1)
    (if (length ub =? 0)%nat then cnt else SIZE_MAXZ).
Proof.
intros W mem tb ub live peak cnt res HN.
destruct HN as [(-> & _ & HG) | [(Hne & _ & _ & HG) | (_ & Hne & _)]].
- exact HG.
- destruct ub as [|c ub']; [exfalso; exact (Hne eq_refl)|]. exact HG.
- exfalso. exact (Hne eq_refl).
Qed.
End s.
