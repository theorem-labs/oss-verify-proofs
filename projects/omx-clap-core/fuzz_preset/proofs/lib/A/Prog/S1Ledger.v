(* fuzz_preset, S1 ALLOC-HEAP, image A (lib/A/Prog): the alloc.c LEDGER LEMMAS the four S1 walks (fuzz_malloc,
   fuzz_realloc, fuzz_free, fuzz_strdup) use to build each arm's post of the texts (lib/A/PRH_FnAlloc.v:
   prh_alloc_post, tfuzz_malloc_specX, tfuzz_realloc_specX, tfuzz_free_specX, tfuzz_strdup_specX) from what a walk
   holds at the return. Over the prh_glob / prh_hblock / prh_ledger (lib/A/PRH_Base.v), in the texts' Section
   context (fx rc cp PI, L PA, B). Preset-only: it names the texts' classes and the ledger; no address.
   Every lemma is generic in HOW the walk got its facts: a fact about the return state is a premise in the form a
   walk has it (a val_mem the symbolic memory gives, an mbyte / aview / mrestrict equality off a named set, the
   block-list change the allocator rule gives, the Hp change poison / unpoison give).
   Layers:
   1. bytes: aview / mrestrict equality -> mbyte equality; val_mem kept off a set; val_mem up to mod 2 ^ (8 n);
      the 8-byte little-endian head written by 8 `sb` (prh_val_mem_hdr8); g_ran_out (the 1-byte object at prh_img_A)
      after ONE `sb` of 1 (prh_val_mem_byte_set1; the 4-byte int form prh_val_mem_int01_set1 too).
   2. prh_glob: kept off prh_pst; rebuilt from the five final values (peak kept, or peak = max (peak, live')).
   3. prh_lblocks (the ledger without its statics: prh_ledger = prh_glob /\ prh_lblocks, prh_ledger_iff): frame to a
      new state, add a block (own), drop a block (disown), and the Hp / freshness / NoDup facts.
   4. the live bound (lsum Lam + n < 2 ^ 64) from the texts' premise blocks_bytes S + (n + cf_head) <= LIVE_MAX and
      ONE fact the texts do not carry: every allocator block size is >= 0, which preset's ARcf gives
      (amc_wf -> wfc_chunks -> chunk_ok_cf; prh_ablocks_nonneg_cf).
   5. the packaged ledger arms: prh_ledger_kept(_aview), prh_ledger_frame, prh_ledger_own, prh_ledger_disown,
      prh_ledger_reown, prh_ledger_move.
   cf_head is CfParams' field; no lemma here needs `cf_head = 16`: the head is read at a - cf_head and written at
   b = (b + cf_head) - cf_head, and the alignment is taken as the premise (b + cf_head) mod 16 = 0, which the texts'
   arms state of res = b + cf_head anyway. Only cf_head_nonneg (a CfParams field) is used.
   RULE-24 (the internal file BRIEF-COMMON.md): the released pieces this file restates over the ledger, by concept and shape:
   - preset plain lib/Prog/Ledger.v:127-148 ledger_frame (frame lemma: Lam's blocks kept + mbyte equal on the
     statics and the head words) -> prh_ledger_kept / prh_lblocks_kept;
   - preset plain lib/Prog/LedgerFacts.v:14 lsum_app, :17 lsum_nonneg, :28 ledger_sizes, :35-71 ledger_free (the
     disown shape: blocks b1 ++ x :: b2 -> b1 ++ b2, the rest of Lam kept) -> prh_lsum_app, prh_lsum_nonneg,
     prh_ledger_sizes, prh_lblocks_drop / prh_ledger_disown;
   - preset plain lib/Prog/MallocRuns.v:293-333 lam_room (freshness of the new block from the blocks' pairwise
     disjointness) -> prh_fresh_core / prh_fresh_malloc / prh_fresh_realloc; its room half is replaced by the
     blocks_bytes route (prh_lsum_room), which the texts' LIVE_MAX premise feeds;
   - released cgif_file_fuzzer (origin/ossv/recipes) lib/A/ACj3.v:55 val_mem_mod (same statement) ->
     prh_val_mem_mod; lib/A/AD1r.v:544 blocks_bytes_ablocks (same statement over its bsum) ->
     prh_blocks_bytes_ablocks; lib/A/ACjc.v:48 val_mem_frame (the frame_of form) -> prh_mbyte_of_mrestrict +
     prh_val_mem_keep;
   - core lib/Reusable/YCbq.v:177-199 (pairwise_app_l, pairwise_In2) for the pairwise style; YI04.v:145
     le_byte_small (cited, used).
   RULE-24 METHOD grep (the four released refs, 'proofs/*', 2026-10-28): no released ledger_own / ledger_disown /
   ledger_reown; ledger_free exists only in other units' allocator models (mosh / openssl AxGrant.v, nccl), over
   their own ledgers. None of the cited modules is Required (cgif's and preset-plain's contexts differ: cgif's lib/A
   image, preset plain's malloc_syms / layout); the pure list facts are re-proved here over YG0f's pairwise /
   zdisjoint and Ledger.lsum.
   NUMERALS: 8 and 4 are LENGTH (the C widths of size_t and int, the head word's width); 16 is DERIVED (the block
   alignment of the allocator law, as the texts state it); 2 ^ 64 and 256 are WORD (the machine word, a byte);
   0 and 1 are WORD (g_ran_out's two values). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure list facts (no machine state) ---- *)

Lemma prh_zdisjoint_sym : forall x y : Z * Z, zdisjoint x y -> zdisjoint y x.
Proof. intros x y H. unfold zdisjoint in *. lia. Qed.

Lemma prh_pw_last : forall {X} (R : X -> X -> Prop) (l : list X) (x : X),
  YG0f.pairwise R (l ++ [x]) -> forall y, In y l -> R y x.
Proof.
intros X R l x. induction l as [|z t IH]; cbn [app YG0f.pairwise]; intros H y Hy; [destruct Hy|].
destruct H as [Hf Hp]. destruct Hy as [<-|Hy].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. left. reflexivity.
- exact (IH Hp y Hy).
Qed.

Lemma prh_pw_perm : forall {X} (R : X -> X -> Prop) (l l' : list X), (forall x y, R x y -> R y x) ->
  Permutation l l' -> YG0f.pairwise R l -> YG0f.pairwise R l'.
Proof.
intros X R l l' Hs Hp. induction Hp as [|x l l' Hp IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [YG0f.pairwise]; intros H.
- exact I.
- destruct H as [Hf H]. split; [|exact (IH H)]. rewrite Forall_forall in Hf |- *. intros z Hz.
  apply Hf. exact (Permutation_in _ (Permutation_sym Hp) Hz).
- destruct H as [Hf1 [Hf2 H]]. rewrite Forall_forall in Hf1, Hf2. split; [|split; [|exact H]]; rewrite Forall_forall.
  + intros z [<-|Hz]; [apply Hs; apply Hf1; left; reflexivity | apply Hf2; exact Hz].
  + intros z Hz. apply Hf1. right. exact Hz.
- exact (IH2 (IH1 H)).
Qed.

Lemma prh_remove_notin : forall (x : Z) (l : list Z), ~ In x l -> remove Z.eq_dec x l = l.
Proof.
intros x l. induction l as [|y t IH]; intros H; [reflexivity|]. cbn [remove].
destruct (Z.eq_dec x y) as [E|E].
- exfalso. apply H. left. symmetry. exact E.
- f_equal. apply IH. intros Hx. apply H. right. exact Hx.
Qed.

Lemma prh_remove_app : forall (x : Z) (l1 l2 : list Z),
  remove Z.eq_dec x (l1 ++ l2) = remove Z.eq_dec x l1 ++ remove Z.eq_dec x l2.
Proof.
intros x l1. induction l1 as [|y t IH]; intros l2; [reflexivity|]. cbn [app remove].
destruct (Z.eq_dec x y); [exact (IH l2)|]. cbn [app]. f_equal. exact (IH l2).
Qed.

(* the head base leaves Hp entirely (Stdlib remove drops every copy) *)
Lemma prh_hp_remove_notin : forall (x : Z) (Hp : list Z), ~ In x (remove Z.eq_dec x Hp).
Proof.
intros x Hp. induction Hp as [|y t IH]; cbn [remove]; [intros []|].
destruct (Z.eq_dec x y) as [E|E]; [exact IH|]. intros [H|H]; [exact (E (eq_sym H)) | exact (IH H)].
Qed.

(* realloc SUCCESS removes the old base twice (the unpoison, then the realloc rule's Hp law): once is enough *)
Lemma prh_remove_idem : forall (x : Z) (l : list Z),
  remove Z.eq_dec x (remove Z.eq_dec x l) = remove Z.eq_dec x l.
Proof. intros x l. exact (prh_remove_notin x _ (prh_hp_remove_notin x l)). Qed.

Lemma prh_perm_remove : forall (x : Z) (l l' : list Z),
  Permutation l l' -> Permutation (remove Z.eq_dec x l) (remove Z.eq_dec x l').
Proof.
intros x l l' H. induction H as [|y l l' H IH|y z l|l l' l'' H1 IH1 H2 IH2].
- constructor.
- cbn [remove]. destruct (Z.eq_dec x y); [exact IH | apply perm_skip; exact IH].
- cbn [remove]. destruct (Z.eq_dec x y), (Z.eq_dec x z); cbn; first [apply Permutation_refl | apply perm_swap].
- exact (Permutation_trans IH1 IH2).
Qed.

(* NoDup below is the one in scope after LinuxProcessSemantics' imports (stdpp's, the one prh_ledger states);
   the proofs pass to Stdlib's List.NoDup by stdpp's NoDup_ListNoDup *)

(* realloc's refused arm re-hides the old head: (p - cf_head) :: remove (p - cf_head) Hp is Hp again *)
Lemma prh_perm_reown : forall (x : Z) (l : list Z), NoDup l -> In x l -> Permutation (x :: remove Z.eq_dec x l) l.
Proof.
intros x l HN Hx. apply NoDup_ListNoDup in HN. destruct (in_split x l Hx) as (l1 & l2 & ->).
pose proof (NoDup_remove_2 _ _ _ HN) as Hn.
rewrite prh_remove_app. cbn [remove]. destruct (Z.eq_dec x x) as [_|E]; [|exfalso; exact (E eq_refl)].
rewrite !prh_remove_notin by (intros H; apply Hn; apply in_or_app; first [left; exact H | right; exact H]).
apply Permutation_middle.
Qed.

Lemma prh_fst_unique : forall (l : list (Z * Z)) a x y, NoDup (map fst l) -> In (a, x) l -> In (a, y) l -> x = y.
Proof.
intros l. induction l as [|[b z] t IH]; intros a x y HN Hx Hy; [destruct Hx|].
apply NoDup_ListNoDup in HN. cbn [map fst] in HN. apply NoDup_cons_iff in HN as [Hn HN].
apply NoDup_ListNoDup in HN.
destruct Hx as [Ex|Hx], Hy as [Ey|Hy].
- congruence.
- exfalso. apply Hn. apply in_map_iff. exists (a, y). split; [cbn; congruence | exact Hy].
- exfalso. apply Hn. apply in_map_iff. exists (a, x). split; [cbn; congruence | exact Hx].
- exact (IH a x y HN Hx Hy).
Qed.

Lemma prh_lam_rest_notin : forall (l1 l2 : list (Z * Z)) p k,
  NoDup (map fst (l1 ++ (p, k) :: l2)) -> ~ In p (map fst (l1 ++ l2)).
Proof.
intros l1 l2 p k H. apply NoDup_ListNoDup in H. rewrite map_app in H |- *. cbn [map fst] in H.
exact (NoDup_remove_2 _ _ _ H).
Qed.

Lemma prh_lam_rest_nodup : forall (l1 l2 : list (Z * Z)) p k,
  NoDup (map fst (l1 ++ (p, k) :: l2)) -> NoDup (map fst (l1 ++ l2)).
Proof.
intros l1 l2 p k H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
rewrite map_app in H |- *. cbn [map fst] in H. exact (NoDup_remove_1 _ _ _ H).
Qed.

Lemma prh_nodup_shift : forall (c : Z) (Lam : list (Z * Z)),
  NoDup (map fst Lam) -> NoDup (map (fun ak => fst ak - c) Lam).
Proof.
intros c Lam. induction Lam as [|[a k] t IH]; cbn [map fst]; intros H; apply NoDup_ListNoDup; [constructor|].
apply NoDup_ListNoDup in H. apply NoDup_cons_iff in H as [Hn H]. constructor.
- intros Hin. apply in_map_iff in Hin as ([a' k'] & E & Hin). cbn [fst] in E.
  apply Hn. apply in_map_iff. exists (a', k'). split; [cbn; lia | exact Hin].
- apply NoDup_ListNoDup. apply IH. apply NoDup_ListNoDup. exact H.
Qed.

Lemma prh_nodup_blocks : forall (c : Z) (Lam : list (Z * Z)),
  NoDup (map fst Lam) -> NoDup (map (fun ak => (fst ak - c, snd ak + c)) Lam).
Proof.
intros c Lam. induction Lam as [|[a k] t IH]; cbn [map fst snd]; intros H; apply NoDup_ListNoDup; [constructor|].
apply NoDup_ListNoDup in H. apply NoDup_cons_iff in H as [Hn H]. constructor.
- intros Hin. apply in_map_iff in Hin as ([a' k'] & E & Hin). cbn [fst snd] in E. injection E as E1 E2.
  apply Hn. apply in_map_iff. exists (a', k'). split; [cbn; lia | exact Hin].
- apply NoDup_ListNoDup. apply IH. apply NoDup_ListNoDup. exact H.
Qed.

Lemma prh_in_split_other : forall (bl bl' b1 b2 : list (Z * Z)) (x y : Z * Z),
  bl = b1 ++ x :: b2 -> incl (b1 ++ b2) bl' -> y <> x -> In y bl -> In y bl'.
Proof.
intros bl bl' b1 b2 x y E Hi Hne Hy. subst bl. apply Hi. apply in_app_or in Hy. apply in_or_app.
destruct Hy as [Hy|[Hy|Hy]]; [left; exact Hy | exfalso; exact (Hne (eq_sym Hy)) | right; exact Hy].
Qed.

Lemma prh_incl_perm_cons : forall (L l : list (Z * Z)) (x : Z * Z), Permutation L (x :: l) -> incl l L.
Proof. intros L l x H y Hy. apply (Permutation_in _ (Permutation_sym H)). right. exact Hy. Qed.

(* the plain lsum facts (LedgerFacts.v:14, :17), over the Ledger.lsum *)
Lemma prh_lsum_app : forall l1 l2, Ledger.lsum (l1 ++ l2) = Ledger.lsum l1 + Ledger.lsum l2.
Proof. intros l1. induction l1 as [|[a k] l1 IH]; intros l2; cbn [app Ledger.lsum]; [reflexivity | rewrite IH; lia]. Qed.

Lemma prh_lsum_split : forall l1 l2 p k, Ledger.lsum (l1 ++ (p, k) :: l2) = Ledger.lsum (l1 ++ l2) + k.
Proof. intros l1 l2 p k. rewrite !prh_lsum_app. cbn [Ledger.lsum]. lia. Qed.

Lemma prh_lsum_nonneg : forall Lam, Forall (fun ak => 0 <= snd ak) Lam -> 0 <= Ledger.lsum Lam.
Proof.
intros Lam H. induction H as [|[a k] t Hk _ IH]; cbn [Ledger.lsum]; [lia|]. cbn [snd] in Hk. lia.
Qed.

Lemma prh_lsum_perm : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof.
intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [Ledger.lsum]; lia.
Qed.

(* the sum of the sizes of a block list *)
Fixpoint prh_bsum (l : list (Z * Z)) : Z :=
  match l with [] => 0 | x :: t => snd x + prh_bsum t end.

Lemma prh_bsum_app : forall l1 l2, prh_bsum (l1 ++ l2) = prh_bsum l1 + prh_bsum l2.
Proof. intros l1. induction l1 as [|x t IH]; intros l2; cbn [app prh_bsum]; [reflexivity | rewrite IH; lia]. Qed.

Lemma prh_bsum_nonneg : forall l, Forall (fun b => 0 <= snd b) l -> 0 <= prh_bsum l.
Proof. intros l H. induction H as [|x t Hx _ IH]; cbn [prh_bsum]; [lia|]. cbv beta in Hx. lia. Qed.

(* distinct members of a list of nonnegative sizes sum to at most the list's sum *)
Lemma prh_bsum_sub : forall l L, NoDup l -> incl l L -> Forall (fun b => 0 <= snd b) L -> prh_bsum l <= prh_bsum L.
Proof.
intros l. induction l as [|x t IH]; intros L HN Hi HF; cbn [prh_bsum].
- exact (prh_bsum_nonneg L HF).
- apply NoDup_ListNoDup in HN. apply NoDup_cons_iff in HN as [Hx HN]. apply NoDup_ListNoDup in HN.
  destruct (in_split x L (Hi x (or_introl eq_refl))) as (L1 & L2 & E). subst L.
  rewrite Forall_forall in HF.
  assert (Ht : incl t (L1 ++ L2)).
  { intros y Hy. assert (Hy2 : In y (L1 ++ x :: L2)) by (apply Hi; right; exact Hy).
    apply in_app_or in Hy2. apply in_or_app. destruct Hy2 as [H|[H|H]].
    - left; exact H.
    - subst y. contradiction.
    - right; exact H. }
  assert (HF' : Forall (fun b => 0 <= snd b) (L1 ++ L2)).
  { rewrite Forall_forall. intros y Hy. apply HF. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [H|H]; [left; exact H | right; right; exact H]. }
  pose proof (IH (L1 ++ L2) HN Ht HF') as HI.
  assert (H0 : 0 <= snd x) by (apply HF; apply in_or_app; right; left; reflexivity).
  rewrite prh_bsum_app in HI |- *. cbn [prh_bsum]. lia.
Qed.

Lemma prh_bsum_shift : forall (c : Z) (Lam : list (Z * Z)),
  prh_bsum (map (fun ak => (fst ak - c, snd ak + c)) Lam) = Ledger.lsum Lam + c * Z.of_nat (length Lam).
Proof.
intros c Lam. induction Lam as [|[a k] t IH]; cbn [map prh_bsum Ledger.lsum length fst snd]; [lia|].
rewrite IH. lia.
Qed.

Lemma prh_req_size_pos : forall x, 0 <= x -> 0 < req_size x.
Proof. intros x Hx. unfold req_size. destruct (x =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.

(* ==== 1. bytes ==== *)

(* the journal's form (ajournal_x clauses, aview equality) gives the byte the ledger reads *)
Lemma prh_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a. unfold aview.
destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
cbn [option_map]; intros E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* the runner's form (frame_of / ajournal_x_pst_write: mrestrict equality off a write set Wr) *)
Lemma prh_mbyte_of_mrestrict : forall (Wr : Z -> Prop) (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict H' m' x = mrestrict H m x) ->
  0 <= a < 2 ^ 64 -> ~ Wr a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
intros Wr H H' m m' a Hf Ha Hw. unfold mbyte.
assert (E : bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64) by (rewrite Z_to_bv_unsigned; reflexivity).
rewrite (Hf (Z_to_bv 64 a)); [reflexivity|]. rewrite E, Z.mod_small by exact Ha. exact Hw.
Qed.

Lemma prh_val_mem_keep : forall (m m' : word -> option byte) (a : Z) (n : nat) (v : Z),
  val_mem segs m a n v ->
  (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m' a n v.
Proof. intros m m' a n v Hv He k Hk. rewrite (He k Hk). exact (Hv k Hk). Qed.

(* a stored value is read up to the word: (cnt + 1) mod 2 ^ 64 and cnt + 1 give the same 8 bytes *)
Lemma prh_val_mem_mod : forall (m : word -> option byte) (a : Z) (n : nat) (v : Z),
  val_mem segs m a n (v mod 2 ^ (8 * Z.of_nat n)) <-> val_mem segs m a n v.
Proof.
intros m a n v. unfold val_mem.
assert (Hz : 2 ^ (8 * Z.of_nat n) <> 0) by (apply Z.pow_nonzero; lia).
split; intros H k Hk; rewrite (H k Hk); do 2 f_equal.
- change ((Z.shiftr ((v mod 2 ^ (8 * Z.of_nat n)) mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) mod 256 =
          (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) mod 256).
  rewrite Z.mod_mod by exact Hz. reflexivity.
- change ((Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) mod 256 =
          (Z.shiftr ((v mod 2 ^ (8 * Z.of_nat n)) mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) mod 256).
  rewrite Z.mod_mod by exact Hz. reflexivity.
Qed.

(* n bytes written one by one, byte k being v >> 8k (the `srli` / `sb` pairs), are v little endian *)
Lemma prh_val_mem_le_bytes : forall (m : word -> option byte) (a : Z) (n : nat) (v : Z),
  0 <= v < 2 ^ (8 * Z.of_nat n) ->
  (forall k, (k < n)%nat -> mbyte segs m (a + Z.of_nat k) = Some (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)))) ->
  val_mem segs m a n v.
Proof. intros m a n v Hv H k Hk. rewrite (le_byte_small v n k Hv Hk). exact (H k Hk). Qed.

(* the harness head: the 8 `sb` of n's bytes at the block base b (own, inlined in image A's fuzz_malloc and twice in
   fuzz_realloc: the new block, and the old block again on the refused arm) *)
Lemma prh_val_mem_hdr8 : forall (m : word -> option byte) (b v : Z),
  0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> mbyte segs m (b + Z.of_nat k) = Some (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)))) ->
  val_mem segs m b 8 v.
Proof. intros m b v Hv H. apply prh_val_mem_le_bytes; [exact Hv | exact H]. Qed.

(* g_ran_out after ONE `sb` of 1 into a 4-byte int whose old value is 0 or 1: bytes 1-3 stay 0 (the width a Theorem Labs lane read
   before the generated pi_gz_ran_out; kept until PresetS1 says to delete it) *)
Lemma prh_val_mem_int01_set1 : forall (m m' : word -> option byte) (a ran : Z),
  val_mem segs m a 4 ran -> (ran = 0 \/ ran = 1) ->
  mbyte segs m' a = Some (Z_to_bv 8 1) ->
  (forall k, (1 <= k < 4)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m' a 4 1.
Proof.
intros m m' a ran Hv Hr H0 H13 k Hk.
assert (Hr4 : 0 <= ran < 2 ^ (8 * Z.of_nat 4)) by (cbn; lia).
assert (H14 : 0 <= 1 < 2 ^ (8 * Z.of_nat 4)) by (cbn; lia).
rewrite (le_byte_small 1 4 k H14 Hk).
destruct k as [|k].
- cbn [Z.of_nat]. rewrite Z.add_0_r, H0. reflexivity.
- rewrite (H13 (S k) ltac:(lia)), (Hv (S k) Hk), (le_byte_small ran 4 (S k) Hr4 Hk).
  do 2 f_equal. destruct Hr as [-> | ->]; destruct k as [|[|[|k]]]; try lia; reflexivity.
Qed.

(* g_ran_out as the 1-byte object it is (asan_globals size 1; `lbu` / `sb`): ONE `sb` of 1 *)
Lemma prh_val_mem_byte_set1 : forall (m m' : word -> option byte) (a ran : Z),
  val_mem segs m a 1 ran -> (ran = 0 \/ ran = 1) ->
  mbyte segs m' a = Some (Z_to_bv 8 1) ->
  val_mem segs m' a 1 1.
Proof.
intros m m' a ran _ _ H0 k Hk.
assert (H11 : 0 <= 1 < 2 ^ (8 * Z.of_nat 1)) by (cbn; lia).
rewrite (le_byte_small 1 1 k H11 Hk).
assert (Ek : k = 0%nat) by lia. subst k.
cbn [Z.of_nat]. rewrite Z.add_0_r, H0. reflexivity.
Qed.

(* ==== 2. the statics (prh_glob) ==== *)

(* each static is read at its GENERATED width (PrhImg's pi_gz_*, from the image's asan_globals descriptors; at
   prh_img_A: 8, 8, 8, 8 and 1 for g_ran_out, which LLVM shrank to one byte), as the prh_glob / prh_pst read it *)

Lemma prh_pst_live : forall k, (k < pi_gz_live)%nat -> Exists (in_zr (pi_g_live + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma prh_pst_peak : forall k, (k < pi_gz_peak)%nat -> Exists (in_zr (pi_g_peak + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma prh_pst_count : forall k, (k < pi_gz_count)%nat -> Exists (in_zr (pi_g_count + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. do 2 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma prh_pst_fail : forall k, (k < pi_gz_fail)%nat -> Exists (in_zr (pi_g_fail + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma prh_pst_ran : forall k, (k < pi_gz_ran_out)%nat -> Exists (in_zr (pi_g_ran_out + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma prh_pst_most : forall k, (k < pi_gz_most)%nat -> Exists (in_zr (pi_g_most + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma prh_pst_own : forall k, (k < pi_gz_own_ran_out)%nat -> Exists (in_zr (pi_g_own_ran_out + Z.of_nat k)) prh_pst.
Proof. intros k Hk. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.

(* nothing the statics hold changed (a callee whose journal keeps the image, e.g. __asan_memcpy after fuzz_malloc) *)
Lemma prh_glob_kept : forall W mem W' mem' live peak cnt fail ran most own,
  prh_glob W mem live peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst ->
     mbyte segs (mrestrict (w_H W') mem') a = mbyte segs (mrestrict (w_H W) mem) a) ->
  prh_glob W' mem' live peak cnt fail ran most own.
Proof.
intros W mem W' mem' live peak cnt fail ran most own (H1 & H2 & H3 & H4 & H5 & (H6 & M) & (H7 & O) & R) He.
unfold prh_glob, prh_most, prh_own.
split; [apply (prh_val_mem_keep _ _ _ _ _ H1); intros k Hk; apply He, prh_pst_live, Hk|].
split; [apply (prh_val_mem_keep _ _ _ _ _ H2); intros k Hk; apply He, prh_pst_peak, Hk|].
split; [apply (prh_val_mem_keep _ _ _ _ _ H3); intros k Hk; apply He, prh_pst_count, Hk|].
split; [apply (prh_val_mem_keep _ _ _ _ _ H4); intros k Hk; apply He, prh_pst_fail, Hk|].
split; [apply (prh_val_mem_keep _ _ _ _ _ H5); intros k Hk; apply He, prh_pst_ran, Hk|].
split; [split; [apply (prh_val_mem_keep _ _ _ _ _ H6); intros k Hk; apply He, prh_pst_most, Hk | exact M]|].
split; [split; [apply (prh_val_mem_keep _ _ _ _ _ H7); intros k Hk; apply He, prh_pst_own, Hk | exact O]|].
exact R.
Qed.

(* the five final values, g_peak NOT raised (live' <= peak): CHOSEN-FAIL (live' = live, g_count + 1,
   g_fail_at = SIZE_MAX), REFUSED (g_ran_out = 1 by prh_val_mem_byte_set1 at width 1), fuzz_free (live' = live - n),
   realloc REFUSED (live' = live); g_most and g_own_ran_out are the entry's (these steps write neither) *)
Lemma prh_glob_final_le : forall W mem W' mem' live peak cnt fail ran live' cnt' fail' ran' most own,
  prh_glob W mem live peak cnt fail ran most own ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_live pi_gz_live live' -> 0 <= live' <= peak ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_peak pi_gz_peak peak ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_count pi_gz_count cnt' -> 0 <= cnt' < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_fail pi_gz_fail fail' -> 0 <= fail' < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_ran_out pi_gz_ran_out ran' -> (ran' = 0 \/ ran' = 1) ->
  prh_most W' mem' most -> prh_own W' mem' own ->
  prh_glob W' mem' live' peak cnt' fail' ran' most own.
Proof.
intros W mem W' mem' live peak cnt fail ran live' cnt' fail' ran' most own (_ & _ & _ & _ & _ & _ & _ & Hlp & Hpk & _)
  Hl Hl' Hp Hc Hc' Hf Hf' Hr Hr' (Hm & Hm') (Ho & Ho').
unfold prh_glob, prh_most, prh_own. repeat split; try assumption; lia.
Qed.

(* the five final values, g_peak = max (g_peak, g_live') (own's `bgeu` on g_peak): own after fuzz_malloc's and
   fuzz_realloc's successful allocation; g_most and g_own_ran_out are the entry's (these steps write neither) *)
Lemma prh_glob_final : forall W mem W' mem' live peak cnt fail ran live' cnt' fail' ran' most own,
  prh_glob W mem live peak cnt fail ran most own ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_live pi_gz_live live' -> 0 <= live' < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_peak pi_gz_peak (Z.max peak live') ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_count pi_gz_count cnt' -> 0 <= cnt' < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_fail pi_gz_fail fail' -> 0 <= fail' < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W') mem') pi_g_ran_out pi_gz_ran_out ran' -> (ran' = 0 \/ ran' = 1) ->
  prh_most W' mem' most -> prh_own W' mem' own ->
  prh_glob W' mem' live' (Z.max peak live') cnt' fail' ran' most own.
Proof.
intros W mem W' mem' live peak cnt fail ran live' cnt' fail' ran' most own (_ & _ & _ & _ & _ & _ & _ & Hlp & Hpk & _)
  Hl Hl' Hp Hc Hc' Hf Hf' Hr Hr' (Hm & Hm') (Ho & Ho').
unfold prh_glob, prh_most, prh_own. repeat split; try assumption; lia.
Qed.

(* ==== 3. the ledger's blocks (prh_ledger without its statics) ==== *)

Definition prh_lblocks (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
  (Lam : list (Z * Z)) : Prop :=
  NoDup (map fst Lam) /\ Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam /\
  Permutation Hp (map (fun ak => fst ak - cf_head) Lam).

Lemma prh_ledger_iff : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own <->
  prh_glob W mem (Ledger.lsum Lam) peak cnt fail ran most own /\ prh_lblocks ly S Hp W mem Lam.
Proof. intros. unfold prh_ledger, prh_lblocks. reflexivity. Qed.

Lemma prh_lblocks_sizes : forall ly S Hp W mem Lam,
  prh_lblocks ly S Hp W mem Lam -> Forall (fun ak => 0 <= snd ak) Lam.
Proof.
intros ly S Hp W mem Lam (_ & HF & _). eapply Forall_impl; [|exact HF].
intros [a k] H. unfold prh_hblock in H. exact (proj1 H).
Qed.

Lemma prh_ledger_sizes : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Forall (fun ak => 0 <= snd ak) Lam.
Proof. intros ly S Hp W mem Lam peak cnt fail ran most own HL. apply prh_ledger_iff in HL as [_ HB]. exact (prh_lblocks_sizes _ _ _ _ _ _ HB). Qed.

(* what the ledger says of one member (fuzz_free / fuzz_realloc: the block, the hidden base, the head value, the
   alignment of p) *)
Lemma prh_ledger_hblock : forall ly S Hp W mem Lam peak cnt fail ran a k most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam -> prh_hblock B ly S Hp W mem a k.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin. apply prh_ledger_iff in HL as [_ (_ & HF & _)].
rewrite Forall_forall in HF. exact (HF (a, k) Hin).
Qed.

(* the g_live values the stores leave (`sub` then `add`, each mod 2 ^ 64): fuzz_free's live - k and fuzz_realloc's
   (live - k) + n are exact when in range *)
Lemma prh_live_sub : forall live k, 0 <= k <= live -> live < 2 ^ 64 -> (live - k) mod 2 ^ 64 = live - k.
Proof. intros live k Hk Hl. apply Z.mod_small. lia. Qed.

Lemma prh_live_sub_add : forall live k n, 0 <= k <= live -> 0 <= n -> live - k + n < 2 ^ 64 ->
  ((live - k) mod 2 ^ 64 + n) mod 2 ^ 64 = live - k + n.
Proof. intros live k n Hk Hn Hl. rewrite (Z.mod_small (live - k)) by lia. apply Z.mod_small. lia. Qed.

Lemma prh_lblocks_hp_nodup : forall ly S Hp W mem Lam, prh_lblocks ly S Hp W mem Lam -> NoDup Hp.
Proof.
intros ly S Hp W mem Lam (HN & _ & HP).
apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_sym HP)). apply NoDup_ListNoDup.
exact (prh_nodup_shift cf_head Lam HN).
Qed.

(* FRAME, heads given as values at the new state *)
Lemma prh_lblocks_frame_vm : forall ly S Hp W mem ly' S' Hp' W' mem' Lam,
  prh_lblocks ly S Hp W mem Lam ->
  (forall a k, In (a, k) Lam -> val_mem segs (mrestrict (w_H W') mem') (a - cf_head) 8 k) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_lblocks ly' S' Hp' W' mem' Lam.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam (HN & HF & HP) Hv Hb Hpp.
split; [exact HN|]. split; [|exact (Permutation_trans Hpp HP)].
rewrite Forall_forall in HF |- *. intros [a k] Hin. specialize (HF _ Hin).
unfold prh_hblock in HF |- *. cbn [fst snd] in HF |- *.
destruct HF as (Hk & Hbl & Hh & Hal & _).
split; [exact Hk|]. split; [exact (Hb a k Hin Hbl)|].
split; [exact (Permutation_in _ (Permutation_sym Hpp) Hh)|].
split; [exact Hal | exact (Hv a k Hin)].
Qed.

(* FRAME, heads unchanged byte by byte *)
Lemma prh_lblocks_kept : forall ly S Hp W mem ly' S' Hp' W' mem' Lam,
  prh_lblocks ly S Hp W mem Lam ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_lblocks ly' S' Hp' W' mem' Lam.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam HL Hh Hb Hpp.
apply (prh_lblocks_frame_vm ly S Hp W mem); [exact HL | | exact Hb | exact Hpp].
intros a k Hin. destruct HL as (_ & HF & _). rewrite Forall_forall in HF.
specialize (HF _ Hin). unfold prh_hblock in HF. cbn [fst snd] in HF. destruct HF as (_ & _ & _ & _ & Hv).
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros j Hj. apply (Hh a k (Z.of_nat j) Hin). lia.
Qed.

(* OWN (alloc.c own :45-53) at one state: the block (b, n + cf_head), its head holding n, hidden (Hp gains b) *)
Lemma prh_lblocks_add : forall ly S Hp W mem Lam b n,
  prh_lblocks ly S Hp W mem Lam ->
  0 <= n -> In (b, n + cf_head) (ablocks B ly S) -> (b + cf_head) mod 16 = 0 ->
  val_mem segs (mrestrict (w_H W) mem) b 8 n ->
  ~ In (b + cf_head) (map fst Lam) ->
  prh_lblocks ly S (b :: Hp) W mem ((b + cf_head, n) :: Lam).
Proof.
intros ly S Hp W mem Lam b n (HN & HF & HP) Hn Hbl Hal Hv Hfr.
assert (Eb : b + cf_head - cf_head = b) by lia.
split; [cbn [map fst]; apply NoDup_ListNoDup; constructor; [exact Hfr | apply NoDup_ListNoDup; exact HN]|].
split.
- constructor.
  + unfold prh_hblock. cbn [fst snd]. rewrite Eb.
    split; [exact Hn|]. split; [exact Hbl|]. split; [left; reflexivity|]. split; [exact Hal | exact Hv].
  + eapply Forall_impl; [|exact HF]. intros [a k] H. unfold prh_hblock in H |- *. cbn [fst snd] in H |- *.
    destruct H as (H1 & H2 & H3 & H4 & H5).
    split; [exact H1|]. split; [exact H2|]. split; [right; exact H3|]. split; [exact H4 | exact H5].
- cbn [map fst]. rewrite Eb. apply perm_skip. exact HP.
Qed.

(* DISOWN (fuzz_free :118-127, the unpoison) at one state: (p, k) leaves Lam, p - cf_head leaves Hp *)
Lemma prh_lblocks_drop : forall ly S Hp W mem l1 l2 p k,
  prh_lblocks ly S Hp W mem (l1 ++ (p, k) :: l2) ->
  prh_lblocks ly S (remove Z.eq_dec (p - cf_head) Hp) W mem (l1 ++ l2).
Proof.
intros ly S Hp W mem l1 l2 p k (HN & HF & HP).
pose proof (prh_lam_rest_notin l1 l2 p k HN) as Hpn.
split; [exact (prh_lam_rest_nodup l1 l2 p k HN)|].
split.
- rewrite Forall_forall in HF |- *. intros [a ka] Hin.
  assert (Hin0 : In (a, ka) (l1 ++ (p, k) :: l2)).
  { apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
  assert (Hne : a <> p).
  { intros ->. apply Hpn. apply in_map_iff. exists (p, ka). split; [reflexivity | exact Hin]. }
  specialize (HF _ Hin0). unfold prh_hblock in HF |- *. cbn [fst snd] in HF |- *.
  destruct HF as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [apply in_in_remove; [lia | exact H3]|]. split; [exact H4 | exact H5].
- assert (Hpc : ~ In (p - cf_head) (map (fun ak => fst ak - cf_head) (l1 ++ l2))).
  { intros H. apply in_map_iff in H as ([a ka] & E & Hin). cbn [fst] in E. apply Hpn. apply in_map_iff.
    exists (a, ka). split; [cbn; lia | exact Hin]. }
  rewrite map_app in Hpc.
  apply (Permutation_trans (prh_perm_remove _ _ _ HP)). rewrite !map_app, prh_remove_app. cbn [map fst remove].
  destruct (Z.eq_dec (p - cf_head) (p - cf_head)) as [_|E]; [|exfalso; exact (E eq_refl)].
  rewrite !prh_remove_notin by (intros H; apply Hpc; apply in_or_app; first [left; exact H | right; exact H]).
  apply Permutation_refl.
Qed.

(* the block lists the allocator rule gives keep Lam's other blocks *)
Lemma prh_blocks_kept_app : forall ly S ly' S' (l : list (Z * Z)) (x : Z * Z),
  ablocks B ly' S' = ablocks B ly S ++ l -> In x (ablocks B ly S) -> In x (ablocks B ly' S').
Proof. intros ly S ly' S' l x E H. rewrite E. apply in_or_app. left. exact H. Qed.

Lemma prh_blocks_kept_free : forall ly S ly' S' (b1 b2 : list (Z * Z)) p k a ka,
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 -> incl (b1 ++ b2) (ablocks B ly' S') -> a <> p ->
  In (a - cf_head, ka + cf_head) (ablocks B ly S) -> In (a - cf_head, ka + cf_head) (ablocks B ly' S').
Proof.
intros ly S ly' S' b1 b2 p k a ka E Hi Hne H.
apply (prh_in_split_other _ _ b1 b2 (p - cf_head, k + cf_head) _ E Hi); [|exact H].
intros Ex. injection Ex as E1 E2. lia.
Qed.

(* the realloc rule's success block list (YGcallRx aj_realloc_x: ablocks' = b1 ++ b2 ++ [new]) keeps Lam's other
   blocks *)
Lemma prh_blocks_kept_realloc : forall ly S ly' S' (b1 b2 : list (Z * Z)) p k x a ka,
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 -> ablocks B ly' S' = b1 ++ b2 ++ [x] -> a <> p ->
  In (a - cf_head, ka + cf_head) (ablocks B ly S) -> In (a - cf_head, ka + cf_head) (ablocks B ly' S').
Proof.
intros ly S ly' S' b1 b2 p k x a ka E E' Hne H.
apply (prh_blocks_kept_free ly S ly' S' b1 b2 p k a ka E); [|exact Hne | exact H].
rewrite E', app_assoc. apply incl_appl, incl_refl.
Qed.

(* Hp facts: the new base is not hidden; realloc REFUSED's re-hidden Hp is a permutation of Hp *)
Lemma prh_hp_fresh : forall ly S Hp W mem Lam b,
  prh_lblocks ly S Hp W mem Lam -> ~ In (b + cf_head) (map fst Lam) -> ~ In b Hp.
Proof.
intros ly S Hp W mem Lam b (_ & _ & HP) Hfr Hb. apply (Permutation_in _ HP) in Hb.
apply in_map_iff in Hb as ([a k] & E & Hin). cbn [fst] in E. apply Hfr. apply in_map_iff.
exists (a, k). split; [cbn; lia | exact Hin].
Qed.

Lemma prh_hp_reown_perm : forall ly S Hp W mem Lam p k,
  prh_lblocks ly S Hp W mem Lam -> In (p, k) Lam ->
  Permutation ((p - cf_head) :: remove Z.eq_dec (p - cf_head) Hp) Hp.
Proof.
intros ly S Hp W mem Lam p k HL Hin. apply prh_perm_reown; [exact (prh_lblocks_hp_nodup _ _ _ _ _ _ HL)|].
destruct HL as (_ & HF & _). rewrite Forall_forall in HF. specialize (HF _ Hin). unfold prh_hblock in HF.
cbn [fst snd] in HF. exact (proj1 (proj2 (proj2 HF))).
Qed.

(* FRESHNESS (plain MallocRuns.v:293 lam_room's second half): a block disjoint from every block of Lam is not the
   allocator block of a member of Lam *)
Lemma prh_fresh_core : forall (Lam : list (Z * Z)) b m, 0 < m ->
  (forall a k, In (a, k) Lam -> 0 <= k /\ zdisjoint (b, m) (a - cf_head, req_size (k + cf_head))) ->
  ~ In (b + cf_head) (map fst Lam).
Proof.
intros Lam b m Hm H Hin. apply in_map_iff in Hin as ([a k] & Ea & Hin). cbn [fst] in Ea. subst a.
destruct (H _ _ Hin) as (Hk & Hd). pose proof cf_head_nonneg as C.
assert (Hr : 0 < req_size (k + cf_head)) by (apply prh_req_size_pos; lia).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* malloc success: ablocks' = ablocks ++ [(b, n + cf_head)], pairwise disjoint (ARx_blocks_law at the post state) *)
Lemma prh_fresh_malloc : forall ly S Hp W mem ly' S' Lam b n,
  prh_lblocks ly S Hp W mem Lam -> 0 <= n ->
  ablocks B ly' S' = ablocks B ly S ++ [(b, n + cf_head)] ->
  YG0f.pairwise zdisjoint (map (fun x => (fst x, req_size (snd x))) (ablocks B ly' S')) ->
  ~ In (b + cf_head) (map fst Lam).
Proof.
intros ly S Hp W mem ly' S' Lam b n (_ & HF & _) Hn E Hpw.
rewrite E, map_app in Hpw. cbn [map fst snd] in Hpw.
pose proof cf_head_nonneg as C.
apply (prh_fresh_core Lam b (req_size (n + cf_head))); [apply prh_req_size_pos; lia|].
intros a k Hin. rewrite Forall_forall in HF. specialize (HF _ Hin). unfold prh_hblock in HF. cbn [fst snd] in HF.
destruct HF as (Hk & Hbl & _). split; [exact Hk|].
assert (Hy : In (a - cf_head, req_size (k + cf_head)) (map (fun x => (fst x, req_size (snd x))) (ablocks B ly S))).
{ apply in_map_iff. exists (a - cf_head, k + cf_head). split; [reflexivity | exact Hbl]. }
exact (prh_zdisjoint_sym _ _ (prh_pw_last _ _ _ Hpw _ Hy)).
Qed.

(* realloc success: ablocks' a permutation of (q, n + cf_head) :: b1 ++ b2, the old block (p - cf_head, k + cf_head)
   gone from ablocks = b1 ++ old :: b2 *)
Lemma prh_fresh_realloc : forall ly S Hp W mem ly' S' l1 l2 p k q n b1 b2,
  prh_lblocks ly S Hp W mem (l1 ++ (p, k) :: l2) -> 0 <= n ->
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 ->
  Permutation (ablocks B ly' S') ((q, n + cf_head) :: b1 ++ b2) ->
  YG0f.pairwise zdisjoint (map (fun x => (fst x, req_size (snd x))) (ablocks B ly' S')) ->
  ~ In (q + cf_head) (map fst (l1 ++ l2)).
Proof.
intros ly S Hp W mem ly' S' l1 l2 p k q n b1 b2 (HN & HF & _) Hn Eb Hperm Hpw.
pose proof (prh_lam_rest_notin l1 l2 p k HN) as Hpn.
apply (prh_pw_perm _ _ _ prh_zdisjoint_sym (Permutation_map (fun x => (fst x, req_size (snd x))) Hperm)) in Hpw.
cbn [map YG0f.pairwise fst snd] in Hpw. destruct Hpw as [Hf _].
pose proof cf_head_nonneg as C.
apply (prh_fresh_core (l1 ++ l2) q (req_size (n + cf_head))); [apply prh_req_size_pos; lia|].
intros a ka Hin.
assert (Hin0 : In (a, ka) (l1 ++ (p, k) :: l2)).
{ apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|H]; [left; exact H | right; right; exact H]. }
rewrite Forall_forall in HF. specialize (HF _ Hin0). unfold prh_hblock in HF. cbn [fst snd] in HF.
destruct HF as (Hk & Hbl & _). split; [exact Hk|].
assert (Hne : a <> p).
{ intros ->. apply Hpn. apply in_map_iff. exists (p, ka). split; [reflexivity | exact Hin]. }
assert (Hbl' : In (a - cf_head, ka + cf_head) (b1 ++ b2)).
{ rewrite Eb in Hbl. apply in_app_or in Hbl. apply in_or_app.
  destruct Hbl as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H]. }
rewrite Forall_forall in Hf. apply Hf. apply in_map_iff. exists (a - cf_head, ka + cf_head).
split; [reflexivity | exact Hbl'].
Qed.

(* the same at the realloc rule's success form ablocks' = b1 ++ b2 ++ [(q, n + cf_head)] *)
Lemma prh_fresh_realloc_app : forall ly S Hp W mem ly' S' l1 l2 p k q n b1 b2,
  prh_lblocks ly S Hp W mem (l1 ++ (p, k) :: l2) -> 0 <= n ->
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 ->
  ablocks B ly' S' = b1 ++ b2 ++ [(q, n + cf_head)] ->
  YG0f.pairwise zdisjoint (map (fun x => (fst x, req_size (snd x))) (ablocks B ly' S')) ->
  ~ In (q + cf_head) (map fst (l1 ++ l2)).
Proof.
intros ly S Hp W mem ly' S' l1 l2 p k q n b1 b2 HL Hn Eb E' Hpw.
apply (prh_fresh_realloc ly S Hp W mem ly' S' l1 l2 p k q n b1 b2 HL Hn Eb); [|exact Hpw].
rewrite E', app_assoc. apply Permutation_sym, Permutation_cons_append.
Qed.

(* ==== 4. the live bound ==== *)

Lemma prh_blocks_bytes_ablocks : forall ly S, blocks_bytes S = prh_bsum (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, YG01.blocks.
induction (st_chunks S) as [|k t IH]; [reflexivity|].
cbn [List.filter fold_right]. destruct (is_alloc k); cbn [map prh_bsum fst snd]; [rewrite IH; reflexivity | exact IH].
Qed.

(* Lam's allocator blocks are distinct members of ablocks; with every size >= 0 they fit in blocks_bytes *)
Lemma prh_lsum_room : forall ly S Hp W mem Lam,
  prh_lblocks ly S Hp W mem Lam -> Forall (fun b => 0 <= snd b) (ablocks B ly S) ->
  Ledger.lsum Lam + cf_head * Z.of_nat (length Lam) <= blocks_bytes S.
Proof.
intros ly S Hp W mem Lam (HN & HF & _) Hnn.
rewrite (prh_blocks_bytes_ablocks ly S), <- (prh_bsum_shift cf_head Lam).
apply prh_bsum_sub; [exact (prh_nodup_blocks cf_head Lam HN) | | exact Hnn].
intros x Hx. apply in_map_iff in Hx as ([a k] & <- & Hin). rewrite Forall_forall in HF. specialize (HF _ Hin).
unfold prh_hblock in HF. cbn [fst snd] in HF |- *. exact (proj1 (proj2 HF)).
Qed.

(* the bound that keeps g_live exact (town_specX's `Ledger.lsum Lam + n < 2 ^ 64`), from the texts' premise
   blocks_bytes S + (n + cf_head) <= LIVE_MAX at the entry state; the size fact is prh_ablocks_nonneg_cf at ARcf *)
Lemma prh_live_room : forall ly S Hp W mem Lam peak cnt fail ran n most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  Forall (fun b => 0 <= snd b) (ablocks B ly S) ->
  blocks_bytes S + (n + cf_head) <= LIVE_MAX ->
  Ledger.lsum Lam + n + cf_head <= LIVE_MAX /\ Ledger.lsum Lam + n < 2 ^ 64.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran n most own HL Hnn Hroom. apply prh_ledger_iff in HL as [_ HB].
pose proof (prh_lsum_room ly S Hp W mem Lam HB Hnn) as R. pose proof cf_head_nonneg as C.
assert (0 <= cf_head * Z.of_nat (length Lam)) by (apply Z.mul_nonneg_nonneg; lia).
unfold LIVE_MAX in *. split; lia.
Qed.

Section cf. Context {ci : CfImg}.
(* the size fact at preset's allocator relation ARcf (YG0ncf.v:242): amc_wf -> Wf_cf -> wfc_chunks -> chunk_ok_cf's
   0 <= ck_req *)
Lemma prh_ablocks_nonneg_cf : forall ly S Hp W mem md,
  ARcf segs B ly S Hp W mem md -> Forall (fun b => 0 <= snd b) (ablocks B ly S).
Proof.
intros ly S Hp W mem md (M & _).
pose proof (wfc_chunks _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as HC.
unfold ablocks, YG01.blocks. rewrite Forall_forall in HC |- *. intros x Hx.
apply in_map_iff in Hx as (y & <- & Hy). apply in_map_iff in Hy as (k & <- & Hk).
apply filter_In in Hk as [Hk _]. cbn [snd]. exact (proj1 (proj1 (HC k Hk))).
Qed.
End cf.

(* ==== 5. the ledger arms ==== *)

(* KEPT: statics and Lam's heads unchanged (a callee's journal, e.g. __asan_memcpy in fuzz_strdup) *)
Lemma prh_ledger_kept : forall ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst ->
     mbyte segs (mrestrict (w_H W') mem') a = mbyte segs (mrestrict (w_H W) mem) a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own HL Hs Hh Hb Hpp.
apply prh_ledger_iff in HL as [HG HB]. apply prh_ledger_iff. split.
- exact (prh_glob_kept _ _ _ _ _ _ _ _ _ _ _ HG Hs).
- exact (prh_lblocks_kept _ _ _ _ _ _ _ _ _ _ _ HB Hh Hb Hpp).
Qed.

Lemma prh_ledger_kept_aview : forall ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     aview segs (w_H W') mem' (a - cf_head + i) = aview segs (w_H W) mem (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own HL Hs Hh Hb Hpp.
apply (prh_ledger_kept ly S Hp W mem); [exact HL | | | exact Hb | exact Hpp].
- intros a Ha. apply prh_mbyte_of_aview. exact (Hs a Ha).
- intros a k i Hin Hi. apply prh_mbyte_of_aview. exact (Hh a k i Hin Hi).
Qed.

(* FRAME with new statics: CHOSEN-FAIL (malloc / realloc) and REFUSED (malloc) arms, Lam and Hp unchanged *)
Lemma prh_ledger_frame : forall ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran peak' cnt' fail' ran' most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_glob W' mem' (Ledger.lsum Lam) peak' cnt' fail' ran' most own ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak' cnt' fail' ran' most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran peak' cnt' fail' ran' most own HL HG' Hh Hb Hpp.
apply prh_ledger_iff in HL as [_ HB]. apply prh_ledger_iff. split; [exact HG'|].
exact (prh_lblocks_kept _ _ _ _ _ _ _ _ _ _ _ HB Hh Hb Hpp).
Qed.

(* OWN: fuzz_malloc's SUCCESS arm (Hp' = b :: Hp, ablocks' gains (b, n + cf_head), res = b + cf_head) *)
Lemma prh_ledger_own : forall ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran peak' cnt' fail' ran' b n most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_glob W' mem' (Ledger.lsum Lam + n) peak' cnt' fail' ran' most own ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  0 <= n -> In (b, n + cf_head) (ablocks B ly' S') -> (b + cf_head) mod 16 = 0 ->
  val_mem segs (mrestrict (w_H W') mem') b 8 n ->
  ~ In (b + cf_head) (map fst Lam) ->
  Hp' = b :: Hp ->
  prh_ledger B ly' S' Hp' W' mem' ((b + cf_head, n) :: Lam) peak' cnt' fail' ran' most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran peak' cnt' fail' ran' b n most own
  HL HG' Hh Hb Hn Hbl Hal Hv Hfr EHp.
subst Hp'. apply prh_ledger_iff in HL as [_ HB]. apply prh_ledger_iff. split.
- cbn [Ledger.lsum]. rewrite Z.add_comm. exact HG'.
- apply prh_lblocks_add; try assumption.
  apply (prh_lblocks_kept ly S Hp W mem); [exact HB | exact Hh | exact Hb | apply Permutation_refl].
Qed.

(* DISOWN: fuzz_free's p <> 0 arm (Hp' = remove (p - cf_head) Hp; Lam' = l1 ++ l2) *)
Lemma prh_ledger_disown : forall ly S Hp W mem ly' S' Hp' W' mem' l1 l2 p k peak cnt fail ran peak' cnt' fail' ran' most own,
  prh_ledger B ly S Hp W mem (l1 ++ (p, k) :: l2) peak cnt fail ran most own ->
  prh_glob W' mem' (Ledger.lsum (l1 ++ l2)) peak' cnt' fail' ran' most own ->
  (forall a ka i, In (a, ka) (l1 ++ l2) -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a ka, In (a, ka) (l1 ++ l2) -> In (a - cf_head, ka + cf_head) (ablocks B ly S) ->
     In (a - cf_head, ka + cf_head) (ablocks B ly' S')) ->
  Hp' = remove Z.eq_dec (p - cf_head) Hp ->
  prh_ledger B ly' S' Hp' W' mem' (l1 ++ l2) peak' cnt' fail' ran' most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' l1 l2 p k peak cnt fail ran peak' cnt' fail' ran' most own HL HG' Hh Hb EHp.
subst Hp'. apply prh_ledger_iff in HL as [_ HB]. apply prh_ledger_iff. split; [exact HG'|].
apply (prh_lblocks_kept ly S (remove Z.eq_dec (p - cf_head) Hp) W mem); [| exact Hh | exact Hb | apply Permutation_refl].
exact (prh_lblocks_drop _ _ _ _ _ _ _ _ _ HB).
Qed.

(* REOWN: fuzz_realloc's REFUSED arm (unpoison, realloc NULL, the old head rewritten with k and hidden again:
   Hp' = (p - cf_head) :: remove (p - cf_head) Hp, a permutation of Hp; Lam unchanged) *)
Lemma prh_ledger_reown : forall ly S Hp W mem ly' S' Hp' W' mem' Lam p k peak cnt fail ran peak' cnt' fail' ran' most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (p, k) Lam ->
  prh_glob W' mem' (Ledger.lsum Lam) peak' cnt' fail' ran' most own ->
  (forall a ka i, In (a, ka) Lam -> a <> p -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  val_mem segs (mrestrict (w_H W') mem') (p - cf_head) 8 k ->
  (forall a ka, In (a, ka) Lam -> In (a - cf_head, ka + cf_head) (ablocks B ly S) ->
     In (a - cf_head, ka + cf_head) (ablocks B ly' S')) ->
  Hp' = (p - cf_head) :: remove Z.eq_dec (p - cf_head) Hp ->
  Permutation Hp' Hp /\ prh_ledger B ly' S' Hp' W' mem' Lam peak' cnt' fail' ran' most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam p k peak cnt fail ran peak' cnt' fail' ran' most own HL Hin HG' Hh Hv Hb EHp.
apply prh_ledger_iff in HL as [_ HB].
assert (Hperm : Permutation Hp' Hp) by (subst Hp'; exact (prh_hp_reown_perm _ _ _ _ _ _ _ _ HB Hin)).
split; [exact Hperm|]. apply prh_ledger_iff. split; [exact HG'|].
apply (prh_lblocks_frame_vm ly S Hp W mem); [exact HB | | exact Hb | exact Hperm].
intros a ka Hin'. destruct (Z.eq_dec a p) as [->|Hne].
- assert (Ek : ka = k) by (destruct HB as (HN & _ & _); exact (prh_fst_unique Lam p ka k HN Hin' Hin)).
  rewrite Ek. exact Hv.
- destruct HB as (_ & HF & _). rewrite Forall_forall in HF. specialize (HF _ Hin'). unfold prh_hblock in HF.
  cbn [fst snd] in HF. destruct HF as (_ & _ & _ & _ & Hv0).
  apply (prh_val_mem_keep _ _ _ _ _ Hv0). intros j Hj. apply (Hh a ka (Z.of_nat j) Hin' Hne). lia.
Qed.

(* MOVE: fuzz_realloc's SUCCESS arm (disown (p, k), own the new block (q, n + cf_head), res = q + cf_head,
   Hp' = q :: remove (p - cf_head) Hp, Lam' = (q + cf_head, n) :: l1 ++ l2) *)
Lemma prh_ledger_move : forall ly S Hp W mem ly' S' Hp' W' mem' l1 l2 p k q n peak cnt fail ran peak' cnt' fail' ran' most own,
  prh_ledger B ly S Hp W mem (l1 ++ (p, k) :: l2) peak cnt fail ran most own ->
  prh_glob W' mem' (Ledger.lsum (l1 ++ l2) + n) peak' cnt' fail' ran' most own ->
  (forall a ka i, In (a, ka) (l1 ++ l2) -> 0 <= i < 8 ->
     mbyte segs (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte segs (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a ka, In (a, ka) (l1 ++ l2) -> In (a - cf_head, ka + cf_head) (ablocks B ly S) ->
     In (a - cf_head, ka + cf_head) (ablocks B ly' S')) ->
  0 <= n -> In (q, n + cf_head) (ablocks B ly' S') -> (q + cf_head) mod 16 = 0 ->
  val_mem segs (mrestrict (w_H W') mem') q 8 n ->
  ~ In (q + cf_head) (map fst (l1 ++ l2)) ->
  Hp' = q :: remove Z.eq_dec (p - cf_head) Hp ->
  prh_ledger B ly' S' Hp' W' mem' ((q + cf_head, n) :: l1 ++ l2) peak' cnt' fail' ran' most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' l1 l2 p k q n peak cnt fail ran peak' cnt' fail' ran' most own
  HL HG' Hh Hb Hn Hbl Hal Hv Hfr EHp.
subst Hp'. apply prh_ledger_iff in HL as [_ HB]. apply prh_ledger_iff. split.
- cbn [Ledger.lsum]. rewrite Z.add_comm. exact HG'.
- apply prh_lblocks_add; try assumption.
  apply (prh_lblocks_kept ly S (remove Z.eq_dec (p - cf_head) Hp) W mem); [| exact Hh | exact Hb | apply Permutation_refl].
  exact (prh_lblocks_drop _ _ _ _ _ _ _ _ _ HB).
Qed.

End c.
