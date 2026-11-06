(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfLeafWiden.v, sha256 907e6e3fcd92cacdddbbf32477c7599e50a4bc8b4bc2d1da9c3252fbe213e602 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree (lane W's AllocG / DeallocG / DMspec / DMiface / ImgBaseDG / DGif0, the F1 core's
   YGcfRehidePost / YGcfRecStep, and the per-image cf files of this carry) name lib/B; a sentence is split at a directory
   change, the module order kept.
*)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WalkB2; integrator ReallocPrimary). A cf-layer file (image-free, over segs and B).
   rule 24: no function proved (a lemma about the malloc leaf; no walk).

   The unit premise YGcfMallocCompose.malloc_leaf_widen_cf, proved ONCE for every image. The text is fuzz_preset's
   lib/A/WrapMallocABodyUnit.v (a Theorem Labs lane, commit ff8885d4e860, blob d1d839b2df97): bu_apresent_hi,
   bu_blocks_below, bu_xs_below and malloc_leaf_widen_A, made generic. Only the names changed (bu_ -> lw_,
   tfibsegs -> segs, the local copies malloc_leaf_cf_w_L / MALLOC_IN_STK_L -> the layer's malloc_leaf_cf_w /
   MALLOC_IN_STK_CF), and the two image facts A1's text read became premises:
   - errno_below_stack_cf: errno's four scratch bytes lie below the stack (A1: TfibSyms's as_errno B = TFIB_ERRNO);
   - img_below_ceil_cf: no segment byte at or above ASAN_CEIL (A1: seg_rom_none_high with TFIB_IMG_END <= ASAN_CEIL).
   Each unit proves the two premises from its own image; the rest of the argument is the layer's laws (AR_stack_law_cf,
   AR_blocks_law_cf with lo_stk_ceil, xs_placed_cf) and the k1 leaf's view frame. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YG0dcf.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section J.
Variable segs : list Segment.
Variable B : asyms.
Let LAWS := AR_laws_ok_cf segs B.

(* ---- the two image facts, as premises ---- *)
(* errno's four bytes (ascratch's second disjunct) lie below the stack. *)
Definition errno_below_stack_cf : Prop := forall ly, layout_ok ly -> as_errno B + 4 <= ly_stk_lo ly.
(* No segment byte at or above ASAN_CEIL, so the view of a stack byte is its memory byte. *)
Definition img_below_ceil_cf : Prop := forall a, ASAN_CEIL <= a < 2 ^ 64 -> seg_rom segs (Z_to_bv 64 a) = None.

(* ---- A1's three helper lemmas ---- *)
Lemma lw_apresent_hi : img_below_ceil_cf -> forall (H H' : word -> bool) (m m' : word -> option byte) a,
ASAN_CEIL <= a < 2 ^ 64 -> aview segs H' m' a = aview segs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros ROMHI H H' m m' a Ha E [Hh [b Hb]].
unfold aview, mbyte, mrestrict in E. rewrite Hh, Hb in E. rewrite (ROMHI a Ha) in E.
destruct (H' (Z_to_bv 64 a)) eqn:Hh'; [cbn in E; discriminate E|].
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Hm'; [|cbn in E; discriminate E].
split; [exact Hh' | exists b'; exact Hm'].
Qed.

Lemma lw_blocks_below : forall ly S Hp W mem md p n,
ARcf segs B ly S Hp W mem md -> In (p, n) (blocks S) -> sptr_addr B ly p + req_size n <= ly_stk_lo ly.
Proof.
intros ly S Hp W mem md p n HAR Hin.
assert (Hin' : In (sptr_addr B ly p, n) (ablocks B ly S))
  by (unfold ablocks; exact (in_map (fun b => (sptr_addr B ly (fst b), snd b)) (blocks S) (p, n) Hin)).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md _ _ HAR Hin') as (_ & _ & Hc & _).
pose proof HAR as (M & _). pose proof (lo_stk_ceil ly (amc_layout _ _ _ _ _ M)) as SC. unfold ASAN_CEIL in SC. lia.
Qed.

Lemma lw_xs_below : forall ly S a, xs_placed_cf ly S -> alloc_ceiling <= a -> ~ Exists (in_zr a) (xs_cf ly S).
Proof.
intros ly S a XP Ha EX. apply Exists_exists in EX as (e & Ein & Hin).
unfold xs_placed_cf in XP. rewrite Forall_forall in XP. destruct (XP e Ein) as (_ & _ & Hc & _). unfold in_zr in Hin. lia.
Qed.

(* ---- the unit premise, for every image ---- *)
Theorem malloc_leaf_widen_cf_ok : errno_below_stack_cf -> img_below_ceil_cf -> malloc_leaf_widen_cf segs B.
Proof.
intros ERR ROMHI ly S Hp W regs mem md n ch r W' c' PRE HB
  (ly' & regs' & mem' & md' & Hc & (HAR' & Hle & Hwle & Hrp & Hio & Hfr & HPw) & H10 & Hqt & HN & XP' & HE & HR).
pose proof PRE as (HAR & _ & _ & Hlo & _ & Hhi & Hpres & _).
exists ly', regs', mem', md'. split; [exact Hc|].
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof HAR as (M & _). pose proof (lo_stk_ceil ly (amc_layout _ _ _ _ _ M)) as SC. unfold ASAN_CEIL in SC.
pose proof (lo_top ly (amc_layout _ _ _ _ _ M)) as (_ & _ & _ & Lhi & _). unfold kHighMemEnd in Lhi.
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
pose proof (ERR ly (amc_layout _ _ _ _ _ M)) as Er.
pose proof (xs_placed_of_ARcf segs B ly S Hp W mem md HAR) as XP.
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
  ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
     \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))).
{ intros a Ha [[Hnn Hin]|X].
  - pose proof (lw_blocks_below ly' (snd r) Hp W' mem' md' (fst r) n HAR' (HB Hnn)) as Y. rewrite Elo in Y. lia.
  - apply Exists_app in X as [X|X].
    + exact (lw_xs_below ly S a XP ltac:(lia) X).
    + exact (lw_xs_below ly' (snd r) a XP' ltac:(lia) X). }
assert (NSC : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B MALLOC_IN_STK_CF regs a).
{ intros a Hs Hs1. apply Hs. unfold ascratch in *. unfold ASTACK, MALLOC_IN_STK_CF in *.
  destruct Hs1 as [Hs1|Hs1]; [left; lia | right; exact Hs1]. }
split.
{ split; [exact HAR'|]. split; [exact Hle|]. split; [exact Hwle|]. split; [exact Hrp|]. split; [exact Hio|]. split.
  - intros a Ha Ho Ho' Hs HE'. exact (Hfr a Ha Ho Ho' (NSC a Hs) HE').
  - intros a Ha. destruct (Z_lt_le_dec a (spZ regs - MALLOC_IN_STK_CF)) as [Hgap|Hin]; [|apply HPw; lia].
    assert (Hst : ly_stk_lo ly <= a < ly_stk_hi ly) by (unfold ASTACK, MALLOC_IN_STK_CF in *; lia).
    apply (lw_apresent_hi ROMHI (w_H W) (w_H W') mem mem' a).
    + unfold ASAN_CEIL. lia.
    + apply Hfr; [lia | exact (alc_stack _ _ LAWS ly S Hp W mem md a HAR Hst)
      | apply (alc_stack _ _ LAWS ly' (snd r) Hp W' mem' md' a HAR'); rewrite Elo, Ehi; exact Hst
      | | apply STK; exact Hst].
      unfold ascratch. intros [X|X]; unfold MALLOC_IN_STK_CF in *; lia.
    + apply Hpres. unfold ASTACK, MALLOC_IN_STK_CF in *. lia. }
split; [exact H10|]. split; [exact Hqt|]. split; [exact HN|]. split; [exact XP'|]. split; [exact HE|].
intros x Ho Ho' Hs HE'. exact (HR x Ho Ho' (NSC _ Hs) HE').
Qed.

End J.
End G.

(* Print Assumptions (toolchain/allowed-axioms.txt). *)
Check malloc_leaf_widen_cf_ok.
Print Assumptions malloc_leaf_widen_cf_ok.
