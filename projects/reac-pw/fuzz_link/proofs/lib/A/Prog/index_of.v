(* index_of on image A (fuzz_link.asan 0x86784, listing offset AF_index_of = 0x45b8; listing
   (internal path) (internal record, sha256 3b45a4408bf6)): its contract lib/A/Prog/index_of_c.v
   `index_of_acontract` (link_amem.v `aleaf_rd`, K = 8272, EV 0, SIDE []), from the walk of fuzz_if_nametoindex.

   index_of's 66 instructions are fuzz_if_nametoindex's (0x826cc) word for word except the pc-relative immediates of
   the two auipc pairs (both reach g_nl 0x5dcac0 and the .got word 0xa19d0) and of the three jal (both reach
   wrapper_strcmp 0x4304c, errpath_load4 0x5a45c, errpath_load8 0x5a4fc). fuzz_if_nametoindex.v proves the walk once
   for both entries: `if_lookup_aproof`, parametric in the listing offset AF in {AF_fuzz_if_nametoindex,
   AF_index_of}, at fuzz_if_nametoindex's statement. The two contracts have the same K, read set, write set ([]) and
   Post, and the same Pre up to names (index_of's `astrcmp_arg` is fuzz_if_nametoindex's `astrcmp_arg_ni` word for
   word); `aleaf_rd_pre_mono` carries the walk over, and would
   still if index_of's Pre were the stronger one.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts; STRCMP, the strcmp wrapper's
   contract (Reusable/AStrcmpDef.v form), is discharged on the image by
   lib/A/Rt/RtStrcmpClosed.v `link_astrcmp_closed` (0x4304c; index_of_aproof_img).

   Proves index_of (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk fuzz_if_nametoindex_c index_of_c fuzz_if_nametoindex.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtStrcmpClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

(* a leaf contract with a weaker Pre gives the one with the stronger Pre *)
Lemma aleaf_rd_pre_mono : forall segs rlo rhi B pc K EV SIDE
    (P1 P2 : bvmap 5 word -> (word -> option byte) -> Prop) Rd Wr Post,
  (forall regs m, P2 regs m -> P1 regs m) ->
  aleaf_rd SK segs rlo rhi B pc K EV SIDE P1 Rd Wr Post -> aleaf_rd SK segs rlo rhi B pc K EV SIDE P2 Rd Wr Post.
Proof.
intros segs rlo rhi B pc K EV SIDE P1 P2 Rd Wr Post Himp H.
unfold aleaf_rd in *. intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HR HP.
apply H; [exact HA | exact HR | apply Himp; exact HP].
Qed.

Lemma io_arg : forall segs regs m p s,
  astrcmp_arg segs regs INDEX_OF_AK m p s -> astrcmp_arg_ni segs regs FUZZ_IF_NAMETOINDEX_AK m p s.
Proof.
intros segs regs m p s H. exact H.
Qed.

Lemma io_pre : forall segs regs m, index_of_apre segs regs m -> fuzz_if_nametoindex_apre segs regs m.
Proof.
intros segs regs m (bs & tab & nm & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
exists bs, tab, nm.
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj (io_arg _ _ _ _ _ H7) _))))))).
intros i n2 ix p Hi Hp Hr. exact (io_arg _ _ _ _ _ (H8 i n2 ix p Hi Hp Hr)).
Qed.

Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis STRCMP : AStrcmpDef.astrcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strcmp).

Theorem index_of_aproof : forall rlo rhi, index_of_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold index_of_acontract, index_of_acontract_at.
apply (aleaf_rd_pre_mono _ _ _ _ _ _ _ _ (fuzz_if_nametoindex_apre SEGS)); [apply io_pre|].
replace INDEX_OF_A with (pa_val A_TEXT + AF_index_of) by (rewrite (lv_text LV); reflexivity).
exact (if_lookup_aproof SK B LAWS TL LV STRCMP AF_index_of (or_intror eq_refl) rlo rhi).
Qed.
End w.

(* LAWS and STRCMP discharged on the image's segments: the allocator laws by lib/Reusable/YG0q.v `AR_laws_ok`, the
   strcmp wrapper by lib/A/Rt/RtStrcmpClosed.v `link_astrcmp_closed` from the image's asyms record (lib/A/AF0m.v
   PcapSyms; on the image lib/A/AD2l.v PcapB_syms). *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem index_of_aproof_img : forall B, PALib B -> LinkVals -> AF0m.PcapSyms B ->
  pa_segs = AB1v.tfibsegs -> forall rlo rhi, index_of_acontract SK pa_segs rlo rhi B.
Proof.
intros B TL LV TS Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
apply (index_of_aproof SK B LAWS TL LV).
rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtStrcmpClosed.link_astrcmp_closed B TS).
Qed.
End img.

Print Assumptions index_of_aproof.
Print Assumptions index_of_aproof_img.
