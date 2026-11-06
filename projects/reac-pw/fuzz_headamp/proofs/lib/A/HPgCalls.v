(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgCSpec.v at origin/ossv/recipes 6ebe35ba632
   (the Section form of its lines 32-164) and proofs/libreac/fuzz_grant/lib/A/ACfn.v at origin/ossv/recipes
   2638f9235e2 (lines 50-61 and 87-116: tfib_lib_post_x, tfib_lib_pre_xf, tfib_lib_contract_xf) for
   reac-pw/fuzz_role, image A and image B. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCSpec.v at
   0de5d668c87 for reac-pw/fuzz_headamp, image A (fuzz_headamp.asan) and image B (fuzz_headamp.asan-ubsan): module
   paths changed, the rl_ prefix renamed to hd_, role's ten callee contracts replaced by headamp's ten (the parse,
   its 8-byte wrapper and the eight check functions), and role's two middle-segment contracts replaced by headamp's
   five. What differs from role's file, and why:
   - FOUR live blocks, freed LIFO (pp 19744 bytes, pod len | 1, out 3 (cap + 1), first 3 max(rc, 0) | 1), where role
     has two. The harness walk takes the allocator's operations as Section hypotheses at the malloc / free call
     sites, as role's does; a segment contract names the blocks it needs through hd_fresh_block.
   - FIVE middle segments between the allocator calls, with the names and the cut set of headamp's plain / UBSan
     walk (the plain walk's cuts ENTRY, K13044, K1404c, K14080, K14168, K141b4, RET): headamp_build_contract (M01, the
     inlined pod.h builder, the plain walk's evt headamp_build), headamp_dup_contract (M02, fuzz_dup of the pod),
     headamp_check_contract (M03, the plain walk's evt headamp_check: the parse, the first three checks, expect_of
     with the inlined pod_nearest, the last four checks), headamp_first_contract (M04a, fuzz_dup of out) and
     headamp_plain_contract (M04b, the second parse and check_plain). E01 (ENTRY to the malloc of pp) and X01 (the
     four frees to RET) are NOT contract texts here, for the reason role's E01 and X01 are not: each of them makes
     or ends blocks and the frame for locals, so its post is not of the segment shape (the block list and the frame
     list change); they are proved inside the harness walk, where the allocator and frame operations are Section
     hypotheses (knock's APgMain0 / APgMain7 precedent). Image B's walks consume the same five texts. Image B's M01
     also calls pod_write_ent (B 0x84634, from 0x81538, 0x82648 and 0x8295c; image A inlines it): it has no contract
     text here and is walked inside M01, as role's image B walks its twin.
   - headamp's parse writes a heap block (out), a 12-byte struct in the frame for locals (res) and the errno cell,
     and calls the strtol and strncmp wrappers, which role's program does not; so the parse contract carries the
     stack-guard cells, the errno cell and the four read-only strings those wrappers read.
   - role's pod_nearest contract has no counterpart: headamp inlines pod_nearest into M03 (no symbol, lo = 0,
     hi = 255 folded in), so its steps are part of headamp_check_contract.
   The ASan texts restate the plain contracts of lib/Prog at 87a4cb29502 (
   reac_headamp_prop_parse_result_c.v, reac_headamp_prop_parse_c.v, check_*_c.v) over the same shared model
   (lib/Pod/Headamp.v, lib/Spec/HeadBytes.v) and must not weaken them: each ASan contract's premises are the plain
   ones plus the shadow facts the instrumented checks read, and each post states the plain post's memory and
   register facts in the reader form of this engine. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgCSpec.v; 531 of its 610 lines of code are new or changed and 369 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the CALL ADAPTERS of the image-A walk of LLVMFuzzerTestOneInput (0x80bc0) at the call
   sites of headamp's own functions and at the class-4 frame request. Proves no function (kind: segment lemma):
   each lemma turns a callee's contract into the step a walk lane takes at a `jal`.

   THE FORM. A walk of a middle segment holds, at every pc of the segment, the same frame of facts (hc_core): the
   harness's journal from its entry to the current state, sp = R (the 32-aligned base of the real frame, which no
   middle segment moves), gp and tp, R 16-aligned with the callees' stack [R - T_SEG_STK, R) inside the journal's
   window, and the event bound. At a `jal` to a callee (pc = the callee's entry, ra = the return address) an
   adapter takes the callee's contract and the callee's own premises, and hands the walk the returned state: pc =
   ra, hc_core again (the callee keeps sp, gp, tp and extends the journal by no event), the callee-saved
   registers as at the call, the frames, blocks, I/O state and meter as at the call, every byte outside the
   callee's stack [R - T, R) and its write set as at the call, and what the callee computes. That is
   lib/A/HPgCSpec.v's hd_post read at the call site (hc_call), the shape of fuzz_role's seam lemmas
   (lib/A/RPgM02Base.v m2_pre_call / m2_core_call) stated without
   role's segment record.

   THE SITES (capstone over the unstripped twin; the plan's ev/A/LLVMFuzzerTestOneInput.ann.txt):
     0x82eec jal reac_headamp_prop_parse_result 0x845b4, ra 0x82ef0 (a0 = null ? 0 : pod from 0x82ed0 .. 0x82ed8
             (`ld` R+0x40, `addi -1`, `and` s9), a1 = s8 = out, a2 = s6 = cap, a3 = s10 = F + 0x180 = res);
     0x82ef8 jal check_no_overrun 0x83e3c, ra 0x82efc (a0 = s8 + s4 = out + 3 cap, 0x82ef4);
     0x82f08 jal check_count 0x83ee8, ra 0x82f0c (a1 = s6 = cap, a2 = s10 = res);
     0x82f14 jal check_cells_valid 0x83f7c, ra 0x82f18 (a1 = s11 = rc);
     0x836ac jal check_object 0x8405c, ra 0x836b0 (a0 = s11 = rc, a1 = s10 = res, a2 = s2 = x);
     0x836bc jal check_cells 0x84148, ra 0x836c0 (a1 = s11 = rc, a2 = s2 = x);
     0x836cc jal check_keys 0x842e8, ra 0x836d0 (a1 = s2 = x);
     0x836d8 jal check_refusal 0x84368, ra 0x836dc (a1 = s2 = x);
     0x83780 jal reac_headamp_prop_parse 0x845ac, ra 0x83784 (a1 = s8 = out, a2 = s6 = cap);
     0x83790 jal check_plain 0x843e8, ra 0x83794 = C9 (a2 = s8 = out, a3 = s2 = first);
     0x80c3c jal __asan_stack_malloc_4 0x3ccac, ra 0x80c40 (a0 = 0x280 from 0x80c38; sp = R since 0x80c0c).
   The callees' entries are the .symtab addresses of the unstripped twin; every return address is the `jal`'s pc
   plus 4. No address here is relocated from fuzz_role's image (alreloc is not used).

   THE FRAME REQUEST. 0x80c3c is the class-4 request of the side-stack frame for locals (1024 bytes, 128 shadow
   bytes, the flag pointer in its last 8 bytes, F + 0x3f8). hc_frame_call is lib/Reusable/YCbq.v's
   aj_stack_malloc_at at cid 4, at the request's pcs, with frames = [] (the harness's entry state has no frame), in
   the continuation form above. Its Section hypotheses are the kernel facts YCbq's Section d0 asks for (segs_low,
   errno_low, ML) and the class-4 law at its entry (ASM4: astack_malloc_realizes 4, which the port of
   plugin-hostd/fuzz_command lib/A/Rt/RtSM4.v + RtSM4T.v gives, and HSM4: the symbol record's class-4 entry is
   0x3ccac); stack_malloc_progress is the kernel's YG05.v theorem. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== image A: callees and return addresses ======================================== *)
Definition A_PARSE_RESULT : Z := 0x845b4.     (* reac_headamp_prop_parse_result *)
Definition A_PARSE : Z := 0x845ac.            (* reac_headamp_prop_parse: `mv a3,zero; j 0x845b4` *)
Definition A_CK_NO_OVERRUN : Z := 0x83e3c.
Definition A_CK_COUNT : Z := 0x83ee8.
Definition A_CK_CELLS_VALID : Z := 0x83f7c.
Definition A_CK_OBJECT : Z := 0x8405c.
Definition A_CK_CELLS : Z := 0x84148.
Definition A_CK_KEYS : Z := 0x842e8.
Definition A_CK_REFUSAL : Z := 0x84368.
Definition A_CK_PLAIN : Z := 0x843e8.
Definition A_SM4 : Z := 0x3ccac.              (* __asan_stack_malloc_4 *)
Definition RA_PARSE_RESULT : Z := 0x82ef0.
Definition RA_CK_NO_OVERRUN : Z := 0x82efc.
Definition RA_CK_COUNT : Z := 0x82f0c.
Definition RA_CK_CELLS_VALID : Z := 0x82f18.
Definition RA_CK_OBJECT : Z := 0x836b0.
Definition RA_CK_CELLS : Z := 0x836c0.
Definition RA_CK_KEYS : Z := 0x836d0.
Definition RA_CK_REFUSAL : Z := 0x836dc.
Definition RA_PARSE : Z := 0x83784.
Definition RA_CK_PLAIN : Z := 0x83794.        (* = C9, HPgImgA.headamp_himg_A's hi_c9 *)
Definition RA_SM4 : Z := 0x80c40.
(* The class-4 frame: 64 << 4 bytes, the flag pointer in its last word. *)
Definition HC_FB : Z := 1024.
Definition HC_FLAG : Z := 0x3f8.

Lemma hc_fb : fs_frame_bytes 4 = HC_FB.
Proof. reflexivity. Qed.
Lemma hc_flag_off : HC_FB - 8 = HC_FLAG.
Proof. reflexivity. Qed.
Lemma hc_frames4 : 0 < fs_frames 4.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== words ======================================== *)
Lemma hc_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Lemma hc_ret_ok : forall ret, 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 -> YK0s.ret_ok (w64 ret).
Proof. intros ret Hr He. apply YK0s.ret_ok_even. rewrite hc_u64 by exact Hr. exact He. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.

(* ======================================== the frame of facts of a middle segment ======================================== *)
(* At a pc of a middle segment: the harness's journal from its entry (STK, sp0 = S, FP, own) to the current state,
   with at most k events so far; sp = R, gp, tp as the runtime's; R 16-aligned, the callees' stack below R inside
   the journal's window, and R at or below S. hd_seg_pre gives every conjunct at the segment's start. *)
Definition hc_core (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(regs : bvmap 5 word) (R : Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\ st_nev S + k <= EV_MAX /\
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
R mod 16 = 0 /\ sp0 - STK <= R - T_SEG_STK /\ R <= sp0.

(* What hc_core gives about R: the callees' stack lies at or above the allocator's ceiling, R is a stack address,
   and sp holds it. *)
Lemma hc_core_R : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R,
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
alloc_ceiling + T_SEG_STK <= R /\ R <= 2 ^ 47 /\ spZ regs = R.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (HJ & _ & H2 & _ & _ & _ & Hwin & HRs).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_value as (HCv & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (HR : alloc_ceiling + T_SEG_STK <= R) by lia.
split; [exact HR|]. split; [lia|].
unfold spZ. rewrite H2. apply hc_u64. lia.
Qed.

(* A segment's start state (HPgCSpec.hd_seg_pre, the premise of the five middle contracts) gives hc_core at R. *)
Lemma hc_core_of_seg_pre : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I sh RLO RHI e pos,
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I sh RLO RHI e pos ->
0 <= hi_rsz I ->
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (e_R e).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc I sh RLO RHI e pos
  (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _) Hr.
split; [exact HJ|]. split; [exact Hev|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [lia|]. split; [exact Hwin | lia].
Qed.
(* At image A's record (hi_rsz = 0x1e0). *)
Lemma hc_core_of_seg_pre_A : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos,
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh RLO RHI e pos ->
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (e_R e).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos HP.
apply (hc_core_of_seg_pre STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh RLO RHI e pos HP).
cbn [hi_rsz headamp_himg_A]. lia.
Qed.

(* hc_core and the return address give a callee contract's hd_pre, for any callee stack T <= T_SEG_STK. *)
Lemma hc_pre : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ret T,
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 -> 0 <= T <= T_SEG_STK ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ret T HC Hra Hr1 Hr2 HT.
pose proof (hc_core_R STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (_ & _ & Hsp).
destruct HC as (HJ & Hev & _ & H3 & H4 & Hal & Hwin & HRs).
unfold hd_pre. split; [exact HJ|].
split; [rewrite Hra; apply hc_ret_ok; lia|].
split; [unfold raZ; rewrite Hra, hc_u64 by lia; lia|].
split; [exact H3|]. split; [exact H4|].
rewrite Hsp. split; [exact Hal|]. split; [lia|]. split; [lia | exact Hev].
Qed.

(* A range below the allocator's ceiling (a heap block, a side-stack frame) is outside every callee's stack. *)
Lemma hc_off_low : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R T p n,
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
0 <= T <= T_SEG_STK -> p + n <= alloc_ceiling -> hd_off_stack regs T p n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R T p n HC HT Hp x Hx.
pose proof (hc_core_R STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (HR & _ & Hsp).
rewrite Hsp. lia.
Qed.

(* A live block lies below the allocator's ceiling (YG0d AR_blocks_law). *)
Lemma hc_blk_low : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc b m,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (b, m) (ablocks B lyc Sc) -> 4096 <= b /\ b + req_size m <= alloc_ceiling.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc b m HJ Hin.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok segs B) _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & _).
split; [exact H4096 | exact Hceil].
Qed.

(* A frame the harness holds lies below the allocator's ceiling (YG0d AR_sep_law). *)
Lemma hc_frm_low : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (cid, pos) own ->
4096 <= frame_addr lyc cid pos /\ frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos HJ Hown.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_sep _ _ (AR_laws_ok segs B) _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
split; [exact H4096 | exact Hceil].
Qed.

(* A frame the harness holds is 32-aligned (YG0d AR_frames_law): res = F + 0x180 is 4-aligned, and the granule
   arithmetic of the frame's shadow bytes (lib/A/HPgMem.v's hm_fsh_ra) needs F mod 8 = 0. *)
Lemma hc_frm_align : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (cid, pos) own -> frame_addr lyc cid pos mod 32 = 0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos HJ Hown.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok segs B) _ _ _ _ _ _ _ HAR Hin) as (H32 & _). exact H32.
Qed.

(* The journal keeps the frame area's base (YG0f layout_le fixes ly_F), so a frame's address is the same at
   every state of the journal: before and after a call, at every cut. *)
Lemma hc_frame_addr_j : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frame_addr lyc cid pos = frame_addr ly cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos HJ.
pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
unfold frame_addr. rewrite HF. reflexivity.
Qed.

(* The parse's res cell: a range of a frame the harness holds is a cell the parse may write for its caller
   (HPgBase.hd_wcell, hd_parse_args' premise on res). *)
Lemma hc_wcell_frm : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R T cid pos q n,
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
0 <= T <= T_SEG_STK -> In (cid, pos) own -> 0 <= cid ->
frame_addr lyc cid pos <= q -> q + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
hd_wcell STK sp0 lyc own (spZ regs) T q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R T cid pos q n HC HT Hown Hcid Hq1 Hq2.
pose proof (hc_core_R STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (HR & _ & Hsp).
pose proof HC as (HJ & _).
pose proof (hc_frm_low STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc cid pos HJ Hown) as (_ & Hc).
split.
- right. exists cid, pos. split; [exact Hown|]. split; [exact Hcid|]. split; lia.
- right. rewrite Hsp. lia.
Qed.

(* ======================================== a call of one of headamp's own functions ======================================== *)
(* The callee's contract (any of lib/A/HPgCSpec.v's, in its hd_pre -> SRr hd_post form) at the `jal`'s target,
   and the walk's continuation at the return address. *)
Lemma hc_call : forall (a T ret : Z) (FX : YK11.FPState -> Prop) (E : Z -> Prop)
(Rr : world segs -> bvmap 5 word -> (word -> option byte) -> Prop) (Q : world segs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 -> 0 <= T <= T_SEG_STK ->
(hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
 SRr segs W (cfg_at segs a regs memc mdc)
 (hd_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc FX E Rr)) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> FX fx2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> getr regs2 1 = w64 ret ->
 frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - T <= x < R) -> ~ E x ->
  aview segs (w_H W2) mem2 x = aview segs (w_H W) memc x) ->
 Rr W2 regs2 mem2 ->
 SRr segs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom segs)) md2) Q) ->
SRr segs W (cfg_at segs a regs memc mdc) Q.
Proof.
intros a T ret FX E Rr Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2 HT Hspec K.
pose proof (hc_core_R STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (_ & _ & Hsp).
eapply SRr_bind; [exact (Hspec (hc_pre STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ret T HC Hra Hr1 Hr2 HT))|].
intros W2 c2 Hle (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFX & HJ2 & Hpres & Hra2 & Hfr & Hperm & Hio & Hmo & Hkeep
  & HRr).
rewrite Hra.
destruct HC as (HJ & Hev & H2 & H3 & H4 & Hal & Hwin & HRs).
apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle HFX).
- split; [exact HJ2|]. split; [exact Hev|].
  split; [rewrite <- H2; exact (Hpres 2 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H3; exact (Hpres 3 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H4; exact (Hpres 4 ltac:(unfold acallee_saved; lia))|].
  split; [exact Hal|]. split; [exact Hwin | exact HRs].
- exact Hpres.
- rewrite <- Hra. exact Hra2.
- exact Hfr.
- exact Hperm.
- exact Hio.
- exact Hmo.
- intros x Hx Hs He. apply Hkeep; [exact Hx | rewrite Hsp; exact Hs | exact He].
- exact HRr.
Qed.

(* The eight check functions: stack 32, the float state kept, no write for the caller, nothing computed but the
   return itself. The continuation runs at the caller's own float state. *)
Lemma hc_call_ck : forall (a ret : Z) (Q : world segs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
(hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
 SRr segs W (cfg_at segs a regs memc mdc)
 (hd_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
  (fun f => f = fx) (fun _ => False) (fun _ _ _ => True))) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - T_check_STK <= x < R) ->
  aview segs (w_H W2) mem2 x = aview segs (w_H W) memc x) ->
 SRr segs W2 (cfg_at segs ret regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs a regs memc mdc) Q.
Proof.
intros a ret Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2 Hspec K.
apply (hc_call a T_check_STK ret (fun f => f = fx) (fun _ => False) (fun _ _ _ => True) Q
  STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2 ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) Hspec).
intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres _ Hfr Hperm Hio Hmo Hkeep _. subst fx2.
apply (K W2 ly2 S2 regs2 mem2 md2 Hle HC2 Hpres Hfr Hperm Hio Hmo).
intros x Hx Hs. exact (Hkeep x Hx Hs (fun H => H)).
Qed.

(* ---------------- the eight call sites ---------------- *)
Local Ltac ck_site Hspec :=
  intros; eapply hc_call_ck; [eassumption | eassumption | lia | reflexivity | | eassumption];
  intros HP; eapply Hspec; eassumption.

(* 0x82ef8: check_no_overrun(&out[cap]) *)
Lemma hc_check_no_overrun_call : hd_check_no_overrun_specX segs B MT A_CK_NO_OVERRUN ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R g : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_NO_OVERRUN ->
getr regs 10 = w64 g ->
garr8 segs (mrestrict (w_H W) memc) g (hd_zbytes (repeat GUARD_BYTE 3)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF g 3 ->
hd_off_stack regs T_check_STK g 3 -> hd_app_rng segs g 3 ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - T_check_STK <= x < R) ->
  aview segs (w_H W2) mem2 x = aview segs (w_H W) memc x) ->
 SRr segs W2 (cfg_at segs RA_CK_NO_OVERRUN regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_NO_OVERRUN regs memc mdc) Q.
Proof. intros Hspec. unfold RA_CK_NO_OVERRUN. ck_site Hspec. Qed.

(* 0x82f08: check_count(rc, cap, &res) *)
Lemma hc_check_count_call : hd_check_count_specX segs B MT A_CK_COUNT ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R rcc cap keys r : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_COUNT ->
getr regs 10 = w64 rcc -> getr regs 11 = w64 cap -> getr regs 12 = w64 r ->
-1 <= rcc <= cap -> cap < 2 ^ 31 ->
(0 <= rcc -> r mod 4 = 0 /\
 val_mem segs (mrestrict (w_H W) memc) r 4 (rcc mod 2 ^ 32) /\
 val_mem segs (mrestrict (w_H W) memc) (r + 4) 4 (keys mod 2 ^ 32) /\ rcc <= keys < 2 ^ 31 /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF r 8 /\ hd_off_stack regs T_check_STK r 8 /\
 hd_app_rng segs r 8) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - T_check_STK <= x < R) ->
  aview segs (w_H W2) mem2 x = aview segs (w_H W) memc x) ->
 SRr segs W2 (cfg_at segs RA_CK_COUNT regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_COUNT regs memc mdc) Q.
Proof. intros Hspec. unfold RA_CK_COUNT. ck_site Hspec. Qed.

(* 0x82f14: check_cells_valid(out, rc) *)
Lemma hc_check_cells_valid_call : hd_check_cells_valid_specX segs B MT A_CK_CELLS_VALID ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R rcc o : Z) (cs : list Headamp.cell),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_CELLS_VALID ->
getr regs 10 = w64 o -> getr regs 11 = w64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 ->
(0 < rcc ->
 Z.of_nat (length cs) = rcc /\ Forall Headamp.cell_valid cs /\ 0 <= o /\ o + 3 * rcc <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) o (hd_zbytes (ha_cells_bytes cs)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF o (3 * rcc) /\
 hd_off_stack regs T_check_STK o (3 * rcc) /\ hd_app_rng segs o (3 * rcc)) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - T_check_STK <= x < R) ->
  aview segs (w_H W2) mem2 x = aview segs (w_H W) memc x) ->
 SRr segs W2 (cfg_at segs RA_CK_CELLS_VALID regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_CELLS_VALID regs memc mdc) Q.
Proof. intros Hspec. unfold RA_CK_CELLS_VALID. ck_site Hspec. Qed.

(* 0x836ac: check_object(rc, &res, &x) *)
Lemma hc_check_object_call : hd_check_object_specX segs B MT A_CK_OBJECT ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R rcc xrc r x : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_OBJECT ->
getr regs 10 = w64 rcc -> getr regs 11 = w64 r -> getr regs 12 = w64 x ->
- 2 ^ 31 <= rcc < 2 ^ 31 -> - 2 ^ 31 <= xrc < 2 ^ 31 -> (rcc = -1 <-> xrc = -1) ->
val_mem segs (mrestrict (w_H W) memc) x 4 (xrc mod 2 ^ 32) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF x 4 -> hd_off_stack regs T_check_STK x 4 ->
hd_app_rng segs x 4 -> x mod 4 = 0 ->
(rcc = -1 -> r mod 4 = 0 /\
 garr8 segs (mrestrict (w_H W) memc) r (hd_zbytes (ha_res_bytes 0 0 0)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF r 12 /\ hd_off_stack regs T_check_STK r 12 /\
 hd_app_rng segs r 12 /\ (r + 12 <= x \/ x + 4 <= r)) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall y, 0 <= y < 2 ^ 64 -> ~ (R - T_check_STK <= y < R) ->
  aview segs (w_H W2) mem2 y = aview segs (w_H W) memc y) ->
 SRr segs W2 (cfg_at segs RA_CK_OBJECT regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_OBJECT regs memc mdc) Q.
Proof. intros Hspec. unfold RA_CK_OBJECT. ck_site Hspec. Qed.

(* 0x836bc: check_cells(out, rc, &x) *)
Lemma hc_check_cells_call : hd_check_cells_specX segs B MT A_CK_CELLS ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R rcc o x : Z) (cs : list Headamp.cell),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_CELLS ->
getr regs 10 = w64 o -> getr regs 11 = w64 rcc -> getr regs 12 = w64 x -> - 2 ^ 31 <= rcc <= 10 ->
val_mem segs (mrestrict (w_H W) memc) x 4 (rcc mod 2 ^ 32) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF x 4 -> hd_off_stack regs T_check_STK x 4 ->
hd_app_rng segs x 4 -> x mod 4 = 0 ->
(0 < rcc ->
 Z.of_nat (length cs) = rcc /\ Forall cell_bytes_ok cs /\
 0 <= o /\ o + 3 * rcc <= 2 ^ 63 /\ 0 <= x /\ x + 4 + 12 * rcc <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) o (hd_zbytes (ha_cells_bytes cs)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF o (3 * rcc) /\
 hd_off_stack regs T_check_STK o (3 * rcc) /\ hd_app_rng segs o (3 * rcc) /\
 garr8 segs (mrestrict (w_H W) memc) (x + 4) (hd_zbytes (x_cells_bytes cs)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (x + 4) (12 * rcc) /\
 hd_off_stack regs T_check_STK (x + 4) (12 * rcc) /\ hd_app_rng segs (x + 4) (12 * rcc) /\
 (o + 3 * rcc <= x \/ x + 4 + 12 * rcc <= o)) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall y, 0 <= y < 2 ^ 64 -> ~ (R - T_check_STK <= y < R) ->
  aview segs (w_H W2) mem2 y = aview segs (w_H W) memc y) ->
 SRr segs W2 (cfg_at segs RA_CK_CELLS regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_CELLS regs memc mdc) Q.
Proof. intros Hspec. unfold RA_CK_CELLS. ck_site Hspec. Qed.

(* 0x836cc: check_keys(&res, &x); 0x836d8: check_refusal(&res, &x) *)
Lemma hc_check_word_call : forall (a ret off xoff : Z), hd_check_word_specX segs B MT a off xoff ->
4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R r x v : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret ->
getr regs 10 = w64 r -> getr regs 11 = w64 x -> r mod 4 = 0 -> x mod 4 = 0 ->
val_mem segs (mrestrict (w_H W) memc) (r + off) 4 v ->
val_mem segs (mrestrict (w_H W) memc) (x + xoff) 4 v ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (r + off) 4 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (x + xoff) 4 ->
hd_off_stack regs T_check_STK (r + off) 4 -> hd_off_stack regs T_check_STK (x + xoff) 4 ->
hd_app_rng segs (r + off) 4 -> hd_app_rng segs (x + xoff) 4 ->
(r + off + 4 <= x + xoff \/ x + xoff + 4 <= r + off) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall y, 0 <= y < 2 ^ 64 -> ~ (R - T_check_STK <= y < R) ->
  aview segs (w_H W2) mem2 y = aview segs (w_H W) memc y) ->
 SRr segs W2 (cfg_at segs ret regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs a regs memc mdc) Q.
Proof.
intros a ret off xoff Hspec Hr1 Hr2. intros.
eapply hc_call_ck; [eassumption | eassumption | exact Hr1 | exact Hr2 | | eassumption].
intros HP. eapply Hspec; eassumption.
Qed.

Lemma hc_check_keys_call : hd_check_keys_specX segs B MT A_CK_KEYS ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R r x v : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_KEYS ->
getr regs 10 = w64 r -> getr regs 11 = w64 x -> r mod 4 = 0 -> x mod 4 = 0 ->
val_mem segs (mrestrict (w_H W) memc) (r + 4) 4 v ->
val_mem segs (mrestrict (w_H W) memc) (x + X_KEYS_OFF) 4 v ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (r + 4) 4 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (x + X_KEYS_OFF) 4 ->
hd_off_stack regs T_check_STK (r + 4) 4 -> hd_off_stack regs T_check_STK (x + X_KEYS_OFF) 4 ->
hd_app_rng segs (r + 4) 4 -> hd_app_rng segs (x + X_KEYS_OFF) 4 ->
(r + 4 + 4 <= x + X_KEYS_OFF \/ x + X_KEYS_OFF + 4 <= r + 4) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall y, 0 <= y < 2 ^ 64 -> ~ (R - T_check_STK <= y < R) ->
  aview segs (w_H W2) mem2 y = aview segs (w_H W) memc y) ->
 SRr segs W2 (cfg_at segs RA_CK_KEYS regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_KEYS regs memc mdc) Q.
Proof.
intros Hspec. apply (hc_check_word_call A_CK_KEYS RA_CK_KEYS 4 X_KEYS_OFF Hspec);
[unfold RA_CK_KEYS; lia | reflexivity].
Qed.

Lemma hc_check_refusal_call : hd_check_refusal_specX segs B MT A_CK_REFUSAL ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R r x v : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_REFUSAL ->
getr regs 10 = w64 r -> getr regs 11 = w64 x -> r mod 4 = 0 -> x mod 4 = 0 ->
val_mem segs (mrestrict (w_H W) memc) (r + 8) 4 v ->
val_mem segs (mrestrict (w_H W) memc) (x + X_RF_OFF) 4 v ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (r + 8) 4 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (x + X_RF_OFF) 4 ->
hd_off_stack regs T_check_STK (r + 8) 4 -> hd_off_stack regs T_check_STK (x + X_RF_OFF) 4 ->
hd_app_rng segs (r + 8) 4 -> hd_app_rng segs (x + X_RF_OFF) 4 ->
(r + 8 + 4 <= x + X_RF_OFF \/ x + X_RF_OFF + 4 <= r + 8) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall y, 0 <= y < 2 ^ 64 -> ~ (R - T_check_STK <= y < R) ->
  aview segs (w_H W2) mem2 y = aview segs (w_H W) memc y) ->
 SRr segs W2 (cfg_at segs RA_CK_REFUSAL regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_REFUSAL regs memc mdc) Q.
Proof.
intros Hspec. apply (hc_check_word_call A_CK_REFUSAL RA_CK_REFUSAL 8 X_RF_OFF Hspec);
[unfold RA_CK_REFUSAL; lia | reflexivity].
Qed.

(* 0x83790: check_plain(plain, rc, out, first) *)
Lemma hc_check_plain_call : hd_check_plain_specX segs B MT A_CK_PLAIN ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R rcc o fp : Z) (w : list Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_CK_PLAIN ->
getr regs 10 = w64 rcc -> getr regs 11 = w64 rcc -> getr regs 12 = w64 o -> getr regs 13 = w64 fp ->
- 2 ^ 31 <= rcc < 2 ^ 31 ->
(0 < rcc ->
 Z.of_nat (length w) = 3 * rcc /\ 0 <= o /\ o + 3 * rcc <= 2 ^ 63 /\ 0 <= fp /\ fp + 3 * rcc <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) o w /\ garr8 segs (mrestrict (w_H W) memc) fp w /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF o (3 * rcc) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF fp (3 * rcc) /\
 hd_off_stack regs T_check_STK o (3 * rcc) /\ hd_off_stack regs T_check_STK fp (3 * rcc) /\
 hd_app_rng segs o (3 * rcc) /\ hd_app_rng segs fp (3 * rcc) /\ (o + 3 * rcc <= fp \/ fp + 3 * rcc <= o)) ->
(forall W2 ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 ->
 hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall y, 0 <= y < 2 ^ 64 -> ~ (R - T_check_STK <= y < R) ->
  aview segs (w_H W2) mem2 y = aview segs (w_H W) memc y) ->
 SRr segs W2 (cfg_at segs RA_CK_PLAIN regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_CK_PLAIN regs memc mdc) Q.
Proof. intros Hspec. unfold RA_CK_PLAIN. ck_site Hspec. Qed.

(* ---------------- the two parse sites ---------------- *)
(* The parse's returned state: the float registers outside fa4 and fa5 kept with a zero rounding mode, the bytes
   outside its stack, the cells it writes at out, res (when res <> 0) and the errno cell kept, a0 = the answer's
   rc, the cells at out, res's three words, errno readable. *)
Definition hc_parse_k (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(regs : bvmap 5 word) (R ret O Rs : Z) (o : answer) (Q : world segs -> config -> Prop) : Prop :=
forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
wle W W2 -> hd_fxk [14; 15] fx fx2 ->
hc_core STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
same_io mdc md2 -> mo_le MT Sc S2 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (R - T_parse_STK <= x < R) ->
 ~ ((O <= x < O + 3 * Z.of_nat (length (ans_cells o))) \/ (Rs <> 0 /\ Rs <= x < Rs + 12) \/
    (as_errno B <= x < as_errno B + 4)) ->
 aview segs (w_H W2) mem2 x = aview segs (w_H W) memc x) ->
getr regs2 10 = w64 (ans_rc o) ->
garr8 segs (mrestrict (w_H W2) mem2) O (hd_zbytes (ha_cells_bytes (ans_cells o))) ->
(Rs <> 0 -> garr8 segs (mrestrict (w_H W2) mem2) Rs (hd_zbytes (ans_res_bytes o))) ->
(exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev') ->
SRr segs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom segs)) md2) Q.

Lemma hc_parse_k_call : forall (a ret O Rs : Z) (o : answer) (Q : world segs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R : Z),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
(hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
 SRr segs W (cfg_at segs a regs memc mdc)
 (hd_parse_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc O Rs o)) ->
hc_parse_k STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ret O Rs o Q ->
SRr segs W (cfg_at segs a regs memc mdc) Q.
Proof.
intros a ret O Rs o Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2 Hspec K.
apply (hc_call a T_parse_STK ret (hd_fxk [14; 15] fx)
  (fun x => (O <= x < O + 3 * Z.of_nat (length (ans_cells o))) \/ (Rs <> 0 /\ Rs <= x < Rs + 12) \/
            (as_errno B <= x < as_errno B + 4))
  (fun W2 regs2 mem2 =>
   getr regs2 10 = w64 (ans_rc o) /\
   garr8 segs (mrestrict (w_H W2) mem2) O (hd_zbytes (ha_cells_bytes (ans_cells o))) /\
   (Rs <> 0 -> garr8 segs (mrestrict (w_H W2) mem2) Rs (hd_zbytes (ans_res_bytes o))) /\
   (exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2
  ltac:(unfold T_parse_STK, T_PARSE_FRAME, ESTACK, T_SEG_STK, ASTACK; lia) Hspec).
intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres _ Hfr Hperm Hio Hmo Hkeep (H10 & HO & HRs & Hev).
exact (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep H10 HO HRs Hev).
Qed.

(* 0x82eec: reac_headamp_prop_parse_result(props, out, cap, &res) *)
Lemma hc_parse_result_call : forall RLO RHI akey aph apad asens gotw guard dcs,
hd_parse_result_specX segs B MT A_PARSE_RESULT RLO RHI akey aph apad asens gotw guard dcs ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R null P O Rs cap ev : Z) (bs : list byte),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_PARSE_RESULT ->
0 <= null <= 1 ->
getr regs 10 = w64 (if null =? 0 then P else 0) -> getr regs 11 = w64 O ->
getr regs 12 = w64 cap -> getr regs 13 = w64 Rs ->
hd_parse_args segs B STK sp0 ly S lyc Sc W memc own regs RLO RHI akey aph apad asens gotw guard dcs
  null P O Rs cap ev bs ->
hc_parse_k STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R RA_PARSE_RESULT O Rs
  (Headamp.parse_props (hd_props null bs) cap) Q ->
SRr segs W (cfg_at segs A_PARSE_RESULT regs memc mdc) Q.
Proof.
intros RLO RHI akey aph apad asens gotw guard dcs Hspec Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
  regs R null P O Rs cap ev bs HC Hra Hn H10 H11 H12 H13 HA K.
apply (hc_parse_k_call A_PARSE_RESULT RA_PARSE_RESULT O Rs (Headamp.parse_props (hd_props null bs) cap) Q
  STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra ltac:(unfold RA_PARSE_RESULT; lia)
  ltac:(reflexivity)); [|exact K].
intros HP. exact (Hspec STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P O Rs cap ev bs
  HP Hn H10 H11 H12 H13 HA).
Qed.

(* 0x83780: reac_headamp_prop_parse(props, out, cap), res = NULL *)
Lemma hc_parse_call : forall RLO RHI akey aph apad asens gotw guard dcs,
hd_parse_specX segs B MT A_PARSE RLO RHI akey aph apad asens gotw guard dcs ->
forall (Q : world segs -> config -> Prop) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
(regs : bvmap 5 word) (R null P O cap ev : Z) (bs : list byte),
hc_core STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_PARSE ->
0 <= null <= 1 ->
getr regs 10 = w64 (if null =? 0 then P else 0) -> getr regs 11 = w64 O -> getr regs 12 = w64 cap ->
hd_parse_args segs B STK sp0 ly S lyc Sc W memc own regs RLO RHI akey aph apad asens gotw guard dcs
  null P O 0 cap ev bs ->
hc_parse_k STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R RA_PARSE O 0
  (Headamp.parse_props (hd_props null bs) cap) Q ->
SRr segs W (cfg_at segs A_PARSE regs memc mdc) Q.
Proof.
intros RLO RHI akey aph apad asens gotw guard dcs Hspec Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc
  regs R null P O cap ev bs HC Hra Hn H10 H11 H12 HA K.
apply (hc_parse_k_call A_PARSE RA_PARSE O 0 (Headamp.parse_props (hd_props null bs) cap) Q
  STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra ltac:(unfold RA_PARSE; lia)
  ltac:(reflexivity)); [|exact K].
intros HP. exact (Hspec STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P O cap ev bs
  HP Hn H10 H11 H12 HA).
Qed.

(* ======================================== the class-4 frame request at 0x80c3c ======================================== *)
Section fr.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM4 : astack_malloc_realizes segs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = A_SM4.

(* From the `jal` 0x80c3c (pc = 0x3ccac, ra = 0x80c40) with no frame held yet: the request returns at 0x80c40
   with a0 = F, the class-4 frame at some position pos, held by the harness's journal from here on; its 1024
   bytes' shadow all 0; its last word, F + 0x3f8, holds the flag byte's address; the blocks, events and live bytes
   as before; every byte at or above the allocator's ceiling outside the request's stack as before (acall_kept). *)
Lemma hc_frame_call : forall (Q : world segs -> config -> Prop) W (regsT : bvmap 5 word) memT
STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = w64 RA_SM4 ->
frames Sc = [] ->
(forall S2 (regs2 : bvmap 5 word) mem2 md2 pos,
 ajournal segs B STK sp0 FP ly S W0 mem md ((4, pos) :: own) lyc S2 W mem2 md2 k ->
 aregs_preserved regsT regs2 -> getr regs2 10 = w64 (frame_addr lyc 4 pos) ->
 ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = [(4, pos)] ->
 st_nev S2 = st_nev Sc -> blocks_bytes S2 = blocks_bytes Sc ->
 zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc 4 pos) HC_FB ->
 rdword (aview segs (w_H W) mem2) (frame_addr lyc 4 pos + HC_FLAG) = Some (flag_addr lyc 4 pos) ->
 acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) ->
 SRr segs W (cfg_at segs RA_SM4 regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_SM4 regsT memT mdc) Q.
Proof.
intros Q W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hfr0 K.
assert (Hcnt : count_cid 4 (frames Sc) < fs_frames 4) by (rewrite Hfr0; cbn [count_cid]; exact hc_frames4).
unfold cfg_at at 1. rewrite <- HSM4.
eapply SRr_bind.
{ exact (aj_stack_malloc_at segs B (AR_laws_ok segs B) segs_low errno_low ML
    (stack_malloc_progress (as_universe B)) 4 ASM4 ltac:(lia) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc
    k o (w64 RA_SM4) HJ Hsp Hal Hneg Hbud Hgp Htp Hra
    ltac:(apply hc_ret_ok; unfold RA_SM4; lia) Hcnt). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & Hpres & H10 & Hbl & Hfr2 & _ & Hnev & Hbb
  & Hz & Hflag & Hkept).
rewrite Hfr0 in Hfr2.
apply (K S2 regs2 mem2 md2 pos HJ2 Hpres H10 Hbl Hfr2 Hnev Hbb).
- rewrite <- hc_fb. exact Hz.
- rewrite <- hc_flag_off, <- hc_fb. replace (frame_addr lyc 4 pos + (fs_frame_bytes 4 - 8))
    with (frame_addr lyc 4 pos + fs_frame_bytes 4 - 8) by lia. exact Hflag.
- exact Hkept.
Qed.
End fr.

End c.
End b.

Print Assumptions hc_call.
Print Assumptions hc_call_ck.
Print Assumptions hc_check_no_overrun_call.
Print Assumptions hc_check_count_call.
Print Assumptions hc_check_cells_valid_call.
Print Assumptions hc_check_object_call.
Print Assumptions hc_check_cells_call.
Print Assumptions hc_check_keys_call.
Print Assumptions hc_check_refusal_call.
Print Assumptions hc_check_plain_call.
Print Assumptions hc_parse_result_call.
Print Assumptions hc_parse_call.
Print Assumptions hc_wcell_frm.
Print Assumptions hc_frame_call.
Print Assumptions hc_core_of_seg_pre.
Print Assumptions hc_core_of_seg_pre_A.
Print Assumptions hc_frm_align.
Print Assumptions hc_frame_addr_j.
