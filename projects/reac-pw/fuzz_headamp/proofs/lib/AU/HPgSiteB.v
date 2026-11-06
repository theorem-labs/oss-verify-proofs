(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSiteA.v at commit 0de5d668c87 for reac-pw/fuzz_headamp image A: module paths changed, the rl_ / role_ prefixes renamed to hd_ / headamp_, role's one allocator site and one cut site replaced by headamp's three of each, role's string, cell and table premises replaced by headamp's parse and harness literals, read-only doubles and stack-guard cells, and the call-site lemmas of the parse contract at its two calls and of the eight check functions added. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgSiteA.v at 1b076471cc6 for image B (fuzz_headamp.asan-ubsan): every lemma that HPgSiteA states at image A's record restated at image B's record HPgImgB.headamp_himg_B, with image B's cut lists, literals, doubles, stack-guard cells, frame offsets and segments; the image-independent lemmas of HPgSiteA are used as they stand. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; call sites measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, capstone 5.0.9): the call-site lemmas of rule
   1j-bis for the texts of lib/A/HPgCSpec.v, at the states those texts already state (the segment contracts' starts
   and ends, a callee contract's own premise hd_pre at its call, and the parse contract's post), with image B's
   record lib/AU/HPgImgB.v headamp_himg_B. Each lemma shows that the stated state supplies a premise of the next
   call's contract. Proves no function (kind: statement text).

   Image B's call sites (LLVMFuzzerTestOneInput 0x80c40; R = s1, F = the frame for locals, from R+0x48):
   - C2 0x82efc `jal` malloc (0x530e0), a0 = len + (len == 0) (0x82ef4, 0x82ef8; s5 = len, 0x82ef0); C4 0x82f34,
     a0 = s5 = 3 cap + 3 (0x82f24 .. 0x82f30); C6 0x83900, a0 = s10 + (s10 == 0), s10 = 3 max(rc, 0) (0x838e4 ..
     0x838fc).
   - M03 (from C5 0x82f38): memset(out, 0xa5, 3 cap + 3) 0x82f54; the res granules 0x54, 0x55 := 0x00, 0x04
     (0x82f5c, 0x82f60); memset(res, 0x5a, 12) 0x82f70; the parse 0x82f90 (jal 0x849ac) with a0 = neg(s7) & pod
     (0x82f74 .. 0x82f7c; s7 = 1 - the null flag, loaded from R+0x38 at 0x82f0c), a1 = out (s6), a2 = cap (s4),
     a3 = res = F + 0x2a0 (s10, 0x82f48); check_no_overrun 0x82fa4 (a0 = out + 3 cap, after the pointer-overflow
     test 0x82f94 .. 0x82f98); check_count 0x82fb4 (a0 = rc (s9), a1 = cap, a2 = res); check_cells_valid 0x82fc0
     (a0 = out, a1 = rc); on the non-corrupt path x = F + 0x2c0 (s2, 0x82fdc), its granules 0x58 .. 0x68 := 0
     (0x82fe0 .. 0x83020), memset(x, 0, 0x88) 0x83030; check_object 0x8386c (a0 = rc, a1 = res, a2 = x),
     check_cells 0x8387c (a0 = out, a1 = rc, a2 = x), check_keys 0x8388c and check_refusal 0x83898 (a0 = res,
     a1 = x; both skipped when rc < 0, `bltz s9` 0x83880); the x granules back at 0xf8 0x838a0 .. 0x838e0.
   - M04b (from C8 0x83920): memset(out, 0xa5, R+0x150 = 3 cap + 3) 0x8392c; the 8-byte parse 0x8393c (jal
     0x849a4) with a0 = R+0x140 (the parse's first argument), a1 = out, a2 = cap; check_plain 0x8394c (a0 = the
     answer, a1 = rc (s9), a2 = out (s6), a3 = first (s7)); C9 0x83950.
   Where image B's call-site state differs from image A's: the null flag is kept as 1 - null (R+0x38 and s7; image
   A keeps null at R+0x40) and the parse's first argument is neg(1 - null) & pod (image A (null - 1) & pod), the
   same value XProps; res and x lie at F + 0x2a0 and F + 0x2c0 (image A F + 0x180, F + 0x1a0), so their granules
   are 0x54, 0x55 and 0x58 .. 0x68 of a 116-granule shadow pattern (image A 0x30, 0x31, 0x34 .. 0x44 of 80); first
   is in s7 at C8 and C9 (image A s2), and R+0x148 holds pp (image A R+0xf0); the parse's argument and the out
   block's size are spilled to R+0x140 and R+0x150 (image A R+0x110, R+0x118); image B's check_cells takes a
   0x20-byte frame (the text's T_check_STK = 32 covers it); a pointer-overflow test precedes check_no_overrun.
   - headamp_B_site_malloc_pod / _out / _first: at C2, C4 and C6 the image's cut list puts a0 = len + (len == 0),
     3 cap + 3 and 3 max(rc, 0) + (3 max(rc, 0) == 0), each satisfying the request premise `0 <= n < MALLOC_MAX`
     of the allocator's contract (lib/Reusable/YG0d.v amalloc_realizes).
   - headamp_B_site_cut3 / cut5 / cut7: at C3, C5 and C7 the image's list holds when the list at the call held,
     the call left a0 = the new block, kept every other register the list names and kept the real-frame cells the
     list names.
   - headamp_B_site_strs: at every segment's start (hd_seg_pre), the parse's four literals (hd_parse_args at
     akey = 0x214a0, aph = 0x214c0, apad = 0x214e0, asens = 0x21500), the harness's own strncmp literal 0x20f40
     and strcmp literals 0x21380, 0x213a0, 0x213c0, the parse's four read-only doubles (HPgImgB.headamp_B_dcs) and
     the stack-guard cells (0x9d478, 0x5f8210).
   - at any callee's call: HPgSiteA's headamp_A_site_block, _frame, _block_app, _frame_app and _frame_at hold at
     every image (no image record in their statements) and are used as they stand; hd_app_FB is hd_app_F for image
     B's frame for locals (class 4, 1024 bytes).
   - headamp_B_site_no_overrun (0x82fa4), headamp_B_site_count (0x82fb4, res = F + 0x2a0 with its granule 0x54
     at 0x00), headamp_B_site_cells_valid (0x82fc0), headamp_B_site_plain (0x8394c; out and first apart).
   - headamp_B_site_parse_args / headamp_B_site_parse_args_plain: every premise of the parse contract
     (HPgCSpec.hd_parse_args) at M03's call 0x82f90 (R = F + 0x2a0) and at M04b's call 0x8393c (R = 0)
     (headamp_B_site_parse_core for both).
   - headamp_B_site_object / _cells / _keys / _refusal: the four checks against x at 0x8386c, 0x8387c, 0x8388c
     and 0x83898 (res = F + 0x2a0, x = F + 0x2c0, the frame's shadow headamp_B_shX), with the two ranges each
     check reads apart (res + 12 = F + 0x2ac <= x; out a live block apart from the frame for locals).
   - every check lemma above also concludes HPgCSpec.hd_app_rng for each range it hands its check.
   - headamp_B_img_bytes_rsegs, headamp_B_segs_low, headamp_B_relro_img: the parse lemmas' image hypotheses at
     image B's own segments (lib/AU/Img0U.v; the read-only window RO_LO .. RO_HI = 0x9c100 .. 0x9d4e8 of
     lib/AU/HPgLibU.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0f YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Ltac hd_inB := solve [cbn [In]; repeat (first [left; reflexivity | right])].

Ltac hd_keepB Hregs Hcells :=
  repeat (apply Forall_cons;
    [cbv beta; cbn [fst hd_xv];
     first [ (apply Hregs; [lia | hd_inB])
           | (intros i Hi; apply Hcells; [hd_inB | exact Hi]) ] |]);
  apply Forall_nil.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* ===================== C2, C4, C6: the three allocator requests ===================== *)
Lemma headamp_B_site_malloc_pod : forall H (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
(rest : list byte),
hd_cut segs H mem regs e (hi_L2 headamp_himg_B) -> e_len e = hd_len rest ->
getr regs (Z_to_bv 5 10) = w64 (hd_xv e XLenNZ) /\ hd_xv e XLenNZ = e_len e /\ 8 <= e_len e <= 5440 /\
0 <= hd_xv e XLenNZ < MALLOC_MAX.
Proof.
intros H mem regs e rest HC He.
unfold hd_cut in HC. cbn [hi_L2 headamp_himg_B] in HC. unfold headamp_B_L23 in HC.
apply Forall_cons_iff in HC as [H10 _]. cbn [fst snd hd_at] in H10.
split; [exact H10 | exact (headamp_A_site_malloc_pod e rest He)].
Qed.

Lemma headamp_B_site_malloc_out : forall H (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L4 headamp_himg_B) -> 0 <= e_cap e <= 9 ->
getr regs (Z_to_bv 5 10) = w64 (hd_xv e XCap33) /\
hd_xv e XCap33 = 3 * e_cap e + 3 /\ 3 <= hd_xv e XCap33 <= 30 /\ 0 <= hd_xv e XCap33 < MALLOC_MAX.
Proof.
intros H mem regs e HC Hc.
unfold hd_cut in HC. cbn [hi_L4 headamp_himg_B] in HC. unfold headamp_B_L45 in HC.
apply Forall_cons_iff in HC as [H10 _]. cbn [fst snd hd_at] in H10.
split; [exact H10 | exact (headamp_A_site_malloc_out e Hc)].
Qed.

Lemma headamp_B_site_malloc_first : forall H (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L6 headamp_himg_B) -> -1 <= e_rc e <= e_cap e -> 0 <= e_cap e <= 9 ->
getr regs (Z_to_bv 5 10) = w64 (hd_xv e XRc3NZ) /\ 0 < hd_xv e XRc3NZ <= 27 /\ 0 <= hd_xv e XRc3NZ < MALLOC_MAX.
Proof.
intros H mem regs e HC Hr Hc.
unfold hd_cut in HC. cbn [hi_L6 headamp_himg_B] in HC. unfold headamp_B_L67 in HC.
apply Forall_cons_iff in HC as [H10 _]. cbn [fst snd hd_at] in H10.
split; [exact H10 | exact (headamp_A_site_malloc_first e Hr Hc)].
Qed.

(* ===================== C3, C5, C7: the values after each allocator call returns ===================== *)
Lemma headamp_B_site_cut3 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L2 headamp_himg_B) ->
getr regs' (Z_to_bv 5 10) = w64 (e_pod e) ->
(forall r, r <> 10 -> In r [8; 9; 18; 19; 21; 24; 27] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x8; 0x18; 0x20; 0x38; 0x48; 0xe0; 0x108; 0x120; 0x148] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
hd_cut segs H mem' regs' e (hi_L3 headamp_himg_B).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold hd_cut in HC |- *. cbn [hi_L2 hi_L3 headamp_himg_B] in HC |- *. unfold headamp_B_L23 in HC |- *.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons; [exact H10|].
refine (hd_cut_keep segs H mem mem' regs regs' e _ HC _).
hd_keepB Hregs Hcells.
Qed.

Lemma headamp_B_site_cut5 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L4 headamp_himg_B) ->
getr regs' (Z_to_bv 5 10) = w64 (e_out e) ->
(forall r, r <> 10 -> In r [8; 9; 18; 19; 20; 21; 23; 24; 25; 27] ->
 getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x8; 0x18; 0x48; 0xe0; 0x108; 0x120; 0x148] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
hd_cut segs H mem' regs' e (hi_L5 headamp_himg_B).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold hd_cut in HC |- *. cbn [hi_L4 hi_L5 headamp_himg_B] in HC |- *. unfold headamp_B_L45 in HC |- *.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons; [exact H10|].
refine (hd_cut_keep segs H mem mem' regs regs' e _ HC _).
hd_keepB Hregs Hcells.
Qed.

Lemma headamp_B_site_cut7 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L6 headamp_himg_B) ->
getr regs' (Z_to_bv 5 10) = w64 (e_first e) ->
(forall r, r <> 10 -> In r [8; 9; 19; 20; 21; 22; 25; 26] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x18; 0x140; 0x148; 0x150; 0x158] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
hd_cut segs H mem' regs' e (hi_L7 headamp_himg_B).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold hd_cut in HC |- *. cbn [hi_L6 hi_L7 headamp_himg_B] in HC |- *. unfold headamp_B_L67 in HC |- *.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons; [exact H10|].
refine (hd_cut_keep segs H mem mem' regs regs' e _ HC _).
hd_keepB Hregs Hcells.
Qed.

(* ===================== M03's and M04b's callees: strings, cells and guard at a segment's start ===================== *)
Lemma headamp_B_site_strs : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc sh
RLO RHI e pos,
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_B sh RLO RHI e pos ->
hd_cstr segs (w_H W) memc 0x214a0 (hd_zbytes Headamp.HA_PREFIX) /\
hd_cstr segs (w_H W) memc 0x214c0 (hd_zbytes Headamp.NAME_PHANTOM) /\
hd_cstr segs (w_H W) memc 0x214e0 (hd_zbytes Headamp.NAME_PAD) /\
hd_cstr segs (w_H W) memc 0x21500 (hd_zbytes Headamp.NAME_SENS) /\
hd_cstr segs (w_H W) memc 0x20f40 (hd_zbytes Headamp.HA_PREFIX) /\
hd_cstr segs (w_H W) memc 0x21380 (hd_zbytes Headamp.NAME_PHANTOM) /\
hd_cstr segs (w_H W) memc 0x213a0 (hd_zbytes Headamp.NAME_PAD) /\
hd_cstr segs (w_H W) memc 0x213c0 (hd_zbytes Headamp.NAME_SENS) /\
hd_ro_cells segs (w_H W) memc headamp_B_dcs /\
hd_guard_ok (aview segs (w_H W) memc) 0x9d478 0x5f8210.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & HC & HGd & _).
cbn [hi_strs hi_cells hi_gotw hi_guard headamp_himg_B] in HS, HC, HGd.
unfold hd_ro_cells in HC.
assert (Tk : hd_zbytes Headamp.HA_PREFIX = [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46])
  by (vm_compute; reflexivity).
assert (Tph : hd_zbytes Headamp.NAME_PHANTOM = [112; 104; 97; 110; 116; 111; 109]) by (vm_compute; reflexivity).
assert (Tpad : hd_zbytes Headamp.NAME_PAD = [112; 97; 100]) by (vm_compute; reflexivity).
assert (Tsens : hd_zbytes Headamp.NAME_SENS = [115; 101; 110; 115]) by (vm_compute; reflexivity).
rewrite Tk, Tph, Tpad, Tsens.
assert (Hs : forall a s, In (a, s) headamp_B_strs -> hd_cstr segs (w_H W) memc a s)
  by (intros a s Hin; exact (proj1 (Forall_forall _ _) HS (a, s) Hin)).
assert (Hc : forall a v, In (a, v) headamp_B_cells -> val_mem segs (mrestrict (w_H W) memc) a 8 v)
  by (intros a v Hin; exact (proj1 (Forall_forall _ _) HC (a, v) Hin)).
do 8 (split; [apply Hs; unfold headamp_B_strs; hd_inB|]).
split; [|exact HGd].
unfold hd_ro_cells, headamp_B_dcs.
do 4 (apply Forall_cons; [cbv beta; cbn [fst snd]; apply Hc; unfold headamp_B_cells; hd_inB|]).
apply Forall_nil.
Qed.

(* ===================== the four check functions the parse's answer feeds ===================== *)
(* HPgCSpec.hd_app_rng for a range inside image B's frame for locals F (class 4, 1024 bytes). *)
Lemma hd_app_FB : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc (e : hd_env) pos,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
forall a m, e_F e <= a -> 0 <= m -> a + m <= e_F e + 1024 -> hd_app_rng segs a m.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc e pos HP Hown HF a m H1 H2 H3.
apply (headamp_A_site_frame_app segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc _ _ a m HP Hown).
- rewrite <- HF. exact H1.
- exact H2.
- rewrite <- HF. change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024. exact H3.
Qed.

(* check_no_overrun(out + 3 cap) at 0x82fa4, after the parse at 0x82f90 (res = F + 0x2a0 is the parse's fourth
   argument): as HPgSiteA's headamp_A_site_no_overrun, at image B's res. *)
Lemma headamp_B_site_no_overrun : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
k2 (regs2 : bvmap 5 word) lyc2 Sc2 W2 mem2 mdc2 (e : hd_env) (pos : Z) (props : option (list byte)) (o : answer),
api_env segs B ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
0 <= e_cap e <= 9 -> o = Headamp.parse_props props (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (repeat GUARD_BYTE (Z.to_nat (3 * (e_cap e + 1))))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_parse_STK <= a < spZ regs) ->
 ~ ((e_out e <= a < e_out e + 3 * Z.of_nat (length (ans_cells o))) \/
    (e_F e + 0x2a0 <> 0 /\ e_F e + 0x2a0 <= a < e_F e + 0x2a0 + 12) \/
    (as_errno B <= a < as_errno B + 4)) ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k2 T_check_STK regs2 lyc2 Sc2 W2 mem2 mdc2 ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc2 Sc2) ->
garr8 segs (mrestrict (w_H W2) mem2) (e_out e + 3 * e_cap e) (hd_zbytes (repeat GUARD_BYTE 3)) /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (e_out e + 3 * e_cap e) 3 /\
hd_off_stack regs2 T_check_STK (e_out e + 3 * e_cap e) 3 /\ hd_app_rng segs (e_out e + 3 * e_cap e) 3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc k2 regs2 lyc2 Sc2 W2 mem2 mdc2 e pos props o
  HAPI HP Hown HF Hin Hcap Ho Hg Hmem HP2 Hin2.
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
assert (Hfb : fs_frame_bytes (hi_cid headamp_himg_B) = 1024) by reflexivity.
pose proof (Headamp.parse_props_total props (e_cap e) ltac:(lia)) as Hok. rewrite <- Ho in Hok.
apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : Z.of_nat (length (ans_cells o)) <= e_cap e)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc _ _ HP Hin)
  as (Hp4 & Hbelow & Hlo & HSTK & Hsp & _).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k2 T_check_STK regs2 lyc2 Sc2 W2 mem2 mdc2 _ _
  HP2 Hin2) as (_ & _ & _ & _ & _ & Hra2).
assert (Hsep : e_out e + 3 * (e_cap e + 1) <= e_F e \/ e_F e + 1024 <= e_out e).
{ pose proof HP as (HJ & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
  assert (Hfin : In (hi_cid headamp_himg_B, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
  pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ _ _ HAR Hin Hfin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF, Hrq, Hfb in Hz. exact Hz. }
assert (Herr : forall a, e_out e <= a < e_out e + 3 * (e_cap e + 1) -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. destruct HAPI as (_ & HAi & _).
  pose proof HP as (HJ & _). pose proof HJ as (HAR & _).
  assert (Hcin : exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n)
    by (exists (e_out e), (3 * (e_cap e + 1)); split; [exact Hin | lia]).
  destruct (al_client_img _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc a HAR (or_introl Hcin)) as (_ & Hni).
  exact (Hni (HAi a He)). }
split; [|split; [|split]].
- intros j Hj.
  assert (Hj3 : (j < 3)%nat) by (unfold hd_zbytes in Hj; rewrite length_map, repeat_length in Hj; exact Hj).
  rewrite hd_nth_guard by exact Hj3.
  assert (Hi : (Z.to_nat (3 * e_cap e) + j < length (hd_zbytes (repeat GUARD_BYTE (Z.to_nat (3 * (e_cap e + 1))))))%nat)
    by (unfold hd_zbytes; rewrite length_map, repeat_length; lia).
  destruct (Hg _ Hi) as (Hv & Hr). rewrite hd_nth_guard in Hv, Hr by lia.
  replace (e_out e + Z.of_nat (Z.to_nat (3 * e_cap e) + j)) with (e_out e + 3 * e_cap e + Z.of_nat j) in Hv by lia.
  split; [|exact Hr].
  apply (hd_val_mem_kept segs (w_H W) (w_H W2) memc mem2 _ 1 _); [|exact Hv].
  intros i0 Hi0. apply Hmem.
  + lia.
  + lia.
  + intros [HE|[HE|HE]].
    * lia.
    * lia.
    * exact (Herr (e_out e + 3 * e_cap e + Z.of_nat j + i0) ltac:(lia) HE).
- apply (proj1 (Hra2 (e_out e + 3 * e_cap e) 3 ltac:(lia) ltac:(lia))).
- apply (proj2 (Hra2 (e_out e + 3 * e_cap e) 3 ltac:(lia) ltac:(lia))).
- apply (headamp_A_site_block_app segs B STK sp0 FP ly S W0 mem0 md0 own k2 T_check_STK regs2 lyc2 Sc2 W2 mem2 mdc2
    _ _ _ _ HP2 Hin2); lia.
Qed.

(* check_count(rc, cap, res) at 0x82fb4: as HPgSiteA's headamp_A_site_count, at image B's res F + 0x2a0, whose
   first granule 0x54 is 0x00 in hi_shB. *)
Lemma headamp_B_site_count : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
hd_fsh segs (w_H W) memc (e_F e) (hi_shB headamp_himg_B) ->
Model.pod_rec_wf r -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2a0) (hd_zbytes (ans_res_bytes o)) ->
-1 <= ans_rc o <= e_cap e /\ e_cap e < 2 ^ 31 /\
(0 <= ans_rc o -> (e_F e + 0x2a0) mod 4 = 0 /\
 val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2a0) 4 (ans_rc o mod 2 ^ 32) /\
 val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2a0 + 4) 4 (ans_keys o mod 2 ^ 32) /\
 ans_rc o <= ans_keys o < 2 ^ 31 /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2a0) 8 /\
 hd_off_stack regs T_check_STK (e_F e + 0x2a0) 8 /\ hd_app_rng segs (e_F e + 0x2a0) 8).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcap Ho Hg.
assert (Hk : 0 <= ans_keys o <= 5440).
{ pose proof (Headamp.parse_props_keys (hd_props (e_null e) (Model.buf r)) (e_cap e)) as Hk0. rewrite <- Ho in Hk0.
  assert (Hk1 : 0 <= ans_keys o <=
    match hd_props (e_null e) (Model.buf r) with Some bs => Z.of_nat (length bs) | None => 0 end)
    by (destruct o as [[? ?] [[? ?] ?]]; exact Hk0).
  revert Hk1. unfold hd_props. destruct (e_null e =? 0); cbv beta iota; intros Hk1; [|lia].
  pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hb). lia. }
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
split; [lia|].
intros Hrc. destruct Hcase as [(Hm1 & _)|(Hr0 & Hrl & Hn & Hrk)]; [lia|].
destruct (headamp_A_site_frame segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hown)
  as (Hal & H4k & Hbelow & Hoff).
rewrite <- HF in Hal, H4k, Hbelow, Hoff.
assert (Hfb : fs_frame_bytes (hi_cid headamp_himg_B) = 1024) by reflexivity.
rewrite Hfb in Hbelow, Hoff.
split; [symmetry; apply (Z.mod_unique _ 4 (8 * (e_F e / 32) + 168) 0); [left; lia|];
  pose proof (Z.div_mod (e_F e) 32 ltac:(lia)); lia|].
unfold ans_res_bytes, ha_res_bytes, hd_zbytes in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [G1 G2]. apply garr8_app in G2 as [G2 G3].
rewrite length_map, Mem.length_le4 in G2. change (Z.of_nat 4) with 4 in G2.
split; [rewrite <- Hn; exact (hd_garr8_le4 segs _ _ _ G1)|].
split; [exact (hd_garr8_le4 segs _ _ _ G2)|].
split; [lia|].
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  apply (hd_fsh_granule segs (w_H W) memc (e_F e) (hi_shB headamp_himg_B) 84 0 Hsh).
  + lia.
  + split; [lia | vm_compute; reflexivity].
  + vm_compute. reflexivity.
  + lia.
- split; [apply Hoff; lia|].
  apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia.
Qed.

(* check_cells_valid(out, rc) at 0x82fc0: HPgSiteA's headamp_A_site_cells_valid names no image record (out is a
   live block at the call); it holds at image B's call as it stands. *)
Lemma headamp_B_site_cells_valid : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (props : option (list byte)) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
0 <= e_cap e <= 9 -> o = Headamp.parse_props props (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) ->
- 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
(0 < ans_rc o ->
 Z.of_nat (length (ans_cells o)) = ans_rc o /\ Forall Headamp.cell_valid (ans_cells o) /\
 0 <= e_out e /\ e_out e + 3 * ans_rc o <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * ans_rc o) /\
 hd_off_stack regs T_check_STK (e_out e) (3 * ans_rc o) /\ hd_app_rng segs (e_out e) (3 * ans_rc o)).
Proof. exact (headamp_A_site_cells_valid segs B). Qed.

(* check_plain(plain, rc, out, first) at 0x8394c (a3 = first in s7): HPgSiteA's headamp_A_site_plain names no
   image record; it holds at image B's call as it stands. *)
Lemma headamp_B_site_plain : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (props : option (list byte)) (o1 o2 : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
In (e_first e, hd_xv e XRc3NZ) (ablocks B lyc Sc) ->
0 <= e_cap e <= 9 ->
o1 = Headamp.parse_props props (e_cap e) -> o2 = Headamp.parse_props props (e_cap e) ->
e_rc e = ans_rc o1 ->
garr8 segs (mrestrict (w_H W) memc) (e_first e) (hd_zbytes (ha_cells_bytes (ans_cells o1))) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o2))) ->
ans_rc o2 = e_rc e /\ - 2 ^ 31 <= e_rc e < 2 ^ 31 /\
(0 < e_rc e ->
 Z.of_nat (length (hd_zbytes (ha_cells_bytes (ans_cells o1)))) = 3 * e_rc e /\
 0 <= e_out e /\ e_out e + 3 * e_rc e <= 2 ^ 63 /\ 0 <= e_first e /\ e_first e + 3 * e_rc e <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o1))) /\
 garr8 segs (mrestrict (w_H W) memc) (e_first e) (hd_zbytes (ha_cells_bytes (ans_cells o1))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * e_rc e) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_first e) (3 * e_rc e) /\
 hd_off_stack regs T_check_STK (e_out e) (3 * e_rc e) /\ hd_off_stack regs T_check_STK (e_first e) (3 * e_rc e) /\
 hd_app_rng segs (e_out e) (3 * e_rc e) /\ hd_app_rng segs (e_first e) (3 * e_rc e) /\
 (e_out e + 3 * e_rc e <= e_first e \/ e_first e + 3 * e_rc e <= e_out e)).
Proof. exact (headamp_A_site_plain segs B). Qed.

(* ================ the parse's arguments at its two calls, and the four checks against x ================
   M03 (from C5) writes out with the guard byte (memset 0x82f54), res with 0x5a (memset 0x82f70) and the res
   granules 0x54, 0x55 := 0x00, 0x04 (0x82f5c, 0x82f60) before its parse at 0x82f90; M04b (from C8) writes out
   with the guard byte (memset 0x8392c) before its parse at 0x8393c. Each parse lemma takes the segment's start
   state, the call's own premise hd_pre, the blocks as at the start, and the walk's memory fact HPgSiteA.hd_kept
   between the two states with image B's write ranges, as HPgSiteA's parse lemmas do at image A. *)

(* What a state inside a segment has: its AR, the out block, image B's frame for locals, R above the allocator
   ceiling. *)
Definition hd_cctxB (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(e : hd_env) (pos : Z) : Prop :=
AR segs B lyc Sc W memc mdc /\ In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) /\
In (hi_cid headamp_himg_B, pos) (frames Sc) /\ e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos /\
alloc_ceiling <= e_R e - T_SEG_STK /\ 0 <= e_cap e <= 9.

Lemma hd_cctxB_of : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc sh RLO RHI
(e : hd_env) (pos : Z) k' T (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc',
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_B sh RLO RHI e pos ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_cctxB lyc' Sc' W' memc' mdc' e pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos k' T regs' lyc' Sc' W' memc' mdc'
  HS HO HP HPm.
destruct HS as (HJ & _ & _ & _ & _ & _ & _ & _ & HRS & Hown & HF & _ & Hcap & _).
destruct HP as (HJ' & _).
pose proof HJ' as (HAR' & _ & _ & _ & _ & Hfr' & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hc1 & Hc2 & _).
destruct HO as (_ & HOin & _).
split; [exact HAR'|].
split; [exact (Permutation_in _ (Permutation_sym HPm) HOin)|].
split; [rewrite Hfr'; apply in_or_app; left; exact Hown|].
split; [rewrite HF; symmetry; eapply headamp_A_site_frame_at; [exact HJ | exact HJ']|].
split; [lia | exact Hcap].
Qed.

(* The facts HPgSiteA.hd_cctx_facts states; the frame class is 4 on both images (hi_cid), so hd_cctxB is
   HPgSiteA.hd_cctx. *)
Lemma hd_cctxB_facts : forall lyc Sc W memc mdc e pos, hd_cctxB lyc Sc W memc mdc e pos ->
e_out e mod 8 = 0 /\ 4096 <= e_out e /\ e_out e + 3 * (e_cap e + 1) <= alloc_ceiling /\
(e_out e + 3 * (e_cap e + 1) <= kLowShadowBeg \/ kHighMemBeg <= e_out e) /\
e_F e mod 8 = 0 /\ e_F e mod 32 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\
(e_F e + 1024 <= kLowShadowBeg \/ kHighMemBeg <= e_F e) /\
(forall a, e_out e <= a < e_out e + 3 * (e_cap e + 1) -> ~ in_img segs a) /\
(forall a, e_F e <= a < e_F e + 1024 -> ~ in_img segs a) /\
(0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ alloc_ceiling <= e_R e - T_SEG_STK /\ 0 <= e_cap e <= 9.
Proof.
intros lyc Sc W memc mdc e pos Hc.
apply (hd_cctx_facts segs B lyc Sc W memc mdc e pos). exact Hc.
Qed.

Lemma hd_inw_w3B : forall e a, hd_inw e (hi_w3 headamp_himg_B) a ->
(e_F e + 0x2a0 <= a < e_F e + 0x348) \/ (shadow_addr (e_F e) + 0x54 <= a < shadow_addr (e_F e) + 0x69) \/
(e_R e <= a < e_R e + 0x160).
Proof.
intros e a H. unfold hd_inw in H. cbn [hi_w3 headamp_himg_B] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [fst snd hd_xv] in H. lia.
Qed.

(* A byte below the allocator ceiling, outside res and x, outside their shadow granules and outside out, reads as
   at the segment's start. *)
Lemma hd_kept_atB : forall lyc' Sc' W' memc' mdc' e pos W memc a,
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
0 <= a < alloc_ceiling ->
~ (e_F e + 0x2a0 <= a < e_F e + 0x348) -> ~ (shadow_addr (e_F e) + 0x54 <= a < shadow_addr (e_F e) + 0x69) ->
~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc a Hc HM Ha H1 H2 H3.
pose proof Hc as (_ & _ & _ & _ & HRc & _).
pose proof YCbq.asan_consts as (C1 & _).
unfold hd_kept in HM. apply HM.
- lia.
- unfold T_SEG_STK, ASTACK in *. lia.
- intros [Hw|Ho]; [|exact (H3 Ho)].
  apply hd_inw_w3B in Hw. destruct Hw as [Hw|[Hw|Hw]]; [exact (H1 Hw) | exact (H2 Hw) |].
  unfold T_SEG_STK, ASTACK in *. lia.
Qed.

Lemma hd_kept_imgB : forall lyc' Sc' W' memc' mdc' e pos W memc a,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
in_img segs a -> aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc a Hlow Hc HM Ha.
pose proof (Hlow a Ha) as Hab.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
apply (hd_kept_atB lyc' Sc' W' memc' mdc' e pos W memc a Hc HM).
- unfold kLowMemEnd in Hab. lia.
- intros Hx. exact (Fni a ltac:(lia) Ha).
- unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (e_F e) 8 ltac:(lia) ltac:(lia)). lia.
- intros Hx. exact (Oni a Hx Ha).
Qed.

Lemma hd_kept_shimgB : forall lyc' Sc' W' memc' mdc' e pos W memc x,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
in_img segs x ->
aview segs (w_H W') memc' (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) memc (shadow_of_addr SHADOW_OFF x).
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc x Hlow Hc HM Hx.
pose proof (Hlow x Hx) as Hxb.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
apply (hd_kept_atB lyc' Sc' W' memc' mdc' e pos W memc (shadow_of_addr SHADOW_OFF x) Hc HM);
  unfold shadow_of_addr, shadow_addr, SHADOW_OFF, kLowMemEnd, kLowShadowBeg, kHighMemBeg in *.
- lia.
- lia.
- intros Hs. apply (Fni x); [lia | exact Hx].
- lia.
Qed.

Lemma hd_kept_tailB : forall lyc' Sc' W' memc' mdc' e pos W memc x a,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
in_img segs x -> x < a < x - x mod 8 + 8 ->
aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc x a Hlow Hc HM Hx Ha.
pose proof (Hlow x Hx) as Hxb.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF. pose proof (Z.div_mod (e_out e) 8 ltac:(lia)) as DO.
unfold kLowMemEnd in Hxb.
apply (hd_kept_atB lyc' Sc' W' memc' mdc' e pos W memc a Hc HM).
- lia.
- intros Hs. apply (Fni x); [lia | exact Hx].
- unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (e_F e) 8 ltac:(lia) ltac:(lia)). lia.
- intros Hs. apply (Oni x); [lia | exact Hx].
Qed.

(* A shadow byte of the low application range reads at the call when it read at the start: either the walk kept
   it, or it is one of image B's res and x granules 0x54 .. 0x68, which the walk has at the call. *)
Lemma hd_kept_hullB : forall lyc' Sc' W' memc' mdc' e pos W memc u,
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
(forall i, 0x54 <= i < 0x69 -> aview segs (w_H W') memc' (shadow_addr (e_F e) + i) <> None) ->
kLowShadowBeg <= u < kHighMemBeg -> aview segs (w_H W) memc u <> None -> aview segs (w_H W') memc' u <> None.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc u Hc HM Hfr Hu Hn.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
destruct (Z_le_gt_dec (shadow_addr (e_F e) + 0x54) u) as [H1|H1];
  [destruct (Z_lt_le_dec u (shadow_addr (e_F e) + 0x69)) as [H2|H2]|].
- replace u with (shadow_addr (e_F e) + (u - shadow_addr (e_F e))) by lia. apply Hfr. lia.
- rewrite (hd_kept_atB lyc' Sc' W' memc' mdc' e pos W memc u Hc HM);
    [exact Hn | unfold kLowShadowBeg, kHighMemBeg in *; lia ..].
- rewrite (hd_kept_atB lyc' Sc' W' memc' mdc' e pos W memc u Hc HM);
    [exact Hn | unfold kLowShadowBeg, kHighMemBeg in *; lia ..].
Qed.

(* A byte of a block live at the call, apart from out, reads as at the segment's start. *)
Lemma hd_kept_blockB : forall lyc' Sc' W' memc' mdc' e pos W memc p n a,
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
In (p, n) (ablocks B lyc' Sc') -> (p + req_size n <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= p) ->
p <= a < p + req_size n -> aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc p n a Hc HM Hin Hap Ha.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hc as (HAR & _ & Hfin & HF & _).
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ HAR Hin) as (_ & P4 & Pce & Papp & _).
pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ _ _ HAR Hin Hfin) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF in Hz.
change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024 in Hz.
unfold in_app, ASAN_CEIL in Papp.
pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
apply (hd_kept_atB lyc' Sc' W' memc' mdc' e pos W memc a Hc HM).
- lia.
- lia.
- unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- lia.
Qed.

Lemma hd_cstr_callB : forall lyc' Sc' W' memc' mdc' e pos W memc a s,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctxB lyc' Sc' W' memc' mdc' e pos -> hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
(forall i, 0x54 <= i < 0x69 -> aview segs (w_H W') memc' (shadow_addr (e_F e) + i) <> None) ->
hd_cstr segs (w_H W) memc a s -> hd_cstr segs (w_H W') memc' a s.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc a s Hlow Hc HM Hfr Hs.
pose proof Hs as (_ & _ & _ & Ha0 & _ & Himg & _).
pose proof (Hlow _ (Himg 0 ltac:(lia))) as Hlo.
pose proof (Hlow _ (Himg (Z.of_nat (length s)) ltac:(lia))) as Hhi.
rewrite Z.add_0_r in Hlo.
apply (hd_cstr_kept segs _ _ _ _ a s Hs).
- intros i Hi. exact (hd_kept_imgB lyc' Sc' W' memc' mdc' e pos W memc (a + i) Hlow Hc HM (Himg i Hi)).
- intros x Hx. apply (hd_kept_shimgB lyc' Sc' W' memc' mdc' e pos W memc x Hlow Hc HM).
  replace x with (a + (x - a)) by lia. apply Himg. lia.
- intros u Hu Hn. apply (hd_kept_hullB lyc' Sc' W' memc' mdc' e pos W memc u Hc HM Hfr); [|exact Hn].
  unfold shadow_addr, SHADOW_OFF in Hu. unfold kLowShadowBeg, kHighMemBeg. unfold kLowMemEnd in Hlo, Hhi.
  pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  pose proof (Z.div_mod (a + (Z.of_nat (length s) + 1) - 1) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (a + (Z.of_nat (length s) + 1) - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (0x7fff8000 + a / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (0x7fff8000 + a / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (0x7fff8000 + (a + (Z.of_nat (length s) + 1) - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (0x7fff8000 + (a + (Z.of_nat (length s) + 1) - 1) / 8) 8 ltac:(lia)).
  lia.
- intros u Hu. apply (hd_kept_tailB lyc' Sc' W' memc' mdc' e pos W memc (a + Z.of_nat (length s)) u Hlow Hc HM);
    [apply Himg; lia | exact Hu].
Qed.

(* The image bytes the parse's callees read that no string of the record covers: the parse's four doubles, the
   stack-guard GOT word and the guard (headamp_B_img_bytes_rsegs shows it at image B's segments). *)
Definition headamp_B_img_bytes : Prop :=
forall a, In a [0x10380; 0x10340; 0x103f0; 0x10358; 0x9d478; 0x5f8210] -> forall i, 0 <= i < 8 -> in_img segs (a + i).

(* The parse contract's premises at a call inside a segment of image B; R and its two clauses are the call's
   (headamp_B_site_parse_args gives them for M03's R = F + 0x2a0, headamp_B_site_parse_args_plain for M04b's
   R = 0). *)
Lemma headamp_B_site_parse_core : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
sh RLO RHI (e : hd_env) (pos ev : Z) (r : Model.pod_rec) k' (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc' (R : Z),
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
api_env segs B -> headamp_B_img_bytes ->
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_B sh RLO RHI e pos ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev -> YK0o.frm_zero (@fp_csr fx) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
(forall i, 0x54 <= i < 0x69 -> aview segs (w_H W') memc' (shadow_addr (e_F e) + i) <> None) ->
(R = 0 \/ (hd_wcell STK sp0 lyc' own (spZ regs') T_parse_STK R 12 /\ R mod 4 = 0 /\
 range_addressable (aview segs (w_H W') memc') SHADOW_OFF R 12)) ->
(R = 0 \/ e_pod e + e_len e <= R \/ R + 12 <= e_pod e) ->
hd_parse_args segs B STK sp0 ly S lyc' Sc' W' memc' own regs' RLO RHI
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B)
  (e_null e) (e_pod e) (e_out e) R (e_cap e) ev (Model.buf r).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos ev r k' regs' lyc' Sc' W' memc' mdc' R
  Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM Hfr HR HPR.
pose proof (hd_cctxB_of STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos
  k' T_parse_STK regs' lyc' Sc' W' memc' mdc' HS HOf HP HPm) as Hc.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hc as (HAR' & _).
pose proof (headamp_B_site_strs STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos HS)
  as (S1 & S2 & S3 & S4 & _ & _ & _ & _ & Hdcs & Hgd).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _).
pose proof (Spa.buf_header r Hwf) as (_ & _ & Hu32 & Hlb).
pose proof (hd_buf_len8 r Hwf) as Hl8.
rewrite <- Hlen in Hu32, Hlb, Hl8.
destruct HPf as (Hp0 & Hpin & Hpout).
destruct HOf as (Ho0 & Hoin & Hoout).
assert (Hpin' : In (e_pod e, e_len e) (ablocks B lyc' Sc')) by exact (Permutation_in _ (Permutation_sym HPm) Hpin).
assert (Hoin' : In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc' Sc'))
  by exact (Permutation_in _ (Permutation_sym HPm) Hoin).
assert (Hrqp : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
assert (Hrqo : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc'
  _ _ HP Hpin') as (P4 & Pbelow & _ & PSTK & Psp & Pra).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc'
  _ _ HP Hoin') as (_ & _ & _ & _ & _ & Ora).
rewrite Hrqp in Pbelow, Pra. rewrite Hrqo in Ora.
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ HAR' Hpin') as (Pm16 & _ & _ & Papp & _).
destruct (al_shadow _ _ (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ HAR' Hpin') as (_ & Phull).
rewrite Hrqp in Papp, Phull. unfold in_app, ASAN_CEIL in Papp.
assert (Hpe : e_pod e + e_len e <= as_errno B \/ as_errno B + 4 <= e_pod e).
{ destruct HAPI as (_ & HEi & _).
  destruct (Z_le_gt_dec (e_pod e + e_len e) (as_errno B)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (as_errno B + 4) (e_pod e)) as [H2|H2]; [right; exact H2|].
  exfalso.
  apply (hd_block_not_img segs B lyc' Sc' W' memc' mdc' (e_pod e) (e_len e) (Z.max (e_pod e) (as_errno B))
    HAR' Hpin').
  - rewrite Hrqp. lia.
  - apply HEi. lia. }
unfold hd_parse_args. rewrite <- Hlen.
split.
{ intros _.
  split; [lia|]. split; [exact Pm16|]. split; [lia|]. split; [exact Hl8|]. split; [exact Hu32|].
  split; [lia|].
  split.
  { apply (hd_garr8_kept segs (w_H W) (w_H W') memc memc'); [|exact Hpod].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    apply (hd_kept_blockB lyc' Sc' W' memc' mdc' e pos W memc (e_pod e) (e_len e) _ Hc HM Hpin');
      rewrite Hrqp; [exact Hap | lia]. }
  split; [exact Hpin'|]. split; [exact Hap|]. split; [exact HPR|]. split; [exact Hpe|].
  split; [exact (proj1 (Pra (e_pod e) (e_len e) ltac:(lia) ltac:(lia)))|].
  split; [exact Phull|].
  split; [unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia|].
  exact (proj2 (Pra (e_pod e) (e_len e) ltac:(lia) ltac:(lia))). }
split; [exact Hcap|].
split; [split; [exact Ho0 | split; [exact Hoin' | exact Hoout]]|].
split; [exact (proj1 (Ora (e_out e) (3 * (e_cap e + 1)) ltac:(lia) ltac:(lia)))|].
split; [exact (proj2 (Ora (e_out e) (3 * (e_cap e + 1)) ltac:(lia) ltac:(lia)))|].
split; [exact HR|].
cbn [hi_akey hi_aph hi_apad hi_asens hi_gotw hi_guard hi_dcs headamp_himg_B].
split; [exact (hd_cstr_callB lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S1)|].
split; [exact (hd_cstr_callB lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S2)|].
split; [exact (hd_cstr_callB lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S3)|].
split; [exact (hd_cstr_callB lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S4)|].
split.
{ unfold hd_ro_cells in *. rewrite Forall_forall in Hdcs |- *. intros c Hcin.
  eapply hd_val_mem_kept; [|exact (Hdcs c Hcin)].
  intros i Hi. apply (hd_kept_imgB lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM).
  unfold headamp_B_dcs in Hcin. cbn [In] in Hcin.
  destruct Hcin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; (apply HIMG; [hd_inB | lia]). }
split.
{ unfold hd_guard_ok in *. destruct Hgd as (G1 & can & G2). split.
  - rewrite (hd_rdword_kept (aview segs (w_H W) memc) (aview segs (w_H W') memc') 0x9d478); [exact G1|].
    intros i Hi. apply (hd_kept_imgB lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM).
    apply HIMG; [hd_inB | exact Hi].
  - exists can.
    rewrite (hd_rdword_kept (aview segs (w_H W) memc) (aview segs (w_H W') memc') 0x5f8210); [exact G2|].
    intros i Hi. apply (hd_kept_imgB lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM).
    apply HIMG; [hd_inB | exact Hi]. }
split.
{ destruct HAPI as (_ & HEi & _). intros kk Hkk.
  rewrite (hd_kept_imgB lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM); [exact (Herr kk Hkk)|].
  apply HEi. lia. }
split.
{ intros a Hro Hos Hne.
  rewrite (hd_kept_imgB lyc' Sc' W' memc' mdc' e pos W memc a Hlow Hc HM); [exact (Haro a Hro Hos Hne)|].
  destruct Hro as [(sg & Hsg & _ & Hr)|Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (Hrelro a Hr)]. }
exact Hfrm.
Qed.

Lemma headamp_B_shB_facts : length (hi_shB headamp_himg_B) = 116%nat /\ nth 84 (hi_shB headamp_himg_B) 0 = 0 /\
nth 85 (hi_shB headamp_himg_B) 0 = 4.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(* The 12 bytes of res (F + 0x2a0) are addressable when the frame's shadow has the res granules 0x54, 0x55 at
   0x00, 0x04. *)
Lemma hd_res_addressableB : forall H mem F sh, hd_fsh segs H mem F sh -> F mod 8 = 0 ->
length sh = 116%nat -> nth 84 sh 0 = 0 -> nth 85 sh 0 = 4 ->
forall a m, F + 0x2a0 <= a -> a + m <= F + 0x2ac -> range_addressable (aview segs H mem) SHADOW_OFF a m.
Proof.
intros H mem F sh Hsh Hal Hl H84 H85 a m Ha Ham x Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as HF.
destruct (Z_lt_le_dec x (F + 0x2a8)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  apply (hd_fsh_granule segs H mem F sh 84 0 Hsh Hal); [rewrite Hl; lia | exact H84 | lia].
- exists 4. split.
  + apply (hd_fsh_granule segs H mem F sh 85 4 Hsh Hal); [rewrite Hl; lia | exact H85 | lia].
  + right. assert (Hm : x mod 8 = x - (F + 0x2a8)).
    { symmetry. apply (Z.mod_unique x 8 (F / 8 + 85) (x - (F + 0x2a8))); [left; lia | lia]. }
    lia.
Qed.

(* The parse contract's premises at M03's call 0x82f90 (a0 = the parse's first argument, a1 = out, a2 = cap,
   a3 = res = F + 0x2a0): res is a cell of the class-4 frame for locals, 4-aligned, below the stack window, with its
   granules at 0x00, 0x04 (the walk's hd_fsh at the call, hi_shB), and apart from the pod. *)
Lemma headamp_B_site_parse_args : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
RLO RHI (e : hd_env) (pos ev : Z) (r : Model.pod_rec) k' (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc',
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
api_env segs B -> headamp_B_img_bytes ->
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_B (hi_shA headamp_himg_B)
  RLO RHI e pos ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev -> YK0o.frm_zero (@fp_csr fx) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc' ->
hd_fsh segs (w_H W') memc' (e_F e) (hi_shB headamp_himg_B) ->
hd_parse_args segs B STK sp0 ly S lyc' Sc' W' memc' own regs' RLO RHI
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B)
  (e_null e) (e_pod e) (e_out e) (e_F e + 0x2a0) (e_cap e) ev (Model.buf r).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos ev r k' regs' lyc' Sc' W' memc' mdc'
  Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM Hsh'.
pose proof (hd_cctxB_of STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos
  k' T_parse_STK regs' lyc' Sc' W' memc' mdc' HS HOf HP HPm) as Hc.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hc as (HAR' & _ & Hfin & HF' & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & _).
pose proof HPf as (_ & Hpin & _).
assert (Hpin' : In (e_pod e, e_len e) (ablocks B lyc' Sc')) by exact (Permutation_in _ (Permutation_sym HPm) Hpin).
pose proof headamp_B_shB_facts as (Bl & B84 & B85).
apply (headamp_B_site_parse_core STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos ev r
  k' regs' lyc' Sc' W' memc' mdc' (e_F e + 0x2a0) Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm
  HM).
- intros i Hi. rewrite (Hsh' i); [discriminate|]. rewrite Bl. lia.
- right. split; [|split].
  + destruct (headamp_A_site_frame segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc'
      _ _ HP Hown) as (_ & _ & Hbelow & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & Hlo & _).
    rewrite <- HF' in Hbelow. change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024 in Hbelow.
    unfold hd_wcell. split.
    * right. exists (hi_cid headamp_himg_B), pos. split; [exact Hown|]. rewrite <- HF'.
      change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024. cbn [hi_cid headamp_himg_B]. lia.
    * right. lia.
  + symmetry. apply (Z.mod_unique _ 4 (8 * (e_F e / 32) + 168) 0); [left; lia|].
    pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). lia.
  + apply (hd_res_addressableB (w_H W') memc' (e_F e) (hi_shB headamp_himg_B) Hsh' F8 Bl B84 B85); lia.
- right.
  pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ _ _ HAR' Hpin' Hfin)
    as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF' in Hz.
  change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024 in Hz.
  assert (Hrqp : req_size (e_len e) = e_len e).
  { pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hb). rewrite <- Hlen in Hb.
    unfold req_size. destruct (Z.eqb_spec (e_len e) 0); lia. }
  rewrite Hrqp in Hz. lia.
Qed.

(* The parse contract's premises at M04b's call 0x8393c (R = 0): M04b's own write ranges are hi_w5 (none on image
   B), and the frame's shadow at the call is the segment start's (hi_shB). *)
Lemma headamp_B_site_parse_args_plain : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc
mdc RLO RHI (e : hd_env) (pos ev : Z) (r : Model.pod_rec) k' (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc',
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
api_env segs B -> headamp_B_img_bytes ->
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_B (hi_shB headamp_himg_B)
  RLO RHI e pos ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev -> YK0o.frm_zero (@fp_csr fx) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_kept segs e (hi_w5 headamp_himg_B) W memc W' memc' ->
hd_parse_args segs B STK sp0 ly S lyc' Sc' W' memc' own regs' RLO RHI
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B)
  (e_null e) (e_pod e) (e_out e) 0 (e_cap e) ev (Model.buf r).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos ev r k' regs' lyc' Sc' W' memc' mdc'
  Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM5.
assert (HM : hd_kept segs e (hi_w3 headamp_himg_B) W memc W' memc').
{ unfold hd_kept in *. intros a Ha Hs Hn. apply HM5; [exact Ha | exact Hs |].
  intros [Hw|Ho]; [|apply Hn; right; exact Ho].
  unfold hd_inw in Hw. cbn [hi_w5 headamp_himg_B] in Hw. inversion Hw. }
pose proof (hd_cctxB_of STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos
  k' T_parse_STK regs' lyc' Sc' W' memc' mdc' HS HOf HP HPm) as Hc.
pose proof (hd_cctxB_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh0 & _).
pose proof headamp_B_shB_facts as (Bl & _ & _).
apply (headamp_B_site_parse_core STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos ev r
  k' regs' lyc' Sc' W' memc' mdc' 0 Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM).
- intros i Hi.
  assert (Hi' : 0 <= i < Z.of_nat (length (hi_shB headamp_himg_B))) by (rewrite Bl; lia).
  pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
  unfold hd_kept in HM5. rewrite HM5.
  + rewrite (Hsh0 i Hi'). discriminate.
  + unfold shadow_addr, SHADOW_OFF. lia.
  + unfold shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK in *. lia.
  + intros [Hw|Ho]; [unfold hd_inw in Hw; cbn [hi_w5 headamp_himg_B] in Hw; inversion Hw|].
    unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- left. reflexivity.
- left. reflexivity.
Qed.

(* ---- the four checks against x ---- *)
(* The frame's shadow at the four calls: hi_shB with the seventeen x granules 0x58 .. 0x68 in scope (0x82fe0 ..
   0x83020 store 0 into each). *)
Definition headamp_B_shX : list Z := firstn 88 headamp_B_shB ++ repeat 0 17 ++ skipn 105 headamp_B_shB.

Lemma headamp_B_shX_facts : length headamp_B_shX = 116%nat /\ nth 84 headamp_B_shX 0 = 0 /\
nth 85 headamp_B_shX 0 = 4 /\ (forall g, (88 <= g < 105)%nat -> nth g headamp_B_shX 0 = 0).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
intros g Hg.
assert (E : forallb (fun k => Z.eqb (nth k headamp_B_shX 0) 0) (seq 88 17) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. apply Z.eqb_eq. apply E. apply in_seq. lia.
Qed.

(* The 136 bytes of x (F + 0x2c0) are addressable when the seventeen x granules are 0. *)
Lemma hd_x_addressableB : forall H mem F sh, hd_fsh segs H mem F sh -> F mod 8 = 0 -> length sh = 116%nat ->
(forall g, (88 <= g < 105)%nat -> nth g sh 0 = 0) ->
forall a m, F + 0x2c0 <= a -> a + m <= F + 0x348 -> range_addressable (aview segs H mem) SHADOW_OFF a m.
Proof.
intros H mem F sh Hsh Hal Hl Hg a m Ha Ham x Hx. exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod (x - F) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x - F) 8 ltac:(lia)) as M.
apply (hd_fsh_granule segs H mem F sh ((x - F) / 8) 0 Hsh Hal).
- rewrite Hl. lia.
- apply Hg. lia.
- lia.
Qed.

(* Image B's frame for locals at any callee's call: aligned, below the stack window. *)
Lemma hd_check_frameB : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) pos,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
e_F e mod 8 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= 2 ^ 47 /\
(forall a m, e_F e <= a -> a + m <= e_F e + 1024 -> hd_off_stack regs T a m) /\
(forall c, c mod 4 = 0 -> (e_F e + c) mod 4 = 0).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc e pos HP Hown HF.
destruct (headamp_A_site_frame segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc _ _ HP Hown)
  as (Hal & H4k & Hbelow & Hoff).
pose proof (hd_pre_sp0 segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc HP) as (HSTK & Hsp & _).
rewrite <- HF in Hal, H4k, Hbelow, Hoff.
change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024 in Hbelow, Hoff.
split.
{ symmetry. apply (Z.mod_unique _ 8 (4 * (e_F e / 32)) 0); [left; lia|].
  pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). lia. }
split; [exact H4k|]. split; [lia|]. split; [exact Hoff|].
intros c Hc. symmetry. apply (Z.mod_unique _ 4 (8 * (e_F e / 32) + c / 4) 0); [left; lia|].
pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). pose proof (Z.div_mod c 4 ltac:(lia)). lia.
Qed.

(* check_object(rc, res, x) at 0x8386c: as HPgSiteA's headamp_A_site_object, at image B's res F + 0x2a0 and
   x F + 0x2c0. *)
Lemma headamp_B_site_object : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_B_shX ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2a0) (hd_zbytes (ans_res_bytes o)) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2c0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
- 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2c0) 4 (ans_rc o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2c0) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x2c0) 4 /\ hd_app_rng segs (e_F e + 0x2c0) 4 /\ (e_F e + 0x2c0) mod 4 = 0 /\
(ans_rc o = -1 -> (e_F e + 0x2a0) mod 4 = 0 /\
 garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2a0) (hd_zbytes (ha_res_bytes 0 0 0)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2a0) 12 /\
 hd_off_stack regs T_check_STK (e_F e + 0x2a0) 12 /\ hd_app_rng segs (e_F e + 0x2a0) 12 /\
 (e_F e + 0x2a0 + 12 <= e_F e + 0x2c0 \/ e_F e + 0x2c0 + 4 <= e_F e + 0x2a0)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcor Hcap Ho Hres Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words segs _ _ _ Hlc Hx) as (X0 & _ & _ & _).
destruct (hd_check_frameB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_B_shX_facts as (Xl & X84 & X85 & Xg).
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
split; [exact X0|].
split; [apply (hd_x_addressableB _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
split; [apply Hm4; reflexivity|].
intros Hm1. destruct Hcase as [(_ & _ & Hn & Hk & Hrf)|(Hr0 & _)]; [|lia].
split; [apply Hm4; reflexivity|].
split; [unfold ans_res_bytes in Hres; rewrite Hn, Hk, Hrf in Hres; exact Hres|].
split; [apply (hd_res_addressableB _ _ _ _ Hsh F8 Xl X84 X85); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
lia.
Qed.

(* check_cells(out, rc, x) at 0x8387c: as HPgSiteA's headamp_A_site_cells, at image B's x F + 0x2c0. *)
Lemma headamp_B_site_cells : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_B_shX ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2c0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
- 2 ^ 31 <= ans_rc o <= 10 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2c0) 4 (ans_rc o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2c0) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x2c0) 4 /\ hd_app_rng segs (e_F e + 0x2c0) 4 /\ (e_F e + 0x2c0) mod 4 = 0 /\
(0 < ans_rc o ->
 Z.of_nat (length (ans_cells o)) = ans_rc o /\ Forall cell_bytes_ok (ans_cells o) /\
 0 <= e_out e /\ e_out e + 3 * ans_rc o <= 2 ^ 63 /\
 0 <= e_F e + 0x2c0 /\ e_F e + 0x2c0 + 4 + 12 * ans_rc o <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * ans_rc o) /\
 hd_off_stack regs T_check_STK (e_out e) (3 * ans_rc o) /\ hd_app_rng segs (e_out e) (3 * ans_rc o) /\
 garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2c0 + 4) (hd_zbytes (x_cells_bytes (ans_cells o))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2c0 + 4) (12 * ans_rc o) /\
 hd_off_stack regs T_check_STK (e_F e + 0x2c0 + 4) (12 * ans_rc o) /\
 hd_app_rng segs (e_F e + 0x2c0 + 4) (12 * ans_rc o) /\
 (e_out e + 3 * ans_rc o <= e_F e + 0x2c0 \/ e_F e + 0x2c0 + 4 + 12 * ans_rc o <= e_out e)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hin Hwf Hcor Hcap Ho Hout Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & Hval).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words segs _ _ _ Hlc Hx) as (X0 & X1 & _ & _).
destruct (hd_check_frameB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_B_shX_facts as (Xl & X84 & X85 & Xg).
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hin)
  as (Hp4 & Hbelow & _ & HSTK & Hsp & Hra).
rewrite Hrq in Hbelow, Hra.
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
split; [exact X0|].
split; [apply (hd_x_addressableB _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
split; [apply Hm4; reflexivity|].
intros Hpos. destruct Hcase as [(Hm1 & _)|(Hr0 & Hrl & _)]; [lia|].
split; [lia|].
split; [eapply Forall_impl; [|exact Hval]; exact cell_valid_bytes_ok|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hout|].
split; [exact (proj1 (Hra (e_out e) (3 * ans_rc o) ltac:(lia) ltac:(lia)))|].
split; [exact (proj2 (Hra (e_out e) (3 * ans_rc o) ltac:(lia) ltac:(lia)))|].
split; [apply (headamp_A_site_block_app segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
  _ _ _ _ HP Hin); lia|].
split; [exact X1|].
split; [apply (hd_x_addressableB _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
(* out is a live block and x lies in the frame for locals: AR keeps them apart (YCbq.v sep_block_frame). *)
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hfin : In (hi_cid headamp_himg_B, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ _ _ HAR Hin Hfin) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF in Hz.
change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024 in Hz. rewrite Hrq in Hz. lia.
Qed.

(* check_keys(res, x) at 0x8388c and check_refusal(res, x) at 0x83898: as HPgSiteA's headamp_A_site_keys and
   headamp_A_site_refusal, at image B's res F + 0x2a0 and x F + 0x2c0. *)
Lemma headamp_B_site_keys : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_B_shX ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2a0) (hd_zbytes (ans_res_bytes o)) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2c0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
(e_F e + 0x2a0) mod 4 = 0 /\ (e_F e + 0x2c0) mod 4 = 0 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2a0 + 4) 4 (ans_keys o mod 2 ^ 32) /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2c0 + X_KEYS_OFF) 4 (ans_keys o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2a0 + 4) 4 /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2c0 + X_KEYS_OFF) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x2a0 + 4) 4 /\ hd_off_stack regs T_check_STK (e_F e + 0x2c0 + X_KEYS_OFF) 4 /\
hd_app_rng segs (e_F e + 0x2a0 + 4) 4 /\ hd_app_rng segs (e_F e + 0x2c0 + X_KEYS_OFF) 4 /\
(e_F e + 0x2a0 + 4 + 4 <= e_F e + 0x2c0 + X_KEYS_OFF \/ e_F e + 0x2c0 + X_KEYS_OFF + 4 <= e_F e + 0x2a0 + 4).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcor Hcap Ho Hres Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words segs _ _ _ Hlc Hx) as (_ & _ & XK & _).
destruct (hd_res_words segs _ _ _ Hres) as (_ & RK & _).
destruct (hd_check_frameB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_B_shX_facts as (Xl & X84 & X85 & Xg).
unfold X_KEYS_OFF in *.
split; [apply Hm4; reflexivity|]. split; [apply Hm4; reflexivity|].
split; [exact RK|]. split; [exact XK|].
split; [apply (hd_res_addressableB _ _ _ _ Hsh F8 Xl X84 X85); lia|].
split; [apply (hd_x_addressableB _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|]. split; [apply Hoff; lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
lia.
Qed.

Lemma headamp_B_site_refusal : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_B, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_B) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_B_shX ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2a0) (hd_zbytes (ans_res_bytes o)) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x2c0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
(e_F e + 0x2a0) mod 4 = 0 /\ (e_F e + 0x2c0) mod 4 = 0 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2a0 + 8) 4 (ans_rf o mod 2 ^ 32) /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x2c0 + X_RF_OFF) 4 (ans_rf o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2a0 + 8) 4 /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x2c0 + X_RF_OFF) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x2a0 + 8) 4 /\ hd_off_stack regs T_check_STK (e_F e + 0x2c0 + X_RF_OFF) 4 /\
hd_app_rng segs (e_F e + 0x2a0 + 8) 4 /\ hd_app_rng segs (e_F e + 0x2c0 + X_RF_OFF) 4 /\
(e_F e + 0x2a0 + 8 + 4 <= e_F e + 0x2c0 + X_RF_OFF \/ e_F e + 0x2c0 + X_RF_OFF + 4 <= e_F e + 0x2a0 + 8).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcor Hcap Ho Hres Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words segs _ _ _ Hlc Hx) as (_ & _ & _ & XR).
destruct (hd_res_words segs _ _ _ Hres) as (_ & _ & RR).
destruct (hd_check_frameB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_B_shX_facts as (Xl & X84 & X85 & Xg).
unfold X_RF_OFF in *.
split; [apply Hm4; reflexivity|]. split; [apply Hm4; reflexivity|].
split; [exact RR|]. split; [exact XR|].
split; [apply (hd_res_addressableB _ _ _ _ Hsh F8 Xl X84 X85); lia|].
split; [apply (hd_x_addressableB _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|]. split; [apply Hoff; lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
split; [apply (hd_app_FB STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia|].
lia.
Qed.
End b.

(* The image hypotheses of the parse lemmas hold at image B's own segments (lib/AU/Img0U.v, the snapshot of the
   pinned fuzz_headamp.asan-ubsan): the parse's four doubles, the stack-guard GOT word and the guard lie in loaded
   segments; every loaded segment lies below kLowMemEnd (YCbq.v's segs_low); the read-only window of
   lib/AU/HPgLibU.v, 0x9c100 .. 0x9d4e8 (RO_LO .. RO_HI), lies in one loaded segment (PT_LOAD 0x9c0c0 ..
   0x9e000). *)
Lemma headamp_B_img_bytes_rsegs : headamp_B_img_bytes Img0U.rsegs.
Proof.
intros a Ha i Hi. cbn [In] in Ha.
destruct Ha as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  (apply (HPgSat.img_chk_ok Img0U.rsegs _ 8); [vm_compute; reflexivity | lia]).
Qed.

Lemma headamp_B_segs_low : forall a, in_img Img0U.rsegs a -> 0 <= a < kLowMemEnd.
Proof.
assert (E : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? kLowMemEnd) Img0U.rsegs = true)
  by (vm_compute; reflexivity).
intros a (sg & Hin & Hr). rewrite forallb_forall in E. specialize (E sg Hin). apply Z.leb_le in E. lia.
Qed.

Lemma headamp_B_relro_img : forall a, 0x9c100 <= a < 0x9d4e8 -> in_img Img0U.rsegs a.
Proof.
assert (E : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x9c100) &&
  (0x9d4e8 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) Img0U.rsegs = true) by (vm_compute; reflexivity).
intros a Ha. apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

Print Assumptions headamp_B_site_malloc_pod.
Print Assumptions headamp_B_site_malloc_out.
Print Assumptions headamp_B_site_malloc_first.
Print Assumptions headamp_B_site_cut3.
Print Assumptions headamp_B_site_cut5.
Print Assumptions headamp_B_site_cut7.
Print Assumptions headamp_B_site_strs.
Print Assumptions hd_app_FB.
Print Assumptions headamp_B_site_no_overrun.
Print Assumptions headamp_B_site_count.
Print Assumptions headamp_B_site_cells_valid.
Print Assumptions headamp_B_site_plain.
Print Assumptions hd_cctxB_of.
Print Assumptions hd_cctxB_facts.
Print Assumptions hd_inw_w3B.
Print Assumptions hd_kept_atB.
Print Assumptions hd_kept_imgB.
Print Assumptions hd_kept_shimgB.
Print Assumptions hd_kept_tailB.
Print Assumptions hd_kept_hullB.
Print Assumptions hd_kept_blockB.
Print Assumptions hd_cstr_callB.
Print Assumptions headamp_B_site_parse_core.
Print Assumptions headamp_B_shB_facts.
Print Assumptions hd_res_addressableB.
Print Assumptions headamp_B_site_parse_args.
Print Assumptions headamp_B_site_parse_args_plain.
Print Assumptions headamp_B_shX_facts.
Print Assumptions hd_x_addressableB.
Print Assumptions hd_check_frameB.
Print Assumptions headamp_B_site_object.
Print Assumptions headamp_B_site_cells.
Print Assumptions headamp_B_site_keys.
Print Assumptions headamp_B_site_refusal.
Print Assumptions headamp_B_img_bytes_rsegs.
Print Assumptions headamp_B_segs_low.
Print Assumptions headamp_B_relro_img.
