(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Segment R14 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81768, 0x8183c), the official cuts
   Inv_A81768_at -> Inv_A8183c_at of lib/A/Prog/SlotInv.v.  rule 24: no function proved (a slot segment).

   The entry cut is the head of the 32-byte sum loop at turn i (i < 32): a0 = a2 = Phi_r + 18 + i, a1 = the partial
   sum of the first i bytes, a3 = 32 - i.  The segment runs
     81768..81734  the loop (one shadow-byte load and compare per byte; the error arm 0x81794 -> 0x82d44 is not
                   taken because the 32 bytes at Phi_r + 18 are addressable)             [B3Loop.b3_loop1 at i]
     81790 j 81824 ; 81824 zext.b a0,a1 ; 81828 beqz a0,81830  (0x8182c `j 82bf4` not taken: the low byte of the
                   full sum is 0, B3Rtm.a_rtm_sum for turn 0 through B3Loop.b3_sum_low)  [B3Loop.b3_tail1]
     81830 mv a0,s8 ; 81834 mv a1,s2 ; 81838 jal 84498 <reac_box_catalogue_match>        [r14_call]
   and ends at 0x8183c with a0 = want(T, n_0, X(0)) = mrow (B3Rtm.a_rtm_want).

   The callee reads the 50 bytes at Phi_r and the catalogue bytes at T = 0x9e800 (both addressable: the block from
   HB, the catalogue from FRA's frame_AG conjunct), writes its own stack window [sp - 9136, sp), the side-stack bytes
   of the classes 0, 1, 2 and the shadow of its window (r14_W).  Everything the exit cut carries is read back across
   those writes: the frame slots and the frame's 392 shadow bytes are apart from them (the frame is either at sp on
   the real stack or inside the side stack, where fra_fp's fp_dj keeps it apart from the classes 0-2), the data
   spills at [s1 + off] and the saved registers lie above sp, s5 is callee-saved, and the block [Phi_r, Phi_r + n_0)
   is apart from the side stack (a_laws_blocks) and below the window.  ENT moves across the call with ent_munch (no
   entry block, image byte, byte at or above S, or shadow byte of those is in r14_W) and across the model step with
   ent_mat.

   Cut convention: the lemma is stated on the official cuts (exit Inv_A8183c_at, entry Inv_A81768_at). FRA gives the
   callee's window (sp <= A <= S < APPMEM_END; the window addressable by FRA's slot-window conjunct, the frame apart
   from it by fra_frame), and the call's side-stack package (the base FS, the word at tp; fp for the classes 0, 1,
   2; reac_box_catalogue_match_tls; the frame and its shadow apart from those classes) comes from FRA inside the
   proof by Tac_fsfree.fra_fp. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c memcmp_c bcmp_wrap_c reac_box_catalogue_match_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot Tac_fs
  B3Loop.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YN2e.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* ---- The write set of the call: the callee's stack window, the class-0/1/2 side-stack bytes and the shadow of
   the window (the munch of reac_box_catalogue_match_contract). ---- *)
Definition r14_W (S FS : Z) : list ivl :=
  [(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)].

(* The twelve side-stack ranges of the classes 0, 1, 2 in numbers (fs_B c = 64 * 2^c, fs_M c = 2^(14-c)). *)
Lemma r14_fs_ranges : forall FS,
  fs_hint FS 0 = FS /\ fs_hint FS 1 = FS + 8 /\ fs_hint FS 2 = FS + 16 /\
  fs_flag FS 0 0 = FS + 4096 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_flag FS 2 0 = FS + 28672 /\
  fs_M 0 = 16384 /\ fs_M 1 = 8192 /\ fs_M 2 = 4096 /\
  fs_frame FS 0 0 = FS + 36864 /\ fs_frame FS 0 (fs_M 0) = FS + 1085440 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016 /\
  fs_frame FS 2 0 = FS + 2134016 /\ fs_frame FS 2 (fs_M 2) = FS + 3182592.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat split; first [ reflexivity | lia | (vm_compute (2 ^ 15) in *; lia) ].
Qed.

Lemma r14_W_eq : forall S FS, r14_W S FS =
  [(S - CM_K, S);
   (FS, FS + 8); (FS + 4096, FS + 20480); (FS + 36864, FS + 1085440);
   (shadow_addr (FS + 36864), shadow_addr (FS + 1085440));
   (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016));
   (FS + 16, FS + 24); (FS + 28672, FS + 32768); (FS + 2134016, FS + 3182592);
   (shadow_addr (FS + 2134016), shadow_addr (FS + 3182592));
   (shadow_addr (S - CM_K), shadow_addr S)].
Proof.
  intros S FS. destruct (r14_fs_ranges FS) as
    (H0 & H1 & H2 & H3 & H4 & H5 & M0 & M1 & M2 & F0 & F0' & F1 & F1' & F2 & F2').
  unfold r14_W, fp_w, fp_w1. cbn [flat_map app].
  rewrite H0, H1, H2, H3, H4, H5, F0, F0', F1, F1', F2, F2', M0, M1, M2.
  replace (FS + 4096 + 16384) with (FS + 20480) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  replace (FS + 28672 + 4096) with (FS + 32768) by lia.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 16 + 8) with (FS + 24) by lia.
  reflexivity.
Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory (Seg/F6.v f6_app_split). *)
Lemma r14_app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec LOWMEM_END lo) as [L2|L2].
  - pose proof (H lo ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H LOWMEM_END ltac:(lia)) as H3.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow bytes of a contiguous app range are shadow memory (Seg/F6.v f6_shadow_ivl). *)
Lemma r14_shadow_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx. unfold shadow_addr, ASAN_K in Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  unfold in_shadow. destruct (r14_app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* An app byte outside the callee's window and outside the three metadata/frame bands of the classes 0, 1, 2 is
   outside the call's writes: the nine address ranges are those bands, the three shadow ranges and the window's
   shadow are shadow memory. *)
Lemma r14_out_app : forall S FS x,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  app_mem x -> ~ (S - CM_K <= x < S) ->
  ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
  outside (r14_W S FS) x.
Proof.
  intros S FS x HFS0 HFSS HSA HFSapp HWapp Hx Hw H1 H2 H3.
  assert (HK : 0 < CM_K) by (unfold CM_K; lia).
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  rewrite r14_W_eq. cbn [outside].
  repeat split; try (intros HC; lia).
  - intros HC. apply (app_not_shadow x Hx).
    apply (r14_shadow_ivl (FS + 36864) (FS + 1085440) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (r14_shadow_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (r14_shadow_ivl (FS + 2134016) (FS + 3182592) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (r14_shadow_ivl (S - CM_K) S x); [exact HWapp | lia | exact HC].
Qed.

(* The same for a byte at or above the callee's window: the side stack and every shadow byte are below it. *)
Lemma r14_out_hi : forall S FS x,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END -> HIGHMEM_BEG <= S - CM_K -> S <= x ->
  outside (r14_W S FS) x.
Proof.
  intros S FS x HFS0 HFSS HSA HHI Hx.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  assert (HSH : forall y, 0 <= y -> y <= APPMEM_END -> shadow_addr y <= HIGHMEM_BEG).
  { intros y Hy0 Hy1. unfold shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia. }
  pose proof (HSH S ltac:(unfold HIGHMEM_BEG in *; lia) HSA) as HS1.
  pose proof (HSH (FS + 3182592) ltac:(lia) ltac:(unfold HIGHMEM_BEG, APPMEM_END in *; lia)) as HS2.
  assert (HM : forall y z, y <= z -> shadow_addr y <= shadow_addr z).
  { intros y z Hyz. unfold shadow_addr. Z.div_mod_to_equations. lia. }
  pose proof (HM (FS + 1085440) (FS + 3182592) ltac:(lia)) as HM1.
  pose proof (HM (FS + 2134016) (FS + 3182592) ltac:(lia)) as HM2.
  pose proof (HM (S - CM_K) S ltac:(lia)) as HM3.
  rewrite r14_W_eq. cbn [outside].
  repeat split; intros HC; unfold HIGHMEM_BEG in *; lia.
Qed.

(* The shadow byte of an application byte outside the side stack and outside the callee's window is outside the
   call's writes: the ten address ranges are application memory, and the four shadow ranges are the shadow of the
   side stack's frames and of the window, which the byte's granule misses (the side stack's base and the window's
   base are multiples of 8). *)
Lemma r14_out_sh : forall S FS x,
  0 <= FS -> FS mod 8 = 0 -> FS + FS_SIZE <= S - CM_K -> (S - CM_K) mod 8 = 0 -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  app_mem x -> ~ (FS <= x < FS + FS_SIZE) -> ~ (S - CM_K <= x < S) ->
  outside (r14_W S FS) (shadow_addr x).
Proof.
  intros S FS x HFS0 HFS8 HFSS HS8 HSA HFSapp HWapp Hx HnFS HnW.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  pose proof (shadow_of_app x Hx) as Hsh.
  assert (HAPPFS : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE ->
            ~ (lo <= shadow_addr x < hi)).
  { intros lo hi Hlo Hhi HC. apply (app_not_shadow (shadow_addr x)); [|exact Hsh].
    apply HFSapp. lia. }
  rewrite r14_W_eq. cbn [outside].
  repeat split.
  - intros HC. apply (app_not_shadow (shadow_addr x)); [apply HWapp; lia | exact Hsh].
  - exact (HAPPFS FS (FS + 8) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 4096) (FS + 20480) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 36864) (FS + 1085440) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - exact (HAPPFS (FS + 8) (FS + 16) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 20480) (FS + 28672) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 1085440) (FS + 2134016) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - exact (HAPPFS (FS + 16) (FS + 24) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 28672) (FS + 32768) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 2134016) (FS + 3182592) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - intros HC. revert HC HnW. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* Every range of the call's writes begins at or above the end of the image's writable data (Seg/P6.v p6_W_los /
   p6_dj_lo): the side stack is placed there, its shadow lies above ASAN_K, and the window is in high memory. *)
Lemma r14_dj_lo : forall (W : list ivl) (c n : Z), (forall p, In p W -> c + n <= fst p) -> disjoint_from W c n.
Proof.
  induction W as [|[lo hi] W IH]; intros c n H; cbn [disjoint_from]; [exact I|].
  split.
  - left. pose proof (H (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

Lemma r14_W_los : forall S FS p, 6283264 <= FS -> 6283264 <= S - CM_K -> In p (r14_W S FS) ->
  6283264 <= fst p.
Proof.
  intros S FS p HFS HS Hin.
  assert (HK : CM_K = 9136) by reflexivity.
  assert (HD1 : 0 <= (FS + 36864) / 8) by (apply Z.div_pos; lia).
  assert (HD2 : 0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia).
  assert (HD3 : 0 <= (FS + 2134016) / 8) by (apply Z.div_pos; lia).
  assert (HD4 : 0 <= (S - CM_K) / 8) by (apply Z.div_pos; lia).
  rewrite r14_W_eq in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]];
    subst p; cbn [fst]; unfold shadow_addr, ASAN_K in *; lia.
Qed.

(* The spill base named by a spill is FRA's A: both are read off register 9 and both lie in the narrow window
   [-416, 2^47] (Seg/R19.v r19_wrap_out's argument, in the equality form). *)
Lemma r14_spill_A : forall (regs : bvmap 5 word) (m : word -> option byte) (A A0 off v : Z),
  rg regs 9 A -> rg regs 9 A0 -> 0 <= A -> A + 416 <= APPMEM_END -> 0 <= off -> off + 8 <= 416 ->
  q64 m (A0 + off) v -> A0 = A.
Proof.
  intros regs m A A0 off v HA HA0 HA1 HA2 Ho1 Ho2 HQ.
  unfold q64 in HQ. destruct HQ as (Hb0 & Hb1 & _). rewrite length_le8 in Hb1.
  unfold rg in HA, HA0. rewrite HA in HA0.
  assert (Ew : A mod 2 ^ 64 = A0 mod 2 ^ 64)
    by (rewrite <- !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap; rewrite HA0; reflexivity).
  rewrite (Z.mod_small A (2 ^ 64)) in Ew by (unfold APPMEM_END in *; lia).
  pose proof (Z.div_mod A0 (2 ^ 64) ltac:(lia)) as Hdm. rewrite <- Ew in Hdm.
  remember (A0 / 2 ^ 64) as q eqn:Eq. clear Eq.
  change (2 ^ 64) with 18446744073709551616 in *. unfold APPMEM_END in *. cbn [Z.of_nat] in Hb1. lia.
Qed.

(* A byte apart from the twelve side-stack ranges, from the window and from the window's shadow (the route the
   frame and its shadow take: on the side arm the frame lies inside the side stack, so the cut's fp_dj, not the
   side stack's bounds, keeps it apart).  Seg/P6.v p6_out. *)
Lemma r14_out_dj : forall S FS x,
  ~ (S - CM_K <= x < S) -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  ~ (shadow_addr (S - CM_K) <= x < shadow_addr S) ->
  outside (r14_W S FS) x.
Proof.
  intros S FS x H1 H2 H3. unfold r14_W. cbn [app outside]. split; [exact H1|].
  apply fl_out_app; [exact H2|]. cbn [outside]. split; [exact H3 | exact I].
Qed.

(* A shadow byte of [lo, hi) (lo a multiple of 8) is the shadow byte of an address of [lo, hi). *)
Lemma r14_sh_inv : forall lo hi a, lo mod 8 = 0 -> lo <= hi ->
  shadow_addr lo <= a < shadow_addr hi -> lo <= 8 * (a - ASAN_K) < hi /\ a = shadow_addr (8 * (a - ASAN_K)).
Proof. intros lo hi a H8 Hlh HC. unfold shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia. Qed.

(* The shadow bytes of a 3136-byte block apart from [b1, b2) are apart from the shadow of [b1, b2) (Seg/F6.v
   f6_sh_dj). *)
Lemma r14_sh_dj : forall a b1 b2 t, a mod 8 = 0 -> 0 <= a -> 0 <= b1 -> b1 <= b2 ->
  (a + FRAME_BYTES <= b1 \/ b2 <= a) ->
  shadow_addr a <= t < shadow_addr a + FRAME_SHADOW -> ~ (shadow_addr b1 <= t < shadow_addr b2).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a b1 b2 t Ha8 Ha Hb1 Hb12 Hdj Ht HC. unfold shadow_addr, ASAN_K in *.
  destruct Hdj as [H|H]; Z.div_mod_to_equations; lia.
Qed.

(* ---- The side stack's state after the call: the hint word, flag bytes and frames of the classes 0, 1 and 2 come
   from the callee's fp at the return; the metadata of the other classes is unchanged, because the run writes only
   the class-0/1/2 bands, their shadow and the window (Seg/F6.v f6_fs_ok_post, for three classes). ---- *)
Lemma r14_fs_ok : forall (m m' : word -> option byte) (S FS TP : Z) (W D : list ivl),
  ACw.a_fs_ok m FS ->
  munch (r14_W S FS) m m' ->
  fp [0%nat; 1%nat; 2%nat] m' TP FS (S - CM_K) S W D ->
  FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END -> HIGHMEM_BEG <= S - CM_K ->
  ACw.a_fs_ok m' FS.
Proof.
  intros m m' S FS TP W D (HOK1 & HOK2 & HOK3 & HOK4 & HOK5) MU
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HAwin & _ & _) HFSS HSA HHI.
  destruct HP as (HFS0 & HFSmod & HFSgt & HFSapp & HSTK).
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HSZc : ACw.FS_SIZE = 11571200) by reflexivity.
  pose proof (Forall_inv HCL) as HC0.
  pose proof (Forall_inv (Forall_inv_tail HCL)) as HC1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCL))) as HC2.
  assert (HFSub : FS + FS_SIZE <= APPMEM_END).
  { pose proof (HFSapp (FS + FS_SIZE - 1) ltac:(lia)) as Hh.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* a metadata byte of a class other than 0, 1, 2 is outside the write set *)
  assert (HOUT : forall x, FS <= x < FS + FS_SIZE ->
            ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
            outside (r14_W S FS) x).
  { intros x Hx G1 G2 G3.
    apply (r14_out_app S FS x ltac:(lia) HFSS HSA HFSapp HAwin (HFSapp x Hx) ltac:(lia) G1 G2 G3). }
  assert (MB : forall a, outside (r14_W S FS) a -> 0 <= a < 2 ^ 64 -> mbyte rsegs m' a = mbyte rsegs m a).
  { intros a Ho Ha. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Ho. }
  assert (HB64 : FS + FS_SIZE <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct HSTK as (_ & _ & HS).
    destruct (HS a ltac:(lia)) as [Hw (b & Hb)].
    split; [exact Hw | exists b; exact Hb].
  - pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in HW by lia. exact HW.
  - destruct H96 as (_ & _ & H96'). pose proof (H96' 0%nat ltac:(cbn; lia)) as HH.
    cbn [nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
  - intros c Hc.
    destruct (Nat.eq_dec c 0) as [->|Hne0].
    { destruct HC0 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 0) h Hh). }
    destruct (Nat.eq_dec c 1) as [->|Hne1].
    { destruct HC1 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 1) h Hh). }
    destruct (Nat.eq_dec c 2) as [->|Hne2].
    { destruct HC2 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 2) h Hh). }
    destruct (HOK4 c Hc) as (h & Hh). exists h.
    apply (word_mem_frame rsegs m m' _ _ Hh). intros kk Hk.
    assert (Hhint : ACw.a_fs_hint FS c = FS + 8 * Z.of_nat c) by reflexivity.
    assert (Hc3 : 3 <= Z.of_nat c <= 10) by lia.
    apply MB; [rewrite Hhint; apply HOUT; lia | rewrite Hhint; lia].
  - intros c j Hc Hj.
    assert (Hfl : forall (cc : nat) (hh : word) (flags : list byte),
              bytes_at rsegs m' (fs_flag FS cc 0) flags -> Z.of_nat (length flags) = fs_M cc ->
              Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
              0 <= j < ACw.a_fs_M cc ->
              mbyte rsegs m' (ACw.a_fs_flag FS cc j) = Some (Z_to_bv 8 0) \/
              mbyte rsegs m' (ACw.a_fs_flag FS cc j) = Some (Z_to_bv 8 1)).
    { intros cc hh flags Hfb Hfl' Hfb01 Hjj.
      assert (HM : ACw.a_fs_M cc = fs_M cc) by reflexivity.
      rewrite HM in Hjj.
      destruct Hfb as (_ & _ & Hfb).
      assert (HjN : (Z.to_nat j < length flags)%nat) by lia.
      pose proof (Hfb (Z.to_nat j) HjN) as HH.
      destruct (nth_error flags (Z.to_nat j)) as [b|] eqn:E;
        [|exfalso; apply nth_error_None in E; lia].
      assert (Eaddr : fs_flag FS cc 0 + Z.of_nat (Z.to_nat j) = ACw.a_fs_flag FS cc j)
        by (unfold fs_flag, ACw.a_fs_flag; lia).
      rewrite Eaddr in HH.
      pose proof (proj1 (Forall_forall _ flags) Hfb01 b (nth_error_In _ _ E)) as Hb01.
      destruct Hb01 as [->| ->]; [left | right]; exact HH. }
    destruct (Nat.eq_dec c 0) as [->|Hne0].
    { destruct HC0 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 0%nat h flags Hfb Hfl' Hfb01 Hj). }
    destruct (Nat.eq_dec c 1) as [->|Hne1].
    { destruct HC1 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 1%nat h flags Hfb Hfl' Hfb01 Hj). }
    destruct (Nat.eq_dec c 2) as [->|Hne2].
    { destruct HC2 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 2%nat h flags Hfb Hfl' Hfb01 Hj). }
    assert (Hr : FS + 32768 <= ACw.a_fs_flag FS c j < FS + 36864).
    { unfold ACw.a_fs_flag. unfold ACw.a_fs_M in Hj.
      destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]];
        try (exfalso; revert Hc Hne0 Hne1 Hne2; clear; lia);
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj |- *;
        first [ lia | (vm_compute (2 ^ 15) in *; vm_compute in Hj; lia) ]. }
    destruct (HOK5 c j Hc Hj) as [HH|HH]; [left|right];
      (rewrite MB; [exact HH | apply HOUT; lia | lia]).
Qed.

(* ---- Image facts the callee contract asks for. ---- *)

(* Every segment of the image ends below 0x5fe000 (A/BzBridge.v rsegs_below_task, for the writable-data top). *)
Lemma r14_segs_below : BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

(* No image byte lives at or above 0x5fe000, so the callee's stack window has no ROM bytes. *)
Lemma r14_rom_none : forall a, 0 <= a < 2 ^ 64 -> 0x5fe000 <= a -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha Hge. apply seg_rom_unmapped.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (BzBridge.find_segment_below rsegs 0x5fe000 (bv_unsigned (wa a)) 1 s r14_segs_below E ltac:(lia))
    as [Hlt|Hn]; [|lia].
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa_unsigned in Hlt by lia. lia.
Qed.

(* A range is addressable when each of its bytes is (FRA's frame_AG and slot-window conjuncts are per byte). *)
Lemma r14_addr_of1 : forall (m : word -> option byte) lo len,
  0 <= lo -> 0 <= len -> lo + len <= APPMEM_END ->
  (forall i, 0 <= i < len -> addressable m (lo + i) 1) -> addressable m lo len.
Proof.
  intros m lo len Hlo Hlen Hend HA.
  split; [exact Hlo|]. split; [exact Hlen|]. split; [exact Hend|].
  intros i Hi. destruct (HA i Hi) as (_ & _ & _ & H).
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

(* A registered global of frame_AG is addressable over its whole length. *)
Lemma r14_ag_addr : forall (m : word -> option byte) lo len,
  (forall a, in_globals AFw.frame_AG a -> addressable m a 1) ->
  In (lo, len) AFw.frame_AG -> 0 <= lo -> 0 <= len -> lo + len <= APPMEM_END ->
  addressable m lo len.
Proof.
  intros m lo len HAG Hin Hlo Hlen Hend.
  apply (r14_addr_of1 m lo len Hlo Hlen Hend). intros i Hi.
  exact (HAG (lo + i) ltac:(exists lo, len; split; [exact Hin | lia])).
Qed.

(* ---- Generic transport helpers (Seg/R3.v r3_addr_keep / r3_stk_tr, Seg/P7.v p7_stk_sub / p7_rg_inj). ---- *)

Lemma r14_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa_unsigned by lia. exact (HO i Hi).
Qed.

(* One CB cell's rw_cells across a run whose write set W misses the cell's bytes. *)
Lemma r14_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
  munch W m m' -> wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> outside W x) ->
  rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs MU WM HO ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (a_keep W m m' a _ MU); [|exact Hb]. intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (HO x Hx).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (WM _ (Hw i Hi)).
Qed.

Lemma r14_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa_unsigned by lia. exact Ho.
Qed.

Lemma r14_stk_sub : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> stk rsegs m a hi.
Proof. intros m lo hi a (H1 & H2 & H) Ha. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

Lemma r14_rg_inj : forall regs r A A', rg regs r A -> rg regs r A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A = A'.
Proof.
  intros regs r A A' H H' HA HA'. unfold rg in *. rewrite H in H'.
  apply (f_equal (bv_unsigned (n:=64))) in H'. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in H' by lia. exact H'.
Qed.

(* mkR_of made concrete, so the run lemma's register file is the mkR of the evt lemmas (Seg/P6.v p6_mkR_of). *)
Lemma r14_mkR_of : forall regs, Regs6ss.mkR_of regs = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3)
  (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10)
  (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
  (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- The run of [0x81768, 0x81830]: the sum loop entered at turn i, then the low-byte test. ---- *)

(* ---- The callee's mem_inv premise from ro_agree. FRA carries ro_agree, not mem_inv, so the call runs on the
   normalized memory `normalize rsegs m` (MemNorm.evt_normalize; worked example Seg/A1.v a1_req_evt), whose
   mem_inv is MemNorm.mem_inv_normalize; each premise crosses mem_rel forward and each part of the post crosses it
   back (every byte the call reads or writes outside the image lies at or above 0x5fe000, where no byte is
   read-only, or is read through mrd, which mem_rel keeps). ---- *)

(* Above the image there is no read-only byte (Seg/A1.v ro_addr_hi). *)
Lemma r14_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (BzBridge.find_segment_below sg 0x5fe000 x n s r14_segs_below E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma r14_wv : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof. intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r14_ro_hi a Ha)). tauto. Qed.

Lemma r14_rel_stk : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (r14_wv m m0 a HR ltac:(lia)); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma r14_rel_sw : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR. split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    assert (Hhi : 0x5fe000 <= a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia);
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (r14_wv m m0 a HR Hhi); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma r14_rel_ad : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR.
  split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]); (split; [exact H2|]);
    intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); (split; [exact Hap|]); exists b;
    [rewrite <- (mrd_rel rsegs m m0 _ HR) | rewrite (mrd_rel rsegs m m0 _ HR)]; split; assumption.
Qed.

Lemma r14_rel_fsp : forall m m0 FS, mem_rel rsegs m m0 -> (fs_place m FS <-> fs_place m0 FS).
Proof.
  intros m m0 FS HR. assert (HGT : ASAN_GT = 0x5fe000) by reflexivity.
  split; intros (P1 & P2 & P3 & P4 & P5); (split; [exact P1|]); (split; [exact P2|]); (split; [exact P3|]);
    (split; [exact P4|]); pose proof P5 as (_ & P6 & _);
    pose proof (r14_rel_stk m m0 FS (FS + FS_SIZE) HR ltac:(lia) P6) as HS;
    [exact (proj1 HS P5) | exact (proj2 HS P5)].
Qed.

Lemma r14_cells_gen : forall m m1, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m1 a bs) ->
  asan_cells m -> asan_cells m1.
Proof.
  intros m m1 Fb H. unfold asan_cells in *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => apply Fb; assumption end.
Qed.

Lemma r14_rel_cells : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 HR. split; apply r14_cells_gen; intros a bs Hb;
    [exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb) | exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) Hb)].
Qed.

Lemma r14_tlsc_gen : forall m m1 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m1 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m1 TP DT TS C T DB k.
Proof.
  intros m m1 TP DT TS C T DB k Fb
    (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
     & H16 & H17 & HDB & H19).
  unfold asan_tls_cells.
  split; [exact (Fb _ _ H1)|]. split; [exact (Fb _ _ H2)|]. split; [exact (Fb _ _ H3)|].
  split; [exact (Fb _ _ H4)|]. split; [exact (Fb _ _ H5)|]. split; [exact Hk|].
  split; [exact (Fb _ _ H7)|]. split; [exact (Fb _ _ H8)|]. split; [exact (Fb _ _ H9)|].
  split; [exact (Fb _ _ H10)|]. split; [exists tb, te; exact (Fb _ _ H11)|].
  split; [exact (Fb _ _ H12)|]. split; [exact (Fb _ _ H13)|]. split; [exact (Fb _ _ H14)|].
  split; [exact (Fb _ _ H15)|]. split; [exact (Fb _ _ H16)|]. split; [exact (Fb _ _ H17)|].
  split; [exact HDB|]. exact (Fb _ _ H19).
Qed.

Lemma r14_rel_tlsc : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k HR. split; apply r14_tlsc_gen; intros a bs Hb;
    [exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb) | exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) Hb)].
Qed.

Lemma r14_rel_cls : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c HR. unfold fp_cls.
  split; intros (Hc & h & flags & H1 & H2 & H3 & H4); (split; [exact Hc|]); exists h, flags;
    (split; [|split; [|split; [exact H3 | exact H4]]]);
    first [ exact (proj1 (bytes_at_rel rsegs m m0 _ _ HR) H1) | exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) H1)
          | exact (proj1 (bytes_at_rel rsegs m m0 _ _ HR) H2) | exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) H2) ].
Qed.

Lemma r14_rel_fp : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D HR. unfold fp.
  split; intros (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & Hlo & Happ & HW & HD);
    exists DT, TS, C, T, DB, k.
  - split; [exact (proj1 (r14_rel_tlsc m m0 _ _ _ _ _ _ _ HR) HT)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ HR) HTP)|].
    split; [exact (proj1 (r14_rel_fsp m m0 FS HR) HP)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ HR) H88)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ HR) H96)|].
    split; [eapply Forall_impl; [|exact HCL]; intros c Hc; exact (proj1 (r14_rel_cls m m0 FS c HR) Hc)|].
    split; [exact Hlo|]. split; [exact Happ|]. split; [exact HW | exact HD].
  - split; [exact (proj2 (r14_rel_tlsc m m0 _ _ _ _ _ _ _ HR) HT)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) HTP)|].
    split; [exact (proj2 (r14_rel_fsp m m0 FS HR) HP)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) H88)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) H96)|].
    split; [eapply Forall_impl; [|exact HCL]; intros c Hc; exact (proj2 (r14_rel_cls m m0 FS c HR) Hc)|].
    split; [exact Hlo|]. split; [exact Happ|]. split; [exact HW | exact HD].
Qed.

Lemma r14_rel_tls : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  reac_box_catalogue_match_tls m TP FS lo hi -> reac_box_catalogue_match_tls m0 TP FS lo hi.
Proof.
  intros m m0 TP FS lo hi HR H DT TS C T DB k HT.
  exact (H DT TS C T DB k (proj2 (r14_rel_tlsc m m0 _ _ _ _ _ _ _ HR) HT)).
Qed.

(* The writes of the normalized run, read back on the real memory: a byte outside W is unchanged (read-only bytes
   by ro_same, the others through the two normalizations); writability is kept (a writable byte of the real
   memory either lies outside W, so is unchanged, or is not read-only and crosses both normalizations). *)
Lemma r14_rel_munch : forall W m m0 mf m0', mem_rel rsegs m m0 -> mem_rel rsegs mf m0' ->
  munch W m0 m0' -> ro_same rsegs m mf -> munch W m mf.
Proof.
  intros W m m0 mf m0' R1 R2 MU RS x Hx.
  destruct (ro_addr rsegs x) eqn:E; [exact (RS x E)|].
  rewrite <- (mem_rel_rw rsegs mf m0' x R2 E). rewrite (MU x Hx). exact (mem_rel_rw rsegs m m0 x R1 E).
Qed.

Lemma r14_rel_wmono : forall W m m0 mf m0', mem_rel rsegs m m0 -> mem_rel rsegs mf m0' ->
  munch W m mf -> wmono rsegs m0 m0' ->
  (forall x : word, ro_addr rsegs x = true -> outside W (bv_unsigned x)) ->
  wmono rsegs m mf.
Proof.
  intros W m m0 mf m0' R1 R2 MU WM Hro x Hx.
  destruct (ro_addr rsegs x) eqn:E.
  - unfold wview in *. rewrite (MU x (Hro x E)). exact Hx.
  - rewrite <- (wview_rel_rw rsegs mf m0' x R2 E). apply WM.
    rewrite (wview_rel_rw rsegs m m0 x R1 E). exact Hx.
Qed.

Lemma r14_ro_agree_same : forall m mf, ro_agree rsegs m -> ro_same rsegs m mf -> ro_agree rsegs mf.
Proof. intros m mf H RS a Ha. unfold mrd. rewrite (RS a Ha). exact (H a Ha). Qed.

(* No read-only byte is written by the call: every range of r14_W lies at or above 0x5fe000. *)
Lemma r14_W_ro : forall S FS (x : word), 6283264 <= FS -> 6283264 <= S - CM_K ->
  ro_addr rsegs x = true -> outside (r14_W S FS) (bv_unsigned x).
Proof.
  intros S FS x HFS HS E.
  assert (Hx : bv_unsigned x < 0x5fe000).
  { destruct (Z_lt_le_dec (bv_unsigned x) 0x5fe000) as [L|L]; [exact L|].
    exfalso. pose proof (u64_range x) as Hu.
    pose proof (r14_ro_hi (bv_unsigned x) ltac:(lia)) as Hf. unfold wa in Hf.
    rewrite Z_to_bv_bv_unsigned in Hf. rewrite Hf in E. discriminate E. }
  assert (LOS : forall p, In p (r14_W S FS) -> 6283264 <= fst p) by (intros p Hp; exact (r14_W_los S FS p HFS HS Hp)).
  revert LOS. generalize (r14_W S FS) as W. induction W as [|[lo hi] W IH]; intros LOS; cbn [outside]; [exact I|].
  split.
  - pose proof (LOS (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply LOS. right. exact Hp.
Qed.

(* Two word_mem values at the same address agree mod 2 ^ 64 (A/Prog/Seg/P2.v p2_wm_congr): the side stack's base
   read off the tp word has one value, so FSREC's base is the one of fra_fp's package. *)
Lemma r14_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !KindBGlue.kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !YN2e.le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* SlotInv's accumulator in the form B3Loop's loop lemma uses (proved over variables: never unfold rsum at a
   concrete turn index, the kernel would compute the round-trip model). *)
Lemma r14_rsum : forall g b i, rsum g b i = psum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i.
Proof. intros g b i. reflexivity. Qed.

Lemma r14_head :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) ->
    a2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a3 = Z_to_bv 64 (32 - Z.of_nat i) ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m (phi + 18) xs -> addressable m (phi + 18) 32 ->
    blocksum xs = 0 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi xs i E0 E1 E2 E3 E10 Hi Hlen HB AD HS.
  pose proof (psum_range xs 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply evt_cut.
  { apply (b3_loop1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (phi + 18) xs i);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | exact Hi
      | exact Hlen | exact HB | exact AD ]. }
  intros ms' (a4' & a5' & ->).
  replace (phi + 18 + 32) with (phi + 50) by lia.
  eapply evt_cut.
  { apply (b3_tail1 ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 (psum xs 32))
             (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (psum xs 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply evt_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* ---- The run of [0x81830, 0x8183c): the two argument moves and the call. ---- *)

(* A machine state with no pending supervisor call is its MS. *)
Lemma r14_ms_eta : forall s, ms_svc_pending s = None ->
  s = MS (ms_regs s) (ms_fregs s) (ms_pc_val s) (ms_fcsr s) (ms_resv s) (ms_mem s) (ms_rom s).
Proof. intros [] H; cbn in H; subst; reflexivity. Qed.

Lemma r14_call : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat -> bytes_at rsegs m phi fb -> (phi + 50 <= S - CM_K \/ S <= phi) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> 6283264 <= FS -> addressable m (S - CM_K) CM_K ->
    addressable m phi 50 -> app_mem (phi + 50) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8183c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x8183c) fc None m' (seg_rom rsegs) /\
         munch (r14_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs)).
Proof.
  intros CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi0 Hphi50 Hlen HS Hmod HKS HST HROM Hfb HFB HAPART HROc HROA HAC HSW
    Hhi Hsp HFSgt HADW HADf HAPP50 HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  assert (HHMB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  (* the premises on the normalized memory *)
  pose proof (mem_rel_normalize rsegs m HROA) as REL.
  assert (HST0 : stk rsegs (normalize rsegs m) (S - CM_K) S)
    by exact (proj1 (r14_rel_stk m _ (S - CM_K) S REL ltac:(lia) ltac:(lia)) HST).
  assert (HFB0 : bytes_at rsegs (normalize rsegs m) phi fb) by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HFB).
  assert (HROc0 : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs (normalize rsegs m) (wa a) = seg_rom rsegs (wa a))
    by (intros a Ha; rewrite <- (mrd_rel rsegs m _ _ REL); exact (HROc a Ha)).
  assert (HMI0 : mem_inv rsegs (normalize rsegs m)) by apply mem_inv_normalize.
  assert (HAC0 : asan_cells (normalize rsegs m)) by exact (proj1 (r14_rel_cells m _ REL) HAC).
  assert (HSW0 : shadow_rw (normalize rsegs m)) by exact (proj1 (r14_rel_sw m _ REL) HSW).
  assert (HADW0 : addressable (normalize rsegs m) (S - CM_K) CM_K) by exact (proj1 (r14_rel_ad m _ _ _ REL) HADW).
  assert (HADf0 : addressable (normalize rsegs m) phi 50) by exact (proj1 (r14_rel_ad m _ _ _ REL) HADf).
  assert (HADT0 : addressable (normalize rsegs m) CM_T 3256) by exact (proj1 (r14_rel_ad m _ _ _ REL) HADT).
  assert (HADB0 : addressable (normalize rsegs m) REAC_CTRL_PARSE_BC 6)
    by exact (proj1 (r14_rel_ad m _ _ _ REL) HADB).
  assert (HRB0 : bytes_at rsegs (normalize rsegs m) REAL_BCMP (le8 (wa BCMP)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRB).
  assert (HRM0 : bytes_at rsegs (normalize rsegs m) REAL_MEMCMP (le8 (wa MEMCMP)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRM).
  assert (HGC0 : bytes_at rsegs (normalize rsegs m) GOT_CF (le8 (wa CF)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HGC).
  assert (HC2540 : bytes_at rsegs (normalize rsegs m) (CF + 254) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC254).
  assert (HC2550 : bytes_at rsegs (normalize rsegs m) (CF + 255) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC255).
  assert (HFP0 : fp [0%nat; 1%nat; 2%nat] (normalize rsegs m) (bv_unsigned tp) FS (S - CM_K) S
                   (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D phi len))
    by exact (proj1 (r14_rel_fp _ m _ _ _ _ _ _ _ REL) HFP).
  assert (HTLS0 : reac_box_catalogue_match_tls (normalize rsegs m) (bv_unsigned tp) FS (S - CM_K) S)
    by exact (r14_rel_tls m _ _ _ _ _ REL HTLS).
  step. (* 81830 mv a0,s8 *)
  step. (* 81834 mv a1,s2 *)
  step. (* 81838 jal 84498 <reac_box_catalogue_match> *)
  pose proof CMC as HC. unfold reac_box_catalogue_match_contract, REAC_BOX_CATALOGUE_MATCH in HC.
  eapply evt_mono.
  { eapply (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_asan HROA).
    eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST0 | exact HROM | exact Hfb | exact HROc0 | exact HMI0 | exact HAC0 | exact HSW0
               | exact HADW0 | exact HADT0 | exact HADB0 | exact HRB0 | exact HRM0 | exact HGC0 | exact HC2540
               | exact HC2550 | exact HFP0 | exact HTLS0
               | (intros _; split; [lia|]; split; [lia|]; split; [exact HFB0 | exact HAPART])
               | (intros _; split; [exact HADf0 | exact HAPP50])
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' (s0' & PO & HREL & HROS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU0 & WM0 & MI0 & ST0 & AC0 & SW0 & AD0 & FP0 & TL0).
  subst s0'.
  destruct HREL as (ER & EF & EP & ES & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ES, EV, EC, ERo,
    HMR.
  assert (Ems : ms' = MS (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms') (ms_mem ms')
                         (ms_rom ms')) by exact (r14_ms_eta ms' ES).
  rewrite ER, EF, EP, EC, EV, ERo in Ems.
  replace (ret_pc (Z_to_bv 64 0x8183c)) with (Z_to_bv 64 0x8183c) in Ems
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  remember (ms_mem ms') as mf eqn:Emf. clear Emf.
  (* the post on the real memory *)
  assert (MUf : munch (r14_W S FS) m mf) by exact (r14_rel_munch _ m _ mf m0' REL HMR MU0 HROS).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mf.
  split; [exact Ems|].
  split; [exact MUf|].
  split.
  { apply (r14_rel_wmono (r14_W S FS) m _ mf m0' REL HMR MUf WM0).
    intros x E0. exact (r14_W_ro S FS x HFSgt ltac:(lia) E0). }
  split; [exact (r14_ro_agree_same m mf HROA HROS)|].
  split; [exact (proj2 (r14_rel_stk mf m0' (S - CM_K) S HMR ltac:(lia) ltac:(lia)) ST0)|].
  split; [exact (proj2 (r14_rel_cells mf m0' HMR) AC0)|].
  split; [exact (proj2 (r14_rel_sw mf m0' HMR) SW0)|].
  split; [exact (proj2 (r14_rel_ad mf m0' _ _ HMR) AD0)|].
  exact (proj2 (r14_rel_fp _ mf m0' _ _ _ _ _ _ HMR) FP0).
Qed.

(* ---- The segment lemma. ---- *)

Section R14S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CMC : reac_box_catalogue_match_contract.

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r14_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ ACw.a_in_img a /\ ~ ACw.a_on_img_page a /\
    ~ ACw.a_in_fs ACw.ASYMS mem a.
Proof. exact (ACw.a_laws_blocks _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r14_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  ACw.GT <= b /\ b + ACw.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + ACw.FS_SIZE -> app_mem a.
Proof. exact (ACw.a_laws_fs_place _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r14_law_fs_ok : forall H mem md FS, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> ACw.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hb.
  exact (proj1 (ACw.a_laws_fs_state _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hb)).
Qed.

Lemma r14_law_fs_store : forall H mem mem' md FS, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACw.a_store_ok H (law_lo mem md) a -> ~ (FS <= a < FS + ACw.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> ACw.a_fs_ok mem' FS ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACw.a_laws_fs_store _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* The frame [fr, fr + 3136) and its 392 shadow bytes: the left list of the fp_dj that Tac_fsfree.fra_fp gives (the
   frame apart from the side-stack bytes of the callee's classes 0, 1, 2). *)
Definition r14_FRW (fr : Z) : list ivl := [(fr, fr + FRAME_BYTES); (Sfr fr, Sfr fr + FRAME_SHADOW)].

(* The tail block of Inv_A81768_at and of Inv_A8183c_at (SlotInv.v push 13B, the same text on both cuts): the R21
   latch / tail facts, the spills the R6 head Inv_A815cc_at reads on the latch's back edge, PRO and the
   loop-carried RXS.  The call keeps s5 and every spill [s1 + off] (above sp), the frame cells at fr + 2688 /
   fr + 2768 / fr + 3040 / fr + 3056 (frame bytes, off the call's writes), the shadow bytes of the id record, of
   our[] and of the fragment record at fr + 2256 are the frame's, apart from the call's writes, and the input block
   and its shadow bytes are a live heap block's, apart from the call's writes as the block at Phi_r is. *)
Definition R14XS (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 128 (fr + 544) /\ PRO g fr regs m /\ spill regs m 104 0x21140 /\
  spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\ rg regs 21 (fr + 2176) /\
  spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
  (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
  spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
  (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
  spill regs m 152 (Sfr fr + 68) /\ addressable m (fr + 2176) 38 /\
  RXS g fr regs m.

(* PRO (push 13B, push 14D) across a run that keeps the spills [A + 32] .. [A + 280), our[]'s 6 bytes addressable
   and the input block: its bytes, and its addressability when it is a live block of the entry heap. *)
Lemma r14_pro_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha6 Hb Hia
    (H40 & H120 & H136 & H160 & H168 & H176 & H200 & H248 & HA6 & HIN & HG & H184 & H256 & H264 & H272 & H32).
  split; [exact (Hs 40 _ ltac:(lia) H40)|].
  split; [exact (Hs 120 _ ltac:(lia) H120)|].
  split; [exact (Hs 136 _ ltac:(lia) H136)|].
  split; [exact (Hs 160 _ ltac:(lia) H160)|].
  split; [exact (Hs 168 _ ltac:(lia) H168)|].
  split; [exact (Hs 176 _ ltac:(lia) H176)|].
  split; [exact (Hs 208 _ ltac:(lia) H200)|].
  split; [exact (Hs 248 _ ltac:(lia) H248)|].
  split; [exact (Ha6 HA6)|].
  split; [exact (Hb (fun Hn => proj1 (HG Hn)) HIN)|].
  split; [intros Hn; destruct (HG Hn) as (HH & HA); split; [exact HH | exact (Hia HH HA)]|].
  split; [exact (Hs 184 _ ltac:(lia) H184)|].
  split; [exact (Hs 256 _ ltac:(lia) H256)|].
  split; [exact (Hs 264 _ ltac:(lia) H264)|].
  split; [exact (Hs 272 _ ltac:(lia) H272) | exact (Hs 32 _ ltac:(lia) H32)].
Qed.

(* RXS (push 10) across a run that keeps the spills [A + 0] .. [A + 224) and the fragment record's addressability. *)
Lemma r14_rxs_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 0 <= off <= 216 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  RXS g fr regs m -> RXS g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA).
  split; [exact (Hs 48 _ ltac:(lia) H48)|].
  split; [exact (Hs 56 _ ltac:(lia) H56)|].
  split; [exact (Hs 88 _ ltac:(lia) H88)|].
  split; [exact (Hs 80 _ ltac:(lia) H80)|].
  split; [exact (Hs 72 _ ltac:(lia) H72)|].
  split; [exact (Hs 8 _ ltac:(lia) H16)|].
  split; [exact (Hs 0 _ ltac:(lia) H8)|].
  split; [exact (Hs 200 _ ltac:(lia) H192)|].
  split; [exact (Hs 216 _ ltac:(lia) H216) | exact (Ha HA)].
Qed.

Lemma r14_xs_keep : forall g fr regs regs' m m',
  (forall off v, spill regs m off v -> 0 <= off -> off + 8 <= 416 -> spill regs' m' off v) ->
  getr regs' 21 = getr regs 21 -> (addressable m (fr + 2176) 38 -> addressable m' (fr + 2176) 38) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  (forall a n bs, fr <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
     rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs]) ->
  R14XS g fr regs m -> R14XS g fr regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs regs' m m' Hs E21 Had Had6 Hinb Hina Had72 Hrw
    (H128 & HPRO & H104 & H96 & H64 & H21 & H144 & H208 & (idb & Hidb) & (junk & Hjk) & H280 & H240 &
     (jy & Hjy) & (sc & Hsc) & H152 & H38 & HRXS).
  split; [exact (Hs 128 _ H128 ltac:(lia) ltac:(lia))|].
  split; [exact (r14_pro_keep g fr regs regs' m m' (fun off v Ho H => Hs off v H ltac:(lia) ltac:(lia))
                  Had6 Hinb Hina HPRO)|].
  split; [exact (Hs 104 _ H104 ltac:(lia) ltac:(lia))|].
  split; [exact (Hs 96 _ H96 ltac:(lia) ltac:(lia))|].
  split; [exact (Hs 64 _ H64 ltac:(lia) ltac:(lia))|].
  split; [unfold rg in *; rewrite E21; exact H21|].
  split; [exact (Hs 144 _ H144 ltac:(lia) ltac:(lia))|].
  split; [exact (Hs 192 _ H208 ltac:(lia) ltac:(lia))|].
  split; [exists idb; exact (Hrw (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) Hidb)|].
  split; [exists junk; exact (Hrw (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) Hjk)|].
  split; [exact (Hs 280 _ H280 ltac:(lia) ltac:(lia))|].
  split; [exact (Hs 240 _ H240 ltac:(lia) ltac:(lia))|].
  split; [exists jy; exact (Hrw (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) Hjy)|].
  split; [exists sc; exact (Hrw (fr + 3056) 32%nat sc ltac:(lia) ltac:(lia) Hsc)|].
  split; [exact (Hs 152 _ H152 ltac:(lia) ltac:(lia))|].
  split; [exact (Had H38)|].
  exact (r14_rxs_keep g fr regs regs' m m' (fun off v Ho H => Hs off v H ltac:(lia) ltac:(lia)) Had72 HRXS).
Qed.

(* The spill base A of FRA is in range, at or above sp and 416 bytes below the entry sp S (Seg/P7.v fra_A). *)
Lemma r14_fra_A : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ ACw.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\ A + 416 <= g_S g.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  pose proof (u64_range (getr regs 2)) as Hu.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  unfold ACw.aspZ in *. exists A.
  split; [exact Hr9|]. split; [unfold APPMEM_END in *; lia|].
  split; [lia|]. split; [exact Hfa | exact HA416].
Qed.

(* The sp facts the callee contract asks for (Seg/P7.v fra_sp). *)
Lemma r14_fra_sp : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  0 <= ACw.aspZ regs < 2 ^ 64 /\ ACw.aspZ regs mod 16 = 0 /\ ACw.aspZ regs <= APPMEM_END /\
  HIGHMEM_BEG <= ACw.aspZ regs - FN_STACK /\ stk rsegs mem (ACw.aspZ regs - FN_STACK) (ACw.aspZ regs).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & Hstk).
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))
    (hb ++ g_H g) mem md ltac:(destruct HFRA as (A & sp & s5 & _ & HAH & _); exact HAH)) as Hhi.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  split; [unfold ACw.aspZ; exact (u64_range (getr regs 2))|].
  split; [rewrite Haspz; exact Hspm|].
  split; [rewrite Haspz; lia|].
  split; [lia | exact Hstk].
Qed.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame body (the low image, the frame
   header, the spills [A + 16] / [A + 24] / [A + 304], the saved registers) and keeps every shadow byte readable,
   given the new frame-shadow list, the run's heap invariant and stack-low bound, the entry window still backed, the
   registered globals and the slot window outside the frame still addressable, and the side arm's frame record
   FSREC kept (Seg/R3.v r3_fra; push 5b: no mem_inv). *)
Lemma r14_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 16 <= x < bv_unsigned (getr regs 9) + 32 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 304 <= x < bv_unsigned (getr regs 9) + 312 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, g_S g - AFw.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AFw.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HrecK E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold ACw.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r14_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

Lemma seg_R14 : forall b, Hat B APIf ra (Inv_A8183c_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A81768_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & i & regs & mem & md & fr & Ec & HFRA & HENT &
    ((Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & Hi32 & H10 & H12 & H13) & Hb0 & Hi & H11 & HRF &
     Hs112 & Hs16 & Hs8 & Hs192 & Hs216 & HAD2528 & HXS)).
  subst c. subst b.
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  (* the model facts of turn 0 *)
  pose proof HRF as (HRFb & H18).
  pose proof HRFb as (HRB & Hnz & H24 & HF).
  pose proof HRB as (_ & HCUR' & HOUR' & H23' & HIDB & HFGB).
  destruct (a_rtn (g_in g) 0 Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) 0) with (rnb g 0) in Hnb, HLF.
  (* FRA's content *)
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hstklo0 & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (r14_fra_sp g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HspR & Hspm & HspA & HspH & Hwin1).
  destruct (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct (r14_fra_A g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (A & Hr9 & HA64 & HspAle & HfrA3 & HA416).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (EA : A = A') by (apply (r14_rg_inj regs 9 A A' Hr9 Hr9' HA64); unfold stk in Hwin; lia).
  subst A'.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HCMK : CM_K = 9136) by reflexivity.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HSZc : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HHMB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAPE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HLME : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (HGTv : ACw.GT = 0x5fe000) by reflexivity.
  assert (HAK : ASAN_K = 0x7fff8000) by reflexivity.
  (* ---- the call's side-stack package from FRA (Tac_fsfree.fra_fp): the classes 0, 1, 2 (the callee takes a
     class-2 frame, reac_ctrl_parse a class-1 one, reac_box_model_block a class-0 one), K = CM_K, the callee's
     window as the write range (inside the slot window: S - 4096 < sp <= A <= S) and the record's 50 bytes at
     Phi_r as the data range (inside the cut's block (Phi_r, n_0)) ---- *)
  assert (HCS : forall c, In c [0%nat; 1%nat; 2%nat] -> (c <= 5)%nat).
  { intros c' Hc'. cbn [In] in Hc'. destruct Hc' as [<- | [<- | [<- | []]]]; lia. }
  assert (HKr : 8 <= CM_K <= FN_STACK) by lia.
  assert (HWr : forall w, In w (reac_box_catalogue_match_W (ACw.aspZ regs)) ->
     (g_S g - AFw.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
     (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
  { intros w Hw. unfold reac_box_catalogue_match_W in Hw. cbn [In] in Hw. destruct Hw as [<- | []].
    left. cbn [fst snd]. rewrite Haspz. lia. }
  assert (HDr : forall d, In d (reac_box_catalogue_match_D phi (rnb g 0)) -> snd d <= ACw.GT \/
     (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
     (fst d < snd d /\ exists p n, In (p, n) (hb1 phi (rnb g 0) ++ g_H g) /\ p <= fst d /\ snd d <= p + n)).
  { intros d Hd. unfold reac_box_catalogue_match_D in Hd. revert Hd.
    destruct (rnb g 0 <? 50) eqn:E50; intros Hd; [destruct Hd|]. apply Z.ltb_ge in E50.
    cbn [In] in Hd. destruct Hd as [<- | []]. right; right. cbn [fst snd].
    split; [lia|]. exists phi, (rnb g 0).
    split; [unfold hb1; apply in_or_app; left; apply in_eq | lia]. }
  destruct (Tac_fsfree.fra_fp B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md [0%nat; 1%nat; 2%nat] CM_K
              (reac_box_catalogue_match_W (ACw.aspZ regs)) (reac_box_catalogue_match_D phi (rnb g 0))
              HFRA HCS HKr HWr HDr) as (FS & HFP & HTLS0 & HFRW0 & _).
  assert (HTLS : reac_box_catalogue_match_tls mem (ACw.as_tp ACw.ASYMS) FS (ACw.aspZ regs - CM_K) (ACw.aspZ regs))
    by exact HTLS0.
  assert (HFRWdj : fp_dj (r14_FRW fr) (fp_w [0%nat; 1%nat; 2%nat] FS)) by exact HFRW0.
  clear HCS HKr HWr HDr HTLS0 HFRW0.
  (* the base FS is the word at tp (fp's tp bytes), in application memory (fp's fs_place) *)
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & Htp8 & Hfsp & _).
  assert (HFSr : 0 <= FS < 2 ^ 64).
  { destruct Hfsp as (Hfs0 & _ & _ & Hfsa & _).
    assert (Ha : app_mem FS) by (apply Hfsa; unfold SMC.FS_SIZE; lia).
    unfold app_mem in Ha. lia. }
  assert (HFSw : word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS).
  { pose proof (KindBGlue.bytes_at_le8_word rsegs mem _ _ Htp8) as Hw.
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in Hw by lia. exact Hw. }
  clear DT0 TS0 C0 T0 DB0 k0 Htp8 Hfsp.
  unfold ACw.aspZ in Haspz, HFP, HTLS, HspR, Hspm, HspA, HspH, Hwin1, Hplace, HspAle, Hstklo0.
  rewrite Haspz in HFP, HTLS, HspR, Hspm, HspA, HspH, Hwin1, Hplace, HspAle, Hstklo0.
  (* the side stack's placement *)
  destruct (r14_law_fs_place (hb1 phi (rnb g 0) ++ g_H g) mem md FS HAH HFSw HFSr)
    as (HGTFS & HFShi & HFSmod & HFSapp).
  assert (HFSsp : FS + FS_SIZE <= sp - FN_STACK) by lia.
  assert (HFSw2 : FS + FS_SIZE <= sp - CM_K) by lia.
  assert (HFSapp' : forall a, FS <= a < FS + FS_SIZE -> app_mem a)
    by (intros a Ha; apply HFSapp; lia).
  assert (HWapp : forall a, sp - CM_K <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; unfold HIGHMEM_BEG in *; lia).
  (* the callee's window is addressable: FRA's slot-window conjunct byte by byte, the frame being apart from the
     window (fra_frame at K = CM_K) *)
  assert (HADW : addressable mem (sp - CM_K) CM_K).
  { assert (Hfrw0 : fr + FRAME_BYTES <= sp - CM_K \/ sp <= fr) by (apply Hplace; unfold FN_STACK; lia).
    apply r14_addr_of1; [lia | lia | lia |].
    intros k Hk. apply HWA; lia. }
  (* the window and the ROM *)
  assert (HSTw : stk rsegs mem (sp - CM_K) sp) by (apply (r14_stk_sub mem (sp - FN_STACK)); [exact Hwin1 | lia]).
  assert (HROM : forall a, sp - CM_K <= a < sp -> seg_rom rsegs (wa a) = None).
  { intros a Ha. apply r14_rom_none; unfold HIGHMEM_BEG, APPMEM_END in *; lia. }
  (* the catalogue bytes are the image's (the GNU_RELRO range) *)
  assert (HROc : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs mem (wa a) = seg_rom rsegs (wa a)).
  { intros a Ha. unfold CM_T in Ha.
    pose proof (Hgimg a ltac:(exists 0x9e348, 9344; split;
                              [unfold AFw.frame_RELRO; cbn [In]; repeat (first [ (left; reflexivity) | right ]) | lia])) as H.
    rewrite SEGS in H. exact H. }
  (* the registered globals the callee reads *)
  assert (HADT : addressable mem CM_T 3256).
  { apply (r14_ag_addr mem CM_T 3256 HAGf);
      [ unfold AFw.frame_AG; cbn [In]; repeat (first [ (left; reflexivity) | right ])
      | unfold CM_T; lia | lia | unfold CM_T, APPMEM_END; lia ]. }
  assert (HADB : addressable mem REAC_CTRL_PARSE_BC 6).
  { apply (addressable_prefix mem REAC_CTRL_PARSE_BC 7 6); [|lia].
    apply (r14_ag_addr mem REAC_CTRL_PARSE_BC 7 HAGf);
      [ unfold AFw.frame_AG; cbn [In]; repeat (first [ (left; reflexivity) | right ])
      | unfold REAC_CTRL_PARSE_BC; lia | lia | unfold REAC_CTRL_PARSE_BC, APPMEM_END; lia ]. }
  (* the runtime's cells *)
  destruct HRT as (HACm & HSWm & _ & HCF0 & _ & HREAL0 & _).
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  assert (Hsub : forall (m0 : word -> option byte) (a : Z) bs (k0 j0 : nat),
            bytes_at rsegs m0 a bs -> (k0 + j0 <= length bs)%nat ->
            bytes_at rsegs m0 (a + Z.of_nat k0) (firstn j0 (skipn k0 bs))).
  { intros m0 a bs k0 j0 (Ha & HL & H) Hkj.
    assert (Lf : length (firstn j0 (skipn k0 bs)) = j0) by (rewrite length_firstn, length_skipn; lia).
    split; [lia|]. split; [rewrite Lf; lia|].
    intros ii Hii. rewrite Lf in Hii.
    replace (a + Z.of_nat k0 + Z.of_nat ii) with (a + Z.of_nat (k0 + ii)) by lia.
    rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 ii j0) as [_|Cc]; [|lia].
    rewrite nth_error_skipn. reflexivity. }
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (Hsub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14%nat 1%nat HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (Hsub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15%nat 1%nat HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (Etp : bv_unsigned (getr regs 4) = ACw.as_tp ACw.ASYMS).
  { rewrite Hr4. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit. unfold ACw.as_tp, ACw.ASYMS. cbn. lia. }
  (* the block at Phi_r *)
  destruct (a_hb B APIf ra g fr phi (rnb g 0) regs mem md HFRA) as (Hphinz & Hphi4k & Hphistk & Hphiend & Hphib).
  assert (Hsz : ACw.a_size (rnb g 0) = rnb g 0) by (unfold ACw.a_size; lia).
  pose proof HHB as (_ & HAphi0). pose proof HAphi0 as HAphi. rewrite Hsz in HAphi.
  assert (HA50 : addressable mem phi 50) by (apply (addressable_prefix mem phi (rnb g 0) 50 HAphi); lia).
  assert (HA18 : addressable mem (phi + 18) 32)
    by (apply (addressable_sub mem phi (rnb g 0) 18 32 HAphi); lia).
  assert (Hphiapp : forall a, phi <= a < phi + rnb g 0 -> app_mem a)
    by (intros a Ha; exact (proj1 (Hphib a Ha))).
  assert (HAPP50 : app_mem (phi + 50)).
  { pose proof (Hphiapp (phi + 50) ltac:(lia)) as H. exact H. }
  assert (Hphi64 : phi + 50 <= APPMEM_END).
  { pose proof (Hphiapp (phi + 49) ltac:(lia)) as H.
    unfold app_mem in H. unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* the block is apart from the side stack (a_laws_blocks) and below the callee's window *)
  assert (HphiFS : forall a, phi <= a < phi + rnb g 0 -> ~ (FS <= a < FS + FS_SIZE)).
  { intros a Ha HC.
    destruct (r14_law_blocks (hb1 phi (rnb g 0) ++ g_H g) mem md phi (rnb g 0) HAH
                ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (_ & _ & _ & _ & Hb).
    destruct (Hb a Ha) as (_ & _ & _ & _ & Hnfs). apply Hnfs.
    exact (a_fs_in ACw.ASYMS mem FS a HFSw HFSr ltac:(unfold ACw.FS_SIZE; lia)). }
  assert (Hphiwin : phi + rnb g 0 <= sp - CM_K) by lia.
  (* the 50 bytes of the record *)
  change (Z.of_nat 0) with 0 in HF, HLF.
  assert (HFB : bytes_at rsegs mem phi (rt_g (g_in g) 0)).
  { unfold rt_g. rewrite (b3_fr50_eq (rt_F (g_in g) 0) ltac:(lia)).
    pose proof HF as HF'. rewrite <- (firstn_skipn 50 (rt_F (g_in g) 0)) in HF'.
    exact (proj1 (proj1 (bytes_at_app rsegs mem phi _ _) HF')). }
  assert (HFBlen : length (rt_g (g_in g) 0) = 50%nat) by apply fr50_length.
  (* the loop's 32 bytes and their block sum *)
  destruct (b3_blk_at mem phi (rt_F (g_in g) 0) HF ltac:(lia)) as (HBL & HBLlen).
  rewrite <- (b3_rt_g (g_in g) 0) in HBL, HBLlen.
  pose proof (B3Rtm.a_rtm_sum (g_in g) 0 ltac:(lia)) as HSUM.
  pose proof (B3Rtm.a_rtm_want (g_in g)) as HWANT.
  (* run the segment *)
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81768) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8183c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 18 = getr regs 18 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 10 = Z_to_bv 64 (mrow (g_in g)) /\
       munch (r14_W sp FS) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - CM_K) sp /\ asan_cells mem' /\ shadow_rw mem' /\
       addressable mem' (sp - CM_K) CM_K /\
       fp [0%nat; 1%nat; 2%nat] mem' (ACw.as_tp ACw.ASYMS) FS (sp - CM_K) sp
          (reac_box_catalogue_match_W sp) (reac_box_catalogue_match_D phi (rnb g 0)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in H10, H11, H12, H13, H18, H24, Hr26.
    eapply evt_mono.
    + eapply evt_cut.
      { apply (r14_head (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
                 (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
                 (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
                 (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                 (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
                 (getr regs 31) fp_regs fp_csr mem phi (skipn 18 (rt_g (g_in g) 0)) i);
          [ exact H10 | rewrite H11; rewrite r14_rsum; reflexivity | exact H12 | exact H13 | exact Hr26
          | exact Hi | exact HBLlen | exact HBL | exact HA18 | exact HSUM ]. }
      intros ms' (a4' & a5' & ->).
      apply (r14_call CMC) with (phi := phi) (len := rnb g 0) (S := sp) (FS := FS)
              (fb := rt_g (g_in g) 0).
      * exact H24.
      * exact H18.
      * exact Hr2.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact Hspm.
      * lia.
      * exact HSTw.
      * exact HROM.
      * exact HFBlen.
      * exact HFB.
      * left. lia.
      * exact HROc.
      * exact Hro.
      * exact HACm.
      * exact HSWm.
      * lia.
      * lia.
      * lia.
      * exact HADW.
      * exact HA50.
      * exact HAPP50.
      * exact HADT.
      * exact HADB.
      * exact HRBc.
      * exact HRMc.
      * exact HGOTCF.
      * exact HC254.
      * exact HC255.
      * rewrite Etp. exact HFP.
      * rewrite Etp. exact HTLS.
    + intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Hms & MUq & WMq & MIq & STq & ACq & SWq & ADq & FPq).
      assert (EW : want CM_T (rnb g 0) (rt_g (g_in g) 0) = mrow (g_in g)) by exact HWANT.
      do 3 eexists.
      split; [exact Hms|].
      split; [reflexivity|].
      do 13 (split; [reflexivity|]).
      split; [rewrite <- EW; reflexivity|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact MIq|]. split; [exact STq|].
      split; [exact ACq|]. split; [exact SWq|]. split; [exact ADq|]. rewrite Etp in FPq. exact FPq.
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K18 & K21 & K22 & K23 & K24 & K25 & K10 &
       MU & WM & MI' & ST' & AC' & SW' & AD' & FP') Hreg Hmat.
    subst pc'.
    (* ---- the bytes the exit cut needs are outside the call's writes ---- *)
    assert (HSA : sp <= APPMEM_END) by lia.
    assert (OUTapp : forall x, app_mem x -> ~ (sp - CM_K <= x < sp) ->
              ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
              outside (r14_W sp FS) x).
    { intros x Hx H1 H2 H3 H4.
      exact (r14_out_app sp FS x ltac:(lia) HFSw2 HSA HFSapp' HWapp Hx H1 H2 H3 H4). }
    assert (OUThi : forall x, sp <= x -> outside (r14_W sp FS) x)
      by (intros x Hx; exact (r14_out_hi sp FS x ltac:(lia) HFSw2 HSA ltac:(unfold HIGHMEM_BEG in *; lia) Hx)).
    assert (OUTlo : forall x, 0 <= x < 6283264 -> outside (r14_W sp FS) x).
    { intros x Hx. apply OUTapp;
        [unfold app_mem, LOWMEM_END; left; lia | unfold HIGHMEM_BEG in *; lia
         | unfold ACw.GT in HGTFS; lia | unfold ACw.GT in HGTFS; lia | unfold ACw.GT in HGTFS; lia]. }
    (* the frame and its 392 shadow bytes: the cut's fp_dj and the frame's placement *)
    assert (Hfrdj : fr + FRAME_BYTES <= sp - CM_K \/ sp <= fr) by (apply Hplace; unfold FN_STACK; lia).
    assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
    assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
    { intros x Hx.
      assert (Ex : shadow_addr (fr + 8 * (x - Sfr fr)) = x).
      { unfold shadow_addr, Sfr, shadow_addr.
        replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with ((x - (fr / 8 + ASAN_K)) * 8 + fr) by lia.
        rewrite Z.div_add_l by lia. lia. }
      rewrite <- Ex. apply shadow_of_app. apply Hfrapp.
      unfold Sfr, shadow_addr in Hx |- *.
      remember (x - (fr / 8 + ASAN_K)) as y eqn:Ey. assert (0 <= y < FRAME_SHADOW) by lia. clear Ey.
      lia. }
    assert (OUTfrw : forall x, fr <= x < fr + FRAME_BYTES \/ Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
              outside (r14_W sp FS) x).
    { intros x Hx. apply r14_out_dj.
      - destruct Hx as [Hx|Hx]; [lia|].
        intros HC. exact (app_not_shadow x (HWapp x HC) (HshIS x Hx)).
      - destruct Hx as [Hx|Hx].
        + exact (fl_dj_out_r (r14_FRW fr) _ fr (fr + FRAME_BYTES) x HFRWdj (or_introl eq_refl) Hx).
        + exact (fl_dj_out_r (r14_FRW fr) _ (Sfr fr) (Sfr fr + FRAME_SHADOW) x HFRWdj
                   (or_intror (or_introl eq_refl)) Hx).
      - destruct Hx as [Hx|Hx].
        + intros HC. apply (app_not_shadow x (Hfrapp x Hx)).
          apply (r14_shadow_ivl (sp - CM_K) sp x); [exact HWapp | lia | exact HC].
        + unfold Sfr in Hx.
          exact (r14_sh_dj fr (sp - CM_K) sp x Hfr8 ltac:(unfold ACw.GT in HGTfr; lia)
                   ltac:(unfold HIGHMEM_BEG in *; lia) ltac:(lia) Hfrdj Hx). }
    (* the block at Phi_r *)
    assert (OUTphi : forall x, phi <= x < phi + rnb g 0 -> outside (r14_W sp FS) x).
    { intros x Hx. apply OUTapp.
      - exact (Hphiapp x Hx).
      - lia.
      - pose proof (HphiFS x Hx). lia.
      - pose proof (HphiFS x Hx). lia.
      - pose proof (HphiFS x Hx). lia. }
    assert (HFS8 : FS mod 8 = 0) by (revert HFSmod; clear; Z.div_mod_to_equations; lia).
    assert (HCMK8 : (sp - CM_K) mod 8 = 0)
      by (revert Hspm; unfold CM_K; clear; Z.div_mod_to_equations; lia).
    assert (OUTphish : forall x, phi <= x < phi + rnb g 0 -> outside (r14_W sp FS) (shadow_addr x)).
    { intros x Hx.
      exact (r14_out_sh sp FS x ltac:(lia) HFS8 HFSw2 HCMK8 HSA HFSapp' HWapp (Hphiapp x Hx)
               (HphiFS x Hx) ltac:(lia)). }
    (* the frame's own shadow bytes of [fr + 2528, fr + 2540) *)
    assert (OUT2528 : forall k, 0 <= k < 12 -> outside (r14_W sp FS) (shadow_addr (fr + 2528 + k))).
    { intros k Hk. apply OUTfrw. right.
      unfold Sfr, shadow_addr. revert Hfr8 HFSv. clear - Hk. Z.div_mod_to_equations. lia. }
    (* the registered globals' shadow bytes are below the side stack and the window *)
    assert (OUTag : forall a, in_globals AFw.frame_AG a -> outside (r14_W sp FS) (shadow_addr a)).
    { intros a Hin.
      assert (Har : 0x21140 <= a < 0x9f8e8).
      { destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_AG in Hil. cbn in Hil.
        repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]). destruct Hil. }
      exact (r14_out_sh sp FS a ltac:(lia) HFS8 HFSw2 HCMK8 HSA HFSapp' HWapp
               ltac:(unfold app_mem; left; lia) ltac:(lia) ltac:(lia)). }
    (* ---- the heap invariant and the stack-low bound across the call ---- *)
    assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    assert (HFSok : ACw.a_fs_ok mem FS).
    { exact (r14_law_fs_ok (hb1 phi (rnb g 0) ++ g_H g) mem md FS HAH HFSw HFSr). }
    assert (HFSok' : ACw.a_fs_ok mem' FS).
    { exact (r14_fs_ok mem mem' sp FS (ACw.as_tp ACw.ASYMS) _ _ HFSok MU FP' HFSw2 HSA
               ltac:(unfold HIGHMEM_BEG in *; lia)). }
    assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
              ~ ACw.a_store_ok (hb1 phi (rnb g 0) ++ g_H g)
                  (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              ~ (FS <= a < FS + ACw.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + ACw.FS_SIZE /\ a = shadow_addr bb) ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hnok Hnfs Hnsh. apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      rewrite r14_W_eq. cbn [outside].
      assert (Hfs8 : FS mod 8 = 0) by (revert HFSmod; clear; Z.div_mod_to_equations; lia).
      assert (HnotW : ~ (sp - CM_K <= a < sp)).
      { intros HC. apply Hnok. right. left. lia. }
      assert (HnotFS : ~ (FS <= a < FS + FS_SIZE)) by lia.
      assert (HnotSh : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE -> lo <= hi -> lo mod 8 = 0 ->
                ~ (shadow_addr lo <= a < shadow_addr hi)).
      { intros lo hi Hlo Hhi Hlh H8 HC. apply Hnsh.
        destruct (r14_sh_inv lo hi a H8 Hlh HC) as (Hb & Eb).
        exists (8 * (a - ASAN_K)). split; [lia | exact Eb]. }
      assert (HnotWsh : ~ (shadow_addr (sp - CM_K) <= a < shadow_addr sp)).
      { intros HC. destruct (r14_sh_inv (sp - CM_K) sp a HCMK8 ltac:(lia) HC) as (Hb & Eb).
        apply Hnok. right. right. right. exists (8 * (a - ASAN_K)). split; [exact Eb|]. right. left. lia. }
      repeat split; try (intros HC; lia);
        first [ (apply HnotSh; [lia | lia | lia | clear - Hfs8; Z.div_mod_to_equations; lia])
              | exact HnotWsh ]. }
    destruct (r14_law_fs_store (hb1 phi (rnb g 0) ++ g_H g) mem mem' md FS HAH HFSw HFSr
                Hmc Hwrit HFSok') as (HAH' & HOWN' & HSTKeq & HSTKHI').
    (* ---- ENT across the call (ent_munch): no entry block, image byte, byte at or above S, or shadow byte of
       the image, of [S, APPMEM_END) or of an entry block is in r14_W ---- *)
    assert (HENT' : ENT (fx := fx) APIf g (hb1 phi (rnb g 0)) mem' md).
    { eapply ent_munch with (W := r14_W sp FS); [exact HENT | exact HAH | exact MU | | exact HSTKeq | exact HSTKHI' |].
      - intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(bb & Hor & ->) | Hblks]]]].
        + destruct Hblkk as (q & k & ii & Hin & _ & Hii & ->).
          destruct (r14_law_blocks (hb1 phi (rnb g 0) ++ g_H g) mem md q k HAH
                      (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqend & _ & Hqb).
          destruct (Hqb (q + ii) ltac:(lia)) as (Happq & _ & _ & _ & Hnfsq).
          assert (HnFS : ~ (FS <= q + ii < FS + FS_SIZE)).
          { intros HC. apply Hnfsq.
            exact (a_fs_in ACw.ASYMS mem FS (q + ii) HFSw HFSr ltac:(unfold ACw.FS_SIZE; lia)). }
          apply OUTapp; [exact Happq | lia | lia | lia | lia].
        + pose proof (img_below_GT x Hik) as Hxg. unfold ACw.GT in Hxg. apply OUTlo. lia.
        + apply OUThi. lia.
        + assert (Hbb : app_mem bb /\ ~ (FS <= bb < FS + FS_SIZE) /\ ~ (sp - CM_K <= bb < sp)).
          { destruct Hor as [Hib|Hsb].
            - pose proof (img_below_GT bb Hib) as Hbg. unfold ACw.GT in Hbg, HGTFS.
              split; [unfold app_mem, LOWMEM_END; left; lia | split; lia].
            - split; [unfold app_mem; right; lia | split; lia]. }
          destruct Hbb as (Happb & HnFSb & HnWb).
          exact (r14_out_sh sp FS bb ltac:(lia) HFS8 HFSw2 HCMK8 HSA HFSapp' HWapp Happb HnFSb HnWb).
        + (* frame batch 2 item 9: the shadow byte of a byte of an entry block, which is app memory below stklo
             and off the side stack (a_laws_blocks), so below the callee's window *)
          destruct Hblks as (q & k & ii & Hin & _ & Hii & ->).
          destruct (r14_law_blocks (hb1 phi (rnb g 0) ++ g_H g) mem md q k HAH
                      (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqend & _ & Hqb).
          destruct (Hqb (q + ii) ltac:(lia)) as (Happq & _ & _ & _ & Hnfsq).
          assert (HnFS : ~ (FS <= q + ii < FS + FS_SIZE)).
          { intros HC. apply Hnfsq.
            exact (a_fs_in ACw.ASYMS mem FS (q + ii) HFSw HFSr ltac:(unfold ACw.FS_SIZE; lia)). }
          exact (r14_out_sh sp FS (q + ii) ltac:(lia) HFS8 HFSw2 HCMK8 HSA HFSapp' HWapp Happq HnFS ltac:(lia)).
      - intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
    (* ---- the side arm's frame record: the tp word is in the low image, the class-6 flag byte and the slot's
       last word are side-stack bytes above the classes 0-2 (fs_flag FS 6 j = FS + 36352 + j, the slot at
       FS + 6328320 + 4096 j) and below the callee's window ---- *)
    assert (HRECk : FSREC fr mem -> FSREC fr mem').
    { intros (FS' & j & Htp & HFSr' & Hj & Hfr & Hflag & Htail).
      assert (EFS : FS' = FS).
      { pose proof (r14_wm_congr mem _ FS' FS Htp HFSw) as E. rewrite !Z.mod_small in E by lia. exact E. }
      subst FS'.
      assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
      assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
      assert (Hj' : 0 <= j < 256) by (rewrite <- HM6; exact Hj).
      assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + j * 4096)
        by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
      assert (KBlo' : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
      { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
        rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact (OUTlo x ltac:(lia)). }
      exists FS, j.
      split.
      { intros k Hk. rewrite KBlo'.
        - exact (Htp k Hk).
        - unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        - unfold ACw.as_tp, ACw.ASYMS. cbn. lia. }
      split; [exact HFSr'|]. split; [exact Hj|]. split; [exact Hfr|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
        apply OUTapp; [apply HFSapp'; lia | lia | lia | lia | lia]. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. rewrite HB6 in Hx.
        apply OUTapp; [apply HFSapp'; lia | lia | lia | lia | lia]. } }
    (* ---- the slot window outside the frame stays addressable: the callee's window by its post, every other
       window byte because its shadow byte is outside r14_W (r14_out_sh) ---- *)
    assert (HWA' : forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              addressable mem' a 1).
    { intros a Ha Hnf.
      pose proof (ACw.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
      destruct (Z_lt_le_dec a (sp - CM_K)) as [H1|H1]; [|destruct (Z_lt_le_dec a sp) as [H2|H2]].
      2: { replace a with (sp - CM_K + (a - (sp - CM_K))) by lia.
           apply (addressable_sub mem' (sp - CM_K) CM_K (a - (sp - CM_K)) 1 AD'); lia. }
      all: apply (r14_addr_keep (r14_W sp FS) mem mem' a 1 (HWA a Ha Hnf) MU);
        intros k Hk; assert (Ek : k = 0) by lia; subst k; rewrite Z.add_0_r;
        apply (r14_out_sh sp FS a ltac:(lia) HFS8 HFSw2 HCMK8 HSA HFSapp' HWapp);
        [unfold app_mem; right; lia | lia | lia]. }
    (* ---- FRA at 0x8183c ---- *)
    assert (HRDsh : forall a, in_shadow a -> exists bb, mrd rsegs mem' (wa a) = Some bb)
      by (intros a Ha; exact (proj2 (SW' a Ha))).
    assert (HAG' : forall a, in_globals AFw.frame_AG a -> addressable mem' a 1).
    { intros a Hin. apply (r14_addr_keep (r14_W sp FS) mem mem' a 1 (HAGf a Hin) MU).
      intros k Hk. assert (Ek : k = 0) by lia. subst k. rewrite Z.add_0_r. exact (OUTag a Hin). }
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md).
    { apply (r14_fra g fr (hb1 phi (rnb g 0)) regs regs' mem mem' md (r14_W sp FS) HFRA MU WM
               MI').
      - assert (LOS : forall p, In p (r14_W sp FS) -> 6283264 <= fst p).
        { intros p Hp. apply (r14_W_los sp FS p); [unfold ACw.GT in HGTFS; lia | unfold HIGHMEM_BEG in *; lia
                                                   | exact Hp]. }
        unfold rt_disjoint.
        repeat match goal with |- _ /\ _ => split end;
          apply r14_dj_lo; intros p Hp; pose proof (LOS p Hp);
          unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK,
            RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
            RT_AGLOB_LEN in *; lia.
      - exact HAH'.
      - exact HSTKeq.
      - exact HRDsh.
      - destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
        eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. apply OUTfrw. right. lia.
      - exact OUTlo.
      - intros x Hx. apply OUTfrw. left. lia.
      - intros x Hx. apply OUThi. unfold rg in Hr9. rewrite Hr9, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in Hx by lia. lia.
      - intros x Hx. apply OUThi. unfold rg in Hr9. rewrite Hr9, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in Hx by lia. lia.
      - intros x Hx. apply OUThi. lia.
      - intros x Hx. destruct (Z_lt_le_dec x (sp - CM_K)) as [Hlt|Hge].
        + left. apply OUTapp.
          * pose proof (ACw.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
            unfold app_mem. right. lia.
          * lia.
          * lia.
          * lia.
          * lia.
        + destruct (Z_lt_le_dec x sp) as [Hlt2|Hge2].
          * right. destruct ST' as (_ & _ & Hst). exact (proj2 (Hst x ltac:(lia))).
          * left. apply OUThi. lia.
      - exact HAG'.
      - exact HWA'.
      - exact HRECk.
      - rewrite Hreg; exact K2.
      - rewrite Hreg; exact K3.
      - rewrite Hreg; exact K4.
      - rewrite Hreg; exact K8.
      - rewrite Hreg; exact K9.
      - rewrite Hreg; exact K19.
      - rewrite Hreg; exact K26. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 0)) regs' regs' mem' md md' HFRAm);
        try reflexivity. exact Hmat. }
    assert (HENT'' : ENT (fx := fx) APIf g (hb1 phi (rnb g 0)) mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* ---- the exit cut ---- *)
    assert (E9' : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (Ekeep : forall off v, spill regs mem off v -> 0 <= off -> off + 8 <= 416 ->
              spill regs' mem' off v).
    { intros off v (A0 & HA0 & HQ) Hoff1 Hoff2.
      assert (EA0 : A0 = A)
        by (exact (r14_spill_A regs mem A A0 off v Hr9 HA0 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                     Hoff1 Hoff2 HQ)).
      subst A0. exists A. split; [unfold rg in *; rewrite E9'; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact HQ | exact MU |].
      rewrite length_le8. intros x Hx. apply OUThi. lia. }
    assert (HOURk : OURb g fr mem').
    { unfold OURb in *. apply (a_keep (r14_W sp FS) mem mem' (fr + 2624) (OUR (g_in g)) MU);
        [|exact HOUR]. rewrite OUR_length. intros x Hx. apply OUTfrw. left. lia. }
    (* out[]'s 1492 bytes stay addressable: their shadow bytes are frame shadow bytes, outside r14_W *)
    assert (HOUTAk : OUTA fr mem').
    { apply (outa_munch fr mem mem' (r14_W sp FS) HOUTA MU).
      intros k Hk. apply OUTfrw. right.
      unfold Sfr, shadow_addr. revert Hfr8 HFSv. clear - Hk. Z.div_mod_to_equations. lia. }
    assert (HCURk : CUR g 7 regs').
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite Hreg, K22; exact Hc22 | rewrite Hreg, K25; exact Hc25]. }
    assert (H23k : rg regs' 23 (Z.of_nat 0)) by (unfold rg in *; rewrite Hreg, K23; exact H23).
    assert (HHBk : HB mem' phi (rnb g 0)).
    { split; [exact Hphinz|]. rewrite Hsz.
      apply (r14_addr_keep (r14_W sp FS) mem mem' phi (rnb g 0) HAphi MU).
      intros k Hk. apply OUTphish. lia. }
    assert (HRFbk : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs' mem').
    { apply (a_RFb_keep g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs regs' (r14_W sp FS) mem mem' MU);
        [ reflexivity | reflexivity
        | intros x Hx; apply OUTfrw; left; lia
        | intros x Hx; apply OUTphi; lia
        | rewrite Hreg; exact K22 | rewrite Hreg; exact K23 | rewrite Hreg; exact K24
        | rewrite Hreg; exact K25 | exact HRFb ]. }
    rewrite <- SEGS. apply Hexit. exists phi, regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split.
    { split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHBk|]. split; [exact H23k|].
      split; [exact HOURk|]. split; [exact HOUTAk|]. split; [exact HCURk|].
      exact (Ekeep 216 (fr + 2528) Hs216 ltac:(lia) ltac:(lia)). }
    split; [reflexivity|].
    split; [exact HRFbk|].
    split.
    { unfold a0v, rg. rewrite Hreg. exact K10. }
    split; [exact (Ekeep 112 (mrow (g_in g)) Hs112 ltac:(lia) ltac:(lia))|].
    split; [exact (Ekeep 8 (mrow (g_in g) + 16) Hs16 ltac:(lia) ltac:(lia))|].
    split; [exact (Ekeep 0 (mrow (g_in g) + 20) Hs8 ltac:(lia) ltac:(lia))|].
    split; [exact (Ekeep 200 (decl_slot fr) Hs192 ltac:(lia) ltac:(lia))|].
    split.
    { apply (r14_addr_keep (r14_W sp FS) mem mem' (fr + 2528) 12 HAD2528 MU).
      intros k Hk. exact (OUT2528 k Hk). }
    assert (H21k : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (HA38k : addressable mem (fr + 2176) 38 -> addressable mem' (fr + 2176) 38).
    { intros HA38. apply (r14_addr_keep (r14_W sp FS) mem mem' (fr + 2176) 38 HA38 MU).
      intros k Hk. apply OUTfrw. right.
      unfold Sfr, shadow_addr. revert Hfr8 HFSv. clear - Hk. Z.div_mod_to_equations. lia. }
    assert (HA6k : addressable mem (fr + 2624) 6 -> addressable mem' (fr + 2624) 6).
    { intros HA6. apply (r14_addr_keep (r14_W sp FS) mem mem' (fr + 2624) 6 HA6 MU).
      intros k Hk. apply OUTfrw. right.
      unfold Sfr, shadow_addr. revert Hfr8 HFSv. clear - Hk. Z.div_mod_to_equations. lia. }
    assert (HRWk : forall a n bs, fr <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
              rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
    { intros a n bs Ha1 Ha2 HRW. apply (r14_rwcb_keep (r14_W sp FS) mem mem' a n bs MU WM); [|exact HRW].
      intros x Hx. apply OUTfrw. left. lia. }
    (* the fragment record's 72 bytes stay addressable: their shadow bytes S(fr) + 282 .. + 290 are frame shadow
       bytes, outside r14_W *)
    assert (HA72k : addressable mem (fr + 2256) 72 -> addressable mem' (fr + 2256) 72).
    { intros HA72. apply (r14_addr_keep (r14_W sp FS) mem mem' (fr + 2256) 72 HA72 MU).
      intros k Hk. apply OUTfrw. right.
      unfold Sfr, shadow_addr. revert Hfr8 HFSv. clear - Hk. Z.div_mod_to_equations. lia. }
    (* PRO's input block: a live block of the entry heap, so application memory off the side stack and below the
       callee's window (a_laws_blocks), as the block at Phi_r; its bytes and its shadow bytes are outside r14_W *)
    assert (OUTin : In (g_p g, g_n g) (g_H g) -> forall x, g_p g <= x < g_p g + g_n g ->
              outside (r14_W sp FS) x /\ outside (r14_W sp FS) (shadow_addr x)).
    { intros Hin x Hx.
      destruct (r14_law_blocks (hb1 phi (rnb g 0) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hpend & _ & Hpb).
      destruct (Hpb x Hx) as (Happx & _ & _ & _ & Hnfsx).
      assert (HnFSx : ~ (FS <= x < FS + FS_SIZE)).
      { intros HC. apply Hnfsx.
        exact (a_fs_in ACw.ASYMS mem FS x HFSw HFSr ltac:(unfold ACw.FS_SIZE; lia)). }
      split.
      - apply OUTapp; [exact Happx | lia | lia | lia | lia].
      - exact (r14_out_sh sp FS x ltac:(lia) HFS8 HFSw2 HCMK8 HSA HFSapp' HWapp Happx HnFSx ltac:(lia)). }
    assert (HINk : (0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
              bytes_at rsegs mem (g_p g) (g_in g) -> bytes_at rsegs mem' (g_p g) (g_in g)).
    { intros Hin HIN. eapply fl_bytes; [exact HIN | exact MU |].
      intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (OUTin (Hin ltac:(lia)) x Hx)). }
    assert (HINAk : In (g_p g, g_n g) (g_H g) ->
              addressable mem (g_p g) (g_n g) -> addressable mem' (g_p g) (g_n g)).
    { intros Hin HA. apply (r14_addr_keep (r14_W sp FS) mem mem' (g_p g) (g_n g) HA MU).
      intros k Hk. exact (proj2 (OUTin Hin (g_p g + k) ltac:(lia))). }
    exact (r14_xs_keep g fr regs regs' mem mem' Ekeep H21k HA38k HA6k HINk HINAk HA72k HRWk HXS).
Qed.

End R14S.
