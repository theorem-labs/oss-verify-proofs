(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 528 of its 563 lines of code are new or changed and 361 lines of the source are left out. *)
(* Segment P7 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): 0x81bf8-0x81c1c, 10 instructions
   (v1.8 0x81b78-0x81b9c, IDENTICAL-RENUMBER: every pc +0x80, and 0x81c04 reads the spill [s1 + 192], v1.8's
   0x81b84 `ld a0,208(s1)`; both hold fragb fr = fr + 2768).
     81bf8 li s2,-1; 81bfc beq a0,s2,81c04 (taken: a0 = -1, the identity_reply result; the fall-through 81c00
     j 82bf4 to the failure exit is not reached); 81c04 ld a0,192(s1); li a1,0; li a2,0; mv a3,s7; mv a4,s8;
     mv a5,s4; 81c1c jal reac_ctrl_identity_fragment@0x84f68.
   With a1 = fr = 0 the callee refuses (fg_class = FgRefuse): it returns -1 and writes only its stack window
   [sp - 4656, sp). Both cuts are SlotInv's: the entry Inv_A81bf8 and the exit Inv_A81c20 (the entry of P8).

   The cuts carry the frozen body, the register facts the next branch reads and SlotInv's bundle XC (the
   [s1 + 280] = fr + 3040 spill and that byte addressable; no mem_inv, push 5d: p7_evt runs the callee on the
   normalized memory, MemNorm.evt_normalize). Everything else the callee premises and the FRA transport need (the
   frame's placement against the callee window, the FakeStack metadata bound, the frame bytes' writability, the
   sp-anchored stack window) comes from FRA, fra_win and fra_frame. This file also holds the pieces P8-P10 share:
   the run bridge p7_run, the FRA transport across a callee run (stk_call, a wrapper of the canonical
   Tac_b5.sl_callee_keep) and the XC transport (xc_run). Gap 4 (aslot push 11): every cut from Inv_A81bf8 to
   Inv_A81c84 also carries CUR (s6 / s9) and the frame records IDBe (fr + 2688) / FGBe (fr + 2768); stk_call carries
   them across a callee that writes only its stack window, and each run post keeps registers 22 / 25. Push 12: the
   cuts also carry the spill [s1 + 144] = fr + 2688 and the 17 addressable bytes at fr + 2691; stk_call keeps the
   spill (fra_spill144: s1 kept, the cell above sp) and the bytes (sl_addr_keep: the window is application
   memory, so no shadow byte changes). Push 13: the cuts also carry SlotInv's PRO; stk_call keeps it with P1.v's
   pro_fra (the window is at or above stklo and below the spill base A). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 P1.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- generic helpers ---- *)

Lemma p7_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma p7_stk_sub : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> stk rsegs m a hi.
Proof. intros m lo hi a (H1 & H2 & H) Ha. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

Lemma p7_rg_inj : forall regs r A A', rg regs r A -> rg regs r A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A = A'.
Proof.
  intros regs r A A' H H' HA HA'. unfold rg in *. rewrite H in H'.
  apply (f_equal (bv_unsigned (n:=64))) in H'. rewrite !MState.unsigned_lit in H' by lia. exact H'.
Qed.

Lemma fg_refuse0 : forall f pa pp pn len st g, fg_class f 0 pa pp pn len st g = FgRefuse.
Proof. intros. unfold fg_class. rewrite (Z.eqb_refl 0), Bool.orb_true_r. reflexivity. Qed.

(* ---- normalized-memory transport (push 5d): a callee contract that needs mem_inv runs on MemNorm.normalize,
   where mem_inv holds for free; these move its premises there and its post back. Above the image (0x5fe000)
   there is no read-only byte, so stk / shadow / asan cells cross unchanged (worked example a1_req_evt). *)
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma rsegs_below_gt : seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_below : forall segs top x n s,
  seg_tops_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (find_segment_below sg 0x5fe000 x n s rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

(* ro_agree survives a write that misses [0, 0x5fe000): every read-only byte lies there (ro_addr_hi). The form the
   P10 / P12 runs need, whose write sets include frame bytes (app memory at or above GT = 0x5fe000). *)
Lemma p7_ro_keep : forall W mem mem', ro_agree rsegs mem -> munch W mem mem' ->
  (forall x, 0 <= x < 0x5fe000 -> outside W x) -> ro_agree rsegs mem'.
Proof.
  intros W mem mem' Hro MU HW. apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. apply MU.
  pose proof (u64_range a) as Hu.
  destruct (Z_lt_le_dec (bv_unsigned a) 0x5fe000) as [Hlt|Hge]; [apply HW; lia|].
  exfalso. pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as Hf.
  unfold wa in Hf. rewrite Z_to_bv_bv_unsigned in Hf. rewrite Hf in Ha. discriminate.
Qed.

Lemma wview_rel_hi : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (ro_addr_hi a Ha)). split; auto.
Qed.

Lemma stk_rel_hi : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma stk_rel_hi_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma shadow_rw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma ba_rel1 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma asan_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (ba_rel1 m m0 a bs R ltac:(assumption)) end.
Qed.

(* XC is SlotInv.XC (push 5d): the code-byte pointer [s1 + 280] = fr + 3040 and that byte addressable. No
   mem_inv (a callee that needs it runs on the normalized memory, MemNorm.evt_normalize). *)

(* XC moves across a run that keeps s1, writes only app memory and never the spill [s1 + 280]. *)
Lemma xc_run : forall fr regs regs' mem mem' W,
  XC fr regs mem ->
  munch W mem mem' -> all_app W ->
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> forall x, A + 280 <= x < A + 288 -> outside W x) ->
  getr regs' 9 = getr regs 9 ->
  XC fr regs' mem'.
Proof.
  intros fr regs regs' mem mem' W HXC MU HAW HW280 E9.
  destruct HXC as (HAblk & Hadc).
  split.
  { intros A HA HAr. assert (HA0 : rg regs 9 A) by (unfold rg in *; rewrite <- E9; exact HA).
    unfold q64 in *. eapply fl_bytes; [exact (HAblk A HA0 HAr) | exact MU |].
    rewrite length_le8. intros x Hx. apply (HW280 A HA0 HAr). lia. }
  exact (sl_addr_keep mem mem' W (fr + 3040) 1 Hadc MU HAW).
Qed.

(* A spill witness A of s1 is s1's in-range value A0: they agree mod 2^64 and the 8-byte cell at A + off lies in
   [0, 2^64), which leaves only A = A0 when A0 + off < 2^64. *)
Lemma p7_spill_base : forall (regs : bvmap 5 word) (m : word -> option byte) A A0 off v,
  rg regs 9 A0 -> 0 <= A0 -> 0 <= off -> A0 + off < 2 ^ 64 ->
  rg regs 9 A -> q64 m (A + off) v -> A = A0.
Proof.
  intros regs m A A0 off v H0 HA0 Hoff HA0hi H Hq.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
  unfold rg in *. rewrite H0 in H.
  apply (f_equal (@bv_unsigned 64)) in H.
  rewrite (MState.unsigned_lit A0) in H by lia.
  rewrite MState.unsigned_lit_wrap in H.
  change (2 ^ 64) with 18446744073709551616 in *.
  revert H Hq. Z.div_mod_to_equations. lia.
Qed.

(* A spill [s1 + off] = v moves across a run that keeps s1 and does not write the cell. *)
Lemma p7_spill_run : forall regs regs' m m' W off v A0,
  spill regs m off v -> rg regs 9 A0 -> 0 <= A0 -> 0 <= off -> A0 + off < 2 ^ 64 ->
  munch W m m' -> getr regs' 9 = getr regs 9 ->
  (forall x, A0 + off <= x < A0 + off + 8 -> outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A0 (A & HA & Hq) H0 HA0 Hoff Hhi MU E9 HW.
  pose proof (p7_spill_base regs m A A0 off v H0 HA0 Hoff Hhi HA Hq) as ->.
  exists A0. split; [unfold rg in *; rewrite E9; exact H0|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

Section R.
Context {fx : FPState}.

(* Lib-evt -> SR bridge (the callee contracts live in Lib.Exec; as F18's sl_run_lib). *)
Lemma p7_run : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

End R.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The spill base A of FRA is in range, at or above sp and 416 bytes below the entry sp S. *)
Lemma fra_A : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\ A + 416 <= g_S g.
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof (u64_range (getr regs 2)) as Hu.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  unfold AC.aspZ in *. exists A.
  split; [exact Hr9|]. split; [unfold APPMEM_END in *; lia|].
  split; [lia|]. split; [exact Hfa | exact HA416].
Qed.

(* The sp facts the callee contracts ask for, from push 5's entry-anchored stack facts (fra_win) and the
   allocator's stack-high law. *)
Lemma fra_sp : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  0 <= AC.aspZ regs < 2 ^ 64 /\ AC.aspZ regs mod 16 = 0 /\ AC.aspZ regs <= APPMEM_END /\
  HIGHMEM_BEG <= AC.aspZ regs - FN_STACK /\ stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs).
Proof.
  intros g fr hb regs mem md HFRA.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & Hstk).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
    (hb ++ g_H g) mem md ltac:(destruct HFRA as (A & sp & s5 & _ & HAH & _); exact HAH)) as Hhi.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  split; [unfold AC.aspZ; exact (u64_range (getr regs 2))|].
  split; [rewrite Haspz; exact Hspm|].
  split; [rewrite Haspz; lia|].
  split; [lia | exact Hstk].
Qed.

(* The frame is app memory above the image's writable data: push 5c's SlotInv.fra_app. *)
Lemma fr_place : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
Proof.
  intros g fr hb regs mem md HFRA. eapply fra_app. exact HFRA.
Qed.

(* A spill [s1 + off] = v (off <= 400: the spill [s1 + 144] = fr + 2688 of push 12, [s1 + 192] = fragb fr of push
   14) moves across a run that keeps s1 and writes nothing at or above the spill base A (FRA's A is in range and
   416 bytes below S < APPMEM_END). *)
Lemma fra_spill : forall g fr hb regs regs' mem mem' md W off v,
  FRA B APIf ra g fr hb regs mem md -> 0 <= off <= 400 -> spill regs mem off v ->
  munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  (forall A x, rg regs 9 A -> 0 <= A < 2 ^ 64 -> A <= x -> outside W x) ->
  spill regs' mem' off v.
Proof.
  intros g fr hb regs regs' mem mem' md W off v HFRA Hoff HSP MU E9 HW.
  pose proof (u64_range (getr regs 2)) as Hu.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  unfold AC.aspZ in Haspz.
  apply (p7_spill_run regs regs' mem mem' W off v A HSP Hr9);
    [lia | lia | unfold APPMEM_END in HAPP; lia | exact MU | exact E9 |].
  intros x Hx. apply (HW A x Hr9); [unfold APPMEM_END in HAPP; lia | lia].
Qed.


(* A callee run that writes only its stack window [sp - K, sp) (K <= FN_STACK) and keeps the FRA registers keeps
   FRA (moved to the run's end model md'), the entry relation ENT, the bundle XC, our[] and the gap-4 / push-12
   facts: CUR (the run keeps s6 / s9), the spill [s1 + 144] = fr + 2688 (above sp), the 17 addressable bytes at
   fr + 2691 (the window is application memory, so no shadow byte changes) and the two frame records IDBe
   (fr + 2688, 38 bytes) / FGBe (fr + 2768, 72 bytes), frame bytes apart from the callee window (fra_frame). The
   window is inside the slot window [S - SLOT_STACK, S) (fra_win, S - 4096 < sp <= A <= S), so ent_store carries
   ENT across it and ent_mat across the run's lazy-page materialization. Pushes 13 / 14: also PRO (pro_fra), the
   spill [s1 + 192] = fragb fr (above sp) and the record ranges (fragb fr, 72) / (fr + 2688, 38) addressable. *)
Lemma stk_call : forall g fr hb regs regs' mem mem' md md' K c,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md -> XC fr regs mem -> OURb g fr mem ->
  CUR g c regs -> PRO g fr regs mem -> spill regs mem 144 (fr + 2688) -> addressable mem (fr + 2691) 17 ->
  spill regs mem 192 (fragb fr) -> addressable mem (fragb fr) 72 -> addressable mem (fr + 2688) 38 ->
  IDBe g fr RcIdentModel.ID0 mem -> FGBe g fr z72 mem ->
  0 <= K <= FN_STACK ->
  munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> wmono rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - K) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 -> getr regs' 22 = getr regs 22 -> getr regs' 25 = getr regs 25 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md' /\ XC fr regs' mem' /\ OURb g fr mem' /\
  CUR g c regs' /\ PRO g fr regs' mem' /\ spill regs' mem' 144 (fr + 2688) /\ addressable mem' (fr + 2691) 17 /\
  spill regs' mem' 192 (fragb fr) /\ addressable mem' (fragb fr) 72 /\ addressable mem' (fr + 2688) 38 /\
  IDBe g fr RcIdentModel.ID0 mem' /\ FGBe g fr z72 mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' K c HFRA HENT HXC HOUR HCUR HPRO HSP HADR HSP208 HADF HADI HIDB HFGB
    HK MU WM HST' E2 E3 E4 E8 E9 E19 E26 E22 E25 Hmat.
  destruct (fr_place g fr hb regs mem md HFRA) as (HGT & Hfapp).
  destruct (fra_A g fr hb regs mem md HFRA) as (A & HA9 & HAr & HspA & HfrA & HA416).
  destruct (fra_sp g fr hb regs mem md HFRA) as (Hspb & Hspm & HaspB & Hhi & Hwinsp).
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & _).
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & _ & _).
  destruct (sl_ah_stk B APIf ra g fr hb regs mem mem' md K HFRA HK MU WM) as (HAH' & HSTKeq).
  assert (Hro : ro_agree rsegs mem)
    by (destruct HFRA as (A' & sp' & s5' & _ & _ & Hro' & _); exact Hro').
  assert (HAHm : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md)
    by (destruct HFRA as (A' & sp' & s5' & _ & HAH0 & _); exact HAH0).
  assert (Hlok : HIGHMEM_BEG <= AC.aspZ regs - K) by (unfold FN_STACK, AF.SLOT_STACK in *; lia).
  assert (HAW : all_app [(AC.aspZ regs - K, AC.aspZ regs)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, FN_STACK, AF.SLOT_STACK in *. lia. }
  assert (Hroa : ro_agree rsegs mem').
  { apply (Tac_b5.sl_ro_keep [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' Hro MU).
    intros x Hx. cbn [outside]. split; [|exact I]. unfold LOWMEM_END, HIGHMEM_BEG in *. lia. }
  assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> outside [(AC.aspZ regs - K, AC.aspZ regs)] x).
  { intros x Hx. cbn [outside]. split; [|exact I].
    destruct (Hapart K ltac:(lia)) as [Hd|Hd]; lia. }
  assert (HWA : forall A' x, rg regs 9 A' -> 0 <= A' < 2 ^ 64 -> A' <= x ->
           outside [(AC.aspZ regs - K, AC.aspZ regs)] x).
  { intros A' x HA' HA'r Hx. rewrite (p7_rg_inj regs 9 A' A HA' HA9 HA'r HAr) in Hx.
    cbn [outside]. split; [|exact I]. lia. }
  assert (HSwin : g_S g - 4096 < AC.aspZ regs /\ AC.aspZ regs <= g_S g).
  { destruct HFRA as (A' & sp' & s5' & _ & _ & _ & _ & _ & _ & _ & _ & Haspz' &
      _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAS' & Hspa' & _ & _ & HS4' & _).
    unfold AC.aspZ in *. lia. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [outside]. split; [|exact I]. intros [H1 H2]. apply Hns.
    unfold AC.a_store_ok. right; left. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (p1_laws_store APIf (hb ++ g_H g) mem mem' md HAHm HstoreC HwmL) as (_ & Hownif & _ & HSTKhi).
  assert (HFRAm : FRA B APIf ra g fr hb regs' mem' md').
  { apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md');
      [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
       | exact Hmat].
    apply (sl_win_run B APIf ra empty FF g fr hb regs regs' mem mem' md
             [(AC.aspZ regs - K, AC.aspZ regs)] HFRA MU WM Hroa HAW).
    - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [disjoint_from]. unfold HIGHMEM_BEG in Hlok. repeat split; left; lia.
    - exact HAH'.
    - exact HSTKeq.
    - intros x Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx. apply HWfr. lia.
    - intros A' HA' HA'r x Hx. apply (HWA A' x HA' HA'r). lia.
    - intros x Hx. cbn [Frame.outside]. split; [lia | exact I].
    - exact (sl_win_stk B APIf ra g fr hb regs mem md mem' K HFRA HK MU WM HST').
    - intros Hrec. eapply fsrec_munch_lo with (W := [(AC.aspZ regs - K, AC.aspZ regs)]);
        [exact Hrec | exact HAHm
        | first [exact MU | exact (proj1 (fr_munch_ul _ mem mem') MU)
                          | exact (proj2 (fr_munch_ul _ mem mem') MU)] | | ].
      + intros x Hx. unfold HIGHMEM_BEG in Hlok.
        first [ (cbn; split; [lia | exact I])
              | (apply fr_outside_lib; cbn; split; [lia | exact I])
              | (apply (proj2 (fr_outside_lib _ x)); cbn; split; [lia | exact I]) ].
      + intros x _ _ Hx.
        first [ (cbn; split; [lia | exact I])
              | (apply fr_outside_lib; cbn; split; [lia | exact I])
              | (apply (proj2 (fr_outside_lib _ x)); cbn; split; [lia | exact I]) ].
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split; [exact HFRAm|].
  split.
  { (* ent_store states its write set in Tac_slot's flavour of munch / outside; fr_munch_ul and
       fr_outside_lib bridge this file's flavour to it. *)
    assert (HENT1 : ENT APIf g hb mem' md).
    { eapply ent_store with (W := [(AC.aspZ regs - K, AC.aspZ regs)]);
        [exact HENT | exact HFRA
        | first [exact MU | exact (proj1 (fr_munch_ul _ mem mem') MU)
                          | exact (proj2 (fr_munch_ul _ mem mem') MU)]
        | | exact HSTKeq | exact HSTKhi | exact (fun a _ Ho => proj2 (Hownif a) Ho)].
      intros x Hx. destruct (Z_lt_le_dec x (AC.aspZ regs - K)) as [Hlt|Hge].
      - left. first [ (cbn; split; [lia | exact I])
                    | (apply fr_outside_lib; cbn; split; [lia | exact I])
                    | (apply (proj2 (fr_outside_lib _ x)); cbn; split; [lia | exact I]) ].
      - destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hlt2|Hge2].
        + right. left. destruct HSwin as (HSw1 & HSw2).
          unfold FN_STACK, AF.SLOT_STACK in *. lia.
        + left. first [ (cbn; split; [lia | exact I])
                      | (apply fr_outside_lib; cbn; split; [lia | exact I])
                      | (apply (proj2 (fr_outside_lib _ x)); cbn; split; [lia | exact I]) ]. }
    eapply ent_mat; [exact HENT1 | exact Hmat]. }
  split.
  { apply (xc_run fr regs regs' mem mem' _ HXC MU HAW); [|exact E9].
    intros A' HA' HA'r x Hx. apply (HWA A' x HA' HA'r). lia. }
  split.
  { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
    rewrite OUR_length. intros x Hx. apply HWfr. lia. }
  split.
  { destruct HCUR as (Hc & H22 & H25). split; [exact Hc|]. unfold rg in *.
    split; [rewrite E22; exact H22 | rewrite E25; exact H25]. }
  split.
  { apply (pro_fra B APIf ra g fr hb regs regs' mem mem' md [(AC.aspZ regs - K, AC.aspZ regs)] A HFRA HPRO
             HA9 HAr MU E9).
    apply Forall_cons; [|apply Forall_nil]. unfold pro_iv; cbn [fst snd]. left. lia. }
  split; [exact (fra_spill g fr hb regs regs' mem mem' md _ 144 (fr + 2688) HFRA ltac:(lia) HSP MU E9 HWA)|].
  split; [exact (sl_addr_keep mem mem' [(AC.aspZ regs - K, AC.aspZ regs)] (fr + 2691) 17 HADR MU HAW)|].
  split; [exact (fra_spill g fr hb regs regs' mem mem' md _ 192 (fragb fr) HFRA ltac:(lia) HSP208 MU E9 HWA)|].
  split; [exact (sl_addr_keep mem mem' [(AC.aspZ regs - K, AC.aspZ regs)] (fragb fr) 72 HADF MU HAW)|].
  split; [exact (sl_addr_keep mem mem' [(AC.aspZ regs - K, AC.aspZ regs)] (fr + 2688) 38 HADI MU HAW)|].
  split.
  { unfold IDBe in *. eapply fl_bytes; [exact HIDB | exact MU |].
    unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
    intros x Hx. apply HWfr. lia. }
  unfold FGBe in *. eapply fl_bytes; [exact HFGB | exact MU |].
  unfold z72. rewrite repeat_length. intros x Hx. apply HWfr. lia.
Qed.

(* v1.9 round 4: addressable survives a callee run that writes only its stack window [sp - K, sp) (K <= FN_STACK):
   the window is application memory, so no shadow byte changes (sl_addr_keep). P7 .. P9 carry the cuts'
   `addressable m (fr + 2880) 35` (first.sroa.7, made by P3) across their callees with it. *)
Lemma stk_addr_keep : forall g fr hb regs mem mem' md K p n,
  FRA B APIf ra g fr hb regs mem md -> 0 <= K <= FN_STACK ->
  munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> addressable mem p n -> addressable mem' p n.
Proof.
  intros g fr hb regs mem mem' md K p n HFRA HK MU HAD.
  destruct (fra_sp g fr hb regs mem md HFRA) as (Hspb & Hspm & HaspB & Hhi & Hwinsp).
  assert (HAW : all_app [(AC.aspZ regs - K, AC.aspZ regs)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, FN_STACK, AF.SLOT_STACK in *. lia. }
  exact (sl_addr_keep mem mem' [(AC.aspZ regs - K, AC.aspZ regs)] p n HAD MU HAW).
Qed.

(* The WIP callee contract (plan-asan 8.1), a Section Hypothesis as the brief prescribes (as F13). *)
Hypothesis HFRAG : reac_ctrl_identity_fragment_contract.

Lemma p7_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> 0 <= f < 2 ^ 64 ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 f)) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s2' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c20) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81c20) fc None m' (seg_rom rsegs) /\
         s2' = Z_to_bv 64 (-1) /\
         munch [(bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bf8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f -> -> Hf H208 Hal HST HRO HAC HSW Hlo Hhi HRB HRM HGC HC254 HC255.
  assert (HL208 : ov_read_bytes rsegs m (wa (A + 192)) 8 = Some (le8 (Z_to_bv 64 f))).
  { pose proof (bytes_at_ov_read rsegs m (A + 192) (le8 (Z_to_bv 64 f)) 0 8 H208
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. (* 81bf8 li s2,-1 *)
  step. (* 81bfc beq a0,s2,81c04 *)
  if_true.
  step. (* 81c04 ld a0,192(s1) *)
  step. step. step. step. step. (* li a1,0; li a2,0; mv a3,s7; mv a4,s8; mv a5,s4 *)
  step. (* 81c1c jal reac_ctrl_identity_fragment *)
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  eapply LE.evt_mono.
  { eapply evt_normalize; [vm_compute; reflexivity | exact HRO |].
    pose proof HFRAG as HF. unfold reac_ctrl_identity_fragment_contract, REAC_CTRL_IDENTITY_FRAGMENT in HF.
    assert (HSTn : stk rsegs (normalize rsegs m) (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)).
    { apply (stk_rel_hi m (normalize rsegs m));
        [exact REL | unfold HIGHMEM_BEG in Hlo; lia | pose proof (u64_range sp) as Hu; lia | exact HST]. }
    assert (HACn : asan_cells (normalize rsegs m)) by exact (asan_cells_rel m (normalize rsegs m) REL HAC).
    assert (HSWn : shadow_rw (normalize rsegs m)) by exact (shadow_rw_rel m (normalize rsegs m) REL HSW).
    pose proof (mem_inv_normalize rsegs m) as HMIn.
    assert (HRBn : bytes_at rsegs (normalize rsegs m) REAL_BCMP (le8 (wa BCMP)))
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HRB).
    assert (HRMn : bytes_at rsegs (normalize rsegs m) REAL_MEMCMP (le8 (wa MEMCMP)))
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HRM).
    assert (HGCn : bytes_at rsegs (normalize rsegs m) GOT_CF (le8 (wa CF)))
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HGC).
    assert (HC254n : bytes_at rsegs (normalize rsegs m) (CF + 254) [Z_to_bv 8 1])
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HC254).
    assert (HC255n : bytes_at rsegs (normalize rsegs m) (CF + 255) [Z_to_bv 8 1])
      by exact (ba_rel1 m (normalize rsegs m) _ _ REL HC255).
    (* Only the normalized copies may meet the assumption sweep below: matching a goal on normalize rsegs m
       against a hypothesis on m makes the unifier unfold normalize / ro_addr / rsegs. *)
    clear HST HAC HSW HRB HRM HGC HC254 HC255 H208 HL208 HRO REL.
    eapply evt_cut.
    { eapply HF with (f := f) (fr := 0) (len := 0) (pa := bv_unsigned s7) (pp := bv_unsigned s8)
        (pn := bv_unsigned s4) (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
      all: try (symmetry; apply Z_to_bv_bv_unsigned).
      all: try reflexivity.
      all: try assumption.
      all: try (intros _ HH; exfalso; apply HH; reflexivity).
      all: try exact (u64_range _).
      all: lia. }
    intros ms0 Hpost. apply evt_done. exact Hpost. }
  { intros ms' (sn & HCP & HREL & HROS).
    destruct HCP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'0 &
      Esn & MUn & WMn & _ & STn & _ & _ & _).
    rewrite fg_refuse0 in Esn, MUn. cbn [fg_fp] in MUn. change (fg_ret FgRefuse) with (-1) in Esn.
    subst sn.
    destruct ms' as [R' F' pc' svc' rv' fc' mm' rom'].
    destruct HREL as (HRr & HRf & HRpc & HRsvc & HRrv & HRfc & HRrom & HRmem).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in
      HRr, HRf, HRpc, HRsvc, HRrv, HRfc, HRrom, HRmem, HROS.
    subst R' F' pc' svc' rv' fc' rom'.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (Z_to_bv 64 (-1)), mm'.
    split.
    { replace (ret_pc (Z_to_bv 64 531488)) with (Z_to_bv 64 531488)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      reflexivity. }
    split; [reflexivity|].
    split; [exact (munch_rel rsegs [(bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]
                     m (normalize rsegs m) mm' m'0 REL HRmem HROS MUn)|].
    split; [exact (wmono_rel rsegs m (normalize rsegs m) mm' m'0 REL HRmem HROS WMn)|].
    apply (stk_rel_hi_back mm' m'0);
      [exact HRmem | unfold HIGHMEM_BEG in Hlo; lia | pose proof (u64_range sp) as Hu; lia | exact STn]. }
Qed.

Lemma seg_P7 : Hcut B APIf ra (Inv_A81c20 B APIf ra) -> Hcut B APIf ra (Inv_A81bf8 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HOUR & HCUR & HPRO & HSP & HADR & HSP208 & HADF &
    HADI & HIDB & HFGB & Ha0 &
    (f & A1 & HA1 & H208) & HXC & HAF).
  subst c. rewrite SEGS.
  pose proof HXC as (HAblk & Hadc).
  destruct (fra_sp g fr [] regs mem md HFRA) as (Hspb & Hspm & HaspB & Hhi & Hwinsp).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm2 & Haspz & Hstklo & _).
  pose proof HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  assert (HGC : bytes_at rsegs mem GOT_CF (le8 (wa CF))) by exact HGOTCF.
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (p7_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (p7_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  unfold AC.aspZ in Hspb, Hspm, HaspB, Hhi, Hwinsp.
  set (f0 := bv_unsigned (Z_to_bv 64 f)).
  assert (H208' : bytes_at rsegs mem (A1 + 192) (le8 (Z_to_bv 64 f0)))
    by (unfold q64 in H208; subst f0; rewrite Z_to_bv_bv_unsigned; exact H208).
  apply (p7_run regs (Z_to_bv 64 0x81bf8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81c20 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       munch [(AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K, AC.aspZ regs)] mem mem' /\
       wmono rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply p7_evt with (sp := getr regs 2) (A := A1) (f := f0).
      - unfold rg in HA1. exact HA1.
      - unfold a0v, rg in Ha0. exact Ha0.
      - subst f0. exact (u64_range _).
      - exact H208'.
      - exact Hspm.
      - apply (p7_stk_sub mem (bv_unsigned (getr regs 2) - FN_STACK)); [exact Hwinsp|].
        unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_IDENTITY_FRAGMENT_K. lia.
      - exact Hro.
      - exact HAC0.
      - exact HSW0.
      - unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia.
      - exact HaspB.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s2' & m' &
        E & Hs2 & MU & WM & ST').
      eexists _, (Z_to_bv 64 0x81c20), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact Hs2|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM | exact ST']. }
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K10 & K18 & K22 & K25 & MU & WM & ST') Hreg Hmat.
    subst pc'.
    destruct (stk_call g fr [] regs regs' mem mem' md md' REAC_CTRL_IDENTITY_FRAGMENT_K _ HFRA HENT HXC HOUR
      HCUR HPRO HSP HADR HSP208 HADF HADI HIDB HFGB
      ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_IDENTITY_FRAGMENT_K; lia) MU WM ST'
      ltac:(rewrite Hreg; exact K2) ltac:(rewrite Hreg; exact K3) ltac:(rewrite Hreg; exact K4)
      ltac:(rewrite Hreg; exact K8) ltac:(rewrite Hreg; exact K9) ltac:(rewrite Hreg; exact K19)
      ltac:(rewrite Hreg; exact K26) ltac:(rewrite Hreg; exact K22) ltac:(rewrite Hreg; exact K25) Hmat)
      as (HFRA' & HENT' & HXC' & HOUR' & HCUR' & HPRO' & HSP' & HADR' & HSP208' & HADF' & HADI' & HIDB' & HFGB').
    assert (HIexit : Inv_A81c20 B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 0x81c20) mem' (seg_rom rsegs)) md')).
    { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hn|]. split; [exact HOUR'|].
      split; [exact HCUR'|]. split; [exact HPRO'|]. split; [exact HSP'|]. split; [exact HADR'|].
      split; [exact HSP208'|]. split; [exact HADF'|]. split; [exact HADI'|]. split; [exact HIDB'|].
      split; [exact HFGB'|].
      split; [unfold a0v, rg; rewrite Hreg; exact K10|].
      split; [unfold rg; rewrite Hreg; exact K18|]. split; [exact HXC'|].
      (* round 4: first.sroa.7's 35 bytes stay addressable (the callee writes only its window) *)
      exact (stk_addr_keep g fr [] regs mem mem' md REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2880) 35 HFRA
               ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_IDENTITY_FRAGMENT_K; lia) MU HAF). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
