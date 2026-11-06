(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, addresses and numbers changed; 493 of its 537 lines of code are new or changed and 352 lines of the source are left out. *)
(* Segment F26 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0), 0x828a4-0x828b0 (v1.8
   0x82828-0x82834; segment table row S_F26: IDENTICAL), through the call to its return point 0x828b4 (F27's
   entry).
     0x828a4  mv   s7,a0     s7 = the first count t_unk (the result of reac_ports_unknown(blk, fr + 160) at 0x828a0)
     0x828a8  mv   a0,s6     a0 = blk = phi + 18 (s6 = [A+312], 0x82878)
     0x828ac  li   a1,0      a1 = NULL
     0x828b0  jal  reac_ports_unknown
   The range has no branch, no instrumented check and no store. The callee contract (lib/B/Prog/reac_ports_unknown_c.v)
   is the Section Hypothesis HPU: with p = blk <> 0 and c = 0 it reads the 20 bytes [phi + 18, phi + 38) (marked
   usable: they are inside the live block Phi), returns a0 = 4 * pu_nunk bs 12 when pu_decl bs, else -1 (= t_unk,
   since p <> 0), keeps s0-s11, and writes only its 16 stack bytes [sp - 16, sp). The error path of the callee is not
   reached because the bytes are addressable (HB). The callee asks for no mem_inv (its contract names mem_inv only
   in its post), so the run's post carries ro_agree in its place, kept by f26_ro_keep. FRA crosses the
   call by f26_fra (a disjoint stack-scratch write, as F20's ckv_fra); ENT crosses it by Tac_slot.ent_store (the
   scratch lies inside the slot window) and the model step by ent_mat; the F27K bundle, FTL's spills, FTURN, IFS
   (S j) (with the local `first`), the ports words (PORTS) and the first byte (FIRSTb) are frame / block / spill
   bytes outside [sp - 16, sp), and the kind-name table (KNT, inside LK) is image data far below it.
   Entry cut: the official Inv_B828a4_at of lib/B/Prog/SlotInv.v (v1.9 pc 0x828a4; F27K, s4 = len, FTL, s9 = t_rp,
   a0 = t_unk, s6 = phi + 18, PORTS, FIRSTb, the block / call-window disjunction, FTURN, IFS (S j), s5 = fr + 128).
   Exit cut: the official Inv_B828b4_at (F27's entry; v1.8 Inv_B828b4_at). Both carry the heap list
   hb1 phi (a_size len), which is hb1 phi len here (50 <= len, F27K). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Import ListNotations.
(* lib.Prog's RcFrag chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this
   file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.
Module PUC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_unknown_c.

(* A Lib.Exec run is a UL run: the two step relations have the same body. *)
Lemma f26_lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma f26_lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (f26_lu_msteps _ _ H) | exact HQ]. Qed.

(* Z_to_bv 64 is injective on [-400, 2^64) x [0, 2^64 - 400): a spill base read twice is the same base. *)
Lemma f26_inj : forall x y, -400 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 - 400 ->
  Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !MState.unsigned_lit_wrap in E. rewrite (Z.mod_small y) in E by lia.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - assert (Em : x mod 2 ^ 64 = x + 2 ^ 64).
    { rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    lia.
  - rewrite Z.mod_small in E by lia. exact E.
Qed.

(* A spill A + off survives a write [lo, hi) below it (the run keeps s1). *)
Lemma f26_spill_keep : forall regs regs' m m' off v A lo hi,
  spill regs m off v -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  0 <= off <= 336 -> 0 <= A -> A + 448 <= 2 ^ 64 -> hi <= A + off ->
  LFr.munch [(lo, hi)] m m' -> spill regs' m' off v.
Proof.
  intros regs regs' m m' off v A lo hi (A' & HA' & Hq) HA E9 Hoff HA0 HA1 Hhi MU.
  pose proof (LMem.bytes_at_bound rsegs m _ _ Hq) as Hb. rewrite LMem.length_le8 in Hb.
  assert (EA : A' = A).
  { apply f26_inj; [lia | lia |]. unfold rg in *. transitivity (getr regs 9); [symmetry; exact HA' | exact HA]. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact HA'|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite LMem.length_le8.
  intros x Hx. simpl. split; [lia | exact I].
Qed.

(* The callee window with c = 0 (no first-byte output): the 16 stack bytes below sp. *)
Lemma f26_W0 : forall s, PUC.reac_ports_unknown_W s 0 = [(s - 16, s)].
Proof. intros s. reflexivity. Qed.

(* The record bytes: t_g is 50 bytes, so its slices below 50 have their full length. *)
Lemma f26_bsl_len : forall inp j k n, 0 <= k -> 0 <= n -> k + n <= 50 ->
  length (bsl (t_g inp j) k n) = Z.to_nat n.
Proof.
  intros inp j k n Hk Hn Hkn. unfold bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.
Lemma f26_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk. rewrite f26_bsl_len by lia. reflexivity. Qed.
Lemma f26_pbs_len : forall inp j, length (t_pbs inp j) = 20%nat.
Proof. intros inp j. unfold t_pbs. rewrite f26_bsl_len by lia. reflexivity. Qed.

(* The 20 ports bytes the callee reads are the first 20 of the 32 block bytes at blk = phi + 18. *)
Lemma f26_pbs : forall inp j, t_pbs inp j = firstn 20 (t_blk inp j).
Proof. intros inp j. unfold t_pbs, t_blk, bsl. rewrite firstn_firstn. reflexivity. Qed.
Lemma f26_bytes_firstn : forall m a bs n, LMem.bytes_at rsegs m a bs -> LMem.bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H. rewrite <- (firstn_skipn n bs) in H.
  exact (proj1 (proj1 (LMem.bytes_at_app rsegs m a _ _) H)).
Qed.

(* The callee's result for p <> 0 is the model count t_unk (pu_ok p bs = pu_decl bs when p <> 0). *)
Lemma f26_pu_ok : forall inp j p, p <> 0 ->
  (if RcPorts.pu_ok p (t_pbs inp j) then 4 * RcPorts.pu_nunk (t_pbs inp j) 12 else -1) = t_unk inp j.
Proof.
  intros inp j p Hp. unfold RcPorts.pu_ok, t_unk.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp). reflexivity.
Qed.

(* F27K reads only s1 (the spills), s2, s8, s11 and memory (lib/B/Prog/Seg/F27.v's f27_K, with v1.9's s8 = sum_ok). *)
Lemma f26_K : forall g j phi fr regs regs' m,
  F27K g j phi fr regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 27 = getr regs 27 ->
  getr regs' 24 = getr regs 24 ->
  F27K g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m H E9 E18 E27 E24.
  unfold F27K, LK, FLI, spill, rg in *. rewrite E9, E18, E27, E24. exact H.
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot rewritten to
   a concrete value. *)
Lemma f26_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a register slot `getr regs r` to its carried value, from H : rg regs r v. *)
Ltac f26_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* Every runtime cell of rt_disjoint lies in the image, below HIGHMEM_BEG: a write above HIGHMEM_BEG misses them. *)
Lemma f26_rt_hi : forall lo hi, HIGHMEM_BEG <= lo -> rt_disjoint [(lo, hi)].
Proof.
  intros lo hi H. unfold rt_disjoint. simpl.
  repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- _ \/ _ => left; apply (Z.le_trans _ HIGHMEM_BEG _); [apply Z.leb_le; vm_compute; reflexivity | exact H]
  end.
Qed.

(* The ports words [fr + 128, fr + 140) and the first byte fr + 160 are frame bytes: a write outside the frame keeps
   them. *)
Lemma f26_pf_keep : forall g fr j m m' W,
  PORTS g fr j m -> FIRSTb g fr j m -> LFr.munch W m m' ->
  (forall x, fr <= x < fr + FRAME_BYTES -> LFr.outside W x) -> PORTS g fr j m' /\ FIRSTb g fr j m'.
Proof.
  intros g fr j m m' W (HP0 & HP1) HF MU HW. pose proof FRAME_BYTES_val as HFBv.
  unfold FIRSTb, b8 in *. split; [split|].
  - intros E. destruct (HP0 E) as (Ha & Hb & Hc). unfold u32 in *.
    split; [|split].
    + eapply fl_bytes; [exact Ha | exact MU |]. rewrite LMem.length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hb | exact MU |]. rewrite LMem.length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hc | exact MU |]. rewrite LMem.length_le4. intros x Hx. apply HW. lia.
  - intros E. destruct (HP1 E) as (Ha & Hb & Hc). unfold u32 in *.
    split; [|split].
    + eapply fl_bytes; [exact Ha | exact MU |]. rewrite LMem.length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hb | exact MU |]. rewrite LMem.length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hc | exact MU |]. rewrite LMem.length_le4. intros x Hx. apply HW. lia.
  - eapply fl_bytes; [exact HF | exact MU |]. intros x Hx. apply HW. cbn [length] in Hx. lia.
Qed.

(* Push 5c: the cuts carry ro_agree (FRA's third conjunct) in place of mem_inv, so the run's post carries ro_agree
   too. The reac_ports_unknown contract asks for no mem_inv (lib/B/Prog/reac_ports_unknown_c.v:15-41 names it only
   in the post, as mem_inv rsegs m -> mem_inv rsegs m'), so no normalized run is needed here: every read-only byte
   is a byte of a loaded segment and every loaded segment ends below GT (Tac_slot.img_tops_true), so a write set
   whose intervals all start at or above GT -- this segment's W = [sp - 16, sp), high application memory -- changes
   no read-only byte and ro_agree crosses it. Seg/F16.v carries the same three lemmas (f16_ro_lt_GT / f16_out_GT /
   f16_ro_keep) for the same reason. *)
Lemma f26_ro_lt_GT : forall x, LMem.ro_addr rsegs x = true -> bv_unsigned x < AC.GT.
Proof.
  intros x H. unfold LMem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|discriminate H].
  destruct (BZB.find_segment_below rsegs AC.GT (bv_unsigned x) 1 s img_tops_true E ltac:(lia))
    as [L|L]; [exact L | lia].
Qed.
Lemma f26_out_GT : forall (W : list (Z * Z)) x,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> x < AC.GT -> LFr.outside W x.
Proof.
  intros W. induction W as [|[lo hi] W IH]; cbn; intros x H Hx; [exact I|].
  split.
  - pose proof (H lo hi ltac:(left; reflexivity)) as Hlo. lia.
  - apply IH; [intros lo' hi' Hin; apply (H lo' hi'); right; exact Hin | exact Hx].
Qed.
Lemma f26_ro_keep : forall (W : list (Z * Z)) m m',
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> LFr.munch W m m' ->
  ro_agree rsegs m -> ro_agree rsegs m'.
Proof.
  intros W m m' HGT MU Hro a Ha.
  pose proof (Hro a Ha) as H. unfold LMem.mrd in H |- *.
  rewrite (MU a (f26_out_GT W (bv_unsigned a) HGT (f26_ro_lt_GT a Ha))). exact H.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract of reac_ports_unknown (lib/B/Prog/reac_ports_unknown_c.v). *)
Hypothesis HPU : PUC.reac_ports_unknown_contract.

(* FRA across the reac_ports_unknown call: the callee writes only its stack scratch W = [sp - 16, sp) (below the spill
   base A, above the image and the shadow, disjoint from the frame by the frame / window disjunction), keeps the FRA
   registers, keeps the entry-anchored slot window [S - SLOT_STACK, S) (outside W from the entry window, inside W from
   the call's stk post on [sp - FN_STACK, sp)), and materializes pages (mat_le). The same move as F20's ckv_fra.
   ro_agree of the new memory is a premise: the caller gets it from the cut's own ro_agree by f26_ro_keep. The fr
   spill A + 40 is above sp, the window outside the frame stays addressable (sl_addr_keep), the side arm's
   FakeStack frame record FSREC moves by Tac_slot.fsrec_munch_lo (W is above stklo), and the three entry
   stack-top facts read the ghost only. *)
Lemma f26_fra : forall g fr hb regs regs' mem mem' md md',
  FRA B APIf ra g fr hb regs mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (fr + FRAME_BYTES <= AC.aspZ regs - 16 \/ AC.aspZ regs <= fr) ->
  AC.aspZ regs <= APPMEM_END ->
  LFr.munch [(AC.aspZ regs - 16, AC.aspZ regs)] mem mem' ->
  LFr.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' HFRA Hfrapp Hdisjfr HaspB MU WM HroM HSTKW
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  rewrite Haspz in Hdisjfr, HaspB, MU, HSTKW.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
    by (intros x Hx; simpl; split; [lia | exact I]).
  assert (Hallapp : all_app [(sp - 16, sp)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (Hrtdj : rt_disjoint [(sp - 16, sp)]) by (apply f26_rt_hi; unfold AF.SLOT_STACK in *; lia).
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. apply HOW.
    destruct (Z_lt_le_dec a (sp - 16)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as [HAH' _ HSTKeq _].
  assert (HSTKS : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - 16) (g_S g) Hwin ltac:(lia)) as (Hw1 & Hw2).
    destruct (LFr.stk_split rsegs mem (sp - 16) sp (g_S g) Hw2 ltac:(lia)) as (_ & Hw3).
    destruct (LFr.stk_split rsegs mem' (sp - FN_STACK) (sp - 16) sp HSTKW
                ltac:(unfold FN_STACK; lia)) as (_ & HwW).
    assert (Hw1' : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (sp - 16)).
    { eapply (LFr.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
      intros x Hx. left. apply HOW. lia. }
    assert (Hw3' : LFr.stk rsegs mem' sp (g_S g)).
    { eapply (LFr.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
      intros x Hx. left. apply HOW. lia. }
    apply (LFr.stk_merge rsegs mem' _ sp _); [| exact Hw3' | lia].
    apply (LFr.stk_merge rsegs mem' _ (sp - 16) _); [exact Hw1' | exact HwW | lia]. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply (KindBGlue.mbyte_munch sg [(sp - 16, sp)] mem mem' x MU).
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - apply HOW. left. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { exists A, sp, s5.
    split; [exact (AsanRTInv.RT_store sp sp mem mem' md md _ HRT MU WM Hallapp Hrtdj)|].
    split; [exact HAH'|].
    split; [exact HroM|].
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
      - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        destruct Hil as [E|[]]; injection E as <- <-; lia.
      - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        destruct Hil as [E|[]]; injection E as <- <-; lia. }
    split; [rewrite E2; exact Hr2|].
    split; [exact Hspm|].
    split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
    split; [rewrite HSTKeq; exact Hstklo|].
    split; [rewrite E4; exact Hr4|].
    split; [unfold rg in *; rewrite E8; exact Hr8|].
    split; [unfold rg in *; rewrite E9; exact Hr9|].
    split; [rewrite E3; exact Hr3|].
    split; [unfold rg in *; rewrite E19; exact Hr19|].
    split; [unfold rg in *; rewrite E26; exact Hr26|].
    split; [exact Hfrm|].
    split; [exact Hs5|].
    split; [exact HAm|].
    split; [exact HAS|].
    split; [exact Hspa|].
    split; [exact Hfa|].
    split; [exact HA448|].
    split; [exact HS4|].
    split; [exact HAPP|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
      - left. split; [exact H0|]. split; [exact Hspfr|].
        intros a Ha. rewrite HSTKeq. exact (Hreal a Ha).
      - right. split; [exact Hfr0|]. split; [|split].
        + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
          intros k Hk. rewrite <- KBlo.
          * exact (Hw k Hk).
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          * exact (Hw k Hk).
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        + eapply fsrec_munch_lo with (W := [(sp - 16, sp)]); [exact Hrec | exact HAH | exact MU |].
          intros x Hx _. apply HOW. left. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. lia. }
    split.
    { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
      eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, Z2Nat.id by lia. intros x Hx. apply HOW. left.
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
    split; [exact HSTKS|].
    split.
    { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx. apply HOW. right.
      unfold saved_bytes in Hx. rewrite !length_app, !LMem.length_le8 in Hx. cbn in Hx. lia. }
    split.
    { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
    split; [intros a Hin; exact (sl_addr_keep mem mem' [(sp - 16, sp)] a 1 (HAG a Hin) MU Hallapp)|].
    split; [intros a H1 H2; exact (sl_addr_keep mem mem' [(sp - 16, sp)] a 1 (HWA a H1 H2) MU Hallapp)|].
    split; [exact HSHI1|].
    split; [exact HSHI2|].
    split; [exact HSHI3|].
    split; [exact Hhb|]. split; [exact Hlive|].
    (* the input block is below stklo (fra_in_apart), so below [sp - 16, sp) *)
    apply (fra_in_keep g mem mem' [(sp - 16, sp)] Hinb Hinblk MU Hallapp).
    intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & _ & _). apply HOW. left. lia. }
  apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
Qed.

(* S_F26 (forms-asan-ubsan-v190.md (a working note, not in this delivery)) on the v1.9 cuts. *)
Lemma seg_F26 : forall j, Hat B APIf ra (Inv_B828b4_at B APIf ra) j -> Hat B APIf ra (Inv_B828a4_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv. pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_B828a4_at, CUTST in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HK & Hs4 & HFTL &
    Hs9 & Ha0 & Hs6 & HPO & HFI & Hdjphi & HFT & HIFS & Hs5p). subst c.
  (* the cut's heap list hb1 phi (a_size len) is hb1 phi len: 50 <= len (F27K) *)
  assert (Ea : AC.a_size (flen g j) = flen g j)
    by (pose proof HK as (_ & _ & _ & _ & _ & Hfl & _); unfold AC.a_size; lia).
  rewrite Ea in HFRA, HENT.
  rewrite SEGS.
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (HfrK & _).
  destruct (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGT & Hfrapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH) as Hstkhi.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Esp : bv_unsigned (getr regs 2) = sp) by (unfold AC.aspZ in Haspz; exact Haspz).
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by (rewrite Haspz; lia).
  pose proof (HfrK 16 ltac:(unfold FN_STACK; lia)) as Hdisjfr.
  pose proof Hdisjfr as Hdisjfr'. rewrite Haspz in Hdisjfr'.
  pose proof Hdjphi as Hdjphi'. rewrite Haspz in Hdjphi'.
  pose proof HK as (HLK & H18 & H27 & Hphi0 & Hphi50 & Hflen & Hblk & HS312 & HS272 & H24 & HS104 & HS136).
  (* The premises of the reac_ports_unknown contract at its entry 0x88628 (p = blk = phi + 18, c = 0,
     lo = sp - FN_STACK (fra_win), bs = the 20 ports bytes t_pbs). *)
  assert (Ep : bv_unsigned (Z_to_bv 64 (phi + 18)) = phi + 18) by (apply MState.unsigned_lit; lia).
  assert (CK3 : LFr.stk rsegs mem (sp - FN_STACK) (bv_unsigned (getr regs 2)))
    by (rewrite Esp; rewrite Haspz in HW0; exact HW0).
  assert (CK4 : sp - FN_STACK + 16 <= bv_unsigned (getr regs 2))
    by (rewrite Esp; unfold FN_STACK; lia).
  assert (CK5 : phi + 18 <> 0 -> phi + 18 + 20 <= 2 ^ 64 /\ length (t_pbs (g_in g) j) = 20%nat /\
                 bytes_at rsegs mem (phi + 18) (t_pbs (g_in g) j) /\
                 (phi + 18 + 20 <= bv_unsigned (getr regs 2) - 16 \/ bv_unsigned (getr regs 2) <= phi + 18)).
  { intros _. split; [lia|]. split; [apply f26_pbs_len|]. split.
    - rewrite f26_pbs. apply f26_bytes_firstn. exact Hblk.
    - rewrite Esp. lia. }
  assert (CK7 : asan_cells mem) by exact (AsanRTInv.RT_cells sp mem md HRT).
  assert (CK8 : shadow_rw mem) by exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
  assert (CK10 : phi + 18 <> 0 -> addressable mem (phi + 18) 20).
  { intros _. destruct HHB as (_ & Hphiad).
    apply (addressable_sub mem phi (AC.a_size (flen g j)) 18 20 Hphiad); unfold AC.a_size; lia. }
  assert (CK11 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            LFr.outside (PUC.reac_ports_unknown_W (bv_unsigned (getr regs 2)) 0) x).
  { intros x Hx. rewrite f26_W0, Esp. simpl. split; [|exact I].
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, AF.SLOT_STACK in *.
    lia. }
  (* the callee's window starts in high application memory, far above the top of the image GT, so the run keeps
     every read-only byte and the cut's ro_agree crosses it (f26_ro_keep). *)
  assert (HGTW : forall lo hi, In (lo, hi) [(sp - 16, sp)] -> AC.GT <= lo).
  { intros lo hi Hin. cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-.
    unfold AC.GT in *. lia. }
  pose proof HPU as HC.
  unfold PUC.reac_ports_unknown_contract, PUC.REAC_PORTS_UNKNOWN_FRAME, PUC.REAC_PORTS_UNKNOWN in HC.
  (* The one lazy-model run of this segment: Tac_slot.sl_run (AsanLift.evt_SR_canon_lazy). Pages it reads (in the
     callee): the 20 ports bytes [phi + 18, phi + 38) with their shadow bytes ((phi + 18..37) >> 3) + 0x7fff8000 and
     the runtime cells CELL_K / GOT_CELL_K. Pages it writes: only the callee's 16 stack bytes [sp - 16, sp). *)
  apply (sl_run regs (Z_to_bv 64 0x828a4) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x828b4 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27 /\
       getr R 25 = getr regs 25 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 24 = getr regs 24 /\
       getr R 23 = getr regs 10 /\
       getr R 10 = Z_to_bv 64 (t_unk (g_in g) j) /\
       LFr.munch [(sp - 16, sp)] mem mem' /\ LFr.wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ LFr.stk rsegs mem' (sp - FN_STACK) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f26_mkR_of_expand.
    f26_slot Hs6.
    (* 0x828a4 mv s7,a0 ; 0x828a8 mv a0,s6 ; 0x828ac li a1,0 ; 0x828b0 jal reac_ports_unknown *)
    step. step. step. step.
    (* the call: the callee contract at 0x88628, back at 0x828b4 *)
    eapply UEx.evt_cut.
    { apply f26_lu_evt.
      eapply HC with (p := phi + 18) (c := 0) (lo := sp - FN_STACK) (bs := t_pbs (g_in g) j).
      all: first [ reflexivity | assumption | (intros Hc0; exfalso; apply Hc0; reflexivity) ]. }
    intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & Ems & MU & WM & ST & _ & _).
    subst ms'. apply UEx.evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
    split; [apply bv_eq; vm_compute; reflexivity|].
    do 14 (split; [reflexivity|]).
    split; [rewrite (f26_pu_ok (g_in g) j (phi + 18)) by lia; reflexivity|].
    rewrite f26_W0, Esp in MU. rewrite Esp in ST.
    split; [exact MU|]. split; [exact WM|].
    split; [exact (f26_ro_keep [(sp - 16, sp)] mem m' HGTW MU Hro)|]. exact ST.
  - (* continuation: rebuild the exit cut Inv_B828b4_at (F27's entry) and apply it *)
    intros R pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er27 & Er25 & Er20 & Er21 & Er24 & Er23 & Er10 &
       MU & WM & HroM' & ST')
      Hreg Hmat.
    subst pc'. rewrite <- SEGS. apply Hexit.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
      by (intros x Hx; simpl; split; [lia | exact I]).
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> LFr.outside [(sp - 16, sp)] x)
      by (intros x Hx; apply HOW; lia).
    assert (Hallapp : all_app [(sp - 16, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HA0 : 0 <= A) by lia.
    assert (HA1 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in HAPP; lia).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md').
    { apply (f26_fra g fr (hb1 phi (flen g j)) regs regs' mem mem' md md' HFRA Hfrapp Hdisjfr HaspB);
        [ rewrite Haspz; exact MU | exact WM | exact HroM' | rewrite Haspz; exact ST'
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat ]. }
    (* ENT crosses the call: the callee writes only its 16 stack bytes [sp - 16, sp), which lie inside the
       entry-anchored slot window [S - SLOT_STACK, S) (sp <= A <= S and S - 4096 < sp), so no byte ENT speaks of
       changes; a_laws_store gives the two stack-top equalities and the ownership transport it asks for, and the
       model step md -> md' moves by ent_mat. *)
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. apply HOW.
      destruct (Z_lt_le_dec a (sp - 16)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
      exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (lw_store (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as [HAH' Hown' HSTKeq HSTKHIeq].
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { eapply ent_store with (W := [(sp - 16, sp)]) (fr := fr) (regs := regs);
        [ exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKHIeq
        | intros a Hia Ho; exact (proj2 (Hown' a) Ho) ].
      intros x Hx. destruct (Z_le_gt_dec (sp - 16) x) as [D1|D1];
        [destruct (Z_lt_ge_dec x sp) as [D2|D2]|].
      - right; left. unfold AF.SLOT_STACK in *. lia.
      - left. cbn [LFr.outside]. split; [lia | exact I].
      - left. cbn [LFr.outside]. split; [lia | exact I]. }
    (* every spill of s1 = A lies above the callee's 16 stack bytes [sp - 16, sp) (sp <= A) *)
    assert (HSPK : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs.
      apply (f26_spill_keep regs regs' mem mem' off v A (sp - 16) sp Hs Hr9 Fr9); lia || exact MU. }
    (* F27K on the post-call memory (same registers), then moved to regs' by f26_K (s1, s2, s8, s11 kept) *)
    pose proof (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK)))) as
      (Had2624 & Hstkfr & HRid & HRfg & HKNT & Hfst).
    assert (Hfst' : addressable mem' (fr + 2880) 40)
      by exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fr + 2880) 40 Hfst MU Hallapp).
    assert (HK' : F27K g j phi fr regs mem').
    { unfold F27K.
      (* LK (with FLI): the registers are the ones of the entry, so s11 is F27K's own rg regs 27 (-8); the
         callee's 16 stack bytes [sp - 16, sp) sit below the spill base (sp <= A) and above the our[] bytes,
         so every spill of j and of FLI survives (Tac_ro.lk_keep over f26_spill_keep), and the kind-name table
         (image data) lies far below them (Tac_ro.knt_munch). *)
      split.
      { eapply Tac_ro.lk_keep;
          [ exact HLK
          | exact H27
          | exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fr + 2624) 6 Had2624 MU Hallapp)
          | eapply (LFr.stk_transport rsegs [(sp - 16, sp)] mem mem' fr (fr + FRAME_BYTES));
              [ exact Hstkfr | exact MU | exact WM |];
            intros x Hx; left; exact (HWfr x Hx)
          | exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fr + 2688) 38 HRid MU Hallapp)
          | exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fragb fr) 72 HRfg MU Hallapp)
          | apply (Tac_ro.knt_munch [(sp - 16, sp)] mem mem' HKNT MU (munch_meta _ mem mem' MU Hallapp));
            intros x Hx; apply HOW; left; unfold KNC.KIND_NAME, HIGHMEM_BEG, AF.SLOT_STACK in *; lia
          | exact Hfst'
          | unfold OURb in *;
            apply (fl_bytes _ mem mem' (fr + 2624) (OUR (g_in g)) (proj1 (proj2 (proj2 HLK))) MU);
            rewrite OUR_length; intros x Hx; apply HOW; lia
          | intros off v Hoff Hs;
            apply (f26_spill_keep regs regs mem mem' off v A (sp - 16) sp Hs Hr9 eq_refl);
            lia || exact MU ]. }
      split; [exact H18|]. split; [exact H27|]. split; [exact Hphi0|]. split; [exact Hphi50|].
      split; [exact Hflen|].
      split.
      { apply (fl_bytes _ mem mem' (phi + 18) (t_blk (g_in g) j) Hblk MU).
        rewrite f26_blk_len. intros x Hx. apply HOW. lia. }
      split; [apply (f26_spill_keep regs regs mem mem' 312 _ A (sp - 16) sp HS312 Hr9 eq_refl); lia || exact MU|].
      split; [apply (f26_spill_keep regs regs mem mem' 272 _ A (sp - 16) sp HS272 Hr9 eq_refl); lia || exact MU|].
      split; [exact H24|].
      split; [apply (f26_spill_keep regs regs mem mem' 104 _ A (sp - 16) sp HS104 Hr9 eq_refl); lia || exact MU|].
      apply (f26_spill_keep regs regs mem mem' 136 _ A (sp - 16) sp HS136 Hr9 eq_refl); lia || exact MU. }
    destruct (f26_pf_keep g fr j mem mem' _ HPO HFI MU HWfr) as (HPO' & HFI').
    (* the frame bytes at phi (FTURN): the block (phi, len) is live, so it ends at or below stklo
       (a_laws_blocks), which is at or below sp - FN_STACK (fra_win); the callee's 16 stack bytes miss it *)
    assert (Hphilo : phi + flen g j <= sp - 16).
    { destruct (lw_blocks (APIf rc) _ mem md phi (flen g j) HAH
                  ltac:(apply in_or_app; left; left; reflexivity)) as [_ _ Hend _ _].
      rewrite Haspz in Hlow. unfold FN_STACK in Hlow. unfold AF.SLOT_STACK in *. lia. }
    unfold Inv_B828b4_at, CUTST. rewrite Ea.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT' | exact Hmat]|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      exact (sl_addr_keep mem mem' [(sp - 16, sp)] phi (AC.a_size (flen g j)) Hphiad MU Hallapp). }
    split; [exact (f26_K g j phi fr regs regs' mem' HK' Fr9 Fr18 Fr27 Fr24)|].
    split; [unfold rg in *; rewrite Fr20; exact Hs4|].
    split.
    { destruct HFTL as (T21 & T184 & T272 & T24 & T312).
      split; [unfold rg in *; rewrite Fr21; exact T21|].
      split; [exact (HSPK 184 _ ltac:(lia) T184)|].
      split; [exact (HSPK 272 _ ltac:(lia) T272)|].
      split; [unfold rg in *; rewrite Fr24; exact T24 | exact (HSPK 312 _ ltac:(lia) T312)]. }
    split; [unfold rg; rewrite Fr25; exact Hs9|].
    split; [unfold rg; rewrite Hreg, Er23; exact Ha0|].
    split; [unfold rg; rewrite Hreg; exact Er10|].
    split; [exact HPO'|]. split; [exact HFI'|].
    split.
    { apply (Tac_ro.turn_munch g j phi regs regs' [(sp - 16, sp)] mem mem' HFT HSPK MU).
      intros x Hx. apply HOW. left. unfold flen in Hphilo. lia. }
    split; [exact (Tac_ro.ifs_munch g fr (S j) regs regs' [(sp - 16, sp)] mem mem' HIFS MU HWfr Hfst')|].
    unfold rg in *; rewrite Fr21; exact Hs5p.
Qed.

End S.
