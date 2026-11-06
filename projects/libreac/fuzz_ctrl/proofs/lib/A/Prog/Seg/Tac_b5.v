(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 176 of its 211 lines of code are new or changed and 361 lines of the source are left out. *)
(* General helpers for the frame-loop segment lemmas of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A), segments
   F4-F12: register reads through Regs6ss.mkR_of (rg_mkR, reg_mkR, sl_rg_get, sl_mkR_set), the read-only image
   bounds (sl_ro_lo, sl_ro_keep, sl_shadow_not_ro), one instrumented 1-byte shadow read (sl_shadow1), the
   Lib.Exec run lemma (sl_run_lib), and FRA transport across a write below the slot sp (sl_stk_run) and across a
   program callee whose contract writes only its stack window [sp - K, sp) (sl_callee_keep). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
Import ListNotations.
(* A later import shadows YK11.getr (used by FRA); restore it as the default so register equalities match FRA. *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* A register read of the step engine's concrete register file Regs6ss.mkR_of regs is the read of regs (any
   register but x0); simp_regs does not see through mkR_of. Use: rewrite !(rg_mkR regs) by (vm_compute; reflexivity). *)
Lemma rg_mkR : forall (regs : bvmap 5 word) (r : bv 5),
  bv_eqb r 0 = false -> Sem.reg_get (Regs6ss.mkR_of regs) r = Sem.reg_get regs r.
Proof. intros regs r H. symmetry. exact (Regs6ss.mkR_of_eqv regs r H). Qed.

Lemma reg_mkR : forall (regs : bvmap 5 word) (r : bv 5), getr (Regs6ss.mkR_of regs) r = getr regs r.
Proof. intros regs r. apply kb_getr_eqv. apply Regs6ss.mkR_of_eqv. Qed.

(* An rg fact read as a raw reg_get (any register but x0). *)
Lemma sl_rg_get : forall (regs : bvmap 5 word) (i : bv 5) (v : Z),
  rg regs i v -> bv_eqb i 0 = false -> Sem.reg_get regs i = Z_to_bv 64 v.
Proof. intros regs i v H Hi. unfold rg, getr in H. rewrite Hi in H. exact H. Qed.

(* Register concretization for the branch-not-taken discharge: a reg_get of mkR_of regs at a register with a known
   rg value. Use: rewrite (sl_mkR_set regs _ _ R_i) by (vm_compute; reflexivity). *)
Lemma sl_mkR_set : forall (regs : bvmap 5 word) (i : bv 5) (v : Z),
  rg regs i v -> bv_eqb i 0 = false -> Sem.reg_get (Regs6ss.mkR_of regs) i = Z_to_bv 64 v.
Proof. intros regs i v H Hi. rewrite (rg_mkR regs i Hi). exact (sl_rg_get regs i v H Hi). Qed.

(* Every segment of the image ends below LOWMEM_END. *)
Local Definition b5_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma b5_rsegs_low : b5_tops rsegs LOWMEM_END = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma b5_find_below : forall segs top x n s,
  b5_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold b5_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* A read-only image address is below LOWMEM_END. *)
Lemma sl_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < LOWMEM_END.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (b5_find_below rsegs LOWMEM_END (bv_unsigned a) 1 s b5_rsegs_low E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

(* A shadow address is never in a read-only image segment. *)
Lemma sl_shadow_not_ro : forall a, in_shadow a -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [exfalso|reflexivity].
  apply sl_ro_lo in E.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  rewrite Mem.wa_unsigned in E by lia. unfold LOWMEM_END in E. lia.
Qed.

(* ro_agree survives a run that writes nothing below LOWMEM_END (the read-only image bytes are kept). *)
Lemma sl_ro_keep : forall W mem mem',
  ro_agree rsegs mem -> Frame.munch W mem mem' -> (forall x, 0 <= x < LOWMEM_END -> Frame.outside W x) ->
  ro_agree rsegs mem'.
Proof.
  intros W mem mem' Hro MU Hlo. apply (ro_agree_same rsegs mem mem' Hro).
  intros a Ha. apply sl_ro_lo in Ha. apply MU. apply Hlo.
  pose proof (bv_unsigned_in_range 64 a) as Hr. lia.
Qed.

(* One instrumented 1-byte shadow read of an addressable byte X: the shadow byte b is readable at
   (X >> 3) + ASAN_K and passes the check (b = 0, or X mod 8 < b). *)
Lemma sl_shadow1 : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

Section R.
Context {fx : FPState}.

(* sl_run for a Lib.Exec.evt run (sl_run takes the UL evt and applies ul_entry; a callee contract stated in
   Lib.Exec gives a Lib.Exec.evt, which feeds AsanLift.evt_SR_canon_lazy directly). *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
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

(* FRA moves across a run that writes only a region W outside the frame header [fr, fr + 24), the low image
   [0, HIGHMEM_BEG), the spill slot [s1 + 304, s1 + 312), the fr reload and selector spills [s1 + 16, s1 + 32),
   the saved registers [S - 104, S) and the 392 frame shadow bytes (a main-stack write outside the frame, e.g. a
   callee's [sp - K, sp) or a spill store). It is Tac_slot.sl_fr_cl, whose low-image premise is the weaker
   [0, 6283264) (the runtime's sink cells and the RELRO image bytes are all it reads there); the S-anchored
   window comes from the caller, and mem_inv is not involved at all (push 5b: FRA does not carry it; a callee
   reaches its own mem_inv premise through MemNorm.evt_normalize from ro_agree).
   The complement of sl_fr_run, which is for writes inside the frame body. *)
Lemma sl_stk_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 304 <= x < A + 312 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 16 <= x < A + 32 -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HWhdr HWimg HWspill HWsaved HWsh
    HWsel HWwin Hrec' E2 E3 E4 E8 E9 E19 E26.
  apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK);
    [| exact HWhdr | exact HWspill | exact HWsaved | exact HWsh | exact HWsel | exact HWwin | exact Hrec'
     | exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26].
  intros x Hx. apply HWimg. unfold HIGHMEM_BEG. lia.
Qed.

(* FRA moves across a program callee whose contract gives the bespoke post (munch over its own stack window
   [sp - K, sp), wmono) instead of a_call_post, and across the lazy-page materialization md -> md' of the run
   (sl_run / sl_run_lib): sl_stk_run with W = [(sp - K, sp)], then sl_fra_move. The official form (a Theorem Labs lane
   3ef2305c85, a Theorem Labs lane ruling 2026-10-27): the caller gives the S-anchored window of mem' itself (FRA's own
   conjunct, kept through the callee), any K <= FN_STACK (a K < 0 window is empty; it is read as K = 0), the
   window top below APPMEM_END, the frame header apart from the window and the frame below APPMEM_END. The rest
   comes from FRA: the window is above HIGHMEM_BEG (stklo <= sp - FN_STACK by fra_win, HIGHMEM_BEG <= stklo by
   a_laws_stack_high), so it is app memory and a_store_ok (AH / stklo by sl_ah_stk), and misses the image, RT and
   the frame shadow (fr + 3136 <= APPMEM_END, so Sfr fr + 392 <= HIGHMEM_BEG); the spills [A + 16, A + 32),
   [A + 304, A + 312) and the saved registers [S - 104, S) are at or above sp. The side-arm FakeStack record
   moves by fsrec_munch_lo (the window is at or above stklo). mem_inv is not involved (push 5b: FRA does not
   carry it). *)
Lemma sl_callee_keep : forall g fr hb regs regs' mem mem' md md' K,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  K <= FN_STACK -> AC.aspZ regs <= APPMEM_END ->
  (AC.aspZ regs <= fr \/ fr + 24 <= AC.aspZ regs - K) -> fr + FRAME_BYTES <= APPMEM_END ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' K HFRA MU WM Hwin' HK Hsp Hhdr Hfrapp E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & _).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  (* the window as run: K0 = max 0 K (the same bytes; empty for K <= 0) *)
  remember (Z.max 0 K) as K0 eqn:HK0e.
  assert (HK0 : 0 <= K0 <= FN_STACK) by lia.
  assert (MU0 : Frame.munch [(AC.aspZ regs - K0, AC.aspZ regs)] mem mem').
  { intros x Hx. apply MU. cbn [Frame.outside] in *. destruct Hx as (Hx & _). split; [lia | exact I]. }
  destruct (sl_ah_stk B APIf ra g fr hb regs mem mem' md K0 HFRA HK0 MU0 WM) as (HAH' & Hstkeq).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold AC.GT in Hgt.
  assert (Hlo : HIGHMEM_BEG <= AC.aspZ regs - K0) by lia.
  assert (Hout : forall x, x < AC.aspZ regs - K0 \/ AC.aspZ regs <= x ->
                   Frame.outside [(AC.aspZ regs - K0, AC.aspZ regs)] x).
  { intros x Hx. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    assert (HA64 : 0 <= A < 2 ^ 64).
    { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  assert (Hrec' : FSREC fr mem -> FSREC fr mem').
  { intros Hrec. eapply fsrec_munch_lo; [exact Hrec | exact HAH | exact MU0 | |].
    - intros x Hx. apply Hout. left. unfold HIGHMEM_BEG in *. lia.
    - intros x _ _ Hx. apply Hout. left. lia. }
  apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md');
    [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hmat].
  apply (sl_stk_run g fr hb regs regs' mem mem' md [(AC.aspZ regs - K0, AC.aspZ regs)] HFRA MU0 WM).
  - apply (sl_ro_keep _ mem mem' Hro MU0). intros x Hx. apply Hout. left.
    unfold LOWMEM_END, HIGHMEM_BEG in *. lia.
  - cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END in *. lia.
  - unfold rt_disjoint. cbn [disjoint_from].
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    unfold HIGHMEM_BEG in Hlo.
    repeat split; left; lia.
  - exact HAH'.
  - exact Hstkeq.
  - intros x Hx. apply Hout. destruct Hhdr as [Hd|Hd]; lia.
  - intros x Hx. apply Hout. left. lia.
  - intros A' HA' HA'r x Hx. apply Hout. right. rewrite (HA9 A' HA' HA'r) in Hx. lia.
  - intros x Hx. apply Hout. right. lia.
  - intros x Hx. apply Hout. left. unfold Sfr, shadow_addr, ASAN_K in Hx.
    pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)).
    unfold APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros A' HA' HA'r x Hx. apply Hout. right. rewrite (HA9 A' HA' HA'r) in Hx. lia.
  - exact Hwin'.
  - exact Hrec'.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

End S.
