(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 785 of its 828 lines of code are new or changed and 353 lines of the source are left out. *)
(* Segment A3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A, libreac v1.9.0): 0x80f88-0x810e0 and the shadow
   fill call at 0x810e0 (slot-plan-asan.md FP.2-FP.4). seg_A3 : Hcut Inv_A810e4 -> Hcut Inv_A80f88. The run lemma
   a3_evt steps the 87 instructions and calls meta_fill_f8 (v1.9 0x55008) through asan_set_shadow_f8_contract
   (Section Hypothesis SSF8, via f8_call on the normal form of memory: the contract asks mem_inv, the cut gives
   ro_agree, MemNorm.evt_normalize bridges them); seg_A3 assembles the FRAS cut at 0x810e4 in both arms (real:
   sp = fr, AH by a_laws_store; side: sp = A, AH by a_laws_fs_store with the header off the FakeStack metadata,
   FSREC by a3_fsrec). ENT moves across the run by ent_munch / ent_mat, and the input facts (push 6c) by the run's
   write set missing the input block.
   v1.9 re-walk (table of record S_A3 (v190-segment-table.md (a working note, not in this delivery)), CHANGED frame-desc): every pc
   is v1.8 + 0x20; the frame description word at fr + 8 is 0x11b66 (0x80f90 `auipc a1,0xfff91` + 0x80fa8
   `addi a1,a1,-1066`; v1.8 0x20670), the function word at fr + 16 is 0x80edc (0x80f94 / 0x80fac, = AF.ENTRY of
   v1.9), the fill target is meta_fill_f8 at 0x55008 (0x810e0 `jal`), and the frame is FRAME_BYTES = 3136 bytes
   with FRAME_SHADOW = 392 shadow bytes, so the run keeps the last 137 (v1.8: 125) of them. The 87 instructions and
   their order are the v1.8 ones. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YN01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module BzB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.BzBridge.
Module UF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.
Module US := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Step.
Module UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module UM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module UCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.

(* ---- Engine glue. A byte store of a literal register value (`sb s2,o(s3)` with s2 = -8) leaves the bytes as
   le1 (Z_to_bv 64 z), which the UL engine's cell_of_bytes does not read; le1_lit turns them into [Z_to_bv 8 z]. *)
Lemma le1_lit : forall z, UM.le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold UM.le1. cbn [Z_to_le_bytes]. f_equal. apply UM.Z_to_bv8_mod.
  rewrite LMS.unsigned_lit_wrap. rewrite (Z.mod_eq z (2 ^ 64)) by lia.
  replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + (- (z / 2 ^ 64) * 2 ^ 56) * 2 ^ 8) by lia.
  apply Z.mod_add. lia.
Qed.

Local Ltac norm_lit_store_bytes ::=
  try (lazymatch goal with
       | |- UE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (UM.le1 (Z_to_bv 64 ?z))) _) =>
           is_Zlit z; rewrite (le1_lit z)
       | |- UE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (UM.le8 (Z_to_bv 64 z))
       | |- UE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (UM.le4 (Z_to_bv 64 z))
       | |- UE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (UM.le2 (Z_to_bv 64 z))
       | |- UE.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       end).

(* The library (Lib) evt of a callee contract composes with the UL engine's evt: both step the same machine. *)
Lemma lib_msteps_ul : forall s s', LEx.msteps rsegs s s' -> UE.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UE.msteps_refl|].
  eapply UE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma lib_evt_cut : forall (P Q : machine_state -> Prop) ms,
  LEx.evt rsegs P ms -> (forall ms', P ms' -> UE.evt rsegs Q ms') -> UE.evt rsegs Q ms.
Proof.
  intros P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply UE.msteps_trans; [exact (lib_msteps_ul _ _ H1) | exact H2] | exact HQ].
Qed.

Lemma ms_ul_lib : forall R F pc fc rv m ro, MS R F pc fc rv m ro = LMS.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.

(* No image segment reaches GT = 0x5fe000, so no byte at or above it is read-only. *)
Lemma ro_addr_hi : forall x, 0x5fe000 <= bv_unsigned x -> LMem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold LMem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (BzB.find_segment_below rsegs 0x5fe000 (bv_unsigned x) 1 s ltac:(vm_compute; reflexivity) E ltac:(lia))
    as [L|L]; lia.
Qed.

Lemma ro_addr_lo : forall x, LMem.ro_addr rsegs x = true -> bv_unsigned x < 0x5fe000.
Proof.
  intros x H. destruct (Z_lt_ge_dec (bv_unsigned x) 0x5fe000) as [L|L]; [exact L|].
  rewrite (ro_addr_hi x ltac:(lia)) in H. discriminate H.
Qed.

(* Bytes read the same in m and in its normal form (ro_agree). *)
Lemma bytes_norm : forall m a bs, ro_agree rsegs m -> LMem.bytes_at rsegs m a bs ->
  LMem.bytes_at rsegs (normalize rsegs m) a bs.
Proof.
  intros m a bs HRO (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi.
  rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m HRO)). exact (B2 i Hi).
Qed.

Lemma asan_cells_norm : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m HRO (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  refine (conj (bytes_norm _ _ _ HRO K1) (conj (bytes_norm _ _ _ HRO K2) (conj (bytes_norm _ _ _ HRO K3)
    (conj (bytes_norm _ _ _ HRO K4) (conj (bytes_norm _ _ _ HRO K5) (conj (bytes_norm _ _ _ HRO K6)
    (conj (bytes_norm _ _ _ HRO K7) (conj (bytes_norm _ _ _ HRO K8) (conj (bytes_norm _ _ _ HRO K9)
    (conj (bytes_norm _ _ _ HRO K10) (conj (bytes_norm _ _ _ HRO K11) (conj (bytes_norm _ _ _ HRO K12)
    (conj (bytes_norm _ _ _ HRO K13) (conj (bytes_norm _ _ _ HRO K14) (conj (bytes_norm _ _ _ HRO K15)
    (conj (bytes_norm _ _ _ HRO K16) (bytes_norm _ _ _ HRO K17))))))))))))))))).
Qed.

(* A UL junk cell block above GT is a Lib junk cell block of the normal form. *)
Lemma rw_norm : forall m a n junk, ro_agree rsegs m -> 0x5fe000 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  US.rw_cells rsegs m a [CB n junk] -> LSt.rw_cells rsegs (normalize rsegs m) a [LCl.CB n junk].
Proof.
  intros m a n junk HRO Ha Han ((Wf & RB) & WR).
  pose proof (mem_rel_normalize rsegs m HRO) as HREL.
  split; [split|].
  - exact Wf.
  - exact (bytes_norm m a _ HRO RB).
  - destruct WR as (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|]. intros i Hi.
    assert (Hi' : 0 <= i < Z.of_nat n)
      by (cbn [UCl.cells_size UCl.csize LCl.cells_size LCl.csize] in Hi; rewrite Nat.add_0_r in Hi; exact Hi).
    rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ HREL).
    + exact (W2 i Hi).
    + apply ro_addr_hi. rewrite LMem.wa_unsigned; lia.
Qed.

(* The shadow fill call at 0x810e0 through asan_set_shadow_f8_contract (Prog/asan_set_shadow_c.v:22-35; its entry
   ASAN_SET_SHADOW_F8 is meta_fill_f8, 0x55008 in v1.9), run on the normal form of the memory
   (MemNorm.evt_normalize: the contract asks mem_inv, the cut gives ro_agree). *)
Lemma f8_call : asan_set_shadow_f8_contract ->
  forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (a n : Z) junk,
  0x5fe000 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall i, 0 <= i < n -> in_shadow (a + i)) ->
  US.rw_cells rsegs m a [CB (Z.to_nat n) junk] -> asan_cells m -> ro_agree rsegs m ->
  (forall t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
     UF.munch [(a, a + n)] m m' -> UF.wmono rsegs m m' -> ro_agree rsegs m' ->
     LMem.bytes_at rsegs m' a (repeat (Z_to_bv 8 0xf8) (Z.to_nat n)) ->
     UE.evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                           s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  UE.evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                        s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x55008) fc None m (seg_rom rsegs)).
Proof.
  intros HC Q ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a n
    junk Ha Hn Han HIS HRW HAC HRO K.
  pose proof (mem_rel_normalize rsegs m HRO) as HREL.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply LMS.unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply LMS.unsigned_lit; lia).
  rewrite <- mkR_ul, ms_ul_lib.
  eapply lib_evt_cut.
  - apply (evt_normalize rsegs); [vm_compute; reflexivity | exact HRO |].
    pose proof (HC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
      s9 s10 s11 t3 t4 t5 t6 F fc (normalize rsegs m) junk) as H.
    cbv zeta in H. rewrite Ua, Un in H.
    apply H.
    + exact HIS.
    + apply (rw_norm m a (Z.to_nat n) junk HRO Ha); [rewrite Z2Nat.id by lia; lia | exact HRW].
    + exact (asan_cells_norm m HRO HAC).
    + apply mem_inv_normalize.
  - intros ms' (s0' & HP & HMS & HROS).
    destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> &
      MU & WM & MI & RW).
    rewrite Ua, Un in MU, RW.
    destruct ms' as [r' f' pc' svc' rv' fc' mm ro'].
    unfold ms_rel in HMS. cbn in HMS, HROS.
    destruct HMS as (Er & Ef & Epc & Esvc & Erv & Efc & Ero & HMR). subst r' f' pc' svc' rv' fc' ro'.
    refine (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mm _ _ _ _).
    + intros x Hx. destruct (LMem.ro_addr rsegs x) eqn:E.
      * exact (HROS x E).
      * rewrite <- (mem_rel_rw rsegs mm m'' x HMR E). rewrite (MU x Hx). unfold normalize. rewrite E. reflexivity.
    + intros x Hx. destruct (LMem.ro_addr rsegs x) eqn:E.
      * unfold wview in *. rewrite (HROS x E). exact Hx.
      * rewrite <- (wview_rel_rw rsegs mm m'' x HMR E). apply WM.
        rewrite (wview_rel_rw rsegs m (normalize rsegs m) x HREL E). exact Hx.
    + exact (ro_agree_of_mem_rel rsegs mm m'' HMR).
    + destruct RW as ((_ & RB) & _). cbn [LCl.cells_bytes LCl.cbytes] in RB. rewrite app_nil_r in RB.
      destruct RB as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      rewrite (mrd_rel rsegs mm m'' _ HMR). exact (B2 i Hi).
Qed.

Section Run.
Context {fx : FPState}.

(* The state at 0x810e4 the run gives: the footprint (spill, header, the 255 shadow bytes written), the written
   bytes, and the registers seg_A4 reads. *)
Definition KA (regs : bvmap 5 word) (mem : word -> option byte) (A fr S3 : Z)
    (R : bvmap 5 word) (pc' : word) (mem' : word -> option byte) : Prop :=
  pc' = Z_to_bv 64 0x810e4 /\
  LFr.munch [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem mem' /\
  LFr.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
  q64 mem' (A + 304) fr /\ q64 mem' fr 0x41b58ab3 /\ q64 mem' (fr + 8) 0x11b66 /\ q64 mem' (fr + 16) 0x80edc /\
  (exists sh, LMem.bytes_at rsegs mem' S3 sh /\ length sh = 68%nat) /\
  LMem.bytes_at rsegs mem' (S3 + 68) (repeat (Z_to_bv 8 0xf8) 187) /\
  getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
  getr R 9 = Z_to_bv 64 A /\ getr R 21 = getr regs 21 /\ getr R 22 = Z_to_bv 64 fr /\
  getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = Z_to_bv 64 ASAN_K /\
  getr R 18 = Z_to_bv 64 (-8) /\ getr R 19 = Z_to_bv 64 S3 /\ getr R 20 = Z_to_bv 64 (-14) /\
  getr R 25 = Z_to_bv 64 (S3 + 68).

Lemma a3_evt : asan_set_shadow_f8_contract ->
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr S3 : Z) j1 j2 j3 j4,
  getr regs 9 = Z_to_bv 64 A -> getr regs 22 = Z_to_bv 64 fr -> getr regs 26 = Z_to_bv 64 ASAN_K ->
  US.rw_cells rsegs mem (A + 304) [CB 8 j1] -> US.rw_cells rsegs mem fr [CB 24 j2] ->
  US.rw_cells rsegs mem S3 [CB 68 j3] -> US.rw_cells rsegs mem (S3 + 68) [CB 187 j4] ->
  fr + 24 <= A + 304 -> S3 + 255 <= A + 304 -> (fr + 24 <= S3 \/ S3 + 255 <= fr) ->
  0x5fe000 <= fr -> 0x5fe000 <= S3 -> S3 + 255 < 2 ^ 64 -> fr < 2 ^ 64 -> S3 = fr / 8 + ASAN_K ->
  (forall i, 0 <= i < 187 -> in_shadow (S3 + 68 + i)) ->
  asan_cells mem -> ro_agree rsegs mem ->
  UE.evt rsegs (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
                   KA regs mem A fr S3 R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x80f88) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros HC regs mem A fr S3 j1 j2 j3 j4 H9 H22 H26 C1 C2 C3 C4 D1 D2 D3 G1 G2 G3 Hfr HS3 HIS HAC HRO.
  assert (H9' : reg_get regs 9 = Z_to_bv 64 A) by exact H9.
  assert (H22' : reg_get regs 22 = Z_to_bv 64 fr) by exact H22.
  assert (H26' : reg_get regs 26 = Z_to_bv 64 ASAN_K) by exact H26.
  unfold Regs6ss.mkR_of. rewrite mkR_ul. rewrite H9', H22', H26'.
  clear H9 H22 H26 H9' H22' H26'.
  pose proof (UF.munch_refl [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem) as MU.
  pose proof (UF.wmono_refl rsegs mem) as WM.
  do 15 step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 fr)) 3 + ASAN_K)) with (Z_to_bv 64 S3)
    by (f_equal; rewrite LMS.unsigned_lit by lia; rewrite Z.shiftr_div_pow2 by lia; exact HS3).
  do 68 step.
  do 4 step.
  match goal with |- UE.evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HW : forall x : word, 0x5fe000 > bv_unsigned x ->
             UF.outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] (bv_unsigned x)).
  { intros x Hx. cbn [UF.outside]. repeat split; intros [? ?]; lia. }
  assert (HRO1 : ro_agree rsegs m1).
  { intros x Hx. rewrite <- (HRO x Hx). unfold LMem.mrd. rewrite (MU x (HW x ltac:(pose proof (ro_addr_lo x Hx); lia))).
    reflexivity. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem m1 HAC MU).
    cbn [LFr.disjoint_from UF.disjoint_from]. unfold RT_LO, RT_HI. repeat split; lia. }
  eapply (f8_call HC); [lia | lia | lia | exact HIS | exact C4 | exact HAC1 | exact HRO1 |].
  intros t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 MU2 WM2 HRO2 HB2.
  apply UE.evt_done. cbv beta. eexists _, _, m2. split; [reflexivity|].
  unfold KA.
  assert (DJ : forall a k, (a + k <= S3 + 68 \/ S3 + 68 + 187 <= a) -> LFr.disjoint_from [(S3 + 68, S3 + 68 + 187)] a k).
  { intros a k Hd. cbn [LFr.disjoint_from]. split; [exact Hd | exact I]. }
  pose proof (LFr.bytes_at_transport rsegs [(S3 + 68, S3 + 68 + 187)] m1 m2) as TR.
  destruct C1 as ((_ & B1) & _). cbn [UCl.cells_bytes UCl.cbytes] in B1. rewrite app_nil_r in B1.
  destruct C2 as ((_ & B2) & _). cbn [UCl.cells_bytes UCl.cbytes] in B2. rewrite app_nil_r in B2.
  apply (UM.bytes_at_app rsegs) in B2 as [B2a B2r]. rewrite UM.length_le8 in B2r.
  apply (UM.bytes_at_app rsegs) in B2r as [B2b B2c]. rewrite UM.length_le8 in B2c.
  replace (fr + Z.of_nat 8 + Z.of_nat 8) with (fr + 16) in B2c by lia.
  replace (fr + Z.of_nat 8) with (fr + 8) in B2b by lia.
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split.
  { apply (LFr.munch_trans _ mem m1 m2); [exact MU|].
    apply (LFr.munch_weaken [(S3 + 68, S3 + 68 + 187)] _ m1 m2); [|exact MU2].
    intros x Hx. cbn [LFr.outside] in *. destruct Hx as (_ & _ & _ & H4 & _). split; [|exact I].
    intros ?; apply H4; lia. }
  split; [exact (LFr.wmono_trans rsegs mem m1 m2 WM WM2)|].
  split; [exact HRO2|].
  split.
  { unfold q64. apply TR; [exact B1 | exact MU2 |].
    apply DJ. rewrite ?LMem.length_le8, ?UM.length_le8. lia. }
  split.
  { unfold q64. apply TR; [exact B2a | exact MU2 |].
    apply DJ. rewrite ?LMem.length_le8, ?UM.length_le8. lia. }
  split.
  { unfold q64. apply TR; [exact B2b | exact MU2 |].
    apply DJ. rewrite ?LMem.length_le8, ?UM.length_le8. lia. }
  split.
  { unfold q64. apply TR; [exact B2c | exact MU2 |].
    apply DJ. rewrite ?LMem.length_le8, ?UM.length_le8. lia. }
  split.
  { lazymatch type of C3 with US.rw_cells _ _ _ ?cs =>
      destruct C3 as ((Wf3 & B3) & _);
      assert (L3 : length (UCl.cells_bytes cs) = 68%nat)
        by (rewrite (UCl.cells_bytes_length cs Wf3); vm_compute; reflexivity);
      exists (UCl.cells_bytes cs); split; [|exact L3]
    end.
    apply TR; [exact B3 | exact MU2 | apply DJ; rewrite L3; lia]. }
  split; [exact HB2|].
  repeat (split; [reflexivity|]). reflexivity.
Qed.

End Run.

(* ---- Memory facts for the cut assembly at 0x810e4. *)
Lemma word_mem_det : forall m a v v', 0 <= a -> a + 8 <= 2 ^ 64 ->
  word_mem rsegs m a v -> word_mem rsegs m a v' -> v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros m a v v' H0 H1 Hv Hv'.
  destruct (YN01.word_mem_ld rsegs m a v Hv H0 H1) as (bs & Hr & Hb).
  destruct (YN01.word_mem_ld rsegs m a v' Hv' H0 H1) as (bs' & Hr' & Hb').
  rewrite Hr in Hr'. injection Hr' as <-. rewrite Hb in Hb'.
  rewrite !LMS.unsigned_lit_wrap in Hb'. exact Hb'.
Qed.

Lemma word_mem_keep : forall m m' a v, word_mem rsegs m a v ->
  (forall k, 0 <= k < 8 -> mbyte rsegs m' (a + k) = mbyte rsegs m (a + k)) -> word_mem rsegs m' a v.
Proof. intros m m' a v H K k Hk. rewrite (K (Z.of_nat k)) by lia. exact (H k Hk). Qed.

Lemma disj_hi : forall W a n, (forall lo hi, In (lo, hi) W -> 0x5fe000 <= lo) -> a + n <= 0x5fe000 ->
  LFr.disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Han; cbn [LFr.disjoint_from]; [exact I|].
  split; [left; pose proof (HW lo hi (or_introl eq_refl)); lia|].
  apply IH; [intros lo' hi' Hin; exact (HW lo' hi' (or_intror Hin)) | exact Han].
Qed.

Lemma rt_disjoint_hi : forall W, (forall lo hi, In (lo, hi) W -> 0x5fe000 <= lo) -> rt_disjoint W.
Proof.
  intros W HW. unfold rt_disjoint.
  repeat split; apply disj_hi; try exact HW;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

Lemma rd_of_bytes : forall m a bs x, LMem.bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, LMem.mrd rsegs m (LMem.wa x) = Some b.
Proof.
  intros m a bs x (B0 & B1 & B2) Hx.
  assert (Hj : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (B2 (Z.to_nat (x - a)) Hj) as E. rewrite Z2Nat.id in E by lia.
  replace (a + (x - a)) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:N; [exists b; exact E|].
  apply nth_error_None in N. lia.
Qed.

Lemma bytes_of_readable : forall m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, LMem.mrd rsegs m (LMem.wa (a + i)) = Some b) ->
  exists bs, LMem.bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a H0 H1 HR.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (HR 0 ltac:(lia)) as (b & Hb).
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply HR. lia. }
    exists (b :: bs). split; [|cbn; rewrite Hl; reflexivity].
    change (b :: bs) with ([b] ++ bs).
    apply (proj2 (LMem.bytes_at_app rsegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0%nat) as -> by lia.
      exact Hb.
    + replace (a + Z.of_nat (length [b])) with (a + 1) by (cbn; lia). exact Hbs.
Qed.

Lemma out_or_in4 : forall x a1 b1 a2 b2 a3 b3 a4 b4,
  LFr.outside [(a1, b1); (a2, b2); (a3, b3); (a4, b4)] x \/
  (a1 <= x < b1 \/ a2 <= x < b2 \/ a3 <= x < b3 \/ a4 <= x < b4).
Proof.
  intros. assert (D : forall lo hi, {lo <= x < hi} + {~ (lo <= x < hi)}).
  { intros lo hi. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi);
      [left; lia | right; lia | right; lia | right; lia]. }
  destruct (D a1 b1); [right; left; assumption|]. destruct (D a2 b2); [right; right; left; assumption|].
  destruct (D a3 b3); [right; right; right; left; assumption|].
  destruct (D a4 b4); [right; right; right; right; assumption|].
  left. cbn [LFr.outside]. tauto.
Qed.

Lemma stk_keep : forall W m m' lo hi, LFr.stk rsegs m lo hi -> LFr.munch W m m' -> LFr.wmono rsegs m m' ->
  (forall x, lo <= x < hi -> LFr.outside W x \/ exists b, LMem.mrd rsegs m' (LMem.wa x) = Some b) ->
  LFr.stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (S0 & S1 & S) MU WM K. split; [exact S0|]. split; [exact S1|]. intros a Ha.
  destruct (S a Ha) as (Hw & Hb). split; [exact (WM _ Hw)|].
  destruct (K a Ha) as [Ho | Hr]; [|exact Hr].
  destruct Hb as (b & Hb). exists b. unfold LMem.mrd in *. rewrite (MU (LMem.wa a)); [exact Hb|].
  rewrite LMem.wa_unsigned by lia. exact Ho.
Qed.

Lemma fs_meta_in : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj ->]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

Lemma addressable_keep : forall m m' p n, addressable m p n ->
  (forall i, 0 <= i < n ->
     LMem.mrd rsegs m' (LMem.wa (shadow_addr (p + i))) = LMem.mrd rsegs m (LMem.wa (shadow_addr (p + i)))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) K. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|]. exists b. split; [|exact Hok].
  rewrite (K i Hi). exact Hb.
Qed.

Lemma frame_AG_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Ha).
  assert (HB : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB. specialize (HB (lo, len) Hin). cbn [fst snd] in HB.
  apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* The same bound for frame_RELRO, read off the list by computation, so it holds whatever the number of its ranges
   (FrameAPI frame batch 2 has one GNU_RELRO range, v1.8 had three). *)
Lemma frame_RELRO_lo : forall a, in_globals AF.frame_RELRO a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Ha).
  assert (HB : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_RELRO = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB. specialize (HB (lo, len) Hin). cbn [fst snd] in HB.
  apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* Contract.v's a_store_ok (generated), built in ONE place per case this file needs: a real-stack byte, and the
   shadow byte of a real-stack byte. Every site below goes through these two lemmas. *)
Lemma a3_store_ok_stk : forall H lo a, lo <= a < APPMEM_END -> AC.a_store_ok H lo a.
Proof. intros H lo a Ha. unfold AC.a_store_ok. right; left. exact Ha. Qed.

Lemma a3_store_ok_stk_shadow : forall H lo b, lo <= b < APPMEM_END -> AC.a_store_ok H lo (shadow_addr b).
Proof.
  intros H lo b Hb. unfold AC.a_store_ok. right; right; right. exists b. split; [reflexivity|]. right; left. exact Hb.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The shadow fill meta_fill_f8 at 0x810e0 (callee 0x55008), used through its contract only. *)
Hypothesis SSF8 : asan_set_shadow_f8_contract.

(* The generated laws of Contract.v, read ONCE each in this file and only through SlotInv's LawFields records
   (lw_fs_place / lw_fs_ok + lw_fs_bytes / lw_store / lw_mat_le / lw_blocks, which match each field to the law by
   statement): no positional destruct of a generated conclusion is left here. Every site below goes through these
   five lemmas. *)
Lemma a3_fs_place : forall H mem md b, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  YO0d.word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb.
  destruct (lw_fs_place (APIf rc) H mem md b HAH Hw Hb) as [Hgt Hlo _ Happ].
  exact (conj Hgt (conj Hlo Happ)).
Qed.

Lemma a3_fs_rw : forall H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  YO0d.word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  forall a, FS <= a < FS + AC.FS_SIZE -> YP09.writable_at rsegs mem a /\ exists b, YP09.mbyte rsegs mem a = Some b.
Proof.
  intros H mem md FS HAH Hw HFS.
  exact (lw_fs_bytes mem FS (lw_fs_ok (APIf rc) H mem md FS HAH Hw HFS)).
Qed.

Lemma a3_store : forall H mem mem' md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> YP09.writable_at rsegs mem a -> YP09.writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hk Hw.
  destruct (lw_store (APIf rc) H mem mem' md HAH Hk Hw) as [H1 _ H3 H4].
  exact (conj H1 (conj H3 H4)).
Qed.

Lemma a3_mat_le : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hm.
  destruct (lw_mat_le (APIf rc) H mem md md' Hm) as [H1 _ H3 _].
  exact (conj H1 H3).
Qed.

Lemma a3_blocks : forall H mem md p n, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ Hend _ Hall].
  split; [exact Hend|]. intros a Ha.
  destruct (Hall a Ha) as (Happ & _ & _ & _ & Hnfs). exact (conj Happ Hnfs).
Qed.

(* FSREC (the side-arm FakeStack record of SlotInv.v) moves across A3's run. The run writes the spill
   [A + 304, A + 312) (at or above stklo), the header [fr, fr + 24) and shadow bytes (never app memory); the record's
   cells (the tp word in the low image, the class-6 flag byte FS + 36352 + j below the frames, the slot's last word
   at fr + 4088) are app bytes below stklo (a_laws_fs_place: FS + FS_SIZE <= stklo) and outside
   [fr, fr + FRAME_BYTES). Tac_slot's fsrec_stklo / fsrec_munch_lo exclude only the frame body
   [fr + 24, fr + FRAME_BYTES), so they do not take the header store. *)
Lemma a3_fsrec : forall H mem mem' md W fr, FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> LFr.munch W mem mem' ->
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr <= x < fr + FRAME_BYTES) -> LFr.outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros H mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HW.
  destruct (a3_fs_place H mem md FS HAH Htp HFSr) as (HGTb & HFSlo & Happ).
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  assert (Htpb : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= 0x5fe000)
    by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64) by lia.
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite LMS.unsigned_lit by exact Hx.
      apply HW; [unfold app_mem, LOWMEM_END; left; lia | lia | lia]. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; [| lia | lia].
    replace x with (SMC.fs_flag FS 6 j) by lia. apply Happ. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    intros x Hx. rewrite ?LMem.length_le8, ?UM.length_le8 in Hx. rewrite HB6 in Hx.
    apply HW; [apply Happ; lia | lia | lia]. }
Qed.

(* Segment A3 (0x80f88-0x810e0 and the call at 0x810e0, plan-asan FP.2-FP.4): the spill `sd s6,304(s1)`, the frame
   header (0x41b58ab3, 0x11b66, 0x80edc at fr, fr + 8, fr + 16), s3 = S(fr), the 68 single-byte shadow stores at
   S(fr) .. S(fr) + 67, s9 = S(fr) + 68 and the f8 fill of S(fr) + 68 .. S(fr) + 254; the other 137 frame shadow bytes
   (S(fr) + 255 .. S(fr) + 391) keep their bytes. Both arms of Inv_A80f88 (real: sp = fr; side: sp = A) carry
   through to the FRAS cut. *)
Lemma seg_A3 : Hcut B APIf ra (Inv_A810e4 B APIf ra) -> Hcut B APIf ra (Inv_A80f88 B APIf ra).
Proof.
  intros H810 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HInv as (regs & mem & md & A & fr & sp & s5 & Ec & HP & HENT & Hr22 & Hfrm & Hr21 & Hfr & HfA & Hs5 &
    Hr23 & Hr24 & Harm & Hinb & Hina).
  subst c. rewrite SEGS.
  destruct HP as (HRT & HAH & HRO & HSN & HHALT & HGIMG & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 & Hr3 &
    Hr26 & HAm & HAS & HA432 & HspA & HA416 & HS4096 & HSAPP & HWIN & HSAVED & HERRNO & HAG & HWA & HSHI1 &
    HSHI2 & HSHI3 & HNMAX & HLIVE).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as HL.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ HL (g_H g) mem md HAH) as HSH.
  assert (Htp : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= 0x5fe000)
    by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  unfold AF.SLOT_STACK in *.
  (* The frame: AppMem, at or above GT (both arms). *)
  assert (FR : (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ AC.GT <= fr).
  { destruct Harm as [(Hs50 & Hspfr & Hloc) | (Hs5fr & HspA' & Hsep & Hloc & _)].
    - split.
      + intros a Ha. destruct (Hloc a Ha) as [L1 L2]. right. lia.
      + pose proof (Hloc fr ltac:(lia)) as [L1 _]. unfold AC.GT, HIGHMEM_BEG in *. lia.
    - destruct (Hloc fr ltac:(lia)) as (FS & HFS & HFw & HFr).
      destruct (a3_fs_place (g_H g) mem md FS HAH HFw HFS) as (Hgt & _ & _).
      pose proof (Hsep FS HFw HFS) as Hs. split; [|lia].
      intros a Ha. destruct (Hloc a Ha) as (b & Hb & Hbw & Hba).
      destruct (a3_fs_place (g_H g) mem md b HAH Hbw Hb) as (_ & _ & Happ).
      exact (Happ a Hba). }
  destruct FR as (Fapp & Fgt).
  unfold AC.GT in Fgt.
  set (S3 := Sfr fr).
  assert (HS3 : S3 = fr / 8 + ASAN_K) by reflexivity.
  assert (Ffr8 : fr mod 8 = 0) by lia.
  assert (SHI : forall y, S3 <= y < S3 + 392 -> in_shadow y).
  { intros y Hy. apply (shadow_range_in fr 392); [lia | lia | lia | | exact Hy].
    intros x Hx. apply Fapp. lia. }
  assert (SHlo : 0x7fff8000 <= S3) by (pose proof (SHI S3 ltac:(lia)) as X; unfold in_shadow, LOWMEM_END,
    LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X; lia).
  assert (SHhi : S3 + 392 <= HIGHMEM_BEG) by (pose proof (SHI (S3 + 391) ltac:(lia)) as X; unfold in_shadow,
    LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X |- *; lia).
  assert (FAPP0 : fr + 24 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Fapp fr ltac:(lia)) as X1. pose proof (Fapp (fr + 23) ltac:(lia)) as X2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (D3 : fr + 24 <= S3 \/ S3 + 392 <= fr).
  { apply (app_shadow_apart fr (fr + 24) S3 392); [intros x Hx; apply Fapp; lia | lia | exact SHI | lia]. }
  assert (HA : HIGHMEM_BEG <= A) by lia.
  (* The four store regions as junk cells. *)
  destruct (stk_junk mem (g_S g - 1048576) (g_S g) (A + 304) 8 HWIN ltac:(lia) ltac:(lia)) as (j1 & C1).
  pose proof (shadow_stk mem fr 255 (AsanRTInv.RT_shadow_rw _ _ _ HRT) ltac:(lia) Ffr8 ltac:(lia)
    ltac:(intros x Hx; apply Fapp; lia)) as SST.
  destruct (stk_junk mem S3 (S3 + 255) S3 68 SST ltac:(lia) ltac:(lia)) as (j3 & C3).
  destruct (stk_junk mem S3 (S3 + 255) (S3 + 68) 187 SST ltac:(lia) ltac:(lia)) as (j4 & C4).
  assert (HDR : exists j2, US.rw_cells rsegs mem fr [CB 24 j2]).
  { destruct Harm as [(Hs50 & Hspfr & Hloc) | (Hs5fr & HspA' & Hsep & Hloc & _)].
    - subst sp. exact (stk_junk mem (g_S g - 1048576) (g_S g) fr 24 HWIN ltac:(lia) ltac:(lia)).
    - destruct (Hloc fr ltac:(lia)) as (FS & HFS & HFw & HFr).
      destruct (Hloc (fr + 23) ltac:(lia)) as (b & Hb & Hbw & Hba).
      pose proof (word_mem_det mem (AC.as_tp AC.ASYMS) b FS ltac:(lia) ltac:(lia) Hbw HFw) as E.
      rewrite !Z.mod_small in E by lia. subst b.
      pose proof (a3_fs_rw (g_H g) mem md FS HAH HFw HFS) as P1.
      destruct (a3_fs_place (g_H g) mem md FS HAH HFw HFS) as (_ & Hlo & _).
      assert (STF : LFr.stk rsegs mem FS (FS + AC.FS_SIZE)).
      { split; [lia|]. split; [unfold AC.FS_SIZE, APPMEM_END in *; lia|]. intros a Ha. exact (P1 a Ha). }
      exact (stk_junk mem FS (FS + AC.FS_SIZE) fr 24 STF ltac:(unfold AC.FS_SIZE in *; lia)
               ltac:(unfold AC.FS_SIZE in *; lia)). }
  destruct HDR as (j2 & C2).
  (* AH and stklo across a run whose writes are confined to the four regions (the store laws per arm). *)
  assert (AHLAW : forall mem',
    LFr.munch [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem mem' ->
    LFr.wmono rsegs mem mem' ->
    (forall x, (A + 304 <= x < A + 312 \/ fr <= x < fr + 24 \/ S3 <= x < S3 + 255) ->
       exists b, LMem.mrd rsegs mem' (LMem.wa x) = Some b) ->
    AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem' md /\
    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
    AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { intros mem' MU WM RDW.
    assert (WMw : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
    { intros a _ Ha. exact (WM _ Ha). }
    assert (KBw : forall x, 0 <= x < 2 ^ 64 ->
              LFr.outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Ho. apply MU. rewrite LMS.unsigned_lit by exact Hx. exact Ho. }
    assert (SHEQ : forall a, S3 <= a < S3 + 255 -> a = shadow_addr (fr + 8 * (a - S3))).
    { intros a Ha. unfold shadow_addr. replace (fr + 8 * (a - S3)) with (fr + (a - S3) * 8) by ring.
      rewrite Z.div_add by lia. rewrite HS3 in Ha |- *. lia. }
    destruct Harm as [(Hs50 & Hspfr & Hloc) | (Hs5fr & HspA' & Hsep & Hloc & _)].
    - assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
                ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
                mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply KBw; [exact Ha|].
        destruct (out_or_in4 a (A + 304) (A + 312) fr (fr + 24) S3 (S3 + 68) (S3 + 68) (S3 + 255)) as [Ho|Hin];
          [exact Ho|].
        exfalso. apply Hns.
        destruct Hin as [Hin|[Hin|Hin]].
        + apply a3_store_ok_stk. lia.
        + apply a3_store_ok_stk. apply Hloc; lia.
        + rewrite (SHEQ a ltac:(lia)). apply a3_store_ok_stk_shadow. apply Hloc. lia. }
      destruct (a3_store (g_H g) mem mem' md HAH P1 WMw) as (H1 & H3 & H4).
      split; [exact H1 | split; [exact H3 | exact H4]].
    - destruct (Hloc fr ltac:(lia)) as (FS & HFS & HFw & HFr).
      pose proof (Hsep FS HFw HFS) as Hs.
      destruct (a3_fs_place (g_H g) mem md FS HAH HFw HFS) as (Hgt & Hlo & Happ).
      assert (Fin : forall a, fr <= a < fr + FRAME_BYTES -> FS <= a < FS + AC.FS_SIZE).
      { intros a Ha. destruct (Hloc a Ha) as (b & Hb & Hbw & Hba).
        pose proof (word_mem_det mem (AC.as_tp AC.ASYMS) b FS ltac:(lia) ltac:(lia) Hbw HFw) as E.
        rewrite !Z.mod_small in E by lia. subst b. exact Hba. }
      pose proof (Happ (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as HappE.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HappE.
      destruct (a_fs_ok_store_AH _ _ _ _ _ [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)]
        (g_H g) mem mem' md FS HL HAH HFw HFS ltac:(unfold AC.FS_SIZE in *; lia) MU WMw) as (H1 & _ & H3 & H4).
      + intros q Hq Hb.
        destruct (out_or_in4 q (A + 304) (A + 312) fr (fr + 24) S3 (S3 + 68) (S3 + 68) (S3 + 255)) as [Ho|Hin].
        * unfold mbyte. rewrite (KBw q Hq Ho). exact Hb.
        * apply RDW. destruct Hin as [H|[H|[H|H]]]; [left | right; left | right; right | right; right]; lia.
      + intros q Hq. pose proof (fs_meta_in FS q Hq) as [Q1 Q2].
        assert (Qa : app_mem q) by (apply Happ; unfold AC.FS_SIZE; lia).
        cbn [LFr.outside]. split; [lia|]. split; [lia|].
        split; [intros ?; apply (app_not_shadow q Qa); apply SHI; lia|].
        split; [intros ?; apply (app_not_shadow q Qa); apply SHI; lia|]. exact I.
      + intros q Hq Hns Hnf Hnsh. apply KBw; [exact Hq|].
        destruct (out_or_in4 q (A + 304) (A + 312) fr (fr + 24) S3 (S3 + 68) (S3 + 68) (S3 + 255)) as [Ho|Hin];
          [exact Ho|].
        exfalso. destruct Hin as [Hin|[Hin|Hin]].
        * apply Hns. apply a3_store_ok_stk. lia.
        * apply Hnf. apply Fin. lia.
        * apply Hnsh. exists (fr + 8 * (q - S3)). split; [apply Fin; lia | apply SHEQ; lia].
      + split; [exact H1 | split; [exact H3 | exact H4]]. }
  assert (G3' : S3 + 255 < 2 ^ 64) by (unfold HIGHMEM_BEG in SHhi; lia).
  apply (sl_run regs (Z_to_bv 64 0x80f88) mem md (KA regs mem A fr S3) (Post B APIf ra g)).
  - exact HHALT.
  - exact (a3_evt SSF8 regs mem A fr S3 j1 j2 j3 j4 Hr9 Hr22 Hr26 C1 C2 C3 C4 ltac:(lia) ltac:(lia) ltac:(lia)
      Fgt ltac:(lia) G3' ltac:(lia) HS3 ltac:(intros i Hi; apply SHI; lia) (AsanRTInv.RT_cells _ _ _ HRT) HRO).
  - intros R pc' mem' regs' md' HK Hreg Hmat.
    destruct HK as (Hpc & MU & WM & HRO' & Hsp & Hh0 & Hh8 & Hh16 & Hsh68 & Hsh187 & R2 & R3 & R4 & R8 & R9 & R21 &
      R22 & R23 & R24 & R26 & R18 & R19 & R20 & R25).
    subst pc'.
    destruct Hsh68 as (sh68 & Hb68 & Hl68).
    assert (SH255 : LMem.bytes_at rsegs mem' S3 (sh68 ++ repeat (Z_to_bv 8 0xf8) 187)).
    { apply (proj2 (LMem.bytes_at_app rsegs mem' S3 sh68 _)). split; [exact Hb68|]. rewrite Hl68. exact Hsh187. }
    assert (RDW : forall x, (A + 304 <= x < A + 312 \/ fr <= x < fr + 24 \/ S3 <= x < S3 + 255) ->
                  exists b, LMem.mrd rsegs mem' (LMem.wa x) = Some b).
    { intros x [Hx|[Hx|Hx]].
      - apply (rd_of_bytes mem' (A + 304) _ x Hsp). rewrite LMem.length_le8. lia.
      - destruct (Z_lt_ge_dec x (fr + 8)) as [L|L]; [|destruct (Z_lt_ge_dec x (fr + 16)) as [L'|L']].
        + apply (rd_of_bytes mem' fr _ x Hh0). rewrite LMem.length_le8. lia.
        + apply (rd_of_bytes mem' (fr + 8) _ x Hh8). rewrite LMem.length_le8. lia.
        + apply (rd_of_bytes mem' (fr + 16) _ x Hh16). rewrite LMem.length_le8. lia.
      - apply (rd_of_bytes mem' S3 _ x SH255). rewrite length_app, repeat_length, Hl68. lia. }
    assert (KBw : forall x, 0 <= x < 2 ^ 64 ->
              LFr.outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Ho. apply MU. rewrite LMS.unsigned_lit by exact Hx. exact Ho. }
    assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
    { intros sg x H0 H1. unfold mbyte. rewrite (KBw x ltac:(lia)); [reflexivity|].
      cbn [LFr.outside]. repeat split; intros [? ?]; lia. }
    assert (KBsh : forall x, ASAN_K <= x < ASAN_K + 0xbfc00 ->
              LMem.mrd rsegs mem' (LMem.wa x) = LMem.mrd rsegs mem (LMem.wa x)).
    { intros x Hx. unfold LMem.mrd, LMem.wa.
      rewrite (KBw x ltac:(unfold ASAN_K in *; lia)); [reflexivity|].
      cbn [LFr.outside]. unfold ASAN_K, LOWMEM_END, HIGHMEM_BEG in *.
      repeat split; intros [? ?]; lia. }
    destruct (AHLAW mem' MU WM RDW) as (HAH1 & HSTK1 & HSTKhi1).
    destruct (a3_mat_le (g_H g) mem' md md' Hmat) as (HAHm & HSTK2).
    assert (HSTK : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
      by (rewrite HSTK2; exact HSTK1).
    assert (TPK : forall k, 0 <= k < 16 -> mbyte rsegs mem' (AC.as_tp AC.ASYMS + k) =
                                         mbyte rsegs mem (AC.as_tp AC.ASYMS + k)).
    { intros k Hk. apply KBlo; lia. }
    (* the 137 frame shadow bytes S(fr) + 255 .. S(fr) + 391 are kept *)
    assert (G4 : S3 + 392 <= 2 ^ 64) by (unfold HIGHMEM_BEG in SHhi; lia).
    destruct (bytes_of_readable mem (S3 + 255) 137 ltac:(lia) ltac:(change (Z.of_nat 137) with 137; lia))
      as (old & Hold & Hlold).
    { intros i Hi. change (Z.of_nat 137) with 137 in Hi.
      destruct (AsanRTInv.RT_shadow_rw _ _ _ HRT (S3 + 255 + i) (SHI (S3 + 255 + i) ltac:(lia))) as (_ & b & Hb).
      exists b. exact Hb. }
    assert (Hold' : LMem.bytes_at rsegs mem' (S3 + 255) old).
    { apply (LFr.bytes_at_transport rsegs [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)]
        mem mem'); [exact Hold | exact MU |].
      rewrite Hlold. change (Z.of_nat 137) with 137. cbn [LFr.disjoint_from]. repeat split; lia. }
    (* ---- write-set facts for FSREC, ENT, the window and the input facts *)
    assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
    assert (Ffr0 : 0 <= fr) by lia.
    assert (KBmrd : forall x, 0 <= x < 2 ^ 64 ->
              LFr.outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] x ->
              LMem.mrd rsegs mem' (LMem.wa x) = LMem.mrd rsegs mem (LMem.wa x)).
    { intros x Hx Ho. unfold LMem.mrd, LMem.wa. rewrite (KBw x Hx Ho). reflexivity. }
    assert (APP304 : forall x, A + 304 <= x < A + 312 -> app_mem x).
    { intros x Hx. unfold app_mem. right. lia. }
    (* a frame shadow byte is the shadow of a frame byte *)
    assert (Hshfr : forall b, 0 <= b -> ~ (fr <= b < fr + 3136) -> ~ (S3 <= shadow_addr b < S3 + 392)).
    { intros b Hb0 Hnb Hin. apply Hnb. rewrite HS3 in Hin. unfold shadow_addr in Hin.
      revert Hin Ffr8 Hb0 Ffr0. clear. intros. Z.div_mod_to_equations. lia. }
    (* the shadow byte of an app byte off the frame is outside the write set *)
    assert (SHOUT : forall b, app_mem b -> ~ (fr <= b < fr + FRAME_BYTES) ->
              LFr.outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] (shadow_addr b)).
    { intros b Hab Hnb. pose proof (shadow_of_app b Hab) as Hsb.
      assert (Hb0 : 0 <= b) by (unfold app_mem, LOWMEM_END, APPMEM_END in Hab; lia).
      cbn [LFr.outside].
      split; [intros Hx; exact (app_not_shadow (shadow_addr b) (APP304 (shadow_addr b) Hx) Hsb)|].
      split; [intros Hx; exact (app_not_shadow (shadow_addr b) (Fapp (shadow_addr b) ltac:(lia)) Hsb)|].
      split; [intros Hx; exact (Hshfr b Hb0 Hnb ltac:(lia))|].
      split; [intros Hx; exact (Hshfr b Hb0 Hnb ltac:(lia))|]. exact I. }
    (* an entry block's byte (the input block among them) is app memory below stklo, off the frame (real arm: the
       frame is at or above stklo; side arm: it is in the FakeStack, which no block meets), outside the write set *)
    assert (BLK : forall q k, In (q, k) (g_H g) -> forall x, q <= x < q + k ->
              app_mem x /\ 0 <= x < 2 ^ 64 /\ ~ (fr <= x < fr + FRAME_BYTES) /\
              LFr.outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] x).
    { intros q k Hin x Hx.
      destruct (a3_blocks (g_H g) mem md q k HAH Hin) as (Hend & Hall).
      destruct (Hall x Hx) as (Happx & Hnfs).
      assert (Hxr : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx; lia).
      assert (Hnf : ~ (fr <= x < fr + FRAME_BYTES)).
      { intros Hf. destruct Harm as [(Hs50 & Hspfr & Hloc) | (Hs5fr & HspA' & Hsep & Hloc & _)].
        - destruct (Hloc x Hf) as (Hr1 & _). lia.
        - exact (Hnfs (Hloc x Hf)). }
      split; [exact Happx|]. split; [exact Hxr|]. split; [exact Hnf|].
      cbn [LFr.outside].
      split; [lia|]. split; [lia|].
      split; [intros Hs; exact (app_not_shadow x Happx (SHI x ltac:(lia)))|].
      split; [intros Hs; exact (app_not_shadow x Happx (SHI x ltac:(lia)))|]. exact I. }
    rewrite <- SEGS. apply H810.
    unfold Inv_A810e4, CUTST0.
    exists regs', mem', md', fr, s5. split; [reflexivity|].
    split; [|split].
    + unfold FRAS, FRAH. exists A, sp.
      split.
      { apply (AsanRTInv.RT_meta_write sp sp mem mem' md md'
          [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] HRT MU WM).
        - apply rt_disjoint_hi. intros lo hi Hin. cbn in Hin.
          destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
        - intros a Ha. pose proof (in_shadow_range a Ha) as Ra.
          destruct (out_or_in4 a (A + 304) (A + 312) fr (fr + 24) S3 (S3 + 68) (S3 + 68) (S3 + 255)) as [Ho|Hin].
          + destruct (AsanRTInv.RT_shadow_rw _ _ _ HRT a Ha) as (_ & b & Hb). exists b.
            unfold LMem.mrd, LMem.wa in *. rewrite (KBw a ltac:(lia) Ho). exact Hb.
          + apply RDW. destruct Hin as [H|[H|[H|H]]]; [left | right; left | right; right | right; right]; lia. }
      split; [exact (HAHm HAH1)|].
      split; [exact HRO'|].
      split.
      { destruct HSN as (Hcse & Hohd & Hfd). split; [|split].
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
          + rewrite Hhead. lia.
        - rewrite (sl_mat_fds md md' Hmat). exact Hfd. }
      split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact HHALT|].
      split.
      { intros a Hin. rewrite KBlo.
        - exact (HGIMG a Hin).
        - pose proof (frame_RELRO_lo a Hin) as Ra. lia.
        - pose proof (frame_RELRO_lo a Hin) as Ra. lia. }
      split; [rewrite Hreg, R2; exact Hr2|].
      split; [exact Hspm|].
      split; [unfold AC.aspZ in *; rewrite Hreg, R2; exact Haspz|].
      split; [rewrite HSTK; exact Hstklo|].
      split; [rewrite Hreg, R4; exact Hr4|].
      split; [unfold rg in *; rewrite Hreg, R8; exact Hr8|].
      split; [unfold rg in *; rewrite Hreg; exact R9|].
      split; [rewrite Hreg, R3; exact Hr3|].
      split; [unfold rg in *; rewrite Hreg; exact R19|].
      split; [unfold rg in *; rewrite Hreg; exact R26|].
      split; [exact Hfrm|].
      split; [exact Hs5|].
      split; [exact HAm|].
      split; [exact HAS|].
      split; [exact HspA|].
      split; [exact HfA|].
      split; [exact HA416|].
      split; [exact HS4096|].
      split; [exact HSAPP|].
      split; [exact Hsp|].
      split.
      { destruct Harm as [(Hs50 & Hspfr & Hloc) | (Hs5fr & HspA' & Hsep & Hloc & Hrec)].
        - left. split; [exact Hs50|]. split; [exact Hspfr|]. intros a Ha. rewrite HSTK. exact (Hloc a Ha).
        - right. split; [exact Hs5fr|]. split.
          + intros FS HW' HR'. apply (Hsep FS); [|exact HR'].
            apply (word_mem_keep mem'); [exact HW'|]. intros k Hk. symmetry. apply TPK. lia.
          + split.
            * intros a Ha. destruct (Hloc a Ha) as (b & Hb & Hbw & Hba). exists b.
              split; [exact Hb|]. split; [|exact Hba].
              apply (word_mem_keep mem); [exact Hbw|]. intros k Hk. apply TPK. lia.
            * apply (a3_fsrec (g_H g) mem mem' md _ fr Hrec HAH MU).
              intros x Hxa Hxlo Hxf. cbn [LFr.outside].
              split; [lia|]. split; [lia|].
              split; [intros Hs; exact (app_not_shadow x Hxa (SHI x ltac:(lia)))|].
              split; [intros Hs; exact (app_not_shadow x Hxa (SHI x ltac:(lia)))|]. exact I. }
      split; [exact Hh0|].
      (* the function word 0x80edc at fr + 16 (0x80fb8 `sd a2,16(s6)`) is AF.ENTRY, the v1.9 entry *)
      split; [exact Hh16|].
      split.
      { exists ((sh68 ++ repeat (Z_to_bv 8 0xf8) 187) ++ old). split.
        - apply (proj2 (LMem.bytes_at_app rsegs mem' S3 _ old)). split; [exact SH255|].
          rewrite length_app, repeat_length, Hl68.
          change (S3 + Z.of_nat (68 + 187)) with (S3 + 255). exact Hold'.
        - rewrite !length_app, repeat_length, Hl68, Hlold. reflexivity. }
      split.
      { apply (stk_keep [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem mem' _ _ HWIN
          MU WM).
        intros x Hx.
        destruct (out_or_in4 x (A + 304) (A + 312) fr (fr + 24) S3 (S3 + 68) (S3 + 68) (S3 + 255)) as [Ho|Hin].
        - left. exact Ho.
        - right. apply RDW. destruct Hin as [H|[H|[H|H]]]; [left | right; left | right; right | right; right]; lia. }
      split.
      { apply (LFr.bytes_at_transport rsegs [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)]
          mem mem'); [exact HSAVED | exact MU |].
        unfold saved_bytes. rewrite !length_app, !LMem.length_le8.
        cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ LFr.disjoint_from]. repeat split; lia. }
      split; [intros a Ha; exact (WM (Z_to_bv 64 a) (HERRNO a Ha))|].
      split.
      { intros a Ha. apply (addressable_keep mem); [exact (HAG a Ha)|]. intros i Hi.
        pose proof (frame_AG_lo a Ha) as Ra. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
        apply KBsh. unfold shadow_addr.
        assert (a / 8 < 0xbfc00) by (apply Z.div_lt_upper_bound; lia).
        assert (0 <= a / 8) by (apply Z.div_pos; lia). lia. }
      (* push 5c: the slot window off the frame stays addressable (its shadow bytes are off the write set) *)
      split.
      { intros a Ha Hnf. unfold AF.SLOT_STACK in Ha.
        apply (addressable_keep mem); [exact (HWA a Ha)|]. intros i Hi.
        assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
        assert (Happa : app_mem a) by (unfold app_mem; right; lia).
        pose proof (shadow_of_app a Happa) as Hsa. destruct (in_shadow_range _ Hsa) as (R1' & R2').
        apply KBmrd; [lia | exact (SHOUT a Happa Hnf)]. }
      split; [exact HSHI1|].
      split; [exact HSHI2|].
      split; [exact HSHI3|].
      split; [cbn; lia|].
      exact HLIVE.
    + (* ENT: the run writes no address ENT speaks of *)
      apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
      apply (ent_munch APIf g [] mem mem' md
               [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] HENT HAH MU);
        [| exact HSTK1 | exact HSTKhi1 |].
      * (* ent_kept taken apart once, here: the only ENT transport of this file *)
        intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hbsh]]]].
        -- destruct Hblkk as (q & k & i & Hin & _ & Hi & ->).
           exact (proj2 (proj2 (proj2 (BLK q k Hin (q + i) ltac:(lia))))).
        -- pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
           cbn [LFr.outside]. repeat split; intros [? ?]; lia.
        -- cbn [LFr.outside]. repeat split; intros [? ?]; lia.
        -- assert (Hab : app_mem b /\ ~ (fr <= b < fr + FRAME_BYTES)).
           { destruct Hor as [Hi|Hr].
             - pose proof (img_below_GT b Hi) as X. unfold AC.GT in X.
               split; [unfold app_mem, LOWMEM_END; left; lia | lia].
             - split; [unfold app_mem; right; lia | lia]. }
           destruct Hab as (Hab & Hnb). exact (SHOUT b Hab Hnb).
        -- (* batch 2 item 9: the shadow byte of an entry block byte (app memory off the frame, by BLK) *)
           destruct Hbsh as (q & k & i & Hin & _ & Hi & ->).
           destruct (BLK q k Hin (q + i) ltac:(lia)) as (Happx & _ & Hnf & _).
           exact (SHOUT (q + i) Happx Hnf).
      * intros a Hia Ho.
        exact (proj1 (ent_owned_img APIf (g_H g) (g_H g) mem md mem' md a HAH HAH1 HSTK1 TPK Hia) Ho).
    + split; [exact HNMAX|].
      split; [unfold rg in *; rewrite Hreg; exact R18|].
      split; [unfold rg in *; rewrite Hreg; exact R20|].
      split; [unfold rg in *; rewrite Hreg, R21; exact Hr21|].
      split; [unfold rg in *; rewrite Hreg; exact R22|].
      split; [unfold rg in *; rewrite Hreg, R23; exact Hr23|].
      split; [unfold rg in *; rewrite Hreg, R24; exact Hr24|].
      split; [unfold rg in *; rewrite Hreg; exact R25|].
      (* push 6c: the input facts; the input block is an entry block (BLK) *)
      split.
      * eapply fl_bytes; [exact Hinb | exact MU |]. intros x Hx. rewrite <- (g_n_len g) in Hx.
        destruct (Z.lt_ge_cases 0 (g_n g)) as [Hn|Hn]; [|lia].
        destruct (Hina Hn) as (Hinp & _).
        exact (proj2 (proj2 (proj2 (BLK _ _ Hinp x Hx)))).
      * intros Hn. destruct (Hina Hn) as (Hinp & Hadp). split; [exact Hinp|].
        apply (addressable_keep mem); [exact Hadp|]. intros i Hi.
        destruct (BLK _ _ Hinp (g_p g + i) ltac:(lia)) as (Happx & _ & Hnf & _).
        pose proof (shadow_of_app _ Happx) as Hsx. destruct (in_shadow_range _ Hsx) as (R1' & R2').
        apply KBmrd; [lia | exact (SHOUT _ Happx Hnf)].
Qed.

End S.
