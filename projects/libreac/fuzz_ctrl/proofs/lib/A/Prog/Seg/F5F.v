(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 1027 of its 1075 lines of code are new or changed and 348 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F5.v, with its module paths and module names changed; 205 of its 648 lines of code are new or changed and 632 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F5.v e6ca704db8bc (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_run corollary re-derives the plain lib.Lib Exec.evt run at ExecF.RNG_all. There is NO
   <r>_of_F_verbatim pin in this file, because F5.v states NO run lemma: its four runs are the `sl_run` argument
   inside the four Hat proofs (seg_F5_df0 :766, seg_F5 :927, seg_F5_e10 :1009, seg_F5_e0c :1111), so there is no
   F5.<r> constant to pin against (reported to the lead and to the auditor a Theorem Labs lane).
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of the four segment runs of F5.v (seg_F5_df0, seg_F5, seg_F5_e10, seg_F5_e0c): each run
   that the segment proof gives Tac_slot.sl_run (a lib.A.Tk.UL Exec.evt: sl_run, Tac_slot.v:124-131, takes the UL
   engine's evt and carries it into lib.Lib's by SmLib.ul_entry) is re-stepped here with lib.Lib StepF as an
   ExecF.evtF under a universally quantified footprint RNG, with the same post-state predicate, and one rng premise
   per memory region the run reads or writes (instruction fetch is not an access). The runs make no instrumented
   check, so no premise names a shadow byte. Each <seg>_run corollary re-derives the UL Exec.evt form that sl_run
   consumes, from <seg>_run_F with RNG_all, through f5F_ul_of_lib (the UL form of lib.Lib's evt, as Seg/A5F.v's
   a5F_ul_of_lib does). F5.v itself is unchanged apart from comment text.

   v1.9.0 (2026-10-28): this file replaces the v1.8 copy of the same name on the base (a working branch
   fdd2ed9f9d7). The four runs, their premises and their post predicates are F5.v's v1.9 text, taken from the
   `sl_run` argument of each Hat proof; only the pcs moved: v1.8 0x81dec / 0x81df0 / 0x81e0c / 0x81e10 / 0x81e28 /
   0x81ebc -> v1.9 0x81e84 / 0x81e88 / 0x81ea4 / 0x81ea8 / 0x81ec0 / 0x81f54. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F5.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read of rg, FRA and the sl_run post-state) as the default. *)
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* The UL engine's evt (the one Tac_slot.sl_run consumes, Tac_slot.v:124-131) from the lib.Lib one: both are
   msteps of `ms_svc_pending ms = None /\ step = MachineOk ms'` (Seg/A5F.v a5F_ul_of_lib). *)
Lemma f5F_ul_of_lib : forall Q ms, LE.evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [exact Hs | exact IH].
Qed.

(* F5.f5_mkR_expand with lib.Lib's mkR (the register map StepF reads): mkR_of regs is definitionally the explicit
   31-slot map. *)
Lemma f5F_mkR_expand : forall regs, Regs6ss.mkR_of regs =
  LFr.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* F5.f5_subst_slot (an Ltac of F5's section, so not exported): rewrite a known register slot `getr regs r` to its
   carried concrete value, from H : rg regs r v. *)
Ltac f5F_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* store_ok of an 8-byte cell [a, a+8) in a memory that is write-monotone over one where the cell is in a present,
   writable stack window [lo, hi). *)
Lemma f5F_store_ok : forall m m' lo hi a,
  stk rsegs m lo hi -> wmono rsegs m m' -> lo <= a -> a + 8 <= hi -> store_ok rsegs m' (wa a) 8 = true.
Proof.
  intros m m' lo hi a (Hlo & Hhi & HS) HW Ha Hb.
  assert (WR : wr_at rsegs m' a 8).
  { split; [lia|]. split; [lia|]. intros i Hi. apply HW. exact (proj1 (HS (a + i) ltac:(lia))). }
  pose proof (wr_at_store_ok rsegs m' a 8 0 8 WR ltac:(lia) ltac:(lia)) as H.
  rewrite Z.add_0_r in H. exact H.
Qed.

(* ---- seg_F5_df0: 0x81e88 -> 0x81f54. bnez s8 (s8 = 0, not taken); li s6,0; li s9,0; sd zero,240(s1);
   sd zero,280(s1); li s4,1; j 0x81f54. The run writes the two 8-byte spill cells [s1+240] and [s1+280]. *)
Lemma seg_F5_df0_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (Asp : Z) (RNG : footprint),
  rg regs 24 0 -> rg regs 9 Asp -> stk rsegs mem (Asp + 240) (Asp + 288) ->
  rng RNG (Asp + 240) 8 -> rng RNG (Asp + 280) 8 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81f54 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 22 = Z_to_bv 64 0 /\ getr R 25 = Z_to_bv 64 0 /\ getr R 20 = Z_to_bv 64 1 /\
       mem' = write_to_mem (write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
                           (wa (Asp + 280)) (le8 (Z_to_bv 64 0)))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81e88) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem Asp RNG Hs8 Hr9 HSTK R240 R280.
  assert (HS1 : store_ok rsegs mem (wa (Asp + 240)) 8 = true)
    by (apply (f5F_store_ok mem mem (Asp + 240) (Asp + 288)); [exact HSTK | apply wmono_refl | lia | lia]).
  rewrite f5F_mkR_expand. f5F_subst_slot Hs8. f5F_subst_slot Hr9.
  (* 0x81e88 bnez s8 : s8 = 0, not taken *)
  step. if_false.
  (* 0x81e8c li s6,0 ; 0x81e90 li s9,0 ; 0x81e94 sd zero,240(s1) *)
  step. step. step.
  lazymatch goal with |- evtF _ _ _ (LM.MS _ _ _ _ _ ?mm _) =>
    assert (HS2 : store_ok rsegs mm (wa (Asp + 280)) 8 = true)
      by (apply (f5F_store_ok mem mm (Asp + 240) (Asp + 288));
          [exact HSTK | apply wmono_write; apply wmono_refl | lia | lia]) end.
  (* 0x81e98 sd zero,280(s1) ; 0x81e9c li s4,1 ; 0x81ea0 j 81f54 *)
  step. step. step.
  finish.
  all: simp_regs; try reflexivity.
  all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

Lemma seg_F5_df0_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (Asp : Z),
  rg regs 24 0 -> rg regs 9 Asp -> stk rsegs mem (Asp + 240) (Asp + 288) ->
  ULE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81f54 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 22 = Z_to_bv 64 0 /\ getr R 25 = Z_to_bv 64 0 /\ getr R 20 = Z_to_bv 64 1 /\
       mem' = write_to_mem (write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
                           (wa (Asp + 280)) (le8 (Z_to_bv 64 0)))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81e88) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem Asp Hs8 Hr9 HSTK.
  pose proof HSTK as (Hlo & Hhi & _).
  apply f5F_ul_of_lib.
  eapply evtF_evt, (seg_F5_df0_run_F regs mem Asp RNG_all); try assumption; apply rng_all; lia.
Qed.

(* ---- seg_F5: 0x81e84 -> 0x81e88. mv s8,a0 (a0 = 0). Register-only: no memory access. *)
Lemma seg_F5_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (RNG : footprint),
  rg regs 10 0 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81e88 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = Z_to_bv 64 0)
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81e84) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem RNG Ha0.
  rewrite f5F_mkR_expand. f5F_subst_slot Ha0.
  (* 0x81e84 mv s8,a0 *)
  step. finish.
  all: simp_regs; try reflexivity.
  all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

Lemma seg_F5_run : forall (regs : bvmap 5 word) (mem : word -> option byte),
  rg regs 10 0 ->
  ULE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81e88 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = Z_to_bv 64 0)
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81e84) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem Ha0.
  apply f5F_ul_of_lib.
  eapply evtF_evt, (seg_F5_run_F regs mem RNG_all); exact Ha0.
Qed.

(* ---- seg_F5_e10: 0x81ea8 -> 0x81ec0. li a1,0; addi a0,s6,-1; addi a2,s7,18; and s6,a0,s9; li a3,32; mv a0,a2.
   Register-only: no memory access. *)
Lemma seg_F5_e10_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (phi : Z) (RNG : footprint),
  rg regs 22 0 -> rg regs 23 phi -> rg regs 25 (phi + 18) ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81ec0 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\
       getr R 22 = Z_to_bv 64 (Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 (phi + 18)))) /\
       getr R 10 = Z_to_bv 64 (phi + 18) /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 32)
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ea8) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem phi RNG Hs6 Hs7 Hs9.
  rewrite f5F_mkR_expand. f5F_subst_slot Hs6. f5F_subst_slot Hs7. f5F_subst_slot Hs9.
  (* 0x81ea8 li a1,0 ; 0x81eac addi a0,s6,-1 ; 0x81eb0 addi a2,s7,18 ; 0x81eb4 and s6,a0,s9 ;
     0x81eb8 li a3,32 ; 0x81ebc mv a0,a2 ; fall into 0x81ec0 *)
  step. step. step. step. step. step.
  finish.
  all: simp_regs; try reflexivity.
  all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

Lemma seg_F5_e10_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (phi : Z),
  rg regs 22 0 -> rg regs 23 phi -> rg regs 25 (phi + 18) ->
  ULE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81ec0 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\
       getr R 22 = Z_to_bv 64 (Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 (phi + 18)))) /\
       getr R 10 = Z_to_bv 64 (phi + 18) /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 32)
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ea8) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem phi Hs6 Hs7 Hs9.
  apply f5F_ul_of_lib.
  eapply evtF_evt, (seg_F5_e10_run_F regs mem phi RNG_all); assumption.
Qed.

(* ---- seg_F5_e0c: 0x81ea4 -> 0x81ea8. sd zero,240(s1); fall into 0x81ea8. The run writes the 8-byte spill cell
   [s1+240]. *)
Lemma seg_F5_e0c_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (Asp : Z) (RNG : footprint),
  rg regs 9 Asp -> stk rsegs mem (Asp + 240) (Asp + 288) ->
  rng RNG (Asp + 240) 8 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81ea8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 22 = getr regs 22 /\
       mem' = write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ea4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem Asp RNG Hr9 HSTK R240.
  assert (HS1 : store_ok rsegs mem (wa (Asp + 240)) 8 = true)
    by (apply (f5F_store_ok mem mem (Asp + 240) (Asp + 288)); [exact HSTK | apply wmono_refl | lia | lia]).
  rewrite f5F_mkR_expand. f5F_subst_slot Hr9.
  (* 0x81ea4 sd zero,240(s1) ; fall into 0x81ea8 *)
  step. finish.
  all: simp_regs; try reflexivity.
  all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

Lemma seg_F5_e0c_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (Asp : Z),
  rg regs 9 Asp -> stk rsegs mem (Asp + 240) (Asp + 288) ->
  ULE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81ea8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 22 = getr regs 22 /\
       mem' = write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ea4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem Asp Hr9 HSTK.
  pose proof HSTK as (Hlo & Hhi & _).
  apply f5F_ul_of_lib.
  eapply evtF_evt, (seg_F5_e0c_run_F regs mem Asp RNG_all); try assumption; apply rng_all; lia.
Qed.

End RunF.

(* ---- Source tie (auditor a Theorem Labs lane): for each cut lemma of F5.v whose inline Tac_slot.sl_run run these corollaries
   re-derive, re-do that cut's own proof line for line, with the inline run discharged by the matching bridged
   corollary (seg_F5_*_run). This Section re-declares F5.v's Section S variables, so the F5 section-local helpers
   apply through the notations below (B APIf ra baked in), exactly as inside F5.v; the only changes from F5.v's text
   are: the inline sl_run evt bullet replaced by `apply (seg_F5_*_run ...)`, and the two store_ok asserts that only
   fed that bullet dropped (the run proof needs only the stk premise). It compiles only if each corollary is exactly
   the run its cut consumes. *)
Section Src.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}
        {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* F5's section-local helpers, closed with B APIf ra (and empty FF for f5_fra_spill) baked in, so the copied proof
   text calls them exactly as F5.v does. *)
Local Notation f5_spill_stk := (F5.f5_spill_stk B APIf ra) (only parsing).
Local Notation f5_fra_spill := (F5.f5_fra_spill B APIf ra empty FF) (only parsing).
Local Notation f5_keep := (F5.f5_keep B APIf ra) (only parsing).
Local Notation f5_pf_keep := (F5.f5_pf_keep B APIf ra) (only parsing).
(* The cut chaining (seg_F5 -> seg_F5_df0, seg_F5_e0c -> seg_F5_e10) uses F5's own proved cuts. *)
Local Notation seg_F5_df0 := (F5.seg_F5_df0 B APIf ra empty FF) (only parsing).
Local Notation seg_F5_e10 := (F5.seg_F5_e10 B APIf ra empty FF) (only parsing).

Lemma seg_F5_df0_src_in : forall j,
  Hat B APIf ra (Inv_A81f54_at B APIf ra) j -> Hat B APIf ra (Inv_A81e88_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Hs8 & Hu32 & HID & HF17 & _)). subst c.
  rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A & H9 & HA & HSP) & HPH & HFR & HFS & HKN).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Happ).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr0 : 0 < fr) by (unfold AC.GT in HGT; lia).
  assert (HAeq : A = Asp).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  destruct HF17 as (A7 & H97 & HA7 & Hq7).
  assert (EA7 : A7 = Asp) by (apply f5_id; [lia | lia |]; unfold rg in H97, Hr9; rewrite <- H97; exact Hr9).
  subst A7.
  assert (Hk0 : t_k (g_in g) j = 0) by (apply f5_k; exact Hlen50).
  rewrite Hk0 in Hs8.
  pose proof (f5_spill_stk g fr (hb1 phi (AC.a_size (flen g j))) regs mem md Asp
              (Asp + 240) (Asp + 288) HFRA Hr9 HAspR ltac:(lia) ltac:(lia) ltac:(lia)) as HSTK.
  apply (sl_run regs (Z_to_bv 64 0x81e88) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81f54 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 22 = Z_to_bv 64 0 /\ getr R 25 = Z_to_bv 64 0 /\ getr R 20 = Z_to_bv 64 1 /\
       mem' = write_to_mem (write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
                           (wa (Asp + 280)) (le8 (Z_to_bv 64 0)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - apply (seg_F5_df0_run regs mem Asp Hs8 Hr9 HSTK).
  - intros R pc' mem' regs'' md'
      (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & HR22 & HR25 & HR20 & Hmem)
      Hreg Hmat.
    subst pc'.
    set (W := [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)]).
    assert (MU1 : Frame.munch W mem (write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))).
    { subst W. apply (munch_write _ mem mem (Asp + 240) (le8 (Z_to_bv 64 0)));
        [ apply munch_refl | lia | rewrite length_le8; lia
        | rewrite length_le8; cbn [inside]; left; lia ]. }
    assert (MU : Frame.munch W mem mem').
    { subst mem'. apply (munch_write _ mem _ (Asp + 280) (le8 (Z_to_bv 64 0)));
        [ exact MU1 | lia | rewrite length_le8; lia
        | subst W; rewrite length_le8; cbn [inside]; right; left; lia ]. }
    assert (WM : Frame.wmono rsegs mem mem')
      by (subst mem'; apply wmono_write; apply wmono_write; apply wmono_refl).
    assert (HAW : all_app W).
    { subst W. cbn [all_app].
      split; [apply f5_app_ivl; lia | split; [apply f5_app_ivl; lia | exact I]]. }
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst mem'. apply stk_write; [apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]
                                   | lia | rewrite length_le8; lia]. }
    assert (HFE : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs'' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { apply (f5_fra_spill g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem mem' md md' Asp
               HFRA HENT Hr9 HAspR MU WM HWIN' Hmat); rewrite Hreg; assumption. }
    destruct HFE as (HFRA'' & HENT'').
    assert (Hq280 : q64 mem' (Asp + 280) 0).
    { subst mem'. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (HWout1 : forall x, x < Asp + 240 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HWout2 : forall x, Asp + 248 <= x < Asp + 280 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem' md W HFRA HHB HFLSI HLK HC HID Hr9 HAspR
                MU WM HAW HWout1 HWout2 HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    assert (Hq240 : q64 mem' (Asp + 240) 0).
    { subst mem'. unfold q64. apply bytes_at_write_other;
        [ apply bytes_at_write_same; [lia | rewrite length_le8; lia] | lia | rewrite length_le8; lia
        | rewrite !length_le8; lia ]. }
    assert (H9'' : rg regs'' 9 Asp) by (unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9).
    assert (H8819f : t_8819 (g_in g) j = false) by (apply f5_8819; exact Hlen50).
    assert (HF17' : b5_F17 g j phi fr regs'' mem').
    { exists Asp. split; [exact H9''|]. split; [exact HAspR|].
      exact (f5_q64_keep W mem mem' _ _ Hq7 MU ltac:(intros x Hx; apply HWout1; lia)). }
    assert (HW240' : b5_W240 g j regs'' mem').
    { exists Asp. split; [exact H9''|]. split; [exact HAspR|].
      exists 0. split; [exact Hq240|]. split; [lia|].
      split; [intros E; rewrite H8819f in E; discriminate | intros _; reflexivity]. }
    assert (HPF' : b5_PF g j phi fr regs'' mem').
    { exists Asp. split; [exact H9''|]. split; [exact HAspR|].
      split; [intros Hl; exfalso; lia | intros E; rewrite H8819f in E; discriminate]. }
    assert (E22 : (if t_big (g_in g) j then phi + 18 else 0) = 0)
      by (rewrite (f5_big (g_in g) j Hlen50); reflexivity).
    assert (E25 : b2z (t_tfill (g_in g) j) = 0)
      by (rewrite (f5_tfill (g_in g) j Hlen50); reflexivity).
    assert (E20 : 1 - b2z (t_sum_ok (g_in g) j) = 1)
      by (rewrite (f5_sum (g_in g) j Hlen50); reflexivity).
    assert (E280 : b2z (t_sum_ok (g_in g) j) = 0)
      by (rewrite (f5_sum (g_in g) j Hlen50); reflexivity).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [|split; [exact HID'|]; split; [exact HF17'|]; split; [exact HW240' | exact HPF']].
    unfold b5_K. rewrite E20, E22, E25, E280.
    split; [unfold rg; rewrite Hreg; exact HR20|].
    split; [unfold rg; rewrite Hreg; exact HR22|].
    split; [unfold rg; rewrite Hreg, HR24, Hk0; unfold rg in Hs8; exact Hs8|].
    split; [unfold rg; rewrite Hreg; exact HR25|].
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|].
      split; [lia | exact Hq280]. }
    split; [exact (f5_u32_keep W mem mem' _ _ Hu32 MU ltac:(intros x Hx; apply HWout1; lia))|].
    apply f5_reply; [exact (proj1 HHB) | exact Hfr0].
Qed.

Lemma seg_F5_src_in : forall j,
  Hat B APIf ra (Inv_A81f54_at B APIf ra) j -> Hat B APIf ra (Inv_A81e84_at B APIf ra) j.
Proof.
  intros j Hexit.
  pose proof (seg_F5_df0 j Hexit) as Hdf0.
  intros g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Ha0 & Hu32 & HID & HF17 & HPF)). subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hk0 : t_k (g_in g) j = 0) by (apply f5_k; exact Hlen50).
  rewrite Hk0 in Ha0.
  apply (sl_run regs (Z_to_bv 64 0x81e84) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81e88 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = Z_to_bv 64 0)
    (Post B APIf ra g)).
  - exact Hhalt.
  - apply (seg_F5_run regs mem Ha0).
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24) Hreg Hmat.
    subst pc' mem'. rewrite <- SEGS. apply Hdf0.
    exists phi, regs'', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
        [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
        | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
        | rewrite Hreg; exact HR26 | exact Hmat ]. }
    split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
    assert (MU0 : Frame.munch (@nil (Z * Z)) mem mem) by apply munch_refl.
    assert (WM0 : Frame.wmono rsegs mem mem) by apply wmono_refl.
    assert (HAW0 : all_app (@nil (Z * Z))) by (cbn [all_app]; exact I).
    assert (HO0 : forall x : Z, Frame.outside (@nil (Z * Z)) x) by (intros x; cbn [Frame.outside]; exact I).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem md (@nil (Z * Z))
                HFRA HHB HFLSI HLK HC HID Hr9 HAspR MU0 WM0 HAW0
                (fun x (_ : x < Asp + 240) => HO0 x)
                (fun x (_ : Asp + 248 <= x < Asp + 280) => HO0 x)
                HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [unfold rg; rewrite Hreg, HR24, Hk0; reflexivity|].
    split; [exact Hu32|]. split; [exact HID'|].
    destruct HF17 as (A7 & H97 & HA7 & Hq7).
    split.
    { exists A7. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H97; exact H97|].
      split; [exact HA7 | exact Hq7]. }
    destruct HPF as (A9 & H99 & HPF9).
    exists A9. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H99; exact H99 | exact HPF9].
Qed.

Lemma seg_F5_e10_src_in : forall j,
  Hat B APIf ra (Inv_A81ec0_at B APIf ra) j -> Hat B APIf ra (Inv_A81ea8_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Hs6 & Hs8 & Hs9 & Hq240 & Hu32 & HID & HF17 & HW240 & HPF)).
  subst c.
  rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A & H9 & HA & HSP) & HPH & HFR & HFS & HKN).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hphi : 0 <= phi /\ phi + 50 <= 2 ^ 64).
  { destruct HHB as (_ & Had). destruct Had as (Hp0 & Hn0 & Hpn & _).
    unfold AC.a_size in Hpn, Hn0. lia. }
  apply (sl_run regs (Z_to_bv 64 0x81ea8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81ec0 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\
       getr R 22 = Z_to_bv 64 (Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 (phi + 18)))) /\
       getr R 10 = Z_to_bv 64 (phi + 18) /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 32)
    (Post B APIf ra g)).
  - exact Hhalt.
  - apply (seg_F5_e10_run regs mem phi Hs6 Hs23 Hs9).
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & HR25 &
       HR22 & HR10 & HR12 & HR11 & HR13) Hreg Hmat.
    rewrite (f5_and_ones (phi + 18) ltac:(lia)) in HR22.
    subst pc' mem'. rewrite <- SEGS. apply Hexit.
    exists phi, regs'', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
        [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
        | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
        | rewrite Hreg; exact HR26 | exact Hmat ]. }
    split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
    assert (MU0 : Frame.munch (@nil (Z * Z)) mem mem) by apply munch_refl.
    assert (WM0 : Frame.wmono rsegs mem mem) by apply wmono_refl.
    assert (HAW0 : all_app (@nil (Z * Z))) by (cbn [all_app]; exact I).
    assert (HO0 : forall x : Z, Frame.outside (@nil (Z * Z)) x) by (intros x; cbn [Frame.outside]; exact I).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem md (@nil (Z * Z))
                HFRA HHB HFLSI HLK HC HID Hr9 HAspR MU0 WM0 HAW0
                (fun x (_ : x < Asp + 240) => HO0 x)
                (fun x (_ : Asp + 248 <= x < Asp + 280) => HO0 x)
                HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [unfold rg; rewrite Hreg; exact HR10|].
    split; [unfold rg; rewrite Hreg; exact HR11|].
    split; [unfold rg; rewrite Hreg; exact HR12|].
    split; [unfold rg; rewrite Hreg; exact HR13|].
    split; [unfold rg; rewrite Hreg; exact HR22|].
    split; [unfold rg; rewrite Hreg, HR24; unfold rg in Hs8; exact Hs8|].
    split; [unfold rg; rewrite Hreg, HR25; unfold rg in Hs9; exact Hs9|].
    destruct Hq240 as (A' & H9' & HA' & Hq).
    split.
    { exists A'. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H9'; exact H9'|].
      split; [exact HA' | exact Hq]. }
    split; [exact Hu32|]. split; [exact HID'|].
    destruct HF17 as (A7 & H97 & HA7 & Hq7).
    split.
    { exists A7. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H97; exact H97|].
      split; [exact HA7 | exact Hq7]. }
    destruct HW240 as (A8 & H98 & HA8 & HW8).
    split.
    { exists A8. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H98; exact H98|].
      split; [exact HA8 | exact HW8]. }
    destruct HPF as (A9 & H99 & HPF9).
    exists A9. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H99; exact H99 | exact HPF9].
Qed.

Lemma seg_F5_e0c_src_in : forall j,
  Hat B APIf ra (Inv_A81ec0_at B APIf ra) j -> Hat B APIf ra (Inv_A81ea4_at B APIf ra) j.
Proof.
  intros j Hexit.
  pose proof (seg_F5_e10 j Hexit) as He10.
  intros g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Hs6 & Hs8 & Hs9 & H8819 & Hu32 & HID & HF17 & HPF)). subst c.
  rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A & H9 & HA & HSP) & HPH & HFR & HFS & HKN).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  destruct HF17 as (A7 & H97 & HA7 & Hq7).
  assert (EA7 : A7 = Asp) by (apply f5_id; [lia | lia |]; unfold rg in H97, Hr9; rewrite <- H97; exact Hr9).
  subst A7.
  pose proof (f5_spill_stk g fr (hb1 phi (AC.a_size (flen g j))) regs mem md Asp
              (Asp + 240) (Asp + 288) HFRA Hr9 HAspR ltac:(lia) ltac:(lia) ltac:(lia)) as HSTK.
  apply (sl_run regs (Z_to_bv 64 0x81ea4) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81ea8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 22 = getr regs 22 /\
       mem' = write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - apply (seg_F5_e0c_run regs mem Asp Hr9 HSTK).
  - intros R pc' mem' regs'' md'
      (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & HR25 & HR22 & Hmem)
      Hreg Hmat.
    subst pc'.
    set (W := [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)]).
    assert (MU : Frame.munch W mem mem').
    { subst mem' W. apply (munch_write _ mem mem (Asp + 240) (le8 (Z_to_bv 64 0)));
        [ apply munch_refl | lia | rewrite length_le8; lia
        | rewrite length_le8; cbn [inside]; left; lia ]. }
    assert (WM : Frame.wmono rsegs mem mem') by (subst mem'; apply wmono_write; apply wmono_refl).
    assert (HAW : all_app W).
    { subst W. cbn [all_app].
      split; [apply f5_app_ivl; lia | split; [apply f5_app_ivl; lia | exact I]]. }
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst mem'. apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]. }
    assert (HFE : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs'' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { apply (f5_fra_spill g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem mem' md md' Asp
               HFRA HENT Hr9 HAspR MU WM HWIN' Hmat); rewrite Hreg; assumption. }
    destruct HFE as (HFRA'' & HENT'').
    assert (Hq240 : q64 mem' (Asp + 240) 0).
    { subst mem'. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (HWout1 : forall x, x < Asp + 240 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HWout2 : forall x, Asp + 248 <= x < Asp + 280 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem' md W HFRA HHB HFLSI HLK HC HID Hr9 HAspR
                MU WM HAW HWout1 HWout2 HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    pose proof (f5_pf_keep g j phi fr Asp regs regs'' mem mem' md W HFRA HPF Hr9 HAspR MU HAW HWout1 HE9)
      as HPF'.
    assert (E240 : b2z (t_8819 (g_in g) j) = 0) by (rewrite H8819; reflexivity).
    rewrite <- SEGS. apply He10.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [unfold rg; rewrite Hreg, HR22; unfold rg in Hs6; exact Hs6|].
    split; [unfold rg; rewrite Hreg, HR24; unfold rg in Hs8; exact Hs8|].
    split; [unfold rg; rewrite Hreg, HR25; unfold rg in Hs9; exact Hs9|].
    rewrite E240.
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|].
      split; [lia | exact Hq240]. }
    split; [exact (f5_u32_keep W mem mem' _ _ Hu32 MU ltac:(intros x Hx; apply HWout1; lia))|].
    split; [exact HID'|].
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|].
      split; [lia | exact (f5_q64_keep W mem mem' _ _ Hq7 MU ltac:(intros x Hx; apply HWout1; lia))]. }
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|]. split; [lia|].
      exists 0. split; [exact Hq240|]. split; [lia|].
      split; [intros E; rewrite H8819 in E; discriminate | intros _; reflexivity]. }
    exact HPF'.
Qed.

End Src.

(* The compiled source ties: each _src states F5.<cut>'s exact closed type and is inhabited by the in-section
   re-derivation above (which discharged the inline run by the matching bridged corollary). `exact` closes it only
   if the discharged type is F5.<cut>'s, term for term. *)
Lemma seg_F5_df0_src : ltac:(let T := type of (@F5.seg_F5_df0) in exact T).
Proof. exact @seg_F5_df0_src_in. Qed.

Lemma seg_F5_src : ltac:(let T := type of (@F5.seg_F5) in exact T).
Proof. exact @seg_F5_src_in. Qed.

Lemma seg_F5_e10_src : ltac:(let T := type of (@F5.seg_F5_e10) in exact T).
Proof. exact @seg_F5_e10_src_in. Qed.

Lemma seg_F5_e0c_src : ltac:(let T := type of (@F5.seg_F5_e0c) in exact T).
Proof. exact @seg_F5_e0c_src_in. Qed.
