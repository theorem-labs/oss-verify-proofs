(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths changed; 842 of its 961 lines of code are new or changed and 2438 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A4.v, with its module paths and module names changed; 83 of its 193 lines of code are new or changed and 851 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/A4.v blob d44831231112 at 6a74d5929d2.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: a4_evt_of_F re-derives A4.a4_evt at ExecF.RNG_all; a4_evt_of_F_verbatim checks by constr_eq that its
   type is the type of A4.a4_evt. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (ExecF.evtF) twin of A4.v's one run lemma a4_evt (segment-runs-A.tsv row S_A4, a4_evt:168): the
   198 instructions 0x810e4-0x813fc. The run only WRITES: the 137 tail shadow bytes of the frame and the spill
   block of the prologue save area. Both regions are named by the lemma's own cell premises, so a4_evt_F appends
   exactly two rng premises:
     ExecF.rng RNG (S3 + 255) 137   (premise `rw_cells rsegs m (S3 + 255) [CB 137 jsh]`, the shadow stores
                                     0x810e4-0x812e4 and 0x8138c)
     ExecF.rng RNG (A + 16) 272     (premise `rw_cells rsegs m (A + 16) [CB 272 jsp]`, the spill stores
                                     0x81318-0x813fc)
   The two `stk` premises get NO rng premise: the run performs no access in [lo, hi) (they are carried to the post
   through munch), and the window [S3 + 255, S3 + 392) of the second one is the shadow region above.
   A4.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 1 of its code lines changed or removed, 1 added. a4_evt_of_F re-derives it at ExecF.RNG_all.

   A4.v's run is on the UL engine (lib/A/Tk/UL), with the UL copies of `rw_cells` / `cell` in its statement, while
   the re-run is stepped by lib.Lib's StepF on the lib.Lib machine state. So, as Seg/F10F.v does:
   - a4F_ul_of_lib carries lib.Lib's evt to the UL engine's evt for the corollary (both are msteps of
     `ms_svc_pending ms = None /\ step = MachineOk ms'`);
   - a4F_rw_CB restates a UL byte-block cell premise as the lib.Lib one StepF's store bookkeeping consumes (the
     two definitions are byte copies of each other, so the Prop is the same up to delta);
   - A4.v's cells_bytes_at / cell8_q64 / cell1_b8 and its a4_q64 / a4_b8 / a4_fin / norm_lit_store_bytes tactics
     are restated here over lib.Lib's cells and over evtF goals. Nothing else of the script changes. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Exec Cells Step Tac Bytes.
(* The UL engine is NOT imported here: a4_evt's statement names its evt / rw_cells / CB through these paths. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Exec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs A4.
(* Last: StepF's step / if_true_by / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* After StepF: getr and FPState are YK11's, as in A4.v. *)
Import YK11.
Open Scope Z_scope.

Module ULM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module ULMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.
Module ULFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.
Module A4LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module ULS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Step.
Module ULC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.

(* The UL engine's evt from the lib.Lib one (Seg/F10F.v f10F_ul_of_lib). *)
Lemma a4F_ul_of_lib : forall Q ms, A4LE.evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [exact Hs | exact IH].
Qed.

(* A UL byte-block cell premise as the lib.Lib one: both unfold to
   `(length bs = n /\ True) /\ bytes_at rsegs m A (bs ++ []) /\ wr_at rsegs m A (Z.of_nat (n + 0))`. *)
Lemma a4F_rw_CB : forall (m : word -> option byte) (A : Z) (n : nat) (bs : list byte),
  ULS.rw_cells rsegs m A [ULC.CB n bs] -> rw_cells rsegs m A [CB n bs].
Proof.
  intros m A n bs ((Hwf & Hb) & Hw). split; [split; [exact Hwf | exact Hb] | exact Hw].
Qed.

(* A4.v's cells_bytes_at / cell8_q64 / cell1_b8 over lib.Lib's cells (A4.v's proofs, unchanged). *)
Lemma a4F_cells_bytes_at : forall m A cs k c, cells_at rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [Hwf Hb] Hk.
  destruct (cell_at_split cs k c c Hk) as (pre & post & Ecs & Hsz & _).
  subst cs. apply cells_wf_app in Hwf. destruct Hwf as [Hpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A _ _)) in Hb. destruct Hb as [_ Hb].
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in Hb. destruct Hb as [Hb _].
  rewrite (cells_bytes_length pre Hpre), Hsz in Hb. exact Hb.
Qed.

Lemma a4F_cell8_q64 : forall m A cs k w v, cells_at rsegs m A cs -> cell_at cs k = Some (C8 w) ->
  w = Z_to_bv 64 v -> q64 m (A + Z.of_nat k) v.
Proof.
  intros m A cs k w v H Hk ->. unfold q64.
  exact (a4F_cells_bytes_at m A cs k (C8 (Z_to_bv 64 v)) H Hk).
Qed.

Lemma a4F_cell1_b8 : forall m A cs k b v, cells_at rsegs m A cs -> cell_at cs k = Some (C1 b) ->
  b = Z_to_bv 8 v -> b8 m (A + Z.of_nat k) v.
Proof.
  intros m A cs k b v H Hk ->. unfold b8.
  exact (a4F_cells_bytes_at m A cs k (C1 (Z_to_bv 8 v)) H Hk).
Qed.

(* A4.v's store normalizer and the cell bookkeeping after it, as ONE tactic run after each `step`. StepF's own
   `mem_after_store_opt` only absorbs a store whose byte list is already canonical, so the normalization A4.v puts
   into `norm_lit_store_bytes` is done here (the frame poison bytes come from NEGATIVE literals s2 = -8, s4 = -14,
   hence `norm_lit_byte_mod256`), and `mem_after_store` keeps the two cell blocks of the run. *)
Ltac a4F_store :=
  try (lazymatch goal with
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           rewrite (le1_lit z); norm_lit_byte_mod256; mem_after_store
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) =>
           rewrite (le1_zxb b); mem_after_store
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
       end).

(* A4.v's spill / shadow-byte readers, over lib.Lib's cells. *)
Ltac a4_q64 :=
  lazymatch goal with
  | H : rw_cells rsegs ?mm (?A + 16) ?cs |- q64 _ (?A + ?o) _ =>
      let k := eval vm_compute in (Z.to_nat (o - 16)) in
      replace (A + o) with (A + 16 + Z.of_nat k) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
      eapply (a4F_cell8_q64 mm (A + 16) cs k);
      [ exact (proj1 H) | cells_cbv; reflexivity | first [reflexivity | f_equal; lia] ]
  end.

Ltac a4_b8 :=
  lazymatch goal with
  | H : rw_cells rsegs ?mm (?S3 + 255) ?cs |- b8 _ (?S3 + 328) _ =>
      replace (S3 + 328) with (S3 + 255 + Z.of_nat 73) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
      eapply (a4F_cell1_b8 mm (S3 + 255) cs 73);
      [ exact (proj1 H) | cells_cbv; reflexivity | first [reflexivity | vm_compute; reflexivity] ]
  end.

Ltac a4_fin :=
  first
    [ simp_regs; first [ reflexivity | f_equal; lia | apply srli26_0; lia ]
    | a4_q64
    | a4_b8 ].

(* ---- The 198-instruction run under a footprint. *)
Lemma a4_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S3 N fr s5v lo hi : Z) (jsh jsp : list byte),
    s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 (-8) -> s3 = Z_to_bv 64 S3 -> s4 = Z_to_bv 64 (-14) ->
    s5 = Z_to_bv 64 s5v -> s6 = Z_to_bv 64 fr -> s8 = Z_to_bv 64 N -> s9 = Z_to_bv 64 (S3 + 68) ->
    0 <= N < 2 ^ 64 -> 0 <= S3 -> S3 + 392 <= A -> A + 288 <= 2 ^ 64 ->
    ULS.rw_cells rsegs m (S3 + 255) [ULC.CB 137 jsh] ->
    ULS.rw_cells rsegs m (A + 16) [ULC.CB 272 jsp] ->
    stk rsegs m lo hi -> stk rsegs m (S3 + 255) (S3 + 392) ->
    ExecF.rng RNG (S3 + 255) 137 ->
    ExecF.rng RNG (A + 16) 272 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
         ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 22 = s6 /\ getr R 26 = s10 /\
         munch [(S3 + 255, S3 + 392); (A + 16, A + 288)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo hi /\ stk rsegs m' (S3 + 255) (S3 + 392) /\
         (exists sh, bytes_at rsegs m' (S3 + 255) sh /\ length sh = 137%nat) /\
         ((N < 2 ^ 26 /\ pc' = Z_to_bv 64 0x81400 /\ a4_exit fr S3 A s5v s7 s8 R m') \/
          (2 ^ 26 <= N /\ pc' = Z_to_bv 64 0x82b80 /\ getr R 21 = s5)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810e4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A S3 N fr s5v lo hi jsh jsp -> -> -> -> -> -> -> -> HN HS3 HSA HA RWshU RWspU ST1 ST2 Rsh Rsp.
  pose proof (a4F_rw_CB m (S3 + 255) 137 jsh RWshU) as RWsh.
  pose proof (a4F_rw_CB m (A + 16) 272 jsp RWspU) as RWsp.
  clear RWshU RWspU.
  pose proof (munch_refl [(S3 + 255, S3 + 392); (A + 16, A + 288)] m) as MU.
  assert (WM : wmono rsegs m m) by (intros x Hx; exact Hx).
  (* 0x810e4 .. 0x8130c (139 instructions) and the beqz at 0x81310 *)
  do 140 (step; a4F_store).
  destruct (Z_lt_ge_dec N (2 ^ 26)) as [Hlt|Hge].
  - if_true_by (srli26_t N ltac:(lia)).
    (* 0x81318 .. 0x813fc *)
    do 58 (step; a4F_store).
    apply ExecF.evtF_done. do 3 eexists. split; [reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact ST2|].
    split.
    { match goal with
      | H : rw_cells rsegs ?mm (S3 + 255) ?cs |- _ =>
          exists (cells_bytes cs); pose proof H as HH; destruct HH as [[Hwf Hb] _]; split;
            [exact Hb | rewrite (cells_bytes_length cs Hwf); cbn [cells_size csize Nat.add]; reflexivity]
      end. }
    left. split; [lia|]. split; [reflexivity|].
    unfold a4_exit.
    do 37 (split; [a4_fin|]). a4_fin.
  - if_false_by (srli26_f N ltac:(lia)).
    step; a4F_store.
    apply ExecF.evtF_done. do 3 eexists. split; [reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [simp_regs; reflexivity|]. split; [simp_regs; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact ST2|].
    split.
    { match goal with
      | H : rw_cells rsegs ?mm (S3 + 255) ?cs |- _ =>
          exists (cells_bytes cs); pose proof H as HH; destruct HH as [[Hwf Hb] _]; split;
            [exact Hb | rewrite (cells_bytes_length cs Hwf); cbn [cells_size csize Nat.add]; reflexivity]
      end. }
    right. split; [lia|]. split; [reflexivity|].
    simp_regs; reflexivity.
Qed.

(* A4.a4_evt's statement as a corollary (evtF_evt of a4_evt_F at RNG_all, then the UL engine's evt). *)
Lemma a4_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S3 N fr s5v lo hi : Z) (jsh jsp : list byte),
    s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 (-8) -> s3 = Z_to_bv 64 S3 -> s4 = Z_to_bv 64 (-14) ->
    s5 = Z_to_bv 64 s5v -> s6 = Z_to_bv 64 fr -> s8 = Z_to_bv 64 N -> s9 = Z_to_bv 64 (S3 + 68) ->
    0 <= N < 2 ^ 64 -> 0 <= S3 -> S3 + 392 <= A -> A + 288 <= 2 ^ 64 ->
    ULS.rw_cells rsegs m (S3 + 255) [ULC.CB 137 jsh] ->
    ULS.rw_cells rsegs m (A + 16) [ULC.CB 272 jsp] ->
    ULFR.stk rsegs m lo hi -> ULFR.stk rsegs m (S3 + 255) (S3 + 392) ->
    ULE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
         ms' = ULMS.MS R F pc' fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 22 = s6 /\ getr R 26 = s10 /\
         ULFR.munch [(S3 + 255, S3 + 392); (A + 16, A + 288)] m m' /\ ULFR.wmono rsegs m m' /\
         ULFR.stk rsegs m' lo hi /\ ULFR.stk rsegs m' (S3 + 255) (S3 + 392) /\
         (exists sh, ULM.bytes_at rsegs m' (S3 + 255) sh /\ length sh = 137%nat) /\
         ((N < 2 ^ 26 /\ pc' = Z_to_bv 64 0x81400 /\ a4_exit fr S3 A s5v s7 s8 R m') \/
          (2 ^ 26 <= N /\ pc' = Z_to_bv 64 0x82b80 /\ getr R 21 = s5)))
      (ULMS.MS (ULFR.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A S3 N fr s5v lo hi jsh jsp E1 E2 E3 E4 E5 E6 E8 E9 HN HS3 HSA HA RWsh RWsp ST1 ST2.
  apply a4F_ul_of_lib.
  eapply ExecF.evtF_evt.
  exact (a4_evt_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A S3 N fr s5v lo hi jsh jsp E1 E2 E3 E4 E5 E6 E8 E9 HN HS3 HSA HA RWsh RWsp ST1 ST2
           ltac:(apply ExecF.rng_all; lia) ltac:(apply ExecF.rng_all; lia)).
Qed.

(* The pin: a4_evt_of_F's statement is A4.a4_evt's, term for term. *)
Example a4_evt_of_F_verbatim : True.
Proof.
  let a := type of A4.a4_evt in let b := type of a4_evt_of_F in constr_eq a b.
  exact I.
Qed.
