(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 176 of its 211 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/Tac_b5.v, with its module paths and module names changed; 1788 of its 1832 lines of code are new or changed and 167 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F17.v; 115 of its 205 lines of code are new or changed and 1742 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F17.v (an earlier version, blob f83ca6832224, not in this delivery) written on a working branch d65d18383b1 (a Theorem Labs lane's v1.9
   proof, on this branch through a Theorem Labs lane's merge of a working branch), Lemma seg_F17 (:2007), the run bullet of its sl_run
   (:2032-2046).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: seg_F17's run is not a named lemma (it is the first bullet of the sl_run inside seg_F17's own proof), so
   no verbatim pin of the run is possible.  The COMPILED SOURCE TIE instead (auditor a Theorem Labs lane's condition for a
   no-pin extracted run; a Theorem Labs lane 04:52Z, a Theorem Labs lane 04:24Z): seg_F17_src has exactly the type of F17.seg_F17
   (`ltac:(let T := type of F17.seg_F17 in exact T)`) and is proved by RE-DOING seg_F17's own script, with its
   bltz bullet discharged from PF.f17_bltz_of_F (this file's run at ExecF.RNG_all) carried into the UL engine by
   F17.f17_lib_evt; every other line of the script is the source's.  Written by a Theorem Labs lane for the
   glue of stage seg_F17 (lib/A/ACtlG/F17.v), the only consumer; input to the ported walk only.  rule 24: no
   function proved. *)
(* WHY THIS FILE.  Seg/F17F.v (a Theorem Labs lane's re-run of Seg/F17.v) re-runs F17.f17_tail only: it is a run of seg_F17b
   (0x822a0 -> 0x823e8, another stage).  seg_F17 itself (0x8229c -> 0x822a0) has no named run lemma, so the re-run
   lanes had nothing to re-run for it (segF-v19-spec.md (a working note, not in this delivery): rows with "no stated run lemma" are not re-run).  This file
   is that missing footprint run, cut from seg_F17's own script, with no new reasoning:
     0x8229c  bltz a0,82bf4   NOT taken: the entry cut C_A8229c_at carries a0 = v0 with 0 <= v0 < 2 ^ 63 (the
                              reac_identity_ingest result); the fall-through pc is 0x822a0.
   The source states the same branch at F17.v:2032-2046 (`bltz a0,82b34`: F17.v writes the v1.8 abort address; the
   v1.9 listing's target is 0x82bf4, which the run never reaches).  The branch writes no register and no memory, and
   it makes no data access (an instruction fetch is not an access, ExecF.v:98-101), so the run has NO rng premise;
   F17Fs.rng.tsv has one row that says so.
   FORM.  As Seg/F15F.v f15_evt_dc_F (the same single not-taken branch shape, green on this base) and Seg/F14F.v
   f14_evt_e0_F (the same `bltz a0` with an explicit a0 = Z_to_bv 64 r): RNG first, explicit register words, the float
   map Fr and fcsr fc as binders (the glue instantiates fp_regs / fp_csr), the end state is the start state at the
   fall-through pc.  The rom is written with the core's lib/Reusable/YK11 seg_rom (full path: the module has a ctrl
   twin lib/A/Reusable/YK11), the name the glue's cut configuration has; the two seg_rom bodies are the same.
   LAYOUT (as Seg/F17F.v): the file is in Seg/F17.v's own environment (its import block, verbatim, so the tie's
   script reads as the source's); the StepF run lives in Module PF, which imports ExecF / StepF with module-local
   visibility, so StepF's step / Exec names do not shadow the UL engine's outside it.  The six twin modules are
   named A.Reusable.<X> (ctrl's copy, the one Seg/F17.v uses) or by the core's full path, never bare. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* Seg/F17.v's import block (F17.v:12-24), verbatim. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot F18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_f17b Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require PropExec.
(* The source itself, Required, NOT imported. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F17.
(* The core's YK11 (the run's rom name, the one the glue's cut configuration has). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
(* Required, NOT imported at file level: the run lives in Module PF below. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

Module PF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Open Scope Z_scope.

(* A small literal is its own signed value (stdpp's Z_to_bv_signed; the source uses AsanRTFacts.signed_lit). *)
Lemma f17Fs_signed : forall z, -2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

(* ---- seg_F17's run: 0x8229c `bltz a0,82bf4` with a0 = v0, 0 <= v0 < 2 ^ 63: not taken, landing at 0x822a0 with
   the same registers and memory.  No data access. ---- *)
Lemma f17_bltz_F :
  forall (RNG : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 : Z),
    a0v = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 63 ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs RNG
      (fun ms' => ms' = LM.MS (LF.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              Fr (Z_to_bv 64 0x822a0) fc None m
                              (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom
                                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs))
      (LM.MS (LF.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x8229c) fc None m
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom
                OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m v0 -> Hv0.
  (* the branch condition, as F17.v:2041-2042 decides it *)
  assert (Hbltz : bv_lts (Z_to_bv 64 v0) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (f17Fs_signed v0) by lia. rewrite (f17Fs_signed 0) by lia. apply Z.ltb_ge. lia. }
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. (* 0x8229c: bltz a0,82bf4 -- not taken *)
  replace (bv_lts (Z_to_bv 64 v0) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF_done. reflexivity.
Qed.

(* The same run at ExecF.RNG_all, in the Lib.Exec engine. *)
Lemma f17_bltz_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 : Z),
    a0v = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 63 ->
    LE.evt OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs
      (fun ms' => ms' = LM.MS (LF.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              Fr (Z_to_bv 64 0x822a0) fc None m
                              (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom
                                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs))
      (LM.MS (LF.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x8229c) fc None m
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom
                OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m v0 E0 Hv0.
  apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF_evt
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.RNG_all).
  exact (f17_bltz_F OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0v
           a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m v0 E0 Hv0).
Qed.

End PF.

(* ---- The compiled source tie. ---- *)

(* PF.f17_bltz_of_F in the form seg_F17's sl_run bullet needs: the UL engine's evt (F17.f17_lib_evt) from the
   canonical map Regs6ss.mkR_of regs, for any post Q that holds at the fall-through state. *)
Lemma f17_bltz_ul : forall (regs Fr : bvmap 5 word) (fc : bv 32) (mem : word -> option byte) (v0 : Z)
    (Q : machine_state -> Prop),
  A.Reusable.YK11.getr regs 10 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 63 ->
  Q (LM.MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x822a0) fc None mem (A.Reusable.YK11.seg_rom rsegs)) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.evt rsegs Q
    (LM.MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x8229c) fc None mem (A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs Fr fc mem v0 Q E Hv HQ.
  apply F17.f17_lib_evt.
  eapply LE.evt_mono.
  - unfold Regs6ss.mkR_of.
    apply (PF.f17_bltz_of_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc mem v0);
      [exact E | exact Hv].
  - intros ms' ->. exact HQ.
Qed.

(* seg_F17's Section (F17.v:475-481; its HMC, F17.v:486, is not used by seg_F17), with the twin modules named
   A.Reusable.<X>, the copies Seg/F17.v imports. *)
Section F17Src.
Context {fx : A.Reusable.YK11.FPState} {LS : A.Reusable.YO09.lib_shape} {rc : A.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : A.Reusable.YM05.RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : A.Reusable.YI16.sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* F17.v:2007-2111, line for line, except: the bltz bullet (F17.v:2032-2046) is f17_bltz_ul; F17's Section lemmas
   are cited as F17.<name> (to_exit_822a0 with this Section's arguments; the F17.v of record, a Theorem Labs lane's db985828094,
   blob 2530d1eeed7, renames the older to_exit_821c4 to its v1.9 address); getr is written A.Reusable.YK11.getr. *)
Lemma seg_F17_sec : forall j : nat,
  Hat B APIf ra (Inv_A822a0_at B APIf ra) j -> Hat B APIf ra (Inv_A8229c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hj & HHB & HFLSI & HLK &
    Hs7 & Hs22 & Hrec40 & Ha0 & (A & Hs1 & Hv232 & Hb192 & Hq136 & Hq120 & Hq176 & Happ & Hw240 & Hs24 & Hrecg &
    HL12) & Hs18 & Hrecb & H152 & H280 & HIFS3 & Hs20).
  subst c.
  rewrite SEGS.
  destruct Ha0 as (v0 & Ha0r & Ha0b).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hrest).
  eapply (sl_run regs (Z_to_bv 64 0x8229c) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x822a0 /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\ Sem.reg_get R 4 = Sem.reg_get regs 4 /\
       Sem.reg_get R 8 = Sem.reg_get regs 8 /\ Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\ Sem.reg_get R 23 = Sem.reg_get regs 23 /\
       Sem.reg_get R 24 = Sem.reg_get regs 24 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 18 = Sem.reg_get regs 18 /\ Sem.reg_get R 20 = Sem.reg_get regs 20 /\
       mem' = mem)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* 0x8229c: bltz a0,82b34 -- not taken (a0 = ingest result >= 0): this file's run PF.f17_bltz_F (at RNG_all,
       PF.f17_bltz_of_F), carried into the UL engine by f17_bltz_ul; the end state is the start state at 0x822a0 *)
    apply (f17_bltz_ul regs _ _ mem v0 _ Ha0r Ha0b).
    (* the end map is mkR_of regs itself, so each `Sem.reg_get R k = Sem.reg_get regs k` holds by computation (the
       source's regeq, a Section-local tactic of F17.v, is not needed and not visible here) *)
    hnf; do 3 eexists; split; [reflexivity|];
      split; [reflexivity|]; do 13 (split; [reflexivity|]); reflexivity.
  - (* the split cut at 0x822a0: same registers, same memory, model only materialized *)
    intros R pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E21 & E23 & E24 & E22 & E18 & E20 &
      Hmem)
      Hreg Hmat.
    subst pc' mem'.
    assert (G2 : A.Reusable.YK11.getr regs' 2 = A.Reusable.YK11.getr regs 2)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G3 : A.Reusable.YK11.getr regs' 3 = A.Reusable.YK11.getr regs 3)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G4 : A.Reusable.YK11.getr regs' 4 = A.Reusable.YK11.getr regs 4)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G8 : A.Reusable.YK11.getr regs' 8 = A.Reusable.YK11.getr regs 8)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G9 : A.Reusable.YK11.getr regs' 9 = A.Reusable.YK11.getr regs 9)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G19 : A.Reusable.YK11.getr regs' 19 = A.Reusable.YK11.getr regs 19)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G21 : A.Reusable.YK11.getr regs' 21 = A.Reusable.YK11.getr regs 21)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G22 : A.Reusable.YK11.getr regs' 22 = A.Reusable.YK11.getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G23 : A.Reusable.YK11.getr regs' 23 = A.Reusable.YK11.getr regs 23)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G24 : A.Reusable.YK11.getr regs' 24 = A.Reusable.YK11.getr regs 24)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G26 : A.Reusable.YK11.getr regs' 26 = A.Reusable.YK11.getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G18 : A.Reusable.YK11.getr regs' 18 = A.Reusable.YK11.getr regs 18)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (G20 : A.Reusable.YK11.getr regs' 20 = A.Reusable.YK11.getr regs 20)
      by ((etransitivity; [apply Hreg|]); unfold A.Reusable.YK11.getr; cbn [bv_eqb negb]; eassumption).
    assert (ASP : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite G2; reflexivity).
    apply (F17.to_exit_822a0 B APIf ra empty FF j Hexit).
    exists phi, regs', mem, md', fr. rewrite SEGS.
    split; [reflexivity|].
    split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA G2 G3 G4 G8 G9 G19 G26 Hmat)|].
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (F17.flsi_regs g j fr regs regs' mem HFLSI G9)|].
    split.
    { destruct HLK as (HLj & HL21 & HLour). split; [exact HLj|].
      split; [unfold rg in *; rewrite G21; exact HL21 | exact HLour]. }
    split; [unfold rg in *; rewrite G23; exact Hs7|].
    split; [unfold rg in *; rewrite G22; exact Hs22|].
    split; [exact Hrec40|].
    split.
    { exists A.
      split; [unfold rg in *; rewrite G9; exact Hs1|].
      split; [exact Hv232|]. split; [exact Hb192|].
      split; [exact Hq136|]. split; [exact Hq120|]. split; [exact Hq176|].
      split; [exact Happ|]. split; [exact Hw240|].
      split; [unfold rg in *; rewrite G24; exact Hs24|].
      split; [|exact HL12].
      intro HfL. destruct (Hrecg HfL) as (HRI & Hphiw & Hrecw).
      split; [exact HRI|]. split; [rewrite ASP; exact Hphiw | exact Hrecw]. }
    split; [unfold rg in *; rewrite G18; exact Hs18|].
    split; [exact Hrecb|].
    split; [exact (F17.spill_regs regs regs' mem _ _ H152 G9)|].
    split; [exact (F17.spill_regs regs regs' mem _ _ H280 G9)|].
    (* the bltz writes no register and no memory: IFS3 and s4 cross unchanged *)
    split.
    { destruct HIFS3 as (HID & HFG & HFSj). split; [exact HID|]. split; [exact HFG|].
      exact (F17.f17_fsj_regs g fr j regs regs' mem HFSj G9). }
    unfold rg in *. rewrite G20. exact Hs20.
Qed.

End F17Src.

(* The tie: exactly the type of the source lemma F17.seg_F17 (its Section closed), proved by the re-done script.
   `@` keeps F17.seg_F17's maximal implicit binders {fx LS rc} {SH SK} in the type (without it they are inserted as
   unsolvable existential variables). *)
Lemma seg_F17_src : ltac:(let T := type of @F17.seg_F17 in exact T).
Proof. exact @seg_F17_sec. Qed.

(* The tie is the source's type itself, by constr_eq (syntactic, not up to conversion). *)
Example seg_F17_src_verbatim : True.
Proof.
  let A := type of @F17.seg_F17 in let B := type of @seg_F17_src in constr_eq A B.
  exact I.
Qed.
