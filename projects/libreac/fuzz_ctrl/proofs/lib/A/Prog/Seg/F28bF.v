(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names, addresses and numbers changed; 343 of its 388 lines of code are new or changed and 351 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F28a.v, with its module paths and module names changed; 186 of its 257 lines of code are new or changed and 317 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F28aF.v, with its module names changed; 210 of its 280 lines of code are new or changed and 187 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F28b.v blob 5a6359f1736b (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f28b_run_of_F_bounded re-derives F28b.f28b_run at ExecF.RNG_all after the address bounds that F28b.v
   does not state (see below); f28b_run_of_F_bounded_shape shows by a proof that the bounded corollary is
   F28b.f28b_run's statement plus those premises and nothing else. Mechanical re-run, route (a) (lead 22:15Z);
   input to the ported walk only. *)

(* The footprint (_F) form of F28b.v's run lemma f28b_run (0x826d4 -> 0x82750, the check_ports post-loop checks,
   the instrumented check of blk[7] at phi + 25 and its slow block 0x82a8c): the same run, re-stepped with lib.Lib
   StepF as an ExecF.evtF under a universally quantified footprint RNG, with the same post-state predicate
   (F28b.f28b_K) and the same premises, and one ExecF.rng premise per region the run reads (it writes nothing).
   Each region is one of the run's own `ov_read_bytes` premises: the three ports words at fr + 128 / fr + 132 /
   fr + 136, the spill cells [A + 120] and [A + 176], the byte first at fr + 160, the byte blk[7] at phi + 25 and
   its shadow byte at ((phi + 25) >> 3) + ASAN_K.
   The source runs are on the UL engine (lib/A/Tk/UL/Exec.v `evt`); f28bF_ul_of_lib carries the lib.Lib evt the
   corollary gets from evtF_evt back to that engine, as Seg/F10F.v does.
   BOUNDED COROLLARY: F28b.f28b_run states no bound on fr or on A (only `rg regs 7 (fr + 128)` and
   `rg regs 9 A`), so ExecF.rng_all cannot discharge the rng premises of the six regions those two name. Per the
   lane rule, the corollary is f28b_run_of_F_bounded: F28b.f28b_run's statement with exactly `0 <= lo` and
   `lo + len <= 2 ^ 64` for those regions inserted after the source premises, and no verbatim pin.
   F28b.v itself is unchanged. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot B7Cuts F28b.
(* Last: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr, as F28b.v does. *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module F28bLE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module F28bUE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LPE (lib.Lib's PropExec). *)
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* The UL engine's evt from the lib.Lib one (Seg/F10F.v f10F_ul_of_lib). *)
Lemma f28bF_ul_of_lib : forall Q ms, F28bLE.evt rsegs Q ms -> F28bUE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply F28bUE.msteps_refl|].
  eapply F28bUE.msteps_cons; [exact Hs | exact IH].
Qed.

(* F28b.f28b_mkR_of_expand states mkR_of regs over the UL engine's Frame.mkR; lib.Lib StepF reads the lib.Lib one
   (F5F.v's f5F_mkR_expand makes exactly this change). Both sides are Regs6ss.mkR_of regs by delta.
   The slots name lib.Lib's getr (LPE, the core copy, a Theorem Labs lane 08:56Z rule), except a BRIDGE: slots 7 9 11 12 13 17 20
   22 26 keep F28b.v's getr (lib.A.Reusable.YK11), in full path, because f28b_run_F's proof rewrites exactly those
   slots with F28b.v's rg premises (subst_slot), which name that copy; with lib.Lib's getr there, subst_slot finds
   no subterm. *)
Lemma f28bF_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR (LPE.getr regs 1) (LPE.getr regs 2) (LPE.getr regs 3)
    (LPE.getr regs 4) (LPE.getr regs 5) (LPE.getr regs 6)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 7) (LPE.getr regs 8)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 9) (LPE.getr regs 10)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 11)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 12)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 13) (LPE.getr regs 14) (LPE.getr regs 15)
  (LPE.getr regs 16) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 17) (LPE.getr regs 18)
  (LPE.getr regs 19) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 20) (LPE.getr regs 21)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 22) (LPE.getr regs 23) (LPE.getr regs 24)
  (LPE.getr regs 25) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr regs 26) (LPE.getr regs 27)
  (LPE.getr regs 28) (LPE.getr regs 29) (LPE.getr regs 30) (LPE.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* F28b.v's `brf` over evtF: a branch to 0x82bf4 shown not taken, its condition false by pf. *)
Ltac brfF pf :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ (if ?c then _ else _) _ _ _ _)
    =>
      replace c with false by (symmetry; pf); cbv_concl_iota
  end.

(* F28b.v's `converge` over evtF: the same tactic text, matching ExecF.evtF goals instead of the UL engine's evt.
   The fast path (shadow byte = 0) and the slow block 0x82a8c rejoin at 0x82744 with only the scratch register a3
   changed. *)
Ltac convergeF scratch Xe b OK BD :=
  match goal with
  | |- ExecF.evtF ?segs ?RNG ?Q (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R ?F
    (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, ExecF.evtF segs RNG Q
        (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- ExecF.evtF _ _ _
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.sxb; rewrite K0;
               vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- ExecF.evtF _ _ _
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R2 _ _ _ _ _ _) => exact
             (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- ExecF.evtF _ _ _
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.sxb;
               rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota; OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step;
             OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step;
           match goal with |- ExecF.evtF _ _ _
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite
               (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit Xe) by lia;
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota; OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step;
           match goal with |- ExecF.evtF _ _ _
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R2 _ _ _ _ _ _) => exact
             (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

Section F28bF.
Context {fx : FPState}.

(* ---- f28b_run as an evtF: 0x826d4 -> 0x82750 over abstract values. ---- *)
Lemma f28b_run_F : forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
    (fr A phi nin nout nemp nu pf hb : Z) (b7 b25 : byte),
  rg regs 7 (fr + 128) -> rg regs 20 (4 * nu) -> rg regs 9 A -> rg regs 13 nemp -> rg regs 12 nin ->
  rg regs 11 nout -> rg regs 17 pf -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
  0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 -> nin + nout + nemp + nu = 12 ->
  0 <= pf < 256 -> 0 < phi -> phi + 50 <= 2 ^ 64 -> hb = 16 * bv_unsigned b7 ->
  ov_read_bytes rsegs mem (LMem.wa (fr + 128)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nin))) ->
  ov_read_bytes rsegs mem (LMem.wa (fr + 132)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nout))) ->
  ov_read_bytes rsegs mem (LMem.wa (fr + 136)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 hb)) ->
  ov_read_bytes rsegs mem (LMem.wa (A + 120)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 160))) ->
  ov_read_bytes rsegs mem (LMem.wa (fr + 160)) 1 = Some [Z_to_bv 8 pf] ->
  ov_read_bytes rsegs mem (LMem.wa (A + 176)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
  ov_read_bytes rsegs mem (LMem.wa (Z.shiftr (phi + 25) 3 + ASAN_K)) 1 = Some [b25] ->
  (bv_signed b25 = 0 \/ (phi + 25) mod 8 < bv_signed b25) -> -128 <= bv_signed b25 < 128 ->
  ov_read_bytes rsegs mem (LMem.wa (phi + 25)) 1 = Some [b7] ->
  ExecF.rng RNG (fr + 128) 4 ->
  ExecF.rng RNG (fr + 132) 4 ->
  ExecF.rng RNG (fr + 136) 4 ->
  ExecF.rng RNG (A + 120) 8 ->
  ExecF.rng RNG (fr + 160) 1 ->
  ExecF.rng RNG (A + 176) 8 ->
  ExecF.rng RNG (Z.shiftr (phi + 25) 3 + ASAN_K) 1 ->
  ExecF.rng RNG (phi + 25) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R fp_regs pc' fp_csr
    None mem' (LPE.seg_rom rsegs) /\
                                  f28b_K regs fr mem R pc' mem')
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x826d4)
      fp_csr None mem (LPE.seg_rom rsegs)).
Proof.
  intros RNG regs mem fr A phi nin nout nemp nu pf hb b7 b25 Ht2 Hs4 Hs1 Ha3 Ha2 Ha1 Ha7 Hs6 Hs10
    Rin Rout Remp Rnu Hsum Rpf Hphi0 Hphi50 Ehb R0 R4 R8 R120 RFI R176 RSH OK25 BD25 R25
    G128 G132 G136 G120 G160 G176 GSH G25.
  subst hb.
  (* F28b.v states its reads over the UL engine's ULMem.wa, which lib.Lib StepF's solve_load does not unfold; this
     delta step put them in their unfolded form. The reads of f28b_run_F are now lib.Lib's wa (LMem.wa), which
     solve_load unfolds itself, so the step changes no premise; as a proof occurrence it keeps the copy it named,
     in full path. *)
  cbv beta delta [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wa] in R0, R4, R8, R120, RFI, R176, RSH,
    R25.
  unfold f28b_K. rewrite f28bF_mkR_of_expand.
  subst_slot Ht2. subst_slot Hs4. subst_slot Hs1. subst_slot Ha3. subst_slot Ha2. subst_slot Ha1.
  subst_slot Ha7. subst_slot Hs6. subst_slot Hs10.
  (* 0x826d4 lw a0,0(t2) ; andi a4,a0,3 ; bnez a4 (in_ch & 3 = 0) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. brfF ltac:(exact (b7_c80 nin Rin)).
  (* 0x826e0 lw a4,4(t2) ; or a5,a4,s4 ; andi a5,a5,3 ; bnez a5 ((out_ch | unk) & 3 = 0) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. brfF ltac:(exact (b7_c81 nout nu Rout Rnu)).
  (* 0x826f0 ld a5,120(s1) ; lbu a5,0(a5) ; zext.b a6,a7 ; bne a5,a6 (first) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. brfF ltac:(exact (b7_c82 pf Rpf)).
  (* 0x82700 slli a3 ; add s4 ; add s4 ; addw a3 ; ld s9,176(s1) ; li a5,48 ; bne a3,a5 (sum = 48) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    brfF ltac:(exact (b7_c83 nin nout nemp nu Rin Rout Remp Rnu Hsum)).
  (* 0x8271c slliw a2 ; bne a0,a2 (in_ch = 4 n_in) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. brfF ltac:(exact (b7_c84 nin Rin)).
  (* 0x82724 slliw a0,a1 ; bne a4,a0 (out_ch = 4 n_out) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. brfF ltac:(exact (b7_c84 nout Rout)).
  (* 0x8272c addi a0,s6,7 ; srli a1,a0,3 ; add a1,a1,s10 ; lb a2,0(a1) ; lw a1,8(t2) ; bnez a2 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 25)) by lia.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  convergeF (Z_to_bv 5 13) (phi + 25) b25 OK25 BD25.
  (* 0x82744 lbu a0,0(a0) ; slli a0,a0,4 ; bne a1,a0 (headamp_base = 16 blk[7]) *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. brfF ltac:(exact (b7_c86 b7)).
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
    all: OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs; try reflexivity.
Qed.

(* ---- F28b.f28b_run restated at RNG_all (then back to the UL engine). F28b.v bounds neither fr nor A, so the
   eight regions the run reads need their own bounds here: exactly `0 <= lo` and `lo + len <= 2 ^ 64` for the six
   regions fr and A name (the two phi regions are bounded by the run's own `0 < phi` / `phi + 50 <= 2 ^ 64`). ---- *)
Lemma f28b_run_of_F_bounded : forall (regs : bvmap 5 word) (mem : word -> option byte)
    (fr A phi nin nout nemp nu pf hb : Z) (b7 b25 : byte),
  rg regs 7 (fr + 128) -> rg regs 20 (4 * nu) -> rg regs 9 A -> rg regs 13 nemp -> rg regs 12 nin ->
  rg regs 11 nout -> rg regs 17 pf -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
  0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 -> nin + nout + nemp + nu = 12 ->
  0 <= pf < 256 -> 0 < phi -> phi + 50 <= 2 ^ 64 -> hb = 16 * bv_unsigned b7 ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 128)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nin))) ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 132)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nout))) ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 136)) 4 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 hb)) ->
  ov_read_bytes rsegs mem (ULMem.wa (A + 120)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 160))) ->
  ov_read_bytes rsegs mem (ULMem.wa (fr + 160)) 1 = Some [Z_to_bv 8 pf] ->
  ov_read_bytes rsegs mem (ULMem.wa (A + 176)) 8 = Some
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
  ov_read_bytes rsegs mem (ULMem.wa (Z.shiftr (phi + 25) 3 + ASAN_K)) 1 = Some [b25] ->
  (bv_signed b25 = 0 \/ (phi + 25) mod 8 < bv_signed b25) -> -128 <= bv_signed b25 < 128 ->
  ov_read_bytes rsegs mem (ULMem.wa (phi + 25)) 1 = Some [b7] ->
  0 <= fr + 128 -> fr + 128 + 4 <= 2 ^ 64 ->
  0 <= fr + 132 -> fr + 132 + 4 <= 2 ^ 64 ->
  0 <= fr + 136 -> fr + 136 + 4 <= 2 ^ 64 ->
  0 <= A + 120 -> A + 120 + 8 <= 2 ^ 64 ->
  0 <= fr + 160 -> fr + 160 + 1 <= 2 ^ 64 ->
  0 <= A + 176 -> A + 176 + 8 <= 2 ^ 64 ->
  F28bUE.evt rsegs
    (fun ms => exists R pc' mem', ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R fp_regs pc' fp_csr
    None mem' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
                                  f28b_K regs fr mem R pc' mem')
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x826d4)
      fp_csr None mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem fr A phi nin nout nemp nu pf hb b7 b25 Ht2 Hs4 Hs1 Ha3 Ha2 Ha1 Ha7 Hs6 Hs10
    Rin Rout Remp Rnu Hsum Rpf Hphi0 Hphi50 Ehb R0 R4 R8 R120 RFI R176 RSH OK25 BD25 R25
    B128a B128b B132a B132b B136a B136b B120a B120b B160a B160b B176a B176b.
  apply f28bF_ul_of_lib.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f28b_run_F ExecF.RNG_all regs mem fr A phi nin nout nemp nu pf hb b7 b25);
    try assumption;
    apply ExecF.rng_all;
    rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
    unfold ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

(* The shape check: f28b_run_of_F_bounded is F28b.f28b_run's statement plus the twelve bound premises and nothing
   else -- from the source statement the bounded one follows by dropping them. *)
Lemma f28b_run_of_F_bounded_shape :
  (forall (regs : bvmap 5 word) (mem : word -> option byte)
     (fr A phi nin nout nemp nu pf hb : Z) (b7 b25 : byte),
   rg regs 7 (fr + 128) -> rg regs 20 (4 * nu) -> rg regs 9 A -> rg regs 13 nemp -> rg regs 12 nin ->
   rg regs 11 nout -> rg regs 17 pf -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
   0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 -> nin + nout + nemp + nu = 12 ->
   0 <= pf < 256 -> 0 < phi -> phi + 50 <= 2 ^ 64 -> hb = 16 * bv_unsigned b7 ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 128)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nin))) ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 132)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nout))) ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 136)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 hb)) ->
   ov_read_bytes rsegs mem (ULMem.wa (A + 120)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 160))) ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 160)) 1 = Some [Z_to_bv 8 pf] ->
   ov_read_bytes rsegs mem (ULMem.wa (A + 176)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
   ov_read_bytes rsegs mem (ULMem.wa (Z.shiftr (phi + 25) 3 + ASAN_K)) 1 = Some [b25] ->
   (bv_signed b25 = 0 \/ (phi + 25) mod 8 < bv_signed b25) -> -128 <= bv_signed b25 < 128 ->
   ov_read_bytes rsegs mem (ULMem.wa (phi + 25)) 1 = Some [b7] ->
   F28bUE.evt rsegs
     (fun ms => exists R pc' mem', ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R fp_regs pc'
     fp_csr None mem' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
                                   f28b_K regs fr mem R pc' mem')
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x826d4)
     fp_csr None mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))) ->
  (forall (regs : bvmap 5 word) (mem : word -> option byte)
     (fr A phi nin nout nemp nu pf hb : Z) (b7 b25 : byte),
   rg regs 7 (fr + 128) -> rg regs 20 (4 * nu) -> rg regs 9 A -> rg regs 13 nemp -> rg regs 12 nin ->
   rg regs 11 nout -> rg regs 17 pf -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
   0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 -> nin + nout + nemp + nu = 12 ->
   0 <= pf < 256 -> 0 < phi -> phi + 50 <= 2 ^ 64 -> hb = 16 * bv_unsigned b7 ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 128)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nin))) ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 132)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 (4 * nout))) ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 136)) 4 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4 (Z_to_bv 64 hb)) ->
   ov_read_bytes rsegs mem (ULMem.wa (A + 120)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 160))) ->
   ov_read_bytes rsegs mem (ULMem.wa (fr + 160)) 1 = Some [Z_to_bv 8 pf] ->
   ov_read_bytes rsegs mem (ULMem.wa (A + 176)) 8 = Some
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 (fr + 64))) ->
   ov_read_bytes rsegs mem (ULMem.wa (Z.shiftr (phi + 25) 3 + ASAN_K)) 1 = Some [b25] ->
   (bv_signed b25 = 0 \/ (phi + 25) mod 8 < bv_signed b25) -> -128 <= bv_signed b25 < 128 ->
   ov_read_bytes rsegs mem (ULMem.wa (phi + 25)) 1 = Some [b7] ->
   0 <= fr + 128 -> fr + 128 + 4 <= 2 ^ 64 ->
   0 <= fr + 132 -> fr + 132 + 4 <= 2 ^ 64 ->
   0 <= fr + 136 -> fr + 136 + 4 <= 2 ^ 64 ->
   0 <= A + 120 -> A + 120 + 8 <= 2 ^ 64 ->
   0 <= fr + 160 -> fr + 160 + 1 <= 2 ^ 64 ->
   0 <= A + 176 -> A + 176 + 8 <= 2 ^ 64 ->
   F28bUE.evt rsegs
     (fun ms => exists R pc' mem', ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R fp_regs pc'
     fp_csr None mem' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
                                   f28b_K regs fr mem R pc' mem')
     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x826d4)
       fp_csr None mem (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))).
Proof.
  intros H. intros. eapply H; eassumption.
Qed.

End F28bF.
