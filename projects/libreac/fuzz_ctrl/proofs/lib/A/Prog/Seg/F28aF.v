(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names, addresses and numbers changed; 343 of its 388 lines of code are new or changed and 351 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F28a.v, with its module paths and module names changed; 186 of its 257 lines of code are new or changed and 317 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F28a.v blob 0f40e3d517e2 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F28a.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type
   is the type of F28a.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of F28a.v's two run lemmas f28_body and f28_turn (0x8265c -> 0x826c0: one turn of the
   port-slot loop of the inlined check_ports, with the instrumented check of the byte at A): the same runs,
   re-stepped with lib.Lib StepF as ExecF.evtF under a universally quantified footprint RNG, with the same
   post-state predicate and the same premises, and one ExecF.rng premise per region the turn reads: the byte at A
   (the lemma's own `addressable m A 1` / `ov_read_bytes .. A 1` premises; loaded at 0x8266c) and its shadow byte
   at (A >> 3) + ASAN_K (loaded by the instrumented check at 0x82664). The turn writes nothing.
   The source runs are on the UL engine (lib/A/Tk/UL/Exec.v `evt`); f28F_ul_of_lib carries the lib.Lib evt the
   corollaries get from evtF_evt back to that engine, as Seg/F10F.v does. F28a.v itself is unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot B7Cuts F28a.
(* Last: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr, as F28a.v does. *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module F28LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module F28UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* The UL engine's evt from the lib.Lib one: both are msteps of `ms_svc_pending ms = None /\ step = MachineOk ms'`
   (Seg/F10F.v f10F_ul_of_lib). *)
Lemma f28F_ul_of_lib : forall Q ms, F28LE.evt rsegs Q ms -> F28UE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply F28UE.msteps_refl|].
  eapply F28UE.msteps_cons; [exact Hs | exact IH].
Qed.

(* F28a.v's `converge` over evtF: the same tactic text, matching ExecF.evtF goals instead of the UL engine's evt.
   `bnez shadow, slow`: the fast path (shadow byte 0) and the slow path (`andi t0,a0,7; bge t0,a7,error path;
   j back`, the branch to the error path not taken because X mod 8 < b) rejoin at `cont`; the scratch register is
   generalised. Leaves the goal `forall rr, evtF .. cont`. *)
Ltac convergeF scratch Xe b OK BD :=
  match goal with
  | |- ExecF.evtF ?segs ?RNG ?Q (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R ?F
    (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr : word,
                 ExecF.evtF segs RNG Q (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
                   (@bvmap_set 5 word scratch rr R) F cont fc rv m ro)) by
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
               (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit Xe) by
               (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota; OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step;
           match goal with |- ExecF.evtF _ _ _
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R2 _ _ _ _ _ _) => exact
             (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

(* F28a.v's four byte facts restated over the names lib.Lib StepF puts in the goal: F28a.v states b7_in / b7_out /
   b7_emp / b7_brc over the UL engine's zxb and PropExec, while StepF steps produce the lib.Lib ones. The two sets
   of constants have the same bodies, so each restatement is the original term for term after delta; this is the
   name change F10F.v makes for f10F_rd1 / f10F_rd8 / f10F_rdk. The statements and proofs are otherwise F28a.v's. *)
Lemma f28aF_in : forall c : byte,
  bv_unsigned (LPE.v_sltiu (Z_to_bv 64
    (Z.land (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.zxb c)) 253)) 1) =
  if RcLeaf.is_in (bv_unsigned c) then 1 else 0.
Proof. exact b7_in. Qed.

Lemma f28aF_out : forall c : byte,
  bv_unsigned (LPE.v_sltiu (Z_to_bv 64
    (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.zxb c) + -1)) 1) =
  if RcLeaf.is_out (bv_unsigned c) then 1 else 0.
Proof. exact b7_out. Qed.

Lemma f28aF_emp : forall c : byte,
  bv_unsigned (LPE.v_sltiu (Z_to_bv 64
    (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.zxb c) + -3)) 1) =
  if is_empty (bv_unsigned c) then 1 else 0.
Proof. exact b7_emp. Qed.

Lemma f28aF_brc : forall f (c : byte), 0 <= f < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (LPE.v_sltu (Z_to_bv 64 0)
                                            (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                             (bv_unsigned (LPE.v_sltiu (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.zxb c)
                               4))))
         (Z_to_bv 64 0) = (f =? 0) && (4 <=? bv_unsigned c).
Proof. exact b7_brc. Qed.

(* ---- f28_body as an evtF: 0x8265c -> 0x826c0, one turn of the port-slot loop on the code c at A. ---- *)
Lemma f28_body_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A N x1 x2 x3 f : Z) (c : byte),
    a0 = Z_to_bv 64 A -> a4 = Z_to_bv 64 A -> a5 = Z_to_bv 64 N -> a1 = Z_to_bv 64 x1 -> a2 = Z_to_bv 64 x2 ->
    a3 = Z_to_bv 64 x3 -> a6 = Z_to_bv 64 f -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= f < 256 -> addressable m A 1 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [c] ->
    ExecF.rng RNG A 1 ->
    ExecF.rng RNG (Z.shiftr A 3 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists t0' t1' : word,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR ra sp gp tp t0' t1' t2 s0 s1
           (Z_to_bv 64 (A + 1))
                       (Z_to_bv 64 (x1 + if RcLeaf.is_out (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x2 + if RcLeaf.is_in (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x3 + if is_empty (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (A + 1)) (Z_to_bv 64 (N + -1))
                       (Z_to_bv 64 (b7_f f (bv_unsigned c))) (Z_to_bv 64 (b7_f f (bv_unsigned c)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x826c0) fc None m (LPE.seg_rom rsegs))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
        (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8265c) fc None m (LPE.seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A N x1 x2 x3 f c -> -> -> -> -> -> -> -> Hf Had Hrd RA1 RSH.
  pose proof Had as Had'. destruct Had' as (HA0 & _ & HA1 & _).
  destruct (f28_shadow m A Had) as (b & HRsh & OK & BD).
  (* 0x8265c srli a7,a0,3 ; add a7,a7,s10 ; lb a7,0(a7) (the shadow byte) ; bnez a7,0x826c8 *)
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit A) by (unfold APPMEM_END in *; lia).
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  convergeF (Z_to_bv 5 5) A b OK BD.
  (* 0x8266c lbu t0,0(a4) ; zext.b a7,a6 ; sltiu t1,t0,4 ; snez a7,a7 ; or t1,a7,t1 ; mv a7,t0 ; beqz t1 *)
  do 7 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
  rewrite (f28aF_brc f c Hf).
  destruct ((f =? 0) && (4 <=? bv_unsigned c)) eqn:Ec; cbv_concl_iota.
  - do 13 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. rewrite f28aF_in, f28aF_out, f28aF_emp.
    apply ExecF.evtF_done. hnf. eexists _, _. unfold b7_f. rewrite Ec. reflexivity.
  - do 14 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step. rewrite f28aF_in, f28aF_out, f28aF_emp.
    apply ExecF.evtF_done. hnf. eexists _, _. unfold b7_f. rewrite Ec. reflexivity.
Qed.

(* ---- f28_turn as an evtF: the same turn on the model (the code is blk[8 + i] of bs). ---- *)
Lemma f28_turn_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (i : nat) (A N : Z),
    a0 = Z_to_bv 64 A -> a4 = Z_to_bv 64 A -> a5 = Z_to_bv 64 N ->
    a1 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs i) -> a2 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs i) ->
    a3 = Z_to_bv 64 (RcLeaf.cnt is_empty bs i) -> a6 = Z_to_bv 64 (RcPorts.pu_first bs i) ->
    s10 = Z_to_bv 64 ASAN_K -> addressable m A 1 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [nth (8 + i) bs (Z_to_bv 8 0)] ->
    ExecF.rng RNG A 1 ->
    ExecF.rng RNG (Z.shiftr A 3 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists t0' t1' : word,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR ra sp gp tp t0' t1' t2 s0 s1
           (Z_to_bv 64 (A + 1))
                       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs (S i)))
                       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs (S i)))
                       (Z_to_bv 64 (RcLeaf.cnt is_empty bs (S i)))
                       (Z_to_bv 64 (A + 1)) (Z_to_bv 64 (N + -1))
                       (Z_to_bv 64 (RcPorts.pu_first bs (S i))) (Z_to_bv 64 (RcPorts.pu_first bs (S i)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x826c0) fc None m (LPE.seg_rom rsegs))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS
        (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8265c) fc None m (LPE.seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs i A N E0 E4 E5 E1 E2 E3 E6 E26 Had Hrd RA1 RSH.
  destruct (b7_first_spec bs i) as (_ & Hf).
  eapply ExecF.evtF_mono.
  { exact (f28_body_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m A N _ _ _ _ _ E0 E4 E5 E1 E2 E3 E6 E26 Hf Had Hrd RA1 RSH). }
  intros ms' (t0' & t1' & ->). exists t0', t1'.
  rewrite <- (b7_first_step bs i). reflexivity.
Qed.

(* ---- F28a.f28_body / F28a.f28_turn restated: evtF_evt of each twin at RNG_all (then back to the UL engine),
   each rng premise by rng_all. The byte A is bounded by the run's own `addressable m A 1`. ---- *)
Ltac f28_rng_all :=
  apply ExecF.rng_all;
  rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
  unfold shadow_addr, ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia.

Lemma f28_body_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A N x1 x2 x3 f : Z) (c : byte),
    a0 = Z_to_bv 64 A -> a4 = Z_to_bv 64 A -> a5 = Z_to_bv 64 N -> a1 = Z_to_bv 64 x1 -> a2 = Z_to_bv 64 x2 ->
    a3 = Z_to_bv 64 x3 -> a6 = Z_to_bv 64 f -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= f < 256 -> addressable m A 1 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [c] ->
    F28UE.evt rsegs
      (fun ms' => exists t0' t1' : word,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS
                 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra sp gp tp t0' t1' t2 s0 s1
                   (Z_to_bv 64 (A + 1))
                       (Z_to_bv 64 (x1 + if RcLeaf.is_out (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x2 + if RcLeaf.is_in (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x3 + if is_empty (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (A + 1)) (Z_to_bv 64 (N + -1))
                       (Z_to_bv 64 (b7_f f (bv_unsigned c))) (Z_to_bv 64 (b7_f f (bv_unsigned c)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x826c0) fc None m
                    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS
         (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5
            a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8265c) fc None m
            (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A N x1 x2 x3 f c E0 E4 E5 E1 E2 E3 E6 E26 Hf Had Hrd.
  pose proof Had as (HA0 & _ & HA1 & _).
  apply f28F_ul_of_lib.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f28_body_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m A N x1 x2 x3 f c); try assumption; f28_rng_all.
Qed.

Lemma f28_turn_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (i : nat) (A N : Z),
    a0 = Z_to_bv 64 A -> a4 = Z_to_bv 64 A -> a5 = Z_to_bv 64 N ->
    a1 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs i) -> a2 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs i) ->
    a3 = Z_to_bv 64 (RcLeaf.cnt is_empty bs i) -> a6 = Z_to_bv 64 (RcPorts.pu_first bs i) ->
    s10 = Z_to_bv 64 ASAN_K -> addressable m A 1 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [nth (8 + i) bs (Z_to_bv 8 0)] ->
    F28UE.evt rsegs
      (fun ms' => exists t0' t1' : word,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS
                 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra sp gp tp t0' t1' t2 s0 s1
                   (Z_to_bv 64 (A + 1))
                       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs (S i)))
                       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs (S i)))
                       (Z_to_bv 64 (RcLeaf.cnt is_empty bs (S i)))
                       (Z_to_bv 64 (A + 1)) (Z_to_bv 64 (N + -1))
                       (Z_to_bv 64 (RcPorts.pu_first bs (S i))) (Z_to_bv 64 (RcPorts.pu_first bs (S i)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x826c0) fc None m
                    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS
         (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5
            a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8265c) fc None m
            (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs i A N E0 E4 E5 E1 E2 E3 E6 E26 Had Hrd.
  pose proof Had as (HA0 & _ & HA1 & _).
  apply f28F_ul_of_lib.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f28_turn_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m bs i A N); try assumption; f28_rng_all.
Qed.

(* The pins: each *_of_F states F28a's text term for term (constr_eq: syntactic, not up to conversion). *)
Example f28_body_of_F_verbatim : True.
Proof.
  let a := type of F28a.f28_body in let b := type of f28_body_of_F in constr_eq a b.
  exact I.
Qed.

Example f28_turn_of_F_verbatim : True.
Proof.
  let a := type of F28a.f28_turn in let b := type of f28_turn_of_F in constr_eq a b.
  exact I.
Qed.
