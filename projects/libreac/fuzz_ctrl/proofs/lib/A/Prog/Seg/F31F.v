(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v, with its module paths, module names, addresses and numbers changed; 619 of its 695 lines of code are new or changed and 721 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F31.v b14507d1ada3 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F31.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F31.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   This file REPLACES the v1.8 Seg/F31F.v of the base (which carries the v1.8 pcs 0x826ec .. 0x8272c and the v1.8
   wrapper constants). It covers all three of Seg/F31.v's evt runs: f31n_evt (:343), F31.f31c_evt (:368) and
   F31.f31c_norm (:483).

   The wrapper's footprint contract. bcmp_wrap_c.v's bcmp_wrap_contract_F quantifies over every footprint, so it
   does not follow from Seg/F31.v's plain Section Hypothesis HBC, and the corollaries may not assume more than HBC.
   bcmp_wrap_F_at RNG (module F31BW, as Seg/F35F.v's F35BW) is that contract's body at ONE footprint, read in
   bcmp_wrap_c.v's name environment; bcmp_wrap_F_at_owner proves by conversion that it is the owner's text, and
   bcmp_wrap_F_at_all proves its RNG_all instance from the plain contract with ExecF_all.evt_evtF_all. A caller at a
   smaller footprint (the ported walk) takes bcmp_wrap_F_at RNG from bcmp_wrap_contract_F through
   bcmp_wrap_F_at_owner.

   Accesses. F31's own instructions read the three frame spill cells [A + 128], [A + 208], [A + 168] and the three
   source bytes O + 4, O + 5, O + 6 (inside [O + 4, O + 10)); none is instrumented. Everything else is the
   wrapper's, as bcmp_wrap_F_at asks with L = a0 = O + 4, R = a1 = R and N = a2 = 6.

   rule 24: no function proved. The only callee assumption is Seg/F31.v's own HBC (the plain contract, a Section
   Hypothesis of the corollaries); no Axiom, no Parameter, and every lemma below ends in Qed. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot F31.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 may be the plain one here;
   Seg/F31.v states its runs with the image-A one (its alias AYK), which this alias names. seg_rom MUST be that
   one or the _of_F pins below are not the owner's text. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.

(* Seg/F31.v states its runs with its OWN Local Definition copies of the wrapper constants, so the _of_F
   corollaries must name THOSE constants for the constr_eq pins to hold (a same-valued copy here would be a
   different constant). Notation, not Definition: it expands to Seg/F31.v's constant at parse time. *)
Local Notation BCMP_WRAP_K := F31.BCMP_WRAP_K.
Local Notation BCMP := F31.BCMP.
Local Notation REAL_BCMP := F31.REAL_BCMP.
Local Notation REAL_MEMCMP := F31.REAL_MEMCMP.
Local Notation GOT_CF := F31.GOT_CF.
Local Notation CF := F31.CF.
Local Notation MEMCMP := F31.MEMCMP.

(* ---------------- the bcmp wrapper's footprint contract at one footprint ----------------
   The body of bcmp_wrap_c.v's bcmp_wrap_contract_F for one RNG, read in bcmp_wrap_c.v's name environment (its
   imports, then its own definitions, then RngBytes and ExecF), so the names are bcmp_wrap_c's (BCMP_WRAP_K,
   BCMP_WRAP, REAL_BCMP, ...), memcmp_c's MEMCMP and StrFun's memcmp_model, as in Seg/F35F.v's F35BW. *)
Module F31BW.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
  LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State
  LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Arr
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
(* Z_scope: the elaborated term is bcmp_wrap_c.v's (its bv_scope captures no literal of this text). *)
Open Scope Z_scope.

Definition bcmp_wrap_F_at (RNG : footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  rng_bytes RNG ->
  rng RNG 0x10000 0x5ee000 ->
  rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG L N -> (N = 0 \/ rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + N - 1) / 8) + 8 - 8 * (shadow_addr L / 8))) ->
  rng RNG R N -> (N = 0 \/ rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + N - 1) / 8) + 8 - 8 * (shadow_addr R / 8))) ->
  evtF rsegs RNG (bcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

(* It is the owner's text: bcmp_wrap_c.v's bcmp_wrap_contract_F is bcmp_wrap_F_at at every footprint, by
   conversion. *)
Lemma bcmp_wrap_F_at_owner : bcmp_wrap_contract_F <-> forall RNG, bcmp_wrap_F_at RNG.
Proof. split; intros H RNG; exact (H RNG). Qed.
End F31BW.

Notation bcmp_wrap_F_at := F31BW.bcmp_wrap_F_at.

(* Last: StepF's step / if_true / if_false (evtF goals) shadow Step's (evt goals); ExecF's footprint shadows YO0f's;
   RngBytes (rng_bytes) is a lib.Lib leaf over ExecF. Then the image-A YK11 again, and Z_scope on top (ExecF / StepF
   re-open bv_scope on Import). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import AYK.
Open Scope Z_scope.

(* At RNG_all the footprint contract is the plain one: every Exec run is an ExecF run under RNG_all. *)
Lemma bcmp_wrap_F_at_all : BW.bcmp_wrap_contract -> bcmp_wrap_F_at RNG_all.
Proof.
  unfold BW.bcmp_wrap_contract, F31BW.bcmp_wrap_F_at. cbv zeta. intros HBC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo
    BL BR HM HMI HN ADL ADR EL ER AL AR SL SR HST HK HLO HSP HC HSR HRB HRM HGCF HCF1 HCF2 _ _ _ _ _ _ _.
  apply EFA.evt_evtF_all.
  exact (HBC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs
           v lo BL BR HM HMI HN ADL ADR EL ER AL AR SL SR HST HK HLO HSP HC HSR HRB HRM HGCF HCF1 HCF2).
Qed.

(* A shadow-word span of the wrapper's contract from the run's own premise (L + N - 1 written as one sum there). *)
Local Ltac f31_shadow_rng H :=
  first [ exact H
        | eapply rng_sub; [exact H | |]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia ].

(* ===================== the footprint runs ===================== *)

(* 0x82798 with a0 = -1: bnez a0 is taken to 0x82800. One branch, no memory access, so no rng premise. *)
Lemma f31n_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) Fr (Z_to_bv 64 0x82800) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros. subst a0. step. try if_true. apply evtF_done. reflexivity.
Qed.

(* Seg/F31.v's f31n_evt statement, at RNG_all. *)
Lemma f31n_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) Fr (Z_to_bv 64 0x82800) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). apply (f31n_evt_F RNG_all). assumption.
Qed.

(* The pin: f31n_evt_of_F's statement is F31.f31n_evt's, term for term (constr_eq: syntactic, not up to
   conversion). *)
Lemma f31n_evt_of_F_verbatim : True.
Proof.
  let a := type of F31.f31n_evt in let b := type of f31n_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x82798 with a0 = 0: the three byte checks of the source field (00 40 ab) are not taken, then the bcmp wrapper
   compares the 6 bytes at O+4 with the 6 bytes at R. F31's own accesses: the spill cells A+128, A+208, A+168 and
   the bytes O+4, O+5, O+6 (inside [O+4, O+10)); the rest are the wrapper's, as bcmp_wrap_F_at asks. *)
Lemma f31c_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    SF.memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) ->
    bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* F31's own three spill reloads *)
    rng RNG (A + 128) 8 -> rng RNG (A + 168) 8 -> rng RNG (A + 208) 8 ->
    (* the wrapper's footprint at 0x827c8 *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (O + 4) 6 ->
    rng RNG (8 * (shadow_addr (O + 4) / 8)) (8 * (shadow_addr (O + 9) / 8) + 8 - 8 * (shadow_addr (O + 4) / 8)) ->
    rng RNG R 6 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 5) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo -> -> [HO0 HO1] HR0 H128 H200 H168 HBL HBR HLrs Hmm HMI HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    R128 R168 R200 Hrb RIMG RSTK RL RLs RR RRs HF.
  assert (HL128 : ov_read_bytes rsegs m (wa (A + 128)) 8 = Some (le8 (Z_to_bv 64 (O + 4)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 128) _ 0 8 H128 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL200 : ov_read_bytes rsegs m (wa (A + 208)) 8 = Some (le8 (Z_to_bv 64 O))).
  { pose proof (bytes_at_ov_read rsegs m (A + 208) _ 0 8 H200 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL168 : ov_read_bytes rsegs m (wa (A + 168)) 8 = Some (le8 (Z_to_bv 64 R))).
  { pose proof (bytes_at_ov_read rsegs m (A + 168) _ 0 8 H168 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HB4 : ov_read_bytes rsegs m (wa (O + 4)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 0 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 0) with (O + 4) in HH by lia. exact HH. }
  assert (HB5 : ov_read_bytes rsegs m (wa (O + 5)) 1 = Some [Z_to_bv 8 64]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 1 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 1) with (O + 5) in HH by lia. exact HH. }
  assert (HB6 : ov_read_bytes rsegs m (wa (O + 6)) 1 = Some [Z_to_bv 8 171]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 2 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 2) with (O + 6) in HH by lia. exact HH. }
  (* 0x82798 bnez a0 (a0 = 0): not taken *)
  step. try if_false.
  (* 0x8279c ld a0,128(s1) [A+128]; lbu a0,0(a0) = 0x00 [O+4]; bnez a0 (to 0x82bf4): not taken *)
  step. step. step. try if_false.
  (* 0x827a8 ld a0,208(s1) [A+208]; lbu a0,5(a0) = 0x40 [O+5]; li a1,64; bne a0,a1 (to 0x82bf4): not taken *)
  step. step. step. step. try if_false.
  (* 0x827b8 ld a0,208(s1) [A+208]; lbu a0,6(a0) = 0xab [O+6]; li a1,171; bne a0,a1 (to 0x82bf4): not taken *)
  step. step. step. step. try if_false.
  (* 0x827c8 li a2,6; ld a0,128(s1) [A+128]; ld a1,168(s1) [A+168]; jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HF as HB. unfold F31BW.bcmp_wrap_F_at, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 (O + 4)) = O + 4) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evtF_cut.
  { eapply HB with (ls := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; exact HaR6.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - exact Hrb.
    - exact RIMG.
    - exact RSTK.
    - exact RL.
    - right; f31_shadow_rng RLs.
    - exact RR.
    - right; f31_shadow_rng RRs. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* The same run from a memory that agrees with the image on its read-only bytes (a cut carries ro_agree, not
   mem_inv): f31c_evt_F on the normalized memory (MemNormF.evtF_normalize_ro keeps RNG), every premise moved to it
   and the post moved back across mem_rel, as Seg/F31.v's f31c_norm does with MemNorm.evt_normalize. *)
Lemma f31c_norm_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    SF.memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) ->
    bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the same footprint as f31c_evt_F: normalize changes no address *)
    rng RNG (A + 128) 8 -> rng RNG (A + 168) 8 -> rng RNG (A + 208) 8 ->
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (O + 4) 6 ->
    rng RNG (8 * (shadow_addr (O + 4) / 8)) (8 * (shadow_addr (O + 9) / 8) + 8 - 8 * (shadow_addr (O + 4) / 8)) ->
    rng RNG R 6 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 5) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0 H128 H200 H168 HBL HBR HLrs Hmm HRO HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    R128 R168 R200 Hrb RIMG RSTK RL RLs RR RRs HF.
  pose proof (mem_rel_normalize rsegs m HRO) as REL0.
  assert (BR : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m (normalize rsegs m) a bs REL0) Hb)).
  assert (HST0 : stk rsegs (normalize rsegs m) lo (bv_unsigned sp)).
  { apply (RoAdapt.rel_stk_norm m _ _ _ REL0); [|exact HST].
    intros x Hx. apply RoAdapt.ro_addr_false_hi. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO).
    exact (f31c_evt_F RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 Fr fc (normalize rsegs m) A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0
             (BR _ _ H128) (BR _ _ H200) (BR _ _ H168) (BR _ _ HBL) (BR _ _ HBR) HLrs Hmm
             (mem_inv_normalize rsegs m)
             (RoAdapt.rel_addr_norm m _ _ _ REL0 HADL) (RoAdapt.rel_addr_norm m _ _ _ REL0 HADR)
             HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST0 Hlo1 Hlo2 Hspa
             (RoAdapt.rel_ac_norm m _ REL0 HAC) (RoAdapt.rel_sw_norm m _ REL0 HSW)
             (BR _ _ HRB) (BR _ _ HRM) (BR _ _ HGC) (BR _ _ HC254) (BR _ _ HC255)
             R128 R168 R200 Hrb RIMG RSTK RL RLs RR RRs HF). }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & _ & ST & _ & _).
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' REL0 RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' REL0 RM SAME WM)|].
  exact (RoAdapt.rel_stk_back m' m0' _ _ RM ST).
Qed.

(* ===================== Seg/F31.v's statements, at RNG_all ===================== *)

Section F31F.
(* Seg/F31.v's Section Hypothesis HBC (the plain contract): the corollaries take the footprint contract at RNG_all
   from it (bcmp_wrap_F_at_all). *)
Hypothesis HBC : BW.bcmp_wrap_contract.

(* Seg/F31.v's f31c_evt statement: f31c_evt_F at RNG_all. *)
Lemma f31c_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    SF.memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) ->
    bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0 H128 H200 H168 HBL HBR HLrs Hmm HMI HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  (* A has no bound of its own in Seg/F31.v's statement: the three spill cells' bounds come from their bytes_at
   premises, and R's from addressable (as the v1.8 Seg/F31F.v does). *)
  pose proof H128 as (B128 & L128 & _). pose proof H168 as (B168 & L168 & _). pose proof H200 as (B200 & L200 & _).
  rewrite length_le8 in L128, L168, L200.
  pose proof HADR as (AR0 & _ & AR1 & _).
  unfold HIGHMEM_BEG, APPMEM_END in *.
  apply (evtF_evt rsegs RNG_all).
  apply (f31c_evt_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A O R c9 c10 c11 rs vcmp lo); try assumption;
    first [ exact (bcmp_wrap_F_at_all HBC) | intros ? ? ? ? ?; exact I | apply rng_all ];
    unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* Seg/F31.v's f31c_norm statement: f31c_norm_F at RNG_all. *)
Lemma f31c_norm_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    SF.memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) ->
    bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0 H128 H200 H168 HBL HBR HLrs Hmm HRO HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  pose proof H128 as (B128 & L128 & _). pose proof H168 as (B168 & L168 & _). pose proof H200 as (B200 & L200 & _).
  rewrite length_le8 in L128, L168, L200.
  pose proof HADR as (AR0 & _ & AR1 & _).
  unfold HIGHMEM_BEG, APPMEM_END in *.
  apply (evtF_evt rsegs RNG_all).
  apply (f31c_norm_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A O R c9 c10 c11 rs vcmp lo); try assumption;
    first [ exact (bcmp_wrap_F_at_all HBC) | intros ? ? ? ? ?; exact I | apply rng_all ];
    unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

End F31F.

(* The pins: each *_of_F states Seg/F31.v's v1.9 text, term for term (constr_eq: syntactic, not up to conversion).
   Both call corollaries are stated under Seg/F31.v's own Section Hypothesis HBC, so the discharged premise is the
   same one. *)
Lemma f31c_evt_of_F_verbatim : True.
Proof.
  let a := type of F31.f31c_evt in let b := type of f31c_evt_of_F in constr_eq a b.
  exact I.
Qed.

Lemma f31c_norm_of_F_verbatim : True.
Proof.
  let a := type of F31.f31c_norm in let b := type of f31c_norm_of_F in constr_eq a b.
  exact I.
Qed.

(* ===================== route (C): the `_on` twins (a Theorem Labs lane 09:20Z; wave a Theorem Labs lane, frozen form 09:38Z) =====================
   Writer a Theorem Labs lane (a Theorem Labs lane's hand-off 12:54Z, ASSIGN.md (a working note, not in this delivery)). ADDITIVE: every proof line above is unchanged, and every old
   lemma keeps its statement and its own proof. rule 24: no function proved. f31c_evt_F_on / f31c_norm_F_on are
   f31c_evt_F / f31c_norm_F's own proofs re-run under a narrowed shadow premise, against a Theorem Labs lane's narrowed
   footprint contract (bcmp_wrap_c_on.v's bcmp_wrap_contract_F_on, read at one footprint as bcmp_wrap_F_at_on, the
   twin of bcmp_wrap_F_at; bcmp_wrap_F_at_on_owner proves by conversion that it is the owner's text).
   Not a transport-only file: f31c_evt_F / f31c_norm_F take the wrapper's footprint contract (bcmp_wrap_F_at RNG),
   and the one transport (RoAdapt.rel_sw_norm, f31c_norm_F) moves the shadow fact to the normalized memory.
   PRE shadow_rw m -> A.ShadowRwOn.shadow_rw_on (f31c_evt_F_shadow_R O R) m. F31's own accesses (the spill cells
   A + 128, A + 168, A + 208 and the source bytes O + 4, O + 5, O + 6) are app memory and none is a store, so the run
   reads and stores no shadow byte of its own; the wrapper's range checks at the call 0x827d4 (a0 = O + 4, a1 = R,
   a2 = 6) read the aligned shadow words of its two strings, the callee's own region bcmp_wrap_shadow_R (O + 4) R 6,
   and the wrapper stores no shadow byte (bcmp_wrap_post_on keeps every region).
   POST (f31c_evt_F_on) shadow_rw m' -> forall P, shadow_rw_on P m -> shadow_rw_on P m'. f31c_norm_F_on moves the
   region across mem_rel by ShadowRwOnT.shadow_rw_on_rel, in place of RoAdapt.rel_sw_norm; its post has no shadow
   fact. f31n_evt_F has no shadow premise (one branch, no memory access): no twin. f31c_evt_of_F / f31c_norm_of_F get
   no twin: their only users are the constr_eq pins above (a Theorem Labs lane 11:53Z: a pin is not a user). *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
Module BWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SROT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.

(* The body of bcmp_wrap_c_on.v's bcmp_wrap_contract_F_on for one RNG: F31BW's text with the leaf's narrowed shadow
   premise and its post, read in the leaf's name environment. *)
Module F31BWO.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
  LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State
  LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Arr
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on.
Open Scope Z_scope.

Definition bcmp_wrap_F_at_on (RNG : footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R L R N) m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  rng_bytes RNG ->
  rng RNG 0x10000 0x5ee000 ->
  rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG L N -> (N = 0 \/ rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + N - 1) / 8) + 8 - 8 * (shadow_addr L / 8))) ->
  rng RNG R N -> (N = 0 \/ rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + N - 1) / 8) + 8 - 8 * (shadow_addr R / 8))) ->
  evtF rsegs RNG (bcmp_wrap_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

(* It is the owner's text: bcmp_wrap_c_on.v's bcmp_wrap_contract_F_on is bcmp_wrap_F_at_on at every footprint, by
   conversion. *)
Lemma bcmp_wrap_F_at_on_owner : bcmp_wrap_contract_F_on <-> forall RNG, bcmp_wrap_F_at_on RNG.
Proof. split; intros H RNG; exact (H RNG). Qed.
End F31BWO.

Notation bcmp_wrap_F_at_on := F31BWO.bcmp_wrap_F_at_on.

(* The shadow bytes the run needs present through its premise: the wrapper's region at 0x827d4 (O + 4, R, N = 6). *)
Definition f31c_evt_F_shadow_R (O R : Z) : Z -> Prop := BWO.bcmp_wrap_shadow_R (O + 4) R 6.

(* f31c_norm_F's run is f31c_evt_F's on the normalized memory; mem_rel moves the region's bytes unchanged. *)
Definition f31c_norm_F_shadow_R (O R : Z) : Z -> Prop := f31c_evt_F_shadow_R O R.

(* f31c_evt_F under the narrowed premise, against the narrowed footprint contract. *)
Lemma f31c_evt_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    SF.memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (f31c_evt_F_shadow_R O R) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) ->
    bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* F31's own three spill reloads *)
    rng RNG (A + 128) 8 -> rng RNG (A + 168) 8 -> rng RNG (A + 208) 8 ->
    (* the wrapper's footprint at 0x827c8, as in f31c_evt_F *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (O + 4) 6 ->
    rng RNG (8 * (shadow_addr (O + 4) / 8)) (8 * (shadow_addr (O + 9) / 8) + 8 - 8 * (shadow_addr (O + 4) / 8)) ->
    rng RNG R 6 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 5) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at_on RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ (forall P, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo -> -> [HO0 HO1] HR0 H128 H200 H168 HBL HBR HLrs Hmm HMI HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    R128 R168 R200 Hrb RIMG RSTK RL RLs RR RRs HF.
  assert (HL128 : ov_read_bytes rsegs m (wa (A + 128)) 8 = Some (le8 (Z_to_bv 64 (O + 4)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 128) _ 0 8 H128 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL200 : ov_read_bytes rsegs m (wa (A + 208)) 8 = Some (le8 (Z_to_bv 64 O))).
  { pose proof (bytes_at_ov_read rsegs m (A + 208) _ 0 8 H200 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL168 : ov_read_bytes rsegs m (wa (A + 168)) 8 = Some (le8 (Z_to_bv 64 R))).
  { pose proof (bytes_at_ov_read rsegs m (A + 168) _ 0 8 H168 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HB4 : ov_read_bytes rsegs m (wa (O + 4)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 0 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 0) with (O + 4) in HH by lia. exact HH. }
  assert (HB5 : ov_read_bytes rsegs m (wa (O + 5)) 1 = Some [Z_to_bv 8 64]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 1 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 1) with (O + 5) in HH by lia. exact HH. }
  assert (HB6 : ov_read_bytes rsegs m (wa (O + 6)) 1 = Some [Z_to_bv 8 171]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 2 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 2) with (O + 6) in HH by lia. exact HH. }
  (* 0x82798 bnez a0 (a0 = 0): not taken *)
  step. try if_false.
  (* 0x8279c ld a0,128(s1) [A+128]; lbu a0,0(a0) = 0x00 [O+4]; bnez a0 (to 0x82bf4): not taken *)
  step. step. step. try if_false.
  (* 0x827a8 ld a0,208(s1) [A+208]; lbu a0,5(a0) = 0x40 [O+5]; li a1,64; bne a0,a1 (to 0x82bf4): not taken *)
  step. step. step. step. try if_false.
  (* 0x827b8 ld a0,208(s1) [A+208]; lbu a0,6(a0) = 0xab [O+6]; li a1,171; bne a0,a1 (to 0x82bf4): not taken *)
  step. step. step. step. try if_false.
  (* 0x827c8 li a2,6; ld a0,128(s1) [A+128]; ld a1,168(s1) [A+168]; jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HF as HB. unfold F31BWO.bcmp_wrap_F_at_on, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 (O + 4)) = O + 4) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evtF_cut.
  { eapply HB with (ls := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; exact HaR6.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - exact Hrb.
    - exact RIMG.
    - exact RSTK.
    - exact RL.
    - right; f31_shadow_rng RLs.
    - exact RR.
    - right; f31_shadow_rng RRs. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* f31c_norm_F under the narrowed premise: f31c_evt_F_on on the normalized memory, the region moved across mem_rel
   by ShadowRwOnT.shadow_rw_on_rel (the twin of RoAdapt.rel_sw_norm). *)
Lemma f31c_norm_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    SF.memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (f31c_norm_F_shadow_R O R) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) ->
    bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the same footprint as f31c_evt_F: normalize changes no address *)
    rng RNG (A + 128) 8 -> rng RNG (A + 168) 8 -> rng RNG (A + 208) 8 ->
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (O + 4) 6 ->
    rng RNG (8 * (shadow_addr (O + 4) / 8)) (8 * (shadow_addr (O + 9) / 8) + 8 - 8 * (shadow_addr (O + 4) / 8)) ->
    rng RNG R 6 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 5) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at_on RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0 H128 H200 H168 HBL HBR HLrs Hmm HRO HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    R128 R168 R200 Hrb RIMG RSTK RL RLs RR RRs HF.
  pose proof (mem_rel_normalize rsegs m HRO) as REL0.
  assert (BR : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m (normalize rsegs m) a bs REL0) Hb)).
  assert (HST0 : stk rsegs (normalize rsegs m) lo (bv_unsigned sp)).
  { apply (RoAdapt.rel_stk_norm m _ _ _ REL0); [|exact HST].
    intros x Hx. apply RoAdapt.ro_addr_false_hi. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO).
    exact (f31c_evt_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 Fr fc (normalize rsegs m) A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0
             (BR _ _ H128) (BR _ _ H200) (BR _ _ H168) (BR _ _ HBL) (BR _ _ HBR) HLrs Hmm
             (mem_inv_normalize rsegs m)
             (RoAdapt.rel_addr_norm m _ _ _ REL0 HADL) (RoAdapt.rel_addr_norm m _ _ _ REL0 HADR)
             HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST0 Hlo1 Hlo2 Hspa
             (RoAdapt.rel_ac_norm m _ REL0 HAC) (SROT.shadow_rw_on_rel _ m _ REL0 HSW)
             (BR _ _ HRB) (BR _ _ HRM) (BR _ _ HGC) (BR _ _ HC254) (BR _ _ HC255)
             R128 R168 R200 Hrb RIMG RSTK RL RLs RR RRs HF). }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & _ & ST & _ & _).
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' REL0 RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' REL0 RM SAME WM)|].
  exact (RoAdapt.rel_stk_back m' m0' _ _ RM ST).
Qed.
