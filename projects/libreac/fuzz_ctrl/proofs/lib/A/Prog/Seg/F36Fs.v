(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v; 174 of its 302 lines of code are new or changed and 2961 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d.
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F36.v blob 242c29c887f9; callee contract
   lib/A/Prog/reac_box_catalogue_match_c.v (an earlier version, blob 966accdeea1, not in this delivery) (the glue base's and a working branch's; a Theorem Labs lane's
   771ccbb8994 only appends to it, so the plain contract this file cites is the same text there).
   Tools: lib/Lib/StepF.v, lib/Lib/ExecF.v, The Rocq Prover 9.2.  rule 24: no function proved.

   SPLIT STRETCHES of segment F36's call of reac_box_catalogue_match (segF-v19-spec.md (a working note, not in this delivery); Theorem Labs split
   rule two Theorem Labs lanes 04:01Z: a call of a cgif-form fake-stack callee is split, in a NEW file Seg/<S>Fs.v).
   The walk (lib/A/ACtl.v) does not take the callee by its contract: at the call it applies a Theorem Labs lane's cgif-form
   treac_box_catalogue_match_spec (a Theorem Labs lane 03:44Z).  So the two source runs that cross the call are cut there:
     call pc 0x828d4 (jal reac_box_catalogue_match, REAC_BOX_CATALOGUE_MATCH = 0x84498), return pc 0x828d8.
   - f36_evt_call_pre_F: 0x828cc mv a0,s7 ; 0x828d0 mv a1,s2 ; 0x828d4 jal -> the CALLEE ENTRY state (pc =
     REAC_BOX_CATALOGUE_MATCH, ra = 0x828d8), the source's `step. step. step.` prefix.  The three instructions read
     only s7 / s2 and touch no memory, so no rng premise and no source premise is needed (the shape of Seg/F9F.v's
     f9_evtB_pre_F, the same three instructions); the callee contract does not appear.  It is the pre stretch of BOTH
     runs: f36_call_norm normalizes the memory only for the callee's mem_inv premise, and the three instructions keep
     the memory, so the normalization moves past them unchanged.
   - f36_evt_call_post_F / f36_call_norm_post_F: the post stretch is EMPTY: the return pc 0x828d8 is the runs' exit
     (the cut C_A828d8_at).  Zero instructions from a CONCRETE universally quantified start at the return pc with the
     canonical register map Regs6ss.mkR_of regs; premises = exactly the machine-level facts the source script holds
     after the callee contract (the seventeen register values the source post names, then munch / wmono / mem_inv or
     ro_agree / stk / asan_cells / shadow_rw / addressable / fp of the callee post; the callee post's
     reac_box_catalogue_match_tls is not used by the source post, so it is not a premise).  The start keeps the
     source's float registers F and fcsr fc (not fp_regs / fp_csr), because the source post names them (as
     Seg/R10AF.v's r10a_call34_post_F).  The callee post's existential registers are the start map's (AYK.getr).
   - f36_evt_call_of_pre_post / f36_call_norm_of_pre_post: the two stretches at ExecF.RNG_all plus the PLAIN contract
     (the source's own first premise) re-derive F36.f36_evt_call / F36.f36_call_norm by the source's own script (the
     contract application, and for f36_call_norm the normalization lift and the mem_rel transports, cut from F36.v
     unchanged); each is pinned by constr_eq against the source's type (the no-weakening check).
   No footprint contract of the callee is named here.  No Axiom, Parameter, Section hypothesis or admit.
   NAMES: both copies of YK11 are in this file's closure (the plain lib/Prog files load lib/Reusable/YK11), so its
   two YK11 names are written through the alias AYK of the unit copy lib.A.Reusable.YK11 (AYK.getr, AYK.seg_rom),
   the form the porter's rule admits (a Theorem Labs lane 04:24Z / 04:33Z); the Require of YK11 is the lib.A.Reusable form. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c reac_box_catalogue_match_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
(* The source (its runs, helpers and wrapper cells, cited by name) and the segment's _F file; Require, not Import:
   F36.v's helper copies must not shadow this file's names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F36 F36F.
(* Last (as in Seg/F36F.v): StepF's step and ExecF's evtF_done match evtF goals. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* As in Seg/F36.v: the slot's runs are stated with the image-A YK11, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top. *)
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* Seg/F36.v's own constants, by name: the pinned statements name them, so a same-valued copy here would be a
   different constant (Notation, not Definition, as in Seg/F36F.v). *)
Local Notation BCMP := F36.BCMP.
Local Notation REAL_BCMP := F36.REAL_BCMP.
Local Notation REAL_MEMCMP := F36.REAL_MEMCMP.
Local Notation MEMCMP := F36.MEMCMP.
Local Notation f36_W := F36.f36_W.

(* ===================== the pre stretch: 0x828cc -> REAC_BOX_CATALOGUE_MATCH, ra = 0x828d8 ===================== *)

Lemma f36_evt_call_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0 t1 t2 s0 s1 s7 s2 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (AYK.seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (AYK.seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. (* 0x828cc mv a0,s7 *)
  step. (* 0x828d0 mv a1,s2 *)
  step. (* 0x828d4 jal 84498 <reac_box_catalogue_match> *)
  apply evtF_done. reflexivity.
Qed.

(* ===================== the post stretches: zero instructions at the return pc 0x828d8 ===================== *)

(* f36_evt_call's post (the callee post's mem_inv). *)
Lemma f36_evt_call_post_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    AYK.getr regs 1 = Z_to_bv 64 0x828d8 ->
    AYK.getr regs 2 = sp -> AYK.getr regs 3 = gp -> AYK.getr regs 4 = tp -> AYK.getr regs 8 = s0 -> AYK.getr regs 9 = s1 ->
    AYK.getr regs 10 = Z_to_bv 64 (want CM_T len fb) ->
    AYK.getr regs 18 = s2 -> AYK.getr regs 19 = s3 -> AYK.getr regs 20 = s4 -> AYK.getr regs 21 = s5 -> AYK.getr regs 22 = s6 ->
    AYK.getr regs 23 = s7 -> AYK.getr regs 24 = s8 -> AYK.getr regs 25 = s9 -> AYK.getr regs 26 = s10 -> AYK.getr regs 27 = s11 ->
    munch (f36_W S FS) m mem -> wmono rsegs m mem -> mem_inv rsegs mem -> stk rsegs mem (S - CM_K) S ->
    asan_cells mem -> shadow_rw mem -> addressable mem (S - CM_K) CM_K ->
    fp [0%nat; 1%nat; 2%nat] mem (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (AYK.seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x828d8) fc None mem (AYK.seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m phi len S FS fb
    K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 MU WM MI ST AC SW AD FP.
  subst sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  apply evtF_done.
  exists (AYK.getr regs 5), (AYK.getr regs 6), (AYK.getr regs 7), (AYK.getr regs 11), (AYK.getr regs 12), (AYK.getr regs 13),
    (AYK.getr regs 14), (AYK.getr regs 15), (AYK.getr regs 16), (AYK.getr regs 17), (AYK.getr regs 28), (AYK.getr regs 29),
    (AYK.getr regs 30), (AYK.getr regs 31), mem.
  split; [unfold Regs6ss.mkR_of; rewrite <- K1, <- K10; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC|]. split; [exact SW|]. split; [exact AD | exact FP].
Qed.

(* f36_call_norm's post (ro_agree of the caller's memory, moved back from the normalized one). *)
Lemma f36_call_norm_post_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    AYK.getr regs 1 = Z_to_bv 64 0x828d8 ->
    AYK.getr regs 2 = sp -> AYK.getr regs 3 = gp -> AYK.getr regs 4 = tp -> AYK.getr regs 8 = s0 -> AYK.getr regs 9 = s1 ->
    AYK.getr regs 10 = Z_to_bv 64 (want CM_T len fb) ->
    AYK.getr regs 18 = s2 -> AYK.getr regs 19 = s3 -> AYK.getr regs 20 = s4 -> AYK.getr regs 21 = s5 -> AYK.getr regs 22 = s6 ->
    AYK.getr regs 23 = s7 -> AYK.getr regs 24 = s8 -> AYK.getr regs 25 = s9 -> AYK.getr regs 26 = s10 -> AYK.getr regs 27 = s11 ->
    munch (f36_W S FS) m mem -> wmono rsegs m mem -> ro_agree rsegs mem -> stk rsegs mem (S - CM_K) S ->
    asan_cells mem -> shadow_rw mem -> addressable mem (S - CM_K) CM_K ->
    fp [0%nat; 1%nat; 2%nat] mem (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (AYK.seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x828d8) fc None mem (AYK.seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m phi len S FS fb
    K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 MU WM RO ST AC SW AD FP.
  subst sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  apply evtF_done.
  exists (AYK.getr regs 5), (AYK.getr regs 6), (AYK.getr regs 7), (AYK.getr regs 11), (AYK.getr regs 12), (AYK.getr regs 13),
    (AYK.getr regs 14), (AYK.getr regs 15), (AYK.getr regs 16), (AYK.getr regs 17), (AYK.getr regs 28), (AYK.getr regs 29),
    (AYK.getr regs 30), (AYK.getr regs 31), mem.
  split; [unfold Regs6ss.mkR_of; rewrite <- K1, <- K10; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
  split; [exact AC|]. split; [exact SW|]. split; [exact AD | exact FP].
Qed.

(* ===================== the re-derivations of the two source runs ===================== *)

(* F36.f36_evt_call: the pre stretch, the PLAIN contract at the callee entry (F36.v's own application), the post
   stretch at the return pc. *)
Lemma f36_evt_call_of_pre_post : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> AYK.seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = AYK.seg_rom rsegs (wa a)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (AYK.seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (AYK.seg_rom rsegs)).
Proof.
  intros CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HMI HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  (* the PRE stretch: 0x828cc mv a0,s7 ; 0x828d0 mv a1,s2 ; 0x828d4 jal reac_box_catalogue_match *)
  eapply LE.evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    exact (f36_evt_call_pre_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc m). }
  intros ms0 ->.
  subst s7 s2 sp.
  (* the callee by its PLAIN contract: F36.v's f36_evt_call script *)
  pose proof CMC as HC. unfold reac_box_catalogue_match_contract in HC.
  eapply LE.evt_cut.
  { eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST | exact HROM | exact Hfb | exact HFB | exact HROc | exact HMI | exact HAC | exact HSW
               | exact HADW | exact HADf | exact HADT | exact HADB | exact HRB | exact HRM | exact HGC
               | exact HC254 | exact HC255 | exact HFP | exact HTLS | exact Hmod
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x828d8)) with (Z_to_bv 64 0x828d8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the POST stretch: zero instructions at the return pc 0x828d8 *)
  apply (evtF_evt rsegs RNG_all).
  apply (f36_evt_call_post_F RNG_all
           (mkR (Z_to_bv 64 0x828d8) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 len) s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11
                t3' t4' t5' t6')
           m' (Z_to_bv 64 S) gp tp s0 s1 (Z_to_bv 64 len) s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11
           F fc m phi len S FS fb).
  all: try reflexivity.
  - exact MU.
  - exact WM.
  - exact MI'.
  - exact ST'.
  - exact AC'.
  - exact SW'.
  - exact AD'.
  - exact FP'.
Qed.

(* F36.f36_call_norm: the pre stretch on the caller's memory, then F36.v's f36_call_norm script around the callee
   (the normalization lift MemNorm.evt_normalize, the PLAIN contract on the normalized memory, the mem_rel
   transports back), then the post stretch at the return pc. *)
Lemma f36_call_norm_of_pre_post : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> AYK.seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = AYK.seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (AYK.seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (AYK.seg_rom rsegs)).
Proof.
  intros CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HRO HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  (* the PRE stretch, on the caller's memory (the three instructions keep it) *)
  eapply LE.evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    exact (f36_evt_call_pre_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc m). }
  intros ms0 ->.
  subst s7 s2 sp.
  (* F36.v's f36_call_norm script: the normalized memory and the transports *)
  pose proof (mem_rel_normalize rsegs m HRO) as R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs R)).
  assert (Hlo : 0x5fe000 <= S - CM_K) by (unfold HIGHMEM_BEG in Hhi; lia).
  pose proof CMC as HC. unfold reac_box_catalogue_match_contract in HC.
  eapply LE.evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (AYK.seg_rom rsegs) wx_apart_asan HRO).
    eapply (HC _ _ gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 _ s3 s4 s5 s6 _ s8 s9 s10 s11 t3 t4 t5 t6 F fc
              (normalize rsegs m) phi len S FS fb); [reflexivity | reflexivity | reflexivity
              | exact Hphi | exact Hlen | exact HS | exact Hmod | exact HKS | ..].
    - apply (proj1 (F36.f36_stk_rel m _ _ _ R Hlo)). exact HST.
    - exact HROM.
    - exact Hfb.
    - intros H50. destruct (HFB H50) as (P1 & P2 & P3 & P4).
      split; [exact P1|]. split; [exact P2|]. split; [apply BR; exact P3 | exact P4].
    - intros a Ha. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ R). exact (HROc a Ha).
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (F36.f36_cells_rel m _ R)). exact HAC.
    - apply (proj1 (F36.f36_srw_rel m _ R)). exact HSW.
    - exact Hhi.
    - exact Hsp.
    - apply (proj1 (F36.f36_addr_rel m _ _ _ R)). exact HADW.
    - intros H50. destruct (HADf H50) as (P1 & P2).
      split; [apply (proj1 (F36.f36_addr_rel m _ _ _ R)); exact P1 | exact P2].
    - apply (proj1 (F36.f36_addr_rel m _ _ _ R)). exact HADT.
    - apply (proj1 (F36.f36_addr_rel m _ _ _ R)). exact HADB.
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255.
    - apply (proj1 (F36.f36_fp_rel _ m _ _ _ _ _ _ _ R)). exact HFP.
    - apply (proj1 (F36.f36_cmtls_rel m _ _ _ _ _ R)). exact HTLS. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & MI & ST & AC' & SW' & AD' & FP' & TL').
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  replace (ret_pc (Z_to_bv 64 0x828d8)) with (Z_to_bv 64 0x828d8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the POST stretch: zero instructions at the return pc 0x828d8 *)
  apply (evtF_evt rsegs RNG_all).
  apply (f36_call_norm_post_F RNG_all
           (mkR (Z_to_bv 64 0x828d8) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 len) s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11
                t3' t4' t5' t6')
           m' (Z_to_bv 64 S) gp tp s0 s1 (Z_to_bv 64 len) s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11
           F fc m phi len S FS fb).
  all: try reflexivity.
  - exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' R RM SAME MU).
  - exact (wmono_rel rsegs m (normalize rsegs m) m' m0' R RM SAME WM).
  - exact (ro_agree_same rsegs m m' HRO SAME).
  - apply (proj2 (F36.f36_stk_rel m' m0' _ _ RM Hlo)). exact ST.
  - apply (proj2 (F36.f36_cells_rel m' m0' RM)). exact AC'.
  - apply (proj2 (F36.f36_srw_rel m' m0' RM)). exact SW'.
  - apply (proj2 (F36.f36_addr_rel m' m0' _ _ RM)). exact AD'.
  - apply (proj2 (F36.f36_fp_rel _ m' m0' _ _ _ _ _ _ RM)). exact FP'.
Qed.

(* The pins: each re-derivation states Seg/F36.v's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion), the callee's PLAIN contract in the source's own first premise position. *)
Lemma f36_evt_call_of_pre_post_verbatim : True.
Proof.
  let a := type of F36.f36_evt_call in let b := type of f36_evt_call_of_pre_post in constr_eq a b.
  exact I.
Qed.

Lemma f36_call_norm_of_pre_post_verbatim : True.
Proof.
  let a := type of F36.f36_call_norm in let b := type of f36_call_norm_of_pre_post in constr_eq a b.
  exact I.
Qed.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
