(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit Driver_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnHeap BnRep BnIface.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import HxpInit HxpInst.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel. (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition fuzz_one_walk_stmt (STACK : Z) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo B : Z) (errv : word) (D : Z) (d : list Z),
  bn_pre s ls m OW LB AD EA sp lo B errv STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d -> a0 = wz D -> a1 = wz (zlength d) ->
  implM psegs (interp (embed (fuzz_one (tree_ops bptr) d ls))) s
    (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
             (fun rc _ _ a0' => rc = 0 /\ a0' = wz 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz LX_FUZZ) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Lemma fuzz_one_walk_stmt_mono : forall S1 S2, S1 <= S2 -> fuzz_one_walk_stmt S1 -> fuzz_one_walk_stmt S2.
Proof.
  intros S1 S2 LE H. unfold fuzz_one_walk_stmt. intros until d. intros PRE E1 E2 E3 E4 E5.
  refine (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s ls OW LB AD EA lo B errv D d
            _ E1 E2 E3 E4 E5).
  destruct PRE as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10). unfold bn_pre.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|].
  split; [clear - P8 LE; lia|]. split; [exact P9| exact P10].
Qed.

Lemma LIBW_same : LIBW_HX = LIBW_bn.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma drv_cells_client : forall LB SP a, lxs_addr a \/ stderr_addr a -> lx_client LB SP LIBW_bn a.
Proof.
  intros LB SP a Ha. assert (Hni : ~ rin_ivs LIBW_bn a).
  { cbn [rin_ivs LIBW_bn fst snd]. unfold lxs_addr, stderr_addr, LX_GOT_STDERR, LX_STDERR_PTR in Ha. lia. }
  destruct Ha as [Ha|Ha]; [exact (lxs_addr_client _ _ _ a Ha Hni) | exact (stderr_addr_client _ _ _ a Ha Hni)].
Qed.

Theorem rfuzz_of_walk : forall STACK, STACK <= 65536 -> fuzz_one_walk_stmt STACK ->
  rfuzz_one_stmt (LM := LM_bndiv) (LSP := LSP_bndiv).
Proof.
  intros STACK HSTK WALK.
  unfold rfuzz_one_stmt. intros until canary.
  intros HEAP LI LXS SE SSP AUX SPB B63 ST CEIL GLO LO ERR Etp MI SP16 PL FRM Ea0 Ea1.
  destruct LI as (AD & EA & LS0).
  change (lib_one_prog ls d) with (interp (embed (bn_one ls d))). unfold bn_one.
  assert (PRE : bn_pre s ls m OW LB AD EA sp lo B errv STACK).
  { unfold bn_pre. split; [exact HEAP|]. split; [exact LS0|]. split; [exact AUX|]. split; [exact SPB|]. split; [exact ST|].
    split; [exact CEIL|]. split; [exact GLO|]. split.
    { unfold LX_FUZZ_STACK in LO. cbn [LIB_STACK LSP_bndiv] in LO. lia. }
    split; [|exact MI]. subst tp. exact ERR. }
  eapply implM_embed_bind.
  - exact (WALK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s ls OW LB AD EA lo B errv D d
             PRE Etp SP16 PL Ea0 Ea1).
  - intros [rc ls'] s' ms' POST. cbn [embed interp]. apply implM_interp_ret. apply evt_done.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & OW' & errv'
                      & Ems & HEAP' & LS' & AUX' & ST' & ERR' & MI' & PRES & Hfa & Hso & _ & Hrc & Ha0).
    cbn [fst snd] in *.
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES) as AG.
    unfold rfuzz_one_post. cbn [fst snd]. split; [|exact Hrc].
    unfold rlib_post. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc, m', OW'.
    split; [subst tp; exact Ems|].
    assert (Ecan : canary = rr_guard) by exact (ssp_canary_0 _ _ _ _ HEAP SSP).
    split.
    { (* [comment removed for export] *)
      split.
      { exists errv'. unfold lx_env. split; [exact HEAP'|].
        split; [eapply lx_statics_agree; [exact AG | intros a Ha; apply drv_cells_client; left; exact Ha | exact LXS]|].
        split; [eapply stderr_wfile_agree; [exact AG | intros a Ha; apply drv_cells_client; right; exact Ha | exact SE]|].
        split; [rewrite Ecan; exact (RHEAP_ssp _ _ _ HEAP')|].
        split; [exact AUX'|]. split; [exact SPB|]. split; [exact B63|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact GLO|].
        split; [subst tp; exact ERR'|]. split; [exact Etp| exact MI']. }
      split; [exact FRM|]. split; [exact PRES|]. split; [exact Hso| exact Hfa]. }
    split; [exists AD, EA; exact LS'|].
    split; [exact (proj1 (proj2 (proj2 LS')))|].
    split; [exact Ha0|].
    (* [comment removed for export] *)
    eapply payload_ok_agree; [exact AG| exact PL|].
    intros b a Hb Ha. apply (block_client LB (bv_unsigned sp) LIBW_bn b a Hb Ha).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (R1 & R2 & R3 & BC & BI).
    cbn [rin_ivs LIBW_bn fst snd]. unfold GLOBALS_TOP in *. lia.
Qed.
End WithCeiling0.
