(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgTree BgBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace LibInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import FuzzKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition fuzz_one_walk_stmt (STACK : Z) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (OW LB : list block) (EA : BnRep.err_addrs)
    (lo B : Z) (errv : word) (D : Z) (d : list Z),
  bn_pre s st_init m OW LB pl_empty EA sp lo B errv STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d -> a0 = wz D -> a1 = wz (zlength d) ->
  implM bgusegs (interp (embed (fuzz_one_g (tree_ops bptr) d st_init))) s
    (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s st_init OW LB lo B m pl_empty EA
             (fun (rc : Z) (_ : bstate bptr) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz LX_FUZZ) fc None m (seg_rom bgusegs)).

Lemma drv_cells_client : forall LB SP a, lxs_addr a \/ stderr_addr a -> lx_client LB SP LIBW_bgr a.
Proof.
  intros LB SP a Ha. assert (Hni : ~ rin_ivs LIBW_bgr a).
  { intros H. destruct (LIBW_bgr_img a H) as (_ & _ & ND). apply ND. unfold drv_addr. destruct Ha as [Ha|Ha]; [right; right; left; exact Ha| right; left; exact Ha]. }
  destruct Ha as [Ha|Ha]; [exact (lxs_addr_client _ _ _ a Ha Hni) | exact (stderr_addr_client _ _ _ a Ha Hni)].
Qed.

Theorem rfuzz_of_walk : forall STACK, STACK <= 65536 -> fuzz_one_walk_stmt STACK ->
  rfuzz_one_stmt (LM := LM_bg unit tt bg_lib_one) (LSP := LSP_bgr unit tt bg_lib_one).
Proof.
  intros STACK HSTK WALK.
  unfold rfuzz_one_stmt. intros until canary.
  intros HEAP LI LXS SE SSP AUX SPB B63 ST CEIL GLO LO ERR Etp MI SP16 PL FRM Ea0 Ea1.
  destruct (lib_state_init m OW LI) as (EA & LS0 & NDEA).
  change (lib_one_prog ls d) with (interp (embed (tbind (tbind (fuzz_one_g (tree_ops bptr) d st_init) (fun p => TRet (fst p))) (fun rc => TRet (tt, rc))))).
  assert (LO' : lo <= bv_unsigned sp - 65536) by (unfold LX_FUZZ_STACK in LO; cbn [LIB_STACK LSP_bgr] in LO; exact LO).
  assert (PRE : bn_pre s st_init m OW LB pl_empty EA sp lo B errv STACK).
  { unfold bn_pre. split; [exact HEAP|]. split; [exact LS0|].
    split. { split; [|split; [clear - CEIL LO'; lia| exact B63]]. intros iv Hiv. rewrite hpl_only_empty in Hiv. destruct Hiv. }
    split; [exact AUX|]. split; [exact SPB|]. split; [exact B63|]. split; [exact ST|].
    split; [exact CEIL|]. split; [exact GLO|]. split.
    { clear - LO' HSTK. lia. }
    split; [|exact MI]. subst tp. exact ERR. }
  eapply (implM_embed_bind _ _ s
            (fun (rc : Z) s' ms' => exists bs' : bstate bptr,
               bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s st_init OW LB lo B m pl_empty EA
                 (fun (rc : Z) (_ : bstate bptr) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0) (rc, bs') s' ms')).
  - eapply implM_embed_bind.
    + exact (WALK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s OW LB EA lo B errv D d
               PRE Etp SP16 PL Ea0 Ea1).
    + intros [rc bs'] s' ms' POST. cbn [embed interp fst]. apply implM_interp_ret. apply evt_done. exists bs'. exact POST.
  - intros rc s' ms' (bs' & POST). cbn [embed interp]. apply implM_interp_ret. apply evt_done.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & OW' & PL' & errv'
                      & Ems & HEAP' & LS' & AUX' & ST' & ERR' & MI' & PRES & Hfa & Hso & _ & Hrc & Ha0).
    cbn [fst snd] in *.
    assert (PRES' : lx_pres LB (bv_unsigned sp) LIBW_bgr m m').
    { unfold XW in PRES. rewrite hpl_only_empty, app_nil_r in PRES. exact PRES. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
    unfold rfuzz_one_post. cbn [fst snd]. split; [|exact Hrc].
    unfold rlib_post. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc, m', OW'.
    split; [subst tp; exact Ems|].
    assert (Ecan : canary = rr_guard) by exact (ssp_canary_0 _ _ _ _ HEAP SSP).
    split.
    {
      split.
      { exists errv'. unfold lx_env. split; [exact HEAP'|].
        split; [eapply lx_statics_agree; [exact AG | intros a Ha; apply drv_cells_client; left; exact Ha | exact LXS]|].
        split; [eapply stderr_wfile_agree; [exact AG | intros a Ha; apply drv_cells_client; right; exact Ha | exact SE]|].
        split; [rewrite Ecan; exact (RHEAP_ssp _ _ _ HEAP')|].
        split; [exact AUX'|]. split; [exact SPB|]. split; [exact B63|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact GLO|].
        split; [subst tp; exact ERR'|]. split; [exact Etp| exact MI']. }
      split; [exact FRM|]. split; [exact PRES'|]. split; [exact Hso| exact Hfa]. }
    split; [exact (lib_state_fini_any bs' m' OW' PL' EA LS' NDEA)|].
    split; [exact (proj1 (proj1 (proj2 (proj2 LS'))))|].
    split; [exact Ha0|].

    eapply payload_ok_agree; [exact AG| exact PL|].
    intros b a Hb Ha. apply (block_client LB (bv_unsigned sp) LIBW_bgr b a Hb Ha).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (R1 & R2 & R3 & BC & BI).
    intros H. destruct (LIBW_bgr_img a H) as (HR & _). unfold GLOBALS_TOP in *. lia.
Qed.
End WithCeiling0.
