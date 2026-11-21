(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import MState Frame Cells Mem Step Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PlainU7 Require Import PImg RMallocRep RMallocTree RMalloc_iface RF_free_spec RF_malloc_spec.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrBridge MrNodes MrRegsEqvW MrEqv MrFeasLift MrRulesU7 MrGen.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section U7.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.

Section MallocRulesGen.
Variables (R : bvmap 5 word) (M : word -> option byte) (mo : Model) (s : PState) (LB : list block) (X : list bptr)
          (G : PState -> Model -> Prop) (n lo B : Z) (errv : word).
Hypothesis HH : RHEAP s LB M.
Hypothesis HOWN : OWN X G s mo.
Hypothesis HG : frame_ok G.
Hypothesis HAUX : rauxv_ok M B.
Hypothesis HspB : bv_unsigned (reg_get R (Z_to_bv 5 2)) <= B.
Hypothesis HSTK : stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (bv_unsigned (reg_get R (Z_to_bv 5 2))).
Hypothesis Hlo1 : ATOP <= lo.
Hypothesis Hlo2 : lo <= bv_unsigned (reg_get R (Z_to_bv 5 2)) - RMALLOC_STACK.
Hypothesis HERR : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv].
Hypothesis HMI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M.
Hypothesis Htp : reg_get R (Z_to_bv 5 4) = Z_to_bv 64 RATP.
Hypothesis Ha0 : reg_get R (Z_to_bv 5 10) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n < 2^32.

Variable Phi : option bptr -> PState -> Model -> Prop.
Variable Inv0 : Model -> Prop.
Hypothesis HGen : tgenM (raw_malloc n) s Inv0 Phi.
Hypothesis HInv0 : Inv0 mo.

Let g := fun k : Z => reg_get R (Z_to_bv 5 k).
Let Qm := epost (fun a : option bptr * PState =>
            rmalloc_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                         (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB n lo B M (fst a) (snd a)).
Let Pm4 := fun (r : exc (option bptr * PState)) (mo1 : Model) =>
            match r with Unr => False | Ok a => own_ret X G (fst a) (snd a) mo1 end
            /\ match r with Unr => True | Ok (a, s') => Phi a s' mo1 end.

Lemma malloc_twf4 : B.twf node nstep nsafe (raw_malloc n s) mo Pm4.
Proof.
  unfold Pm4. unfold tgenM in HGen.
  exact (tgen_twf (raw_malloc n s) mo Inv0 _ _ (malloc_twf mo s X G n HOWN HG Hn) HGen HInv0).
Qed.

Theorem malloc_rz_2xg : forall (A Bs : TSet),
  B.tfeas node nstep (raw_malloc n s) mo (fun r => is_null r = true) ->
  B.tfeas node nstep (raw_malloc n s) mo (fun r => is_null r = false) ->
  A [] -> Bs [] ->
  (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' -> Phi r s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
              (match r with None => A | Some _ => Bs end)) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) (ShapeAlg.t_alt2 A Bs).
Proof.
  intros A Bs HfA HfB HA0 HB0 HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  eapply (B.impl_realizes_alt2 (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) (raw_malloc n s) Qm Pm4 is_null A Bs).
  - exact (malloc_impl R M s LB n lo B errv HH HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn).
  - exact malloc_twf4.
  - apply mmtree_tsilent. apply mmtree_raw_malloc.
  - exact HfA.
  - exact HfB.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - exact HA0.
  - exact HB0.
  - intros r ms' mo' HQ HP _ _. destruct r as [|[r0 s']]; [destruct HP as [[] _]|].
    destruct HP as [HP HF]. unfold Qm in HQ. cbn [epost fst snd] in HQ, HP.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & Hr).
    assert (MR : malloc_ret R (mkR (g 1) (g 2) (g 3) (g 4) t0 t1 t2 (g 8) (g 9) a0 a1 a2 a3 a4 a5 a6 a7 (g 18) (g 19) (g 20) (g 21) (g 22)
                                   (g 23) (g 24) (g 25) (g 26) (g 27) t3 t4 t5 t6) M m' s s' LB n lo B r0).
    { unfold malloc_ret. split.
      { intros k Hk. unfold kept_regs in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction. }
      do 2 (split; [assumption|]). split; [exists errv'; exact HERR'|]. do 4 (split; [assumption|]).
      destruct r0 as [p|].
      - destruct Hr as (A0 & junk & -> & Hr). exists A0, junk. split; [reflexivity | exact Hr].
      - destruct Hr as [-> Hr]. split; [reflexivity | exact Hr]. }
    pose proof (HK _ _ mo' s' r0 MR HP HF) as H.
    destruct r0; exact H.
Qed.

End MallocRulesGen.
End U7.
