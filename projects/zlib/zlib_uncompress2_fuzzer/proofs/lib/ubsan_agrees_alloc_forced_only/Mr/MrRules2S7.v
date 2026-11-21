(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState Frame Cells Mem Step Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg RMallocRep RMallocTree RMalloc_iface RF_free_spec RF_malloc_spec.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge MrNodes MrRegsEqvW MrEqv MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift MrFeasLift2 MrRoom MrRulesS7
  MrTall MrShape MrAcc MrAccNodes MrAccPath.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.FOU Require Import MrNonNull.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section S7.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.

Section MallocRules2.
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

Variable Phi : option bptr -> PState -> Prop.
Hypothesis HPhi : tallM Phi (raw_malloc n) s.

Let g := fun k : Z => reg_get R (Z_to_bv 5 k).
Let Qm := epost (fun a : option bptr * PState =>
            rmalloc_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                         (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB n lo B M (fst a) (snd a)).
Let Pm2 := fun (r : exc (option bptr * PState)) (mo1 : Model) =>
            match r with Unr => False | Ok a => own_ret X G (fst a) (snd a) mo1 end
            /\ match r with Unr => True | Ok (a, s') => Phi a s' end.

Lemma malloc_twf2 : B.twf node nstep nsafe (raw_malloc n s) mo Pm2.
Proof.
  unfold Pm2. exact (twf_tall' (raw_malloc n s) mo _ _ (malloc_twf mo s X G n HOWN HG Hn) HPhi).
Qed.

Lemma malloc_leaf2 : forall r ms' mo' (K : option bptr -> TSet),
  (forall R' M' mo'' s' r', malloc_ret R R' M M' s s' LB n lo B r' -> own_ret X G r' s' mo'' -> Phi r' s' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo'') (K r')) ->
  Qm r ms' -> Pm2 r mo' ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg ms' mo') (match r with Unr => K None | Ok a => K (fst a) end).
Proof.
  intros [|[r s']] ms' mo' K HK HQ [HP HF]; [contradiction|]. unfold Qm in HQ. cbn [epost fst snd] in HQ, HP |- *.
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & Hr).
  eapply HK; [|exact HP|exact HF].
  unfold malloc_ret. split.
  { intros k Hk. unfold kept_regs in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction. }
  do 2 (split; [assumption|]). split; [exists errv'; exact HERR'|]. do 4 (split; [assumption|]).
  destruct r as [p|].
  - destruct Hr as (A & junk & -> & Hr). exists A, junk. split; [reflexivity | exact Hr].
  - destruct Hr as [-> Hr]. split; [reflexivity | exact Hr].
Qed.

Theorem malloc_rz_2x : forall (A Bs : TSet),
  tpaths (raw_malloc n s) mo (fun r => is_null r = false) ->
  A [] -> Bs [] ->
  (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' -> Phi r s' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
              (match r with None => A | Some _ => Bs end)) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.
Proof.
  intros A Bs HNN HA0 HB0 HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) (raw_malloc n s) Qm (fun r mo1 => Pm2 r mo1 /\ is_null r = false) Bs).
  - exact (malloc_impl R M s LB n lo B errv HH HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn).
  - exact (twf_tpaths _ _ _ _ malloc_twf2 HNN).
  - apply mmtree_tsilent. apply mmtree_raw_malloc.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - intros r ms' mo' HQ [HP Hnn] _ _. destruct r as [|a]; [destruct HP as [[] _]|].
    pose proof (malloc_leaf2 (Ok a) ms' mo' (fun r' => match r' with None => A | Some _ => Bs end) HK HQ HP) as H.
    destruct a as [[p|] s']; cbn in *; [exact H | discriminate Hnn].
Qed.

End MallocRules2.

Section Big.
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

Theorem malloc_rz_big : forall (Bd : Z) (A Bs : TSet),
  MMAP_THRESHOLD <= n ->
  metaok_ps s -> room Bd mo -> n + 20 <= Bd -> 2^24 <= Bd -> Bd + 4096 <= 2^30 ->
  A [] -> Bs [] ->
  (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' -> REL (ps_m s) (ps_m s') ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
              (match r with None => A | Some _ => Bs end)) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.
Proof.
  intros Bd A Bs Hbig Hmeta Hroom HnB HB1 HB2 HA0 HB0 HK.
  assert (HPhi : tallM (fun (_ : option bptr) (s' : PState) => REL (ps_m s) (ps_m s')) (raw_malloc n) s).
  { eapply tall_mono; [| apply (tall_raw_malloc n s (fun st' _ => REL (ps_m s) st')); apply cmalloc_big_shape; exact Hbig].
    intros [|[r s']]; [auto|]. cbn. auto. }
  eapply (malloc_rz_2x R M mo s LB X G n lo B errv HH HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn
            (fun _ s' => REL (ps_m s) (ps_m s')) HPhi A Bs); try assumption.
  eapply (raw_malloc_nonnull_gone X G Bd); eauto; try lia. apply room_grantable; [lia | lia | exact Hroom].
Qed.

End Big.

Theorem free_rz_anyx : forall (R : bvmap 5 word) (M : word -> option byte) (mo : Model)
    (s : PState) (LB : list block) (X : list bptr) (G : PState -> Model -> Prop)
    (p : bptr) (A n lo B : Z) (errv : word) (T : TSet) (Phi : PState -> Prop),
  RHEAP s LB M -> In (p, A, n) LB ->
  OWN (p :: X) G s mo -> frame_ok G ->
  rauxv_ok M B -> bv_unsigned (reg_get R (Z_to_bv 5 2)) <= B ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) -> ATOP <= lo ->
  lo <= bv_unsigned (reg_get R (Z_to_bv 5 2)) - RFREE_STACK ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  reg_get R (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  reg_get R (Z_to_bv 5 10) = Z_to_bv 64 A ->
  tallM (fun _ s' => Phi s') (raw_free p) s ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (mo' : Model) (s' : PState),
      (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) ->
      mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) ->
      rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] -> rauxv_ok M' B ->
      rheap_pres (lb_remove p LB) (bv_unsigned (reg_get R (Z_to_bv 5 2))) M M' ->
      ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (lb_remove p LB) M' -> OWN X G s' mo' -> Phi s' ->
      realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RFREE_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R M mo s LB X G p A n lo B errv T Phi HH Hin HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 HPhi HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RFREE_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  set (g := fun k : Z => reg_get R (Z_to_bv 5 k)).
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb))
            (raw_free p s)
            (epost (fun a => rfree_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                                        (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB p lo B errv M (fst a) (snd a)))
            (fun r mo1 => match r with Unr => False | Ok a => OWN X G (snd a) mo1 end
                          /\ match r with Unr => True | Ok (_, s') => Phi s' end)).
  - unfold mkR_of. fold g.
    exact (rfree_spec_proof (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) (g 16) (g 17)
             (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31)
             bvmap_empty (Z_to_bv 32 0) M s LB p A n lo B errv HH Hin HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0).
  - apply (twf_tall' (raw_free p s) mo _ _ (twf_bridge _ _ _ (raw_free_spec X G p HG s mo HOWN)) HPhi).
  - apply mmtree_tsilent. apply mmtree_raw_free.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - intros [|[[] s']] ms' mo' HQ [HP HF] Hh' Hinv'; [contradiction|]. cbn [epost fst snd] in HQ.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & HH').
    eapply HK; try eassumption.
    intros k Hk. unfold kept_regs in Hk. cbn in Hk.
    repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction.
Qed.

Lemma tall_free_cnt : forall p s, tallM (fun _ s' => cnt (ps_m s') = cnt (ps_m s)) (raw_free p) s.
Proof. intros p s. apply (tall_raw_free p s (fun st' => cnt st' = cnt (ps_m s))). apply cfree_keeps_cnt. Qed.

Section MallocRulesAcc.
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

Variable Phi : option bptr -> PState -> Prop.
Hypothesis HPhi : tallM Phi (raw_malloc n) s.
Variables (C U : Z) (Post : Z -> Z -> Prop).
Hypothesis HCost : taccM (raw_malloc n) s C U (fun _ c u => Post c u).
Hypothesis HAcc : acc C U mo.
Variable Inv : Model -> Prop.
Hypothesis HInvS : mm_inv Inv.
Hypothesis HInv : Inv mo.

Let g := fun k : Z => reg_get R (Z_to_bv 5 k).
Let Qm := epost (fun a : option bptr * PState =>
            rmalloc_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                         (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB n lo B M (fst a) (snd a)).
Let Pm3 := fun (r : exc (option bptr * PState)) (mo1 : Model) =>
            ((match r with Unr => False | Ok a => own_ret X G (fst a) (snd a) mo1 end
              /\ match r with Unr => True | Ok (a, s') => Phi a s' end)
             /\ (exists C' U', match r with Unr => True | Ok (_, _) => Post C' U' end /\ acc C' U' mo1) /\ Inv mo1).

Lemma malloc_twf3 : B.twf node nstep nsafe (raw_malloc n s) mo Pm3.
Proof.
  unfold Pm3.
  exact (tacc_twf_inv Inv HInvS (raw_malloc n s) mo C U _ _
           (twf_tall' (raw_malloc n s) mo _ _ (malloc_twf mo s X G n HOWN HG Hn) HPhi) HCost HAcc HInv).
Qed.

Theorem malloc_rz_2xa : forall (A Bs : TSet),
  tpaths (raw_malloc n s) mo (fun r => is_null r = false) ->
  A [] -> Bs [] ->
  (forall R' M' mo' s' r C' U', malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' -> Phi r s' ->
     Post C' U' -> acc C' U' mo' -> Inv mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
              (match r with None => A | Some _ => Bs end)) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.
Proof.
  intros A Bs HNN HA0 HB0 HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) (raw_malloc n s) Qm (fun r mo1 => Pm3 r mo1 /\ is_null r = false) Bs).
  - exact (malloc_impl R M s LB n lo B errv HH HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn).
  - exact (twf_tpaths _ _ _ _ malloc_twf3 HNN).
  - apply mmtree_tsilent. apply mmtree_raw_malloc.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - intros r ms' mo' HQ [HP Hnn] _ _. destruct r as [|[r0 s']]; [destruct HP as [[[] _] _]|].
    destruct HP as [[HP HF] [(C' & U' & HPost & HAcc') HInv']]. unfold Qm in HQ. cbn [epost fst snd] in HQ, HP.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & Hr).
    assert (MR : malloc_ret R (mkR (g 1) (g 2) (g 3) (g 4) t0 t1 t2 (g 8) (g 9) a0 a1 a2 a3 a4 a5 a6 a7 (g 18) (g 19) (g 20) (g 21) (g 22)
                                   (g 23) (g 24) (g 25) (g 26) (g 27) t3 t4 t5 t6) M m' s s' LB n lo B r0).
    { unfold malloc_ret. split.
      { intros k Hk. unfold kept_regs in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction. }
      do 2 (split; [assumption|]). split; [exists errv'; exact HERR'|]. do 4 (split; [assumption|]).
      destruct r0 as [p|].
      - destruct Hr as (A0 & junk & -> & Hr). exists A0, junk. split; [reflexivity | exact Hr].
      - destruct Hr as [-> Hr]. split; [reflexivity | exact Hr]. }
    pose proof (HK _ _ mo' s' r0 C' U' MR HP HF HPost HAcc' HInv') as H.
    destruct r0; [exact H | discriminate Hnn].
Qed.

End MallocRulesAcc.

Theorem free_rz_anyxa : forall (R : bvmap 5 word) (M : word -> option byte) (mo : Model)
    (s : PState) (LB : list block) (X : list bptr) (G : PState -> Model -> Prop)
    (p : bptr) (A n lo B : Z) (errv : word) (T : TSet) (Phi : PState -> Prop) (C U : Z) (Post : Z -> Z -> Prop) (Inv : Model -> Prop),
  mm_inv Inv -> Inv mo ->
  RHEAP s LB M -> In (p, A, n) LB ->
  OWN (p :: X) G s mo -> frame_ok G ->
  rauxv_ok M B -> bv_unsigned (reg_get R (Z_to_bv 5 2)) <= B ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) -> ATOP <= lo ->
  lo <= bv_unsigned (reg_get R (Z_to_bv 5 2)) - RFREE_STACK ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  reg_get R (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  reg_get R (Z_to_bv 5 10) = Z_to_bv 64 A ->
  tallM (fun _ s' => Phi s') (raw_free p) s ->
  taccM (raw_free p) s C U (fun _ c u => Post c u) -> acc C U mo ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (mo' : Model) (s' : PState) (C' U' : Z),
      (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) ->
      mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) ->
      rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] -> rauxv_ok M' B ->
      rheap_pres (lb_remove p LB) (bv_unsigned (reg_get R (Z_to_bv 5 2))) M M' ->
      ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (lb_remove p LB) M' -> OWN X G s' mo' -> Phi s' -> Post C' U' -> acc C' U' mo' -> Inv mo' ->
      realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RFREE_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R M mo s LB X G p A n lo B errv T Phi C U Post Inv HInvS HInv HH Hin HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 HPhi HCost HAcc HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RFREE_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  set (g := fun k : Z => reg_get R (Z_to_bv 5 k)).
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb))
            (raw_free p s)
            (epost (fun a => rfree_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                                        (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB p lo B errv M (fst a) (snd a)))
            (fun r mo1 => ((match r with Unr => False | Ok a => OWN X G (snd a) mo1 end
                            /\ match r with Unr => True | Ok (_, s') => Phi s' end)
                           /\ (exists C' U', match r with Unr => True | Ok (_, _) => Post C' U' end /\ acc C' U' mo1) /\ Inv mo1))).
  - unfold mkR_of. fold g.
    exact (rfree_spec_proof (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) (g 16) (g 17)
             (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31)
             bvmap_empty (Z_to_bv 32 0) M s LB p A n lo B errv HH Hin HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0).
  - exact (tacc_twf_inv Inv HInvS (raw_free p s) mo C U _ _
             (twf_tall' (raw_free p s) mo _ _ (twf_bridge _ _ _ (raw_free_spec X G p HG s mo HOWN)) HPhi) HCost HAcc HInv).
  - apply mmtree_tsilent. apply mmtree_raw_free.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - intros [|[[] s']] ms' mo' HQ [[HP HF] [(C' & U' & HPost & HAcc') HInv']] Hh' Hinv'; [contradiction|]. cbn [epost fst snd] in HQ.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & HH').
    eapply (HK _ _ _ _ C' U'); try eassumption.
    intros k Hk. unfold kept_regs in Hk. cbn in Hk.
    repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction.
Qed.

End S7.
