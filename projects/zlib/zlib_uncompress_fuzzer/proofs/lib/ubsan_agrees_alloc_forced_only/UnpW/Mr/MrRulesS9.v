(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState Frame Cells Mem Step Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import PImg RMallocRep RMallocTree RMalloc_iface RF_free_spec RF_malloc_spec.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrNodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrRegsEqvW MrEqv MrFeasNull MrFeasNull44 MrFeasSome1. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrFeasLift MrFeasLift2 MrRoom.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.FOU Require Import MrNonNull.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Abbreviation getr := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec.getr.
Abbreviation realizes := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.realizes.
Abbreviation TSet := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.TSet.

(* [comment removed for export] *)
Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

(* [comment removed for export] *)
Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  let g := fun k : Z => reg_get R (Z_to_bv 5 k) in
  mkR (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) (g 16)
      (g 17) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31).

Lemma mkR_of_eqvW : forall R, regs_eqvW (mkR_of R) R.
Proof.
  intros R r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [exfalso; apply Hr; reflexivity|].
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Section S9.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.

(* [comment removed for export] *)
Definition kept_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Theorem free_rz_any : forall (R : bvmap 5 word) (M : word -> option byte) (mo : Model)
    (s : PState) (LB : list block) (X : list bptr) (G : PState -> Model -> Prop)
    (p : bptr) (A n lo B : Z) (errv : word) (T : TSet),
  RHEAP s LB M -> In (p, A, n) LB ->
  OWN (p :: X) G s mo -> frame_ok G ->
  rauxv_ok M B -> bv_unsigned (reg_get R (Z_to_bv 5 2)) <= B ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) -> ATOP <= lo ->
  lo <= bv_unsigned (reg_get R (Z_to_bv 5 2)) - RFREE_STACK ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  reg_get R (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  reg_get R (Z_to_bv 5 10) = Z_to_bv 64 A ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (mo' : Model) (s' : PState),
      (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) ->
      mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) ->
      rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv] -> rauxv_ok M' B ->
      rheap_pres (lb_remove p LB) (bv_unsigned (reg_get R (Z_to_bv 5 2))) M M' ->
      ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
      RHEAP s' (lb_remove p LB) M' -> OWN X G s' mo' ->
      realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RFREE_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R M mo s LB X G p A n lo B errv T HH Hin HOWN HG HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 HK.
  (* [comment removed for export] *)
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RFREE_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  (* [comment removed for export] *)
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  set (g := fun k : Z => reg_get R (Z_to_bv 5 k)).
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb))
            (raw_free p s)
            (epost (fun a => rfree_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                                        (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB p lo B errv M (fst a) (snd a)))
            (fun r mo1 => match r with Unr => False | Ok a => OWN X G (snd a) mo1 end)).
  - (* [comment removed for export] *)
    unfold mkR_of. fold g.
    exact (rfree_spec_proof (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) (g 16) (g 17)
             (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31)
             bvmap_empty (Z_to_bv 32 0) M s LB p A n lo B errv HH Hin HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0).
  - (* [comment removed for export] *)
    apply twf_bridge. exact (raw_free_spec X G p HG s mo HOWN).
  - apply mmtree_tsilent. apply mmtree_raw_free.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - (* [comment removed for export] *)
    intros [|[[] s']] ms' mo' HQ HP Hh' Hinv'; [contradiction|]. cbn [epost fst snd] in HQ.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & HH').
    eapply HK; try eassumption.
    intros k Hk. unfold kept_regs in Hk. cbn in Hk.
    repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition malloc_ret (R R' : bvmap 5 word) (M M' : word -> option byte) (s s' : PState) (LB : list block)
    (n lo B : Z) (r : option bptr) : Prop :=
  (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) /\
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' /\ stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo (bv_unsigned (reg_get R (Z_to_bv 5 2))) /\
  (exists errv', rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (errno_addr (reg_get R (Z_to_bv 5 4))) [C4 errv']) /\
  rauxv_ok M' B /\ rheap_pres LB (bv_unsigned (reg_get R (Z_to_bv 5 2))) M M' /\
  ps_fa s' = ps_fa s /\ ps_so s' = ps_so s /\
  match r with
  | None => reg_get R' (Z_to_bv 5 10) = Z_to_bv 64 0 /\ RHEAP s' LB M'
  | Some p => exists A junk,
      reg_get R' (Z_to_bv 5 10) = Z_to_bv 64 A /\ rblock_range A n /\ RHEAP s' ((p, A, n) :: LB) M'
      /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' A [CB (Z.to_nat n) junk] /\ (raddr_exposed s n -> A = ptr_addr s' p)
  end.

Definition own_ret (X : list bptr) (G : PState -> Model -> Prop) (r : option bptr) (s' : PState) (mo' : Model) : Prop :=
  match r with Some p => OWN (p :: X) G s' mo' | None => OWN X G s' mo' end.

Section MallocRules.
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

Let g := fun k : Z => reg_get R (Z_to_bv 5 k).
Let Qm := epost (fun a : option bptr * PState =>
            rmalloc_post (g 1) (g 2) (g 3) (g 4) (g 8) (g 9) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25)
                         (g 26) (g 27) bvmap_empty (Z_to_bv 32 0) s LB n lo B M (fst a) (snd a)).
Let Pm := fun (r : exc (option bptr * PState)) (mo1 : Model) =>
            match r with Unr => False | Ok a => own_ret X G (fst a) (snd a) mo1 end.

Lemma malloc_impl :
  @impl node (run_segments psegs rc_inp rc_sp rc_mb) (at_node (run_segments psegs rc_inp rc_sp rc_mb)) _ (raw_malloc n s) Qm
        (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  unfold mkR_of. fold g.
  exact (rmalloc_spec (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) (g 16) (g 17)
           (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31)
           bvmap_empty (Z_to_bv 32 0) M s LB n lo B errv HH HAUX HspB HSTK Hlo1 Hlo2 HERR HMI Htp Ha0 Hn).
Qed.

Lemma malloc_twf : B.twf node nstep nsafe (raw_malloc n s) mo Pm.
Proof.
  apply twf_bridge. pose proof (raw_malloc_spec X G n HG (proj1 Hn) s mo HOWN) as H.
  unfold etwf in H. eapply twf_mono; [exact H|]. intros [|[[p|] s']] mo1; cbn; tauto.
Qed.

Lemma malloc_leaf : forall r ms' mo' (K : option bptr -> TSet),
  (forall R' M' mo'' s' r', malloc_ret R R' M M' s s' LB n lo B r' -> own_ret X G r' s' mo'' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo'') (K r')) ->
  Qm r ms' -> Pm r mo' ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg ms' mo') (match r with Unr => K None | Ok a => K (fst a) end).
Proof.
  intros [|[r s']] ms' mo' K HK HQ HP; [contradiction|]. unfold Qm in HQ. cbn [epost fst snd] in HQ, HP |- *.
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & -> & HMI' & HSTK' & HERR' & HAUX' & HPRES & Hfa & Hso & Hr).
  eapply HK; [|exact HP].
  unfold malloc_ret. split.
  { intros k Hk. unfold kept_regs in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [reflexivity|]). contradiction. }
  do 2 (split; [assumption|]). split; [exists errv'; exact HERR'|]. do 4 (split; [assumption|]).
  destruct r as [p|].
  - destruct Hr as (A & junk & -> & Hr). exists A, junk. split; [reflexivity | exact Hr].
  - destruct Hr as [-> Hr]. split; [reflexivity | exact Hr].
Qed.

(* [comment removed for export] *)
Theorem malloc_rz_any : forall (T : TSet),
  (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros T HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) (raw_malloc n s) Qm Pm).
  - exact malloc_impl.
  - exact malloc_twf.
  - apply mmtree_tsilent. apply mmtree_raw_malloc.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - intros r ms' mo' HQ HP _ _. pose proof (malloc_leaf r ms' mo' (fun _ => T) HK HQ HP) as H. destruct r; exact H.
Qed.

(* [comment removed for export] *)
Theorem malloc_rz_2 : forall (A Bs : TSet),
  tpaths (raw_malloc n s) mo (fun r => is_null r = false) ->
  A [] -> Bs [] ->
  (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
              (match r with None => A | Some _ => Bs end)) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.
Proof.
  intros A Bs HNN HA0 HB0 HK.
  apply (realizes_eqv (run_segments psegs rc_inp rc_sp rc_mb)
           (mkCfg (MS (mkR_of R) bvmap_empty (Z_to_bv 64 RMALLOC_SYM) (Z_to_bv 32 0) None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)).
  2:{ split; [|reflexivity]. cbn. split; [apply mkR_of_eqvW|]. repeat split; apply regs_eqv_refl. }
  pose proof HOWN as [(L & Hcr & HKL & Hincl) _].
  eapply (B.impl_realizes_any (run_segments psegs rc_inp rc_sp rc_mb) node (at_node (run_segments psegs rc_inp rc_sp rc_mb)) nstep nexit minv nsafe (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) (raw_malloc n s) Qm (fun r mo1 => Pm r mo1 /\ is_null r = false) Bs).
  - exact malloc_impl.
  - exact (twf_tpaths _ _ _ _ malloc_twf HNN).
  - apply mmtree_tsilent. apply mmtree_raw_malloc.
  - exact (kl_halt _ _ _ HKL).
  - exact (kl_minv _ _ _ HKL).
  - intros r ms' mo' HQ [HP Hnn] _ _. destruct r as [|a]; [destruct HP|].
    pose proof (malloc_leaf (Ok a) ms' mo' (fun r' => match r' with None => A | Some _ => Bs end) HK HQ HP) as H.
    destruct a as [[p|] s']; cbn in *; [exact H | discriminate Hnn].
Qed.

(* [comment removed for export] *)
Theorem malloc_rz_driver : forall (Bd : Z) (A Bs : TSet),
  (allnone (ps_m s) \/ (none44 (ps_m s) /\ full44 (ps_m s))) ->
  metaok_ps s -> room Bd mo -> n + 20 <= Bd -> 2^24 <= Bd -> Bd + 4096 <= 2^30 ->
  A [] -> Bs [] ->
  (forall R' M' mo' s' r, malloc_ret R R' M M' s s' LB n lo B r -> own_ret X G r s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R' (ret_pc (reg_get R (Z_to_bv 5 1))) M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo')
              (match r with None => A | Some _ => Bs end)) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) Bs.
Proof.
  intros Bd A Bs Hact Hmeta Hroom HnB HB1 HB2 HA0 HB0 HK.
  apply (malloc_rz_2 A Bs); try assumption.
  eapply (raw_malloc_nonnull_gone X G Bd); eauto; try lia. apply room_grantable; [lia | lia | exact Hroom].
Qed.

End MallocRules.

End S9.
