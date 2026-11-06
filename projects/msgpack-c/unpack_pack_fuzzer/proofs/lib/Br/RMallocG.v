(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Image ITree Nodes NodesM Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog MSafe KLink KStep KOwn KStepC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocBlocks A_MallocHINV A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv TreeBridge NodeSound TreeBridgeN KRel MPath.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Import ShapeAlg(TSet, t_eq, t_alt, t_alt2, t_emit, t_nil, realizes, node_ok).
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition kept_regs : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma errno_addr_RATP : (bv_unsigned (Z_to_bv 64 RATP) + (-164))%Z = RERRNO.
Proof. reflexivity. Qed.

Record gpost (R : bvmap 5 word) (M : mem) (mo : Model) (LB : list block) (lo B : Z)
             (R' : bvmap 5 word) (M' : mem) (mo' : Model) : Prop := GPOST {
  gp_regs  : forall r, In r kept_regs -> getr R' r = getr R r;
  gp_minv  : mem_inv rsegs M';
  gp_stk   : stk rsegs M' lo (bv_unsigned (getr R 2));
  gp_auxv  : rauxv_ok M' B;
  gp_auxcell : rauxcell_pres M M';
  gp_pres  : rheap_pres LB (bv_unsigned (getr R 2)) M M';
  gp_mo    : mo_ok mo';
  gp_va    : vm_agree mo mo' }.

Lemma kept_mkR : forall (R : bvmap 5 word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) r,
  In r kept_regs ->
  getr (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
          (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
          (getr R 26) (getr R 27) t3 t4 t5 t6) r = getr R r.
Proof.
  intros until r. intros Hr. cbn in Hr.
  repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr.
Qed.

Local Notation rom := (seg_rom rsegs).

Theorem malloc_obs_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (KA KB : TSet),
    getr R 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RMALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    malloc_can_fail s mo n -> malloc_can_succeed s mo n ->
    (forall R' M' mo' s' (errv' : word),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo None s' mo' -> mtr_malloc s n None s' ->
        getr R' 10 = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        RHEAP s' LB M' -> KREL s' LB mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') KA) ->
    (forall R' M' mo' s' (errv' : word) (p : bptr) (A : Z) (junk : list byte),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo (Some p) s' mo' -> mtr_malloc s n (Some p) s' ->
        getr R' 10 = Z_to_bv 64 A -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A n -> rw_cells rsegs M' A [CB (Z.to_nat n) junk] ->
        (raddr_exposed s n -> A = ptr_addr s' p) ->
        RHEAP s' ((p, A, n) :: LB) M' -> KREL s' ((p, A, n) :: LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') KB) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RMALLOC_SYM) fc None M rom) mo) (t_alt2 KA KB).
Proof.
  intros R F fc M mo s LB n lo B errv KA KB Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo Hcf Hcs HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rmalloc_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Hn) as Himpl.
  eapply (implM_mspec_realizes_alt2 rsegs (raw_malloc n) s _ (fun s' mo => s' = s /\ KREL s' LB mo) _ _ mo
            (fun r : option bptr => match r with Some _ => true | None => false end) KA KB Himpl).
  - apply (raw_malloc_spec_K LB n s); lia.
  - split; [reflexivity | exact HK].
  - exact Hmo.
  - destruct Hcf as (s' & mo' & Hp). exists None, s', mo'. split; [exact Hp | reflexivity].
  - destruct Hcs as (p & s' & mo' & Hp). exists (Some p), s', mo'. split; [exact Hp | reflexivity].
  - intros r s' ms' mo' HPOST HQm Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & Hr).
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    assert (GP : gpost R M mo LB lo B
              (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                   (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                   (getr R 26) (getr R 27) t3 t4 t5 t6) m' mo').
    { constructor; try assumption. apply kept_mkR. }
    destruct HQm as [HOWN MTR].
    destruct r as [p|].
    + destruct Hr as (A & junk & -> & Hrng & HRH' & Hcells & Hexp). cbn.
      eapply (HKB _ m' mo' s' errv' p A junk GP Hpath MTR); try assumption; try reflexivity. apply HOWN.
    + destruct Hr as [-> HRH']. cbn.
      eapply (HKA _ m' mo' s' errv' GP Hpath MTR); try assumption; try reflexivity.
Qed.

Theorem malloc_silent_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RMALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    (forall R' M' mo' s' (errv' : word),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo None s' mo' -> mtr_malloc s n None s' ->
        getr R' 10 = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        RHEAP s' LB M' -> KREL s' LB mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    (forall R' M' mo' s' (errv' : word) (p : bptr) (A : Z) (junk : list byte),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo (Some p) s' mo' -> mtr_malloc s n (Some p) s' ->
        getr R' 10 = Z_to_bv 64 A -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A n -> rw_cells rsegs M' A [CB (Z.to_nat n) junk] ->
        (raddr_exposed s n -> A = ptr_addr s' p) ->
        RHEAP s' ((p, A, n) :: LB) M' -> KREL s' ((p, A, n) :: LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RMALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rmalloc_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Hn) as Himpl.
  eapply (implM_mspec_realizes_silent rsegs (raw_malloc n) s _ (fun s' mo => s' = s /\ KREL s' LB mo) _ _ mo K Himpl).
  - apply (raw_malloc_spec_K LB n s); lia.
  - split; [reflexivity | exact HK].
  - exact Hmo.
  - intros r s' ms' mo' HPOST HQm Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & Hr).
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    assert (GP : gpost R M mo LB lo B
              (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                   (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                   (getr R 26) (getr R 27) t3 t4 t5 t6) m' mo').
    { constructor; try assumption. apply kept_mkR. }
    destruct HQm as [HOWN MTR].
    destruct r as [p|].
    + destruct Hr as (A & junk & -> & Hrng & HRH' & Hcells & Hexp).
      eapply (HKB _ m' mo' s' errv' p A junk GP Hpath MTR); try assumption; try reflexivity. apply HOWN.
    + destruct Hr as [-> HRH'].
      eapply (HKA _ m' mo' s' errv' GP Hpath MTR); try assumption; try reflexivity.
Qed.

Theorem malloc_must_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RMALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    malloc_must_succeed s mo n ->
    (forall R' M' mo' s' (errv' : word) (p : bptr) (A : Z) (junk : list byte),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo (Some p) s' mo' -> mtr_malloc s n (Some p) s' ->
        getr R' 10 = Z_to_bv 64 A -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A n -> rw_cells rsegs M' A [CB (Z.to_nat n) junk] ->
        (raddr_exposed s n -> A = ptr_addr s' p) ->
        RHEAP s' ((p, A, n) :: LB) M' -> KREL s' ((p, A, n) :: LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RMALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo Hmust HKB.
  apply (malloc_silent_G R F fc M mo s LB n lo B errv K Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo); [| exact HKB].
  intros R' M' mo' s' errv' _ Hpath. exfalso. exact (Hmust None s' mo' Hpath eq_refl).
Qed.

Lemma bptr_eqb_true : forall p q, bptr_eqb p q = true <-> p = q.
Proof.
  intros [p1 p2] [q1 q2]. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, aptr_eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Lemma lb_remove_cons : forall p b LB,
  lb_remove p (b :: LB) = if bptr_eqb (blk_id b) p then lb_remove p LB else b :: lb_remove p LB.
Proof.
  intros p b LB. unfold lb_remove. cbn [base.filter list_filter].
  destruct (bptr_eqb (blk_id b) p); cbn [negb].
  - destruct (decide (Is_true false)) as [H|H]; [destruct H | reflexivity].
  - destruct (decide (Is_true true)) as [H|H]; [reflexivity | exfalso; apply H; exact I].
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. induction LB as [|b LB IH]; intros Hn; [reflexivity|].
  rewrite lb_remove_cons. cbn [map In] in Hn.
  destruct (bptr_eqb (blk_id b) p) eqn:E.
  - apply bptr_eqb_true in E. exfalso. apply Hn. left. exact E.
  - f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma lb_remove_perm : forall p A n LB,
  In (p, A, n) LB -> List.NoDup (map blk_id LB) -> Permutation LB ((p, A, n) :: lb_remove p LB).
Proof.
  intros p A n LB. induction LB as [|b LB IH]; intros Hin Hnd; [destruct Hin|].
  cbn [map] in Hnd. inversion Hnd as [|x l Hnotin Hnd']; subst.
  rewrite lb_remove_cons.
  destruct Hin as [-> | Hin].
  - cbn [blk_id fst]. rewrite (proj2 (bptr_eqb_true p p) eq_refl).
    cbn [blk_id fst] in Hnotin. rewrite lb_remove_notin by exact Hnotin. apply Permutation_refl.
  - assert (Hne : bptr_eqb (blk_id b) p = false).
    { destruct (bptr_eqb (blk_id b) p) eqn:E; [|reflexivity]. apply bptr_eqb_true in E.
      exfalso. apply Hnotin. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact Hin]. }
    rewrite Hne.
    eapply Permutation_trans; [apply perm_skip; apply IH; assumption | apply perm_swap].
Qed.

Theorem free_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 A -> In (p, A, n) LB ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RFREE_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    (forall R' M' mo' s',
        gpost R M mo (lb_remove p LB) lo B R' M' mo' -> mpath (raw_free p) s mo tt s' mo' -> mtr_free s p s' ->
        rw_cells rsegs M' RERRNO [C4 errv] ->
        RHEAP s' (lb_remove p LB) M' -> KREL s' (lb_remove p LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RFREE_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB p A n lo B errv K Ha0 Hin Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKK.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rfree_spec_proof (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB p A n lo B errv HRH Hin Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0) as Himpl.
  assert (HK' : OWNS (p :: map blk_id (lb_remove p LB)) GT s mo).
  { change (p :: map blk_id (lb_remove p LB)) with (map blk_id ((p, A, n) :: lb_remove p LB)).
    eapply OWNS_perm; [| exact HK]. apply Permutation_map. apply lb_remove_perm; [exact Hin|].
    eapply KREL_nodup_id. exact HK. }
  eapply (implM_mspec_realizes_silent rsegs (raw_free p) s _ (fun s' mo => s' = s /\ OWNS (p :: map blk_id (lb_remove p LB)) GT s' mo) _ _ mo K Himpl).
  - apply (raw_free_spec_cp (map blk_id (lb_remove p LB)) p s).
  - split; [reflexivity | exact HK'].
  - exact Hmo.
  - intros [] s' ms' mo' HPOST [HQm MTR] Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & HRH').
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    eapply (HKK _ m' mo' s'); try assumption; try exact MTR.
    constructor; try assumption. apply kept_mkR.
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStepC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMalloc_iface.TwinB RF_malloc_spec.TwinB RF_free_spec.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NodeSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Import ShapeAlg(TSet, t_eq, t_alt, t_alt2, t_emit, t_nil, realizes, node_ok).
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition kept_regs : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma errno_addr_RATP : (bv_unsigned (Z_to_bv 64 RATP) + (-164))%Z = RERRNO.
Proof. reflexivity. Qed.

Record gpost (R : bvmap 5 word) (M : mem) (mo : Model) (LB : list block) (lo B : Z)
             (R' : bvmap 5 word) (M' : mem) (mo' : Model) : Prop := GPOST {
  gp_regs  : forall r, In r kept_regs -> getr R' r = getr R r;
  gp_minv  : mem_inv rsegs M';
  gp_stk   : stk rsegs M' lo (bv_unsigned (getr R 2));
  gp_auxv  : rauxv_ok M' B;
  gp_auxcell : rauxcell_pres M M';
  gp_pres  : rheap_pres LB (bv_unsigned (getr R 2)) M M';
  gp_mo    : mo_ok mo';
  gp_va    : vm_agree mo mo' }.

Lemma kept_mkR : forall (R : bvmap 5 word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) r,
  In r kept_regs ->
  getr (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
          (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
          (getr R 26) (getr R 27) t3 t4 t5 t6) r = getr R r.
Proof.
  intros until r. intros Hr. cbn in Hr.
  repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr.
Qed.

Local Notation rom := (seg_rom rsegs).

Theorem malloc_obs_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (KA KB : TSet),
    getr R 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RMALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    malloc_can_fail s mo n -> malloc_can_succeed s mo n ->
    (forall R' M' mo' s' (errv' : word),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo None s' mo' -> mtr_malloc s n None s' ->
        getr R' 10 = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        RHEAP s' LB M' -> KREL s' LB mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') KA) ->
    (forall R' M' mo' s' (errv' : word) (p : bptr) (A : Z) (junk : list byte),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo (Some p) s' mo' -> mtr_malloc s n (Some p) s' ->
        getr R' 10 = Z_to_bv 64 A -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A n -> rw_cells rsegs M' A [CB (Z.to_nat n) junk] ->
        (raddr_exposed s n -> A = ptr_addr s' p) ->
        RHEAP s' ((p, A, n) :: LB) M' -> KREL s' ((p, A, n) :: LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') KB) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RMALLOC_SYM) fc None M rom) mo) (t_alt2 KA KB).
Proof.
  intros R F fc M mo s LB n lo B errv KA KB Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo Hcf Hcs HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rmalloc_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Hn) as Himpl.
  eapply (implM_mspec_realizes_alt2 rsegs (raw_malloc n) s _ (fun s' mo => s' = s /\ KREL s' LB mo) _ _ mo
            (fun r : option bptr => match r with Some _ => true | None => false end) KA KB Himpl).
  - apply (raw_malloc_spec_K LB n s); lia.
  - split; [reflexivity | exact HK].
  - exact Hmo.
  - destruct Hcf as (s' & mo' & Hp). exists None, s', mo'. split; [exact Hp | reflexivity].
  - destruct Hcs as (p & s' & mo' & Hp). exists (Some p), s', mo'. split; [exact Hp | reflexivity].
  - intros r s' ms' mo' HPOST HQm Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & Hr).
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    assert (GP : gpost R M mo LB lo B
              (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                   (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                   (getr R 26) (getr R 27) t3 t4 t5 t6) m' mo').
    { constructor; try assumption. apply kept_mkR. }
    destruct HQm as [HOWN MTR].
    destruct r as [p|].
    + destruct Hr as (A & junk & -> & Hrng & HRH' & Hcells & Hexp). cbn.
      eapply (HKB _ m' mo' s' errv' p A junk GP Hpath MTR); try assumption; try reflexivity. apply HOWN.
    + destruct Hr as [-> HRH']. cbn.
      eapply (HKA _ m' mo' s' errv' GP Hpath MTR); try assumption; try reflexivity.
Qed.

Theorem malloc_silent_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RMALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    (forall R' M' mo' s' (errv' : word),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo None s' mo' -> mtr_malloc s n None s' ->
        getr R' 10 = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        RHEAP s' LB M' -> KREL s' LB mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    (forall R' M' mo' s' (errv' : word) (p : bptr) (A : Z) (junk : list byte),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo (Some p) s' mo' -> mtr_malloc s n (Some p) s' ->
        getr R' 10 = Z_to_bv 64 A -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A n -> rw_cells rsegs M' A [CB (Z.to_nat n) junk] ->
        (raddr_exposed s n -> A = ptr_addr s' p) ->
        RHEAP s' ((p, A, n) :: LB) M' -> KREL s' ((p, A, n) :: LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RMALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rmalloc_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Hn) as Himpl.
  eapply (implM_mspec_realizes_silent rsegs (raw_malloc n) s _ (fun s' mo => s' = s /\ KREL s' LB mo) _ _ mo K Himpl).
  - apply (raw_malloc_spec_K LB n s); lia.
  - split; [reflexivity | exact HK].
  - exact Hmo.
  - intros r s' ms' mo' HPOST HQm Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & Hr).
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    assert (GP : gpost R M mo LB lo B
              (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                   (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                   (getr R 26) (getr R 27) t3 t4 t5 t6) m' mo').
    { constructor; try assumption. apply kept_mkR. }
    destruct HQm as [HOWN MTR].
    destruct r as [p|].
    + destruct Hr as (A & junk & -> & Hrng & HRH' & Hcells & Hexp).
      eapply (HKB _ m' mo' s' errv' p A junk GP Hpath MTR); try assumption; try reflexivity. apply HOWN.
    + destruct Hr as [-> HRH'].
      eapply (HKA _ m' mo' s' errv' GP Hpath MTR); try assumption; try reflexivity.
Qed.

Theorem malloc_must_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RMALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    malloc_must_succeed s mo n ->
    (forall R' M' mo' s' (errv' : word) (p : bptr) (A : Z) (junk : list byte),
        gpost R M mo LB lo B R' M' mo' -> mpath (raw_malloc n) s mo (Some p) s' mo' -> mtr_malloc s n (Some p) s' ->
        getr R' 10 = Z_to_bv 64 A -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A n -> rw_cells rsegs M' A [CB (Z.to_nat n) junk] ->
        (raddr_exposed s n -> A = ptr_addr s' p) ->
        RHEAP s' ((p, A, n) :: LB) M' -> KREL s' ((p, A, n) :: LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RMALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo Hmust HKB.
  apply (malloc_silent_G R F fc M mo s LB n lo B errv K Ha0 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo); [| exact HKB].
  intros R' M' mo' s' errv' _ Hpath. exfalso. exact (Hmust None s' mo' Hpath eq_refl).
Qed.

Lemma bptr_eqb_true : forall p q, bptr_eqb p q = true <-> p = q.
Proof.
  intros [p1 p2] [q1 q2]. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, aptr_eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Lemma lb_remove_cons : forall p b LB,
  lb_remove p (b :: LB) = if bptr_eqb (blk_id b) p then lb_remove p LB else b :: lb_remove p LB.
Proof.
  intros p b LB. unfold lb_remove. cbn [base.filter list_filter].
  destruct (bptr_eqb (blk_id b) p); cbn [negb].
  - destruct (decide (Is_true false)) as [H|H]; [destruct H | reflexivity].
  - destruct (decide (Is_true true)) as [H|H]; [reflexivity | exfalso; apply H; exact I].
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. induction LB as [|b LB IH]; intros Hn; [reflexivity|].
  rewrite lb_remove_cons. cbn [map In] in Hn.
  destruct (bptr_eqb (blk_id b) p) eqn:E.
  - apply bptr_eqb_true in E. exfalso. apply Hn. left. exact E.
  - f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma lb_remove_perm : forall p A n LB,
  In (p, A, n) LB -> List.NoDup (map blk_id LB) -> Permutation LB ((p, A, n) :: lb_remove p LB).
Proof.
  intros p A n LB. induction LB as [|b LB IH]; intros Hin Hnd; [destruct Hin|].
  cbn [map] in Hnd. inversion Hnd as [|x l Hnotin Hnd']; subst.
  rewrite lb_remove_cons.
  destruct Hin as [-> | Hin].
  - cbn [blk_id fst]. rewrite (proj2 (bptr_eqb_true p p) eq_refl).
    cbn [blk_id fst] in Hnotin. rewrite lb_remove_notin by exact Hnotin. apply Permutation_refl.
  - assert (Hne : bptr_eqb (blk_id b) p = false).
    { destruct (bptr_eqb (blk_id b) p) eqn:E; [|reflexivity]. apply bptr_eqb_true in E.
      exfalso. apply Hnotin. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact Hin]. }
    rewrite Hne.
    eapply Permutation_trans; [apply perm_skip; apply IH; assumption | apply perm_swap].
Qed.

Theorem free_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 A -> In (p, A, n) LB ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RFREE_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->
    (forall R' M' mo' s',
        gpost R M mo (lb_remove p LB) lo B R' M' mo' -> mpath (raw_free p) s mo tt s' mo' -> mtr_free s p s' ->
        rw_cells rsegs M' RERRNO [C4 errv] ->
        RHEAP s' (lb_remove p LB) M' -> KREL s' (lb_remove p LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RFREE_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB p A n lo B errv K Ha0 Hin Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKK.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rfree_spec_proof (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB p A n lo B errv HRH Hin Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0) as Himpl.
  assert (HK' : OWNS (p :: map blk_id (lb_remove p LB)) GT s mo).
  { change (p :: map blk_id (lb_remove p LB)) with (map blk_id ((p, A, n) :: lb_remove p LB)).
    eapply OWNS_perm; [| exact HK]. apply Permutation_map. apply lb_remove_perm; [exact Hin|].
    eapply KREL_nodup_id. exact HK. }
  eapply (implM_mspec_realizes_silent rsegs (raw_free p) s _ (fun s' mo => s' = s /\ OWNS (p :: map blk_id (lb_remove p LB)) GT s' mo) _ _ mo K Himpl).
  - apply (raw_free_spec_cp (map blk_id (lb_remove p LB)) p s).
  - split; [reflexivity | exact HK'].
  - exact Hmo.
  - intros [] s' ms' mo' HPOST [HQm MTR] Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & HRH').
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    eapply (HKK _ m' mo' s'); try assumption; try exact MTR.
    constructor; try assumption. apply kept_mkR.
Qed.

End CEIL.
End TwinB.
