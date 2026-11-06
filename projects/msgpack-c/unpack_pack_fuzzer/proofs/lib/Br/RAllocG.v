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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog ProgR MSafe KLink KStep KStepC KOwn KRealloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocBlocks A_MallocHINV A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMalloc_iface RF_aligned16 RRealloc_iface RF_realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv TreeBridge NodeSound TreeBridgeN KRel MPath RMallocG.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Import ShapeAlg(TSet, realizes).
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Local Notation rom := (seg_rom rsegs).

Definition mtr_realloc (s : PState) (p : bptr) (n : Z) (r : option bptr) (s' : PState) : Prop := True.

Theorem aligned16_silent_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 16 -> getr R 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RALIGNED16_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    rw_cells rsegs M RMREPL [C4 (wz 0)] ->
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
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RALIGNED16_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Ha1 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hrepl Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (raligned16_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Hrepl Ha0 Ha1 Hn) as Himpl.
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

Lemma RHEAP_RCERT : forall s LB m p A old, RHEAP s LB m -> In (p, A, old) LB -> RCERT s p A old.
Proof.
  intros s LB m p A old (st & LB0 & HP & Hs & HM & [_ AR]) Hin.
  exists st, LB0, ref_reserved. split; [exact Hs|]. split; [exact AR|].
  split; [eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]|].
  destruct HM as ((Hres & Hreg & _) & _). split.
  - intros rid r Hr. rewrite Hres. exact (proj2 (proj2 (proj2 (proj2 (Hreg rid r Hr))))).
  - rewrite Hres. unfold ref_reserved. repeat constructor.
Qed.

Lemma raw_realloc_spec_K : forall LB p A old n s0, In (p, A, old) LB -> List.NoDup (map blk_id LB) -> 0 <= n < 2 ^ 48 ->
  mspec (fun s mo => (s = s0 /\ KREL s LB mo) /\ RCERT s p A old /\ m_vm_lazy mo = []) (raw_realloc p A n)
        (fun r s mo => match r with
                       | Some p' => forall A' n', KREL s ((p', A', n') :: lb_remove p LB) mo
                       | None => KREL s LB mo
                       end).
Proof.
  intros LB p A old n s0 Hin Hnd Hn.
  pose proof (Permutation_map blk_id (lb_remove_perm p A old LB Hin Hnd)) as PERM. cbn [map blk_id fst snd] in PERM.
  eapply mspec_post; [eapply mspec_pre; [apply (raw_realloc_spec_s (map blk_id (lb_remove p LB)) GT p A old n frame_ok_GT Hn)|]|].
  - intros s mo [[-> HK] [RC HL]]. split; [| split; [exact RC | exact HL]].
    unfold KREL in HK. eapply OWNS_perm; [exact PERM | exact HK].
  - intros [p'|] s mo H; cbn beta iota in *.
    + intros A' n'. unfold KREL. exact H.
    + unfold KREL. eapply OWNS_perm; [apply Permutation_sym; exact PERM | exact H].
Qed.

Theorem realloc_silent_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbs : list byte) (K : TSet),
    getr R 10 = Z_to_bv 64 A -> getr R 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    In (p, A, old) LB -> bytes_at rsegs M A oldbs -> Z.of_nat (length oldbs) = old ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RREALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->

    (forall R' M' mo' s' (errv' : word),
        gpost R M mo LB lo B R' M' mo' -> mtr_realloc s p n None s' ->
        getr R' 10 = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        RHEAP s' LB M' -> KREL s' LB mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->

    (forall R' M' mo' s' (errv' : word) (p' : bptr) (A' : Z) (junk : list byte),
        gpost R M mo (lb_remove p LB) lo B R' M' mo' -> mtr_realloc s p n (Some p') s' ->
        getr R' 10 = Z_to_bv 64 A' -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A' n ->
        rw_cells rsegs M' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min old n)) oldbs ++ junk)] ->
        RHEAP s' ((p', A', n) :: lb_remove p LB) M' -> KREL s' ((p', A', n) :: lb_remove p LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RREALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB p A old n lo B errv oldbs K Ha0 Ha1 Hn Hin Hbytes Hlen Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rrealloc_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB p A old n lo B errv oldbs HRH Hin Hbytes Hlen Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Ha1 Hn) as Himpl.
  eapply (implM_mspec_realizes_silent rsegs (raw_realloc p A n) s _
            (fun s' mo => (s' = s /\ KREL s' LB mo) /\ RCERT s' p A old /\ m_vm_lazy mo = []) _ _ mo K Himpl).
  - apply (raw_realloc_spec_K LB p A old n s Hin (KREL_nodup_id _ _ _ HK) Hn).
  - split; [split; [reflexivity | exact HK]|]. split; [exact (RHEAP_RCERT s LB M p A old HRH Hin)|]. exact (mo_ok_lazy _ Hmo).
  - exact Hmo.
  - intros r s' ms' mo' HPOST HQm Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & Hr).
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    destruct r as [p'|].
    + destruct Hr as (A' & junk & -> & Hrng & HRH' & Hcells).
      eapply (HKB _ m' mo' s' errv' p' A' junk); try assumption; try reflexivity; try exact I.
      * constructor; try assumption. apply kept_mkR.
      * apply HQm.
    + destruct Hr as (-> & HRH' & Hpres2).
      eapply (HKA _ m' mo' s' errv'); try assumption; try reflexivity; try exact I.
      constructor; try assumption. apply kept_mkR.
Qed.

Theorem realloc_null_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 0 -> getr R 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RREALLOC_STACK ->
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
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RREALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Ha1 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rrealloc_null_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Ha1 Hn) as Himpl.
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

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ProgR OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStepC OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KRealloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMalloc_iface.TwinB RF_aligned16.TwinB RRealloc_iface.TwinB RF_realloc.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NodeSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath.
Import RMallocG.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Import ShapeAlg(TSet, realizes).
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Local Notation rom := (seg_rom rsegs).

Definition mtr_realloc (s : PState) (p : bptr) (n : Z) (r : option bptr) (s' : PState) : Prop := True.

Theorem aligned16_silent_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 16 -> getr R 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RALIGNED16_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    rw_cells rsegs M RMREPL [C4 (wz 0)] ->
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
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RALIGNED16_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Ha1 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hrepl Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (raligned16_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Hrepl Ha0 Ha1 Hn) as Himpl.
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

Lemma RHEAP_RCERT : forall s LB m p A old, RHEAP s LB m -> In (p, A, old) LB -> RCERT s p A old.
Proof.
  intros s LB m p A old (st & LB0 & HP & Hs & HM & [_ AR]) Hin.
  exists st, LB0, ref_reserved. split; [exact Hs|]. split; [exact AR|].
  split; [eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]|].
  destruct HM as ((Hres & Hreg & _) & _). split.
  - intros rid r Hr. rewrite Hres. exact (proj2 (proj2 (proj2 (proj2 (Hreg rid r Hr))))).
  - rewrite Hres. unfold ref_reserved. repeat constructor.
Qed.

Lemma raw_realloc_spec_K : forall LB p A old n s0, In (p, A, old) LB -> List.NoDup (map blk_id LB) -> 0 <= n < 2 ^ 48 ->
  mspec (fun s mo => (s = s0 /\ KREL s LB mo) /\ RCERT s p A old /\ m_vm_lazy mo = []) (raw_realloc p A n)
        (fun r s mo => match r with
                       | Some p' => forall A' n', KREL s ((p', A', n') :: lb_remove p LB) mo
                       | None => KREL s LB mo
                       end).
Proof.
  intros LB p A old n s0 Hin Hnd Hn.
  pose proof (Permutation_map blk_id (lb_remove_perm p A old LB Hin Hnd)) as PERM. cbn [map blk_id fst snd] in PERM.
  eapply mspec_post; [eapply mspec_pre; [apply (raw_realloc_spec_s (map blk_id (lb_remove p LB)) GT p A old n frame_ok_GT Hn)|]|].
  - intros s mo [[-> HK] [RC HL]]. split; [| split; [exact RC | exact HL]].
    unfold KREL in HK. eapply OWNS_perm; [exact PERM | exact HK].
  - intros [p'|] s mo H; cbn beta iota in *.
    + intros A' n'. unfold KREL. exact H.
    + unfold KREL. eapply OWNS_perm; [apply Permutation_sym; exact PERM | exact H].
Qed.

Theorem realloc_silent_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbs : list byte) (K : TSet),
    getr R 10 = Z_to_bv 64 A -> getr R 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    In (p, A, old) LB -> bytes_at rsegs M A oldbs -> Z.of_nat (length oldbs) = old ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RREALLOC_STACK ->
    rw_cells rsegs M RERRNO [C4 errv] -> mem_inv rsegs M ->
    mo_ok mo ->

    (forall R' M' mo' s' (errv' : word),
        gpost R M mo LB lo B R' M' mo' -> mtr_realloc s p n None s' ->
        getr R' 10 = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        RHEAP s' LB M' -> KREL s' LB mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->

    (forall R' M' mo' s' (errv' : word) (p' : bptr) (A' : Z) (junk : list byte),
        gpost R M mo (lb_remove p LB) lo B R' M' mo' -> mtr_realloc s p n (Some p') s' ->
        getr R' 10 = Z_to_bv 64 A' -> rw_cells rsegs M' RERRNO [C4 errv'] ->
        rblock_range A' n ->
        rw_cells rsegs M' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min old n)) oldbs ++ junk)] ->
        RHEAP s' ((p', A', n) :: lb_remove p LB) M' -> KREL s' ((p', A', n) :: lb_remove p LB) mo' ->
        realizes rsegs (mkCfg (MS R' F (getr R 1) fc None M' rom) mo') K) ->
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RREALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB p A old n lo B errv oldbs K Ha0 Ha1 Hn Hin Hbytes Hlen Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rrealloc_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB p A old n lo B errv oldbs HRH Hin Hbytes Hlen Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Ha1 Hn) as Himpl.
  eapply (implM_mspec_realizes_silent rsegs (raw_realloc p A n) s _
            (fun s' mo => (s' = s /\ KREL s' LB mo) /\ RCERT s' p A old /\ m_vm_lazy mo = []) _ _ mo K Himpl).
  - apply (raw_realloc_spec_K LB p A old n s Hin (KREL_nodup_id _ _ _ HK) Hn).
  - split; [split; [reflexivity | exact HK]|]. split; [exact (RHEAP_RCERT s LB M p A old HRH Hin)|]. exact (mo_ok_lazy _ Hmo).
  - exact Hmo.
  - intros r s' ms' mo' HPOST HQm Hpath Hmo' Hva.
    destruct HPOST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' &
                       -> & Hmi' & Hstk' & Herr2 & Haux' & Hcell & Hpres & _ & _ & Hr).
    rewrite Hret. rewrite Htp, errno_addr_RATP in Herr2.
    destruct r as [p'|].
    + destruct Hr as (A' & junk & -> & Hrng & HRH' & Hcells).
      eapply (HKB _ m' mo' s' errv' p' A' junk); try assumption; try reflexivity; try exact I.
      * constructor; try assumption. apply kept_mkR.
      * apply HQm.
    + destruct Hr as (-> & HRH' & Hpres2).
      eapply (HKA _ m' mo' s' errv'); try assumption; try reflexivity; try exact I.
      constructor; try assumption. apply kept_mkR.
Qed.

Theorem realloc_null_G :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : mem) (mo : Model)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
    getr R 10 = Z_to_bv 64 0 -> getr R 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 48 ->
    getr R 4 = Z_to_bv 64 RATP -> ret_pc (getr R 1) = getr R 1 ->
    RHEAP s LB M -> KREL s LB mo ->
    rauxv_ok M B -> bv_unsigned (getr R 2) <= B ->
    stk rsegs M lo (bv_unsigned (getr R 2)) -> alloc_ceiling <= lo -> lo <= bv_unsigned (getr R 2) - RREALLOC_STACK ->
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
    realizes rsegs (mkCfg (MS R F (Z_to_bv 64 RREALLOC_SYM) fc None M rom) mo) K.
Proof.
  intros R F fc M mo s LB n lo B errv K Ha0 Ha1 Hn Htp Hret HRH HK Haux HB Hstk Hlo1 Hlo2 Herr Hmi Hmo HKA HKB.
  apply realizes_to_mkR. unfold mkR_of.
  assert (Herr' : rw_cells rsegs M (bv_unsigned (getr R 4) + (-164)) [C4 errv]).
  { rewrite Htp, errno_addr_RATP. exact Herr. }
  pose proof (rrealloc_null_spec (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 F fc M s LB n lo B errv HRH Haux HB Hstk Hlo1 Hlo2 Herr' Hmi Htp Ha0 Ha1 Hn) as Himpl.
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

End CEIL.
End TwinB.
