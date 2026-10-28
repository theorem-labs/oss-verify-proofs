(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_realloc. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit
     Fz_T_lock_new Fz_T_sk Fz_I1_defs Fz_I1_new Fz_I2_pstring.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition FZ_PROPERTY_PARSE_INIT : Z := 0xefedc.
(* [comment removed for export] *)
Definition PPI_STACK : Z := 240 + CRE_STACK.
Definition PPI_EV : nat := 20.
Definition PPI_NA : Z := 19.
(* [comment removed for export] *)
Definition CTX_A : Z := 0x32dec8.
Definition CTX_PSD : Z := CTX_A + 168.
(* [comment removed for export] *)
Definition PROP_FNS : lh_fns := mkFns 0xf0a90 0xf0a5c 0xf0fa4 0xf0fc4.
Definition PROP_DAW : Z := 0xf0fe4.
Definition PROP_DAAW : Z := 0xf1004.
(* [comment removed for export] *)
Definition PROP_SK_CMPT : Z := 0xf0ad8.
Definition PROP_SK_FREET : Z := 0xf0b2c.
Definition PROP_SK_COPYT : Z := 0xf0b04.

Record ppk : Type := PPK { k_ps : bptr; k_pk : bptr; k_pl1 : bptr; k_pb1 : bptr; k_pl2 : bptr; k_pb2 : bptr; k_pq1 : bptr; k_pq2 : bptr;
                           a_S : Z; a_LK : Z; a_lh1 : Z; a_B1 : Z; a_lh2 : Z; a_B2 : Z; a_Q1 : Z; a_Q2 : Z }.
(* [comment removed for export] *)
Definition ppk_blocks (KP : ppk) : list block :=
  [(k_pq2 KP, a_Q2 KP, 56); (k_pq1 KP, a_Q1 KP, 56); (k_pb2 KP, a_B2 KP, 128); (k_pl2 KP, a_lh2 KP, 104); (k_pb1 KP, a_B1 KP, 128); (k_pl1 KP, a_lh1 KP, 104);
   (k_pk KP, a_LK KP, 40); (k_ps KP, a_S KP, 48)].
Definition ppk_ids (KP : ppk) : list bptr := [k_pq2 KP; k_pq1 KP; k_pb2 KP; k_pl2 KP; k_pb1 KP; k_pl1 KP; k_pk KP; k_ps KP].
Definition ppk_T (KP : ppk) : bptr -> Prop := fun q => In q (ppk_ids KP).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition psd_rep (m : mem) (LBall : list block) (L : @clist bptr) (KP : ppk) : Prop :=
     cown LBall L (k_ps KP) (a_S KP) 48 48
  /\ rw_cells usegs m (a_S KP) [C8 (wz (a_LK KP)); C8 (wz (a_lh1 KP)); C8 (wz (a_lh2 KP)); C4 z64; C4 z64; C8 (wz (a_Q1 KP)); C8 (wz (a_Q2 KP))]
  /\ cown LBall L (k_pk KP) (a_LK KP) 40 40 /\ rw_cells usegs m (a_LK KP) (mutex_cells z64 z64)
  /\ lh_rep (fun _ => True) m LBall L PROP_FNS (a_lh1 KP) (k_pl1 KP) (k_pb1 KP) (a_B1 KP) 128 (mkGeo 8 16 0 8 0) (repeat [] 16)
  /\ lh_rep (fun _ => True) m LBall L PROP_FNS (a_lh2 KP) (k_pl2 KP) (k_pb2 KP) (a_B2 KP) 128 (mkGeo 8 16 0 8 0) (repeat [] 16)
  /\ cown LBall L (k_pq1 KP) (a_Q1 KP) 56 56
  /\ rw_cells usegs m (a_Q1 KP) (sk_cells z64 z64 z64 (wz 1) z64 z64 (wz PROP_SK_CMPT) (wz PROP_SK_FREET) (wz PROP_SK_COPYT))
  /\ cown LBall L (k_pq2 KP) (a_Q2 KP) 56 56
  /\ rw_cells usegs m (a_Q2 KP) (sk_cells z64 z64 z64 (wz 1) z64 z64 (wz PROP_SK_CMPT) (wz PROP_SK_FREET) (wz PROP_SK_COPYT))
  /\ List.NoDup (ppk_ids KP).

(* [comment removed for export] *)
Definition psd_fp (KP : ppk) (a : Z) : Prop := exists b, In b (ppk_blocks KP) /\ blk_addr b <= a < blk_addr b + blk_size b.

Lemma psd_rep_blocks : forall m LBall L KP b, psd_rep m LBall L KP -> In b (ppk_blocks KP) -> In b LBall.
Proof.
  intros m LBall L KP b (O1 & _ & O2 & _ & R1 & R2 & O7 & _ & O8 & _ & _) Hb.
  destruct R1 as (_ & O3 & _ & _ & O4 & _). destruct R2 as (_ & O5 & _ & _ & O6 & _). cbn [g_na] in O4, O6.
  unfold ppk_blocks in Hb. cbn [In] in Hb.
  destruct Hb as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    [exact (proj1 O8)| exact (proj1 O7)| exact (proj1 O6)| exact (proj1 O5)| exact (proj1 O4)| exact (proj1 O3)| exact (proj1 O2)| exact (proj1 O1)].
Qed.

Lemma psd_rep_agree : forall (m m' : mem) LBall L LBall' L' KP,
  psd_rep m LBall L KP -> agree_on (psd_fp KP) m m' ->
  (forall q A n nm, In q (ppk_ids KP) -> cown LBall L q A n nm -> cown LBall' L' q A n nm) ->
  psd_rep m' LBall' L' KP.
Proof.
  intros m m' LBall L LBall' L' KP (O1 & C1 & O2 & C2 & R1 & R2 & O7 & C7 & O8 & C8' & ND) AG HO.
  assert (CELLS : forall A cs k, rw_cells usegs m A cs -> nth_error (ppk_blocks KP) k = Some (nth k (map blk_id (ppk_blocks KP)) (k_ps KP), A, Z.of_nat (cells_size cs)) ->
                  rw_cells usegs m' A cs).
  { intros A cs k C Hk. eapply rw_cells_agree; [exact AG| exact C|]. intros a Ha. exists (nth k (map blk_id (ppk_blocks KP)) (k_ps KP), A, Z.of_nat (cells_size cs)).
    split; [eapply nth_error_In; exact Hk|]. unfold blk_addr, blk_size; cbn [fst snd]. exact Ha. }
  split; [apply HO; [do 7 right; left; reflexivity| exact O1]|]. split; [exact (CELLS _ _ 7%nat C1 eq_refl)|].
  split; [apply HO; [do 6 right; left; reflexivity| exact O2]|]. split; [exact (CELLS _ _ 6%nat C2 eq_refl)|].
  split. { eapply lh_rep_agree; [exact R1| |].
    - eapply agree_on_mono; [exact AG|]. intros a [Ha|[Ha|(p & A & Hp & _)]]; [exists (k_pl1 KP, a_lh1 KP, 104)| exists (k_pb1 KP, a_B1 KP, 128)| exfalso; clear - Hp].
      + split; [do 5 right; left; reflexivity| unfold blk_addr, blk_size; cbn [fst snd]; exact Ha].
      + split; [do 4 right; left; reflexivity| unfold blk_addr, blk_size; cbn [fst snd g_na] in *; lia].
      + cbn in Hp. exact Hp.
    - intros q A n nm [E|[E|Hq]] O; [apply HO; [rewrite E; do 5 right; left; reflexivity| exact O]| apply HO; [rewrite E; do 4 right; left; reflexivity| exact O]|].
      exfalso. clear - Hq. cbn in Hq. exact Hq. }
  split. { eapply lh_rep_agree; [exact R2| |].
    - eapply agree_on_mono; [exact AG|]. intros a [Ha|[Ha|(p & A & Hp & _)]]; [exists (k_pl2 KP, a_lh2 KP, 104)| exists (k_pb2 KP, a_B2 KP, 128)| exfalso; clear - Hp].
      + split; [do 3 right; left; reflexivity| unfold blk_addr, blk_size; cbn [fst snd]; exact Ha].
      + split; [do 2 right; left; reflexivity| unfold blk_addr, blk_size; cbn [fst snd g_na] in *; lia].
      + cbn in Hp. exact Hp.
    - intros q A n nm [E|[E|Hq]] O; [apply HO; [rewrite E; do 3 right; left; reflexivity| exact O]| apply HO; [rewrite E; do 2 right; left; reflexivity| exact O]|].
      exfalso. clear - Hq. cbn in Hq. exact Hq. }
  split; [apply HO; [right; left; reflexivity| exact O7]|]. split; [exact (CELLS _ _ 1%nat C7 eq_refl)|].
  split; [apply HO; [left; reflexivity| exact O8]|]. split; [exact (CELLS _ _ 0%nat C8' eq_refl)| exact ND].
Qed.

(* [comment removed for export] *)
Lemma psd_rep_cframe : forall (m m' : mem) T W SP s LBall L s' LBall' L' KP,
  psd_rep m LBall L KP -> cframe T W SP s LBall L m s' LBall' L' m' -> (forall q, In q (ppk_ids KP) -> ~ T q) -> psd_rep m' LBall' L' KP.
Proof.
  intros m m' T W SP s LBall L s' LBall' L' KP REP (CFR & [K1 K2] & _) NT. eapply psd_rep_agree; [exact REP| |].
  - eapply agree_on_mono; [exact CFR|]. intros a (b & Hb & Ra). right; left. exists b. split; [exact (psd_rep_blocks _ _ _ _ _ REP Hb)|]. split; [| exact Ra].
    apply NT. unfold ppk_ids. unfold ppk_blocks in Hb. cbn [In] in Hb. cbn [In].
    destruct Hb as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; unfold blk_id; cbn [fst snd]; tauto.
  - intros q A n nm Hq [I1 I2]. split; [apply K1; [exact I1| apply NT; exact Hq]| apply K2; [exact I2| apply NT; exact Hq]].
Qed.

(* [comment removed for export] *)
Lemma cstate_fresh_ids : forall s (pre LBall LB : list block) (L : @clist bptr) L' m sp tp lo B,
  cstate s (pre ++ LBall) LB L' m sp tp lo B -> cl_own LBall LB L ->
  forall b, In b pre -> forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> blk_id b.
Proof.
  intros s pre LBall LB L L' m sp tp lo B CST (CLB & PERM & IDS) b Hb q Hq E. subst q.
  apply (t_nodup_prefix blk_id pre LBall b (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) Hb).
  destruct Hq as [Hq|Hq]; [exact Hq|]. rewrite <- IDS in Hq.
  eapply Permutation_in; [apply Permutation_map; apply Permutation_sym; exact PERM|]. rewrite map_app. apply in_or_app. left. exact Hq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pstring_rep_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (ps pk pl1 pb1 pl2 pb2 pq1 pq2 : bptr) (S LK lh1 B1 lh2 B2 Q1 Q2 : Z),
    v = Z_to_bv 64 S
    /\ LBall' = (pq2, Q2, 56) :: (pq1, Q1, 56) :: (pb2, B2, 128) :: (pl2, lh2, 104) :: (pb1, B1, 128) :: (pl1, lh1, 104) :: (pk, LK, 40) :: (ps, S, 48) :: LBall
    /\ L' = (pq2, 56) :: (pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: L
    /\ rblock_range S 48 /\ rblock_range LK 40 /\ rblock_range lh1 104 /\ rblock_range B1 128 /\ rblock_range lh2 104 /\ rblock_range B2 128
    /\ rblock_range Q1 56 /\ rblock_range Q2 56
    /\ psd_rep m' LBall' L' (PPK ps pk pl1 pb1 pl2 pb2 pq1 pq2 S LK lh1 B1 lh2 B2 Q1 Q2).

Definition ossl_property_string_data_new_rep_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (8 <= f)%nat -> croom L 8 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PSD_STACK ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PROP_STRING_DATA_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 8 8 0 0 (pstring_rep_res LBall L)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ppi_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 : bptr) (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 : Z),
    v = Z_to_bv 64 1
    /\ LBall' = (p18, A18, 24) :: (p17, A17, 18) :: (p16, A16, 24) :: (p15, A15, 32) :: (p14, A14, 19) :: (p13, A13, 24) :: (p12, A12, 25) :: (p11, A11, 24)
                :: (p10, A10, 48) :: (p9, A9, 21) :: (p8, A8, 24) :: (p7, A7, 22) :: (p6, A6, 24) :: (p5, A5, 20) :: (p4, A4, 24) :: (p3, A3, 23) :: (p2, A2, 24)
                :: (p1, A1, 24) :: LBall
    /\ rblock_range A1 24 /\ rblock_range A2 24 /\ rblock_range A3 23 /\ rblock_range A4 24 /\ rblock_range A5 20 /\ rblock_range A6 24 /\ rblock_range A7 22
    /\ rblock_range A8 24 /\ rblock_range A9 21 /\ rblock_range A10 48 /\ rblock_range A11 24 /\ rblock_range A12 25 /\ rblock_range A13 24 /\ rblock_range A14 19
    /\ rblock_range A15 32 /\ rblock_range A16 24 /\ rblock_range A17 18 /\ rblock_range A18 24.

Definition ossl_property_parse_init_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (KP : ppk),
  (PPI_EV <= f)%nat -> croom L PPI_NA 0 0 -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - PPI_STACK -> bv_unsigned sp mod 16 = 0 ->
  a0 = Z_to_bv 64 CTX_A -> rw_cells usegs m CTX_PSD [C8 (Z_to_bv 64 (a_S KP))] -> psd_rep m LBall L KP ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PROPERTY_PARSE_INIT) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (ppk_T KP) [] PPI_EV PPI_NA 0 0 (ppi_res LBall L)).
End WithCeiling0.
