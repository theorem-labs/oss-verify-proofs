(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes ARep ARepQ ARepQP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ AKitR F_amerge F_aqrec_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition bslot (x : bq) : Z := qb_slot (snd x).
Lemma bslot_merge : forall cur nx, bslot (bq_merge cur nx) = bslot cur. Proof. reflexivity. Qed.
Lemma bslot_empty : forall nx, bslot (bq_empty nx) = bslot nx. Proof. reflexivity. Qed.
Lemma merge_bq_slots : forall R cur,
  Permutation (map bslot (fst (merge_bq cur R) ++ snd (merge_bq cur R))) (map bslot (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur; cbn [merge_bq fst snd app map]; [apply Permutation_refl|].
  destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
  - specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
    rewrite map_app in IH |- *. cbn [map] in IH |- *. rewrite bslot_merge in IH. rewrite bslot_empty.
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    apply (Permutation_trans (l' := bslot nx :: bslot cur :: map bslot R)); [| apply perm_swap].
    apply perm_skip. exact IH.
  - specialize (IH nx). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
    cbn [app map]. apply perm_skip. exact IH.
Qed.
Lemma merge_bq_sizes : forall R cur,
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (fst (merge_bq cur R) ++ snd (merge_bq cur R)).
Proof.
  induction R as [|nx R IH]; intros cur HF; cbn [merge_bq fst snd].
  - rewrite app_nil_r. exact HF.
  - pose proof (Forall_inv HF) as HC. pose proof (Forall_inv (Forall_inv_tail HF)) as HN. pose proof (Forall_inv_tail (Forall_inv_tail HF)) as HR.
    cbv beta in HC, HN.
    destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
      assert (HM : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (bq_merge cur nx :: R)).
      { constructor; [| exact HR]. cbn [bq_merge fst b_size]. lia. }
      specialize (IH HM). apply Forall_app in IH as [I1 I2]. apply Forall_app. split; [exact I1|]. constructor; [| exact I2].
      cbn [bq_empty fst b_size]. lia.
    + specialize (IH nx ltac:(constructor; assumption)). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [app]. constructor; [exact HC| exact IH].
Qed.
Lemma merge_bq_bytes : forall R cur,
  batches_bytes (map fst (fst (merge_bq cur R))) + Q_BATCH_BYTES * Z.of_nat (length (snd (merge_bq cur R)))
  = batches_bytes (map fst (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur; cbn [merge_bq fst snd].
  - cbn [length map]. lia.
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [map length] in IH |- *. rewrite !batches_bytes_cons in *. cbn [bq_merge fst b_size] in IH. rewrite Nat2Z.inj_succ. lia.
    + specialize (IH nx). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [map length app] in IH |- *. rewrite !batches_bytes_cons in *. lia.
Qed.
Lemma merge_bq_length : forall R cur,
  length (fst (merge_bq cur R) ++ snd (merge_bq cur R)) = length (cur :: R).
Proof.
  intros R cur. pose proof (Permutation_length (merge_bq_slots R cur)) as H. rewrite !length_map in H. exact H.
Qed.
Lemma baddr_inj : forall L x y, baddr L x = baddr L y -> bslot x = bslot y.
Proof. intros L x y E. unfold baddr, abatch_addr, aslot_addr, bslot in *. rewrite size_of_class_24 in E. lia. Qed.

Lemma batches_bytes_nonneg : forall (l : list bq),
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l -> 0 <= batches_bytes (map fst l).
Proof.
  intros l HF. pose proof (batches_bytes_lb (map fst l) ltac:(rewrite Forall_map; exact HF)). unfold Q_BATCH_BYTES in *. lia.
Qed.

Lemma Forall_rot : forall (P : bq -> Prop) b G T, Forall P ((b :: G) ++ T) -> Forall P (G ++ (T ++ [b])).
Proof.
  intros P b G T H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
  apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [right; apply in_app_iff; left; exact Hx|].
  apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [right; apply in_app_iff; right; exact Hx| left; reflexivity].
Qed.
Lemma NoDup_rot : forall b G T, base.NoDup (map bslot ((b :: G) ++ T)) -> base.NoDup (map bslot (G ++ (T ++ [b]))).
Proof.
  intros b G T ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
  apply Permutation_map. rewrite app_assoc. cbn [app]. apply (Permutation_cons_append (G ++ T) b).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aqrec_lh : Z := 0x357b0.      (* [comment removed for export] *)
Definition aqrec_lt : Z := 0x357ac.      (* [comment removed for export] *)
Definition aqrec_join : Z := 0x3580c.    (* [comment removed for export] *)

Section Front.
  Variables (L : alayout) (RNG : footprint) (MIN lo : Z).
  Variables (ra gp tp xs0 xs1 a2 a3 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable SPP : Z.   (* [comment removed for export] *)
  Hypothesis MIN0 : 0 <= MIN < 2^63.
  Hypothesis SPP0 : ATOP + 16 <= SPP.
  Hypothesis SPP1 : SPP + 80 <= 2^47.
  Hypothesis RT : rng RNG SPP 32.
  Hypothesis RG : rng RNG AQ_GCACHE 32.

  (* [comment removed for export] *)
  Definition deq_W (tfull : bool) (B TL : Z) : list (Z * Z) :=
    ((SPP, SPP + 32) :: (AQ_GCACHE, AQ_GCACHE + 32) :: (B, B + 8) :: (if tfull then [(TL, TL + 8)] else []))%Z.

  Definition deq_body_post (tfull : bool) (B TL nxn bsz nb gl gb tn : Z) (st1 tf st2 tb cw tls tlc : word) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (tb' : word) m',
      ms' = MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 nxn) (Z_to_bv 64 B) (Z_to_bv 64 (gb - bsz)) xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
                    (Z_to_bv 64 (tn + 1)) (Z_to_bv 64 B) (Z_to_bv 64 (nb - 1)) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 aqrec_lt) fc None m' (seg_rom bsegs)
      /\ munch (deq_W tfull B TL) m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AQ_GCACHE [C8 (Z_to_bv 64 (nb - 1)); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 (gb - bsz))]
      /\ rw_cells bsegs m' B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 cw]
      /\ rw_cells bsegs m' SPP [C8 st1; C8 (if tfull then tf else Z_to_bv 64 B); C8 st2; C8 tb']
      /\ (if tfull then rw_cells bsegs m' TL [C8 (Z_to_bv 64 B); C8 tls; C8 tlc] else True).

  Lemma deq_body_spec : forall (tfull : bool) (B TL nxn bsz nb gl gb tn : Z) (st1 tf st2 tb cw tlx tls tlc a7 t1 t2 : word) (m : amem),
    mem_inv bsegs m ->
    rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 gl); C8 (Z_to_bv 64 gb)] ->
    rw_cells bsegs m B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
    rw_cells bsegs m SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
    (if tfull then rw_cells bsegs m TL [C8 tlx; C8 tls; C8 tlc] /\ 0 < tn /\ AIMG_HI <= TL /\ TL + Q_BATCH_BYTES <= ATOP /\ (B + Q_BATCH_BYTES <= TL \/ TL + Q_BATCH_BYTES <= B)
               /\ rng RNG TL Q_BATCH_BYTES
     else tn = 0) ->
    0 < nb < 2^63 -> 0 <= nxn < 2^64 -> 0 <= gl < 2^64 -> 0 <= bsz <= gb -> gb < 2^63 -> 0 <= tn < 2^62 ->
    AIMG_HI <= B -> B + Q_BATCH_BYTES <= ATOP -> rng RNG B Q_BATCH_BYTES ->
    evtF bsegs RNG (deq_body_post tfull B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tls tlc m)
      (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
               (Z_to_bv 64 tn) (Z_to_bv 64 TL) (Z_to_bv 64 nb) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 aqrec_lh) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros MI GC BC TM TF NB NXN GL BSZ GB TN B0 B1 RB.
    unfold aqrec_lh, AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE, AQUAR_Q in *.
    destruct tfull.
    - destruct TF as (TLC & TN1 & TL0 & TL1 & DBT & RTL).
      pose proof (munch_refl (deq_W true B TL) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold deq_W, AQ_GCACHE in MU.
      (* [comment removed for export] *)
      assert (CONT : forall m1, mem_inv bsegs m1 -> munch [(SPP, SPP + 32); (0xcca10, 0xcca10 + 32); (B, B + 8); (TL, TL + 8)]%Z m m1 -> wmono bsegs m m1 ->
        rw_cells bsegs m1 0xcca10 [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 gb)] ->
        rw_cells bsegs m1 B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
        rw_cells bsegs m1 SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
        rw_cells bsegs m1 TL [C8 tlx; C8 tls; C8 tlc] ->
        evtF bsegs RNG (deq_body_post true B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tls tlc m)
          (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 0xcc970) (Z_to_bv 64 MIN) a2 a3
                   (Z_to_bv 64 tn) (Z_to_bv 64 TL) (Z_to_bv 64 nb) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x357c4) fc None m1 (seg_rom bsegs))).
      { clear MI MU WM GC BC TM TLC. intros m1 MI MU WM GC BC TM TLC.
        zstep. step.                                     (* [comment removed for export] *)
        step. step. zstep. step.                         (* [comment removed for export] *)
        zstep. step.                                     (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].   (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        step. step. step. step.                          (* [comment removed for export] *)
        step. zstep. zstep. zstep.                       (* [comment removed for export] *)
        replace (nb + -1) with (nb - 1) in * by lia.
        apply evtF_done. unfold deq_body_post, aqrec_lt, deq_W, AQ_GCACHE, AQUAR_Q. finish. all: eassumption. }
      step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
      step. step.                                        (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.                   (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K1 by lia. eapply CONT; try eassumption. replace (nxn =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact GC.
      + rewrite ?unsigned_lit in K1 by lia. step.        (* [comment removed for export] *)
        eapply CONT; try eassumption. replace (nxn =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exact GC.
    - pose proof TF as TN1. clear TF. subst tn.
      pose proof (munch_refl (deq_W false B TL) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold deq_W, AQ_GCACHE in MU.
      assert (CONT : forall m1, mem_inv bsegs m1 -> munch [(SPP, SPP + 32); (0xcca10, 0xcca10 + 32); (B, B + 8)]%Z m m1 -> wmono bsegs m m1 ->
        rw_cells bsegs m1 0xcca10 [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 gb)] ->
        rw_cells bsegs m1 B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
        rw_cells bsegs m1 SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
        evtF bsegs RNG (deq_body_post false B TL nxn bsz nb gl gb 0 st1 tf st2 tb cw tls tlc m)
          (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 0xcc970) (Z_to_bv 64 MIN) a2 a3
                   (Z_to_bv 64 0) (Z_to_bv 64 TL) (Z_to_bv 64 nb) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x357c4) fc None m1 (seg_rom bsegs))).
      { clear MI MU WM GC BC TM. intros m1 MI MU WM GC BC TM.
        zstep. step.                                     (* [comment removed for export] *)
        step. step. zstep. step.                         (* [comment removed for export] *)
        zstep. step.                                     (* [comment removed for export] *)
        step. if_lit.                                    (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        step. step.                                      (* [comment removed for export] *)
        step. step. step. step.                          (* [comment removed for export] *)
        step. zstep. zstep. zstep.                       (* [comment removed for export] *)
        replace (nb + -1) with (nb - 1) in * by lia.
        apply evtF_done. unfold deq_body_post, aqrec_lt, deq_W, AQ_GCACHE, AQUAR_Q. finish. all: try eassumption. all: try exact I. }
      step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
      step. step.                                        (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.                   (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K1 by lia. eapply CONT; try eassumption. replace (nxn =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact GC.
      + rewrite ?unsigned_lit in K1 by lia. step.        (* [comment removed for export] *)
        eapply CONT; try eassumption. replace (nxn =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exact GC.
  Qed.

  (* [comment removed for export] *)
  Definition WL (G T : list bq) : list (Z * Z) :=
    ([(SPP, SPP + 32); (AQ_GCACHE, AQ_GCACHE + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (G ++ T))%Z.

  Definition deq_loop_post (G T : list bq) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 tb' : word) m',
      let '(taken, rest, bytes2) := deq_bq G (batches_bytes (map fst G)) MIN in
      ms' = MS (mkR ra (Z_to_bv 64 SPP) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 aqrec_join) fc None m' (seg_rom bsegs)
      /\ munch (WL G T) m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0)); C8 (Z_to_bv 64 bytes2)]
      /\ chain L m' rest 0
      /\ rw_cells bsegs m' SPP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ taken)))); C8 (Z_to_bv 64 (tfirst L (T ++ taken) 0)); C8 (Z_to_bv 64 (tlast L (T ++ taken) 0)); C8 tb']
      /\ chain L m' (T ++ taken) 0
      /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= MIN.

  Lemma deq_bq_go : forall (b : bq) l bytes mn, mn < bytes ->
    deq_bq (b :: l) bytes mn = (let '(taken, rest, bytes') := deq_bq l (bytes - b_size (fst b)) mn in (b :: taken, rest, bytes')).
  Proof. intros b l bytes mn H. cbn [deq_bq]. destruct (Z.ltb_spec mn bytes); [reflexivity| lia]. Qed.
  Lemma deq_bq_stop : forall l bytes mn, ~ mn < bytes -> deq_bq l bytes mn = ([], l, bytes).
  Proof. intros [|b l] bytes mn H; cbn [deq_bq]; [reflexivity|]. destruct (Z.ltb_spec mn bytes); [lia| reflexivity]. Qed.

  Lemma deq_bq_split : forall l bytes mn, (let '(taken, rest, _) := deq_bq l bytes mn in taken ++ rest) = l.
  Proof.
    induction l as [|b l IH]; intros bytes mn; cbn [deq_bq]; [reflexivity|].
    destruct (mn <? bytes); [| reflexivity]. specialize (IH (bytes - b_size (fst b)) mn).
    destruct (deq_bq l (bytes - b_size (fst b)) mn) as [[tk rs] b2]. cbn [app]. rewrite IH. reflexivity.
  Qed.

  Lemma bgeom_num : forall x, bgeom L AQ_GCACHE SPP x ->
    AIMG_HI <= baddr L x /\ baddr L x + Q_BATCH_BYTES <= ATOP /\ (AQ_GCACHE + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= AQ_GCACHE)
    /\ (SPP + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= SPP).
  Proof. intros x H. exact H. Qed.

  Lemma tfirst_range : forall X, Forall (bgeom L AQ_GCACHE SPP) X -> 0 <= tfirst L X 0 < 2^64 /\ (X <> [] -> AIMG_HI <= tfirst L X 0).
  Proof.
    intros [|x X] HF; cbn [tfirst]; [split; [lia| congruence]|].
    pose proof (Forall_inv HF) as (A & B & _). unfold AIMG_HI, Q_BATCH_BYTES in *. split; [lia| intros _; exact A].
  Qed.
  Lemma tlast_range : forall X, Forall (bgeom L AQ_GCACHE SPP) X -> 0 <= tlast L X 0 < 2^64.
  Proof.
    intros X HF. destruct X as [|x X']; [cbn; lia|].
    destruct (tlast_in L (x :: X') 0 ltac:(congruence)) as (z & Hz & ->).
    pose proof (proj1 (Forall_forall _ _) HF z Hz) as (A & B & _). unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
  Qed.

  Lemma deq_loop_spec : forall (d : nat) (G T : list bq) (st1 st2 tb a7 t1 t2 : word) (m : amem),
    d = length G ->
    MIN < batches_bytes (map fst G) ->
    mem_inv bsegs m ->
    rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length G))); C8 (Z_to_bv 64 (tfirst L G 0)); C8 (Z_to_bv 64 (tlast L G 0)); C8 (Z_to_bv 64 (batches_bytes (map fst G)))] ->
    chain L m G 0 ->
    rw_cells bsegs m SPP [C8 st1; C8 (Z_to_bv 64 (tfirst L T 0)); C8 st2; C8 tb] ->
    chain L m T 0 ->
    Forall (bgeom L AQ_GCACHE SPP) (G ++ T) -> Forall (fun x => 0 <= bslot x) (G ++ T) -> base.NoDup (map bslot (G ++ T)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) G -> batches_bytes (map fst G) < 2^56 ->
    Z.of_nat (length (G ++ T)) < 2^40 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (G ++ T) ->
    evtF bsegs RNG (deq_loop_post G T m)
      (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 (tfirst L G 0)) t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
               (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 (tlast L T 0)) (Z_to_bv 64 (Z.of_nat (length G))) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 aqrec_lh) fc None m (seg_rom bsegs)).
  Proof.
    induction d as [|d IH]; intros until m; intros HD GO MI GC CH TM CT GEO SL ND SZ SZS LEN40 RB.
    { exfalso. destruct G; [cbn in GO; clear -GO MIN0; lia| cbn in HD; lia]. }
    destruct G as [|b G']; [cbn in HD; lia|].
    (* [comment removed for export] *)
    destruct (proj1 (chain_cons L _ _ _ _) CH) as [BCELLS CHR]. clear CH.
    destruct BCELLS as (BC & EB & JB & BCNT & BLEN & BRNG). cbn [fst snd] in BC, EB, JB, BCNT, BLEN, BRNG.
    pose proof (bgeom_num b (Forall_inv GEO)) as (GB1 & GB2 & GB3 & GB4).
    pose proof (Forall_inv RB) as RBb. cbv beta in RBb.
    pose proof (Forall_inv SZ) as SZb. cbv beta in SZb.
    assert (GEO' : Forall (bgeom L AQ_GCACHE SPP) G') by (apply Forall_app in GEO as [GEO _]; exact (Forall_inv_tail GEO)).
    assert (GEOT : Forall (bgeom L AQ_GCACHE SPP) T) by (apply Forall_app in GEO as [_ GEO]; exact GEO).
    pose proof (tfirst_range G' GEO') as [NXN NXP]. pose proof (tlast_range (b :: G') ltac:(apply Forall_app in GEO as [GEO _]; exact GEO)) as GL.
    pose proof (batches_bytes_nonneg G' (Forall_inv_tail SZ)) as SZR.
    cbn [map] in SZS, GO. rewrite !batches_bytes_cons in SZS, GO.
    assert (LENG : 0 < Z.of_nat (length (b :: G')) < 2^40 /\ 0 <= Z.of_nat (length T) < 2^40).
    { revert LEN40. clear. rewrite length_app. cbn [length]. intros. lia. }
    unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in GB1, GB2, GB3, GB4.
    fold (baddr L b) in BC, EB, JB. set (B := baddr L b) in *.
    cbn [tfirst] in GC |- *. fold B in GC. fold B.
    (* [comment removed for export] *)
    assert (E1 : Z.of_nat (length (b :: G')) - 1 = Z.of_nat (length G')) by (clear; cbn [length]; lia).
    assert (E2 : (if tfirst L G' 0 =? 0 then 0 else tlast L (b :: G') 0) = tlast L G' 0).
    { destruct G' as [|c G'']; [reflexivity|]. specialize (NXP ltac:(congruence)). unfold AIMG_HI in NXP.
      destruct (Z.eqb_spec (tfirst L (c :: G'') 0) 0); [exfalso; clear -NXP e; lia|]. rewrite tlast_cons_ne by congruence. reflexivity. }
    assert (E3 : b_size (fst b) + batches_bytes (map fst G') - b_size (fst b) = batches_bytes (map fst G')) by (clear; lia).
    assert (E3' : batches_bytes (map fst (b :: G')) - b_size (fst b) = batches_bytes (map fst G')) by (clear; cbn [map]; rewrite batches_bytes_cons; lia).
    atop_facts. unfold AQ_GCACHE, AQUAR_Q in *.
    (* [comment removed for export] *)
    assert (OTH : forall x, In x (G' ++ T) -> bslot x <> bslot b /\ 0 <= bslot x /\ bgeom L AQ_GCACHE SPP x).
    { intros x Hx. split; [| split].
      - apply (nodup_mid bslot [] b (G' ++ T) ND x Hx).
      - eapply (proj1 (Forall_forall _ _) SL). right. exact Hx.
      - eapply (proj1 (Forall_forall _ _) GEO). right. exact Hx. }
    assert (SLb : 0 <= bslot b) by (eapply (proj1 (Forall_forall _ _) SL); left; reflexivity).
    assert (DJB : forall x, In x (G' ++ T) -> baddr L x + 8192 <= B \/ B + 8192 <= baddr L x).
    { intros x Hx. destruct (OTH x Hx) as (N1 & S1 & _). pose proof (baddr_disj L x b N1 S1 SLb) as D. unfold Q_BATCH_BYTES in D. exact D. }
    destruct (list_eq_dec bq_eq_dec T []) as [TNIL|TNE].
    - (* [comment removed for export] *)
      subst T. cbn [tfirst tlast map List.last length Z.of_nat] in TM |- *.
      eapply evtF_cut.
      { eapply (deq_body_spec false B 0 (tfirst L G' 0) (b_size (fst b)) (Z.of_nat (length (b :: G'))) (tlast L (b :: G') 0)
                  (b_size (fst b) + batches_bytes (map fst G')) 0 st1 (Z_to_bv 64 0) st2 tb (Z_to_bv 64 (b_count (fst b))) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
        1: exact MI. 1: exact GC. 1: exact BC. 1: exact TM. 1: reflexivity. 9: exact RBb.
        all: clear -GB1 GB2 GB3 GB4 NXN GL SZb SZR SZS LENG BRNG; unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *; lia. }
      cbv beta. intros ms1 (tb' & m1 & -> & MUc & WMc & MI1 & GC1 & BC1 & TM1 & _). clear MI.
      rewrite E1, E2, E3 in GC1. unfold deq_W, AQ_GCACHE in MUc. unfold AQ_GCACHE in GC1.
      (* [comment removed for export] *)
      assert (REB : forall mf, munch [(SPP, SPP + 32); (0xcca10, 0xcca10 + 32); (B, B + 8)]%Z m mf -> wmono bsegs m mf ->
                rw_cells bsegs mf B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size (fst b))); C8 (Z_to_bv 64 (b_count (fst b)))] ->
                chain L mf G' 0 /\ chain L mf [b] 0).
      { intros mf MUf WMf BCf. split.
        - eapply chain_frame; [exact CHR| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
          destruct (OTH x ltac:(apply in_app_iff; left; exact Hx)) as (_ & _ & Gx). apply bgeom_num in Gx. specialize (DJB x ltac:(apply in_app_iff; left; exact Hx)).
          unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB. lia.
        - pose proof EB as EBf. xport EBf MUf WMf ltac:(clear -BRNG BCNT BLEN GB3 GB4; rewrite length_map, qhdrs_length by exact BLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JB as [jb JBf]. xport JBf MUf WMf ltac:(clear -BRNG GB3 GB4; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst]. fold B.
          split; [exact BCf|]. split; [exact EBf|]. split; [exists jb; exact JBf|]. clear -BCNT BLEN BRNG. tauto. }
      clear BC.
      unfold aqrec_lt. step. if_cases KX; zify_cond KX.          (* [comment removed for export] *)
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        step. step.                                             (* [comment removed for export] *)
        apply evtF_done. unfold deq_loop_post, aqrec_join.
        rewrite deq_bq_go by exact GO. rewrite E3'. rewrite deq_bq_stop by (clear -KX; lia).
        cbn [app length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last]. fold B.
        do 9 eexists. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MUc]. unfold WL, AQ_GCACHE, Q_BATCH_BYTES. rewrite app_nil_r. cbn [map app]. fold B.
                 solve_sub_fpw ltac:(clear; lia). }
        destruct (REB _ MUc WMc BC1) as [CHR1 CHB].
        split; [exact WMc|]. split; [exact MI1|].
        split; [exact GC1|]. split; [exact CHR1|]. split; [exact TM1|]. split; [exact CHB|].
        split; [reflexivity| clear -KX; lia].
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        destruct (REB _ MUc WMc BC1) as [CHR1 CHB].
        rewrite E1. replace (0 + 1) with (Z.of_nat (length [b])) by reflexivity.
        change (Z_to_bv 64 B) with (Z_to_bv 64 (tlast L [b] 0)) at 2.
        eapply evtF_mono.
        { eapply (IH G' [b] st1 st2 tb'); [cbn in HD; clear -HD; lia| exact KX| exact MI1| exact GC1| exact CHR1| exact TM1| exact CHB| ..].
          - exact (Forall_rot _ _ _ _ GEO).
          - exact (Forall_rot _ _ _ _ SL).
          - exact (NoDup_rot _ _ _ ND).
          - exact (Forall_inv_tail SZ).
          - clear -SZS SZb; unfold Q_BATCH_BYTES in SZb; lia.
          - revert LEN40; clear; rewrite !length_app; cbn [length]; intros; lia.
          - exact (Forall_rot _ _ _ _ RB). }
        cbv beta. unfold deq_loop_post, aqrec_join. intros ms' (y0 & y1 & y2 & y4 & y5 & y6 & y7 & tb'' & m' & POST).
        rewrite deq_bq_go by exact GO. rewrite E3'. destruct (deq_bq G' (batches_bytes (map fst G')) MIN) as [[tk rs] b2].
        destruct POST as (-> & MU' & WM' & MI' & GC' & CH' & TM' & CT' & HB2 & HB3).
        cbn [app] in TM', CT' |- *.
        do 9 eexists. split; [reflexivity|].
        split. { eapply (munch_trans_w _ _ _ _ _ _ MUc MU').
                 - unfold WL, Q_BATCH_BYTES. rewrite app_nil_r. cbn [map app]. fold B. solve_sub_fpw ltac:(clear; lia).
                 - unfold WL. apply sub_fp_incl. intros iv Hiv. apply in_app_iff in Hiv. apply in_app_iff. destruct Hiv as [Hiv|Hiv]; [left; exact Hiv| right].
                   rewrite app_nil_r. rewrite map_app in Hiv. cbn [map] in Hiv |- *. apply in_app_iff in Hiv. destruct Hiv as [Hiv|[Hiv|[]]]; [right; exact Hiv| left; exact Hiv]. }
        split; [eapply wmono_trans; [exact WMc| exact WM']|]. split; [exact MI'|].
        split; [exact GC'|]. split; [exact CH'|]. split; [exact TM'|]. split; [exact CT'|]. split; [exact HB2| exact HB3].
    - (* [comment removed for export] *)
      destruct (exists_last TNE) as [T0 [tl ET]].
      pose proof CT as CT'. rewrite ET in CT'. destruct (proj1 (chain_app L _ _ _ _) CT') as [CT0 CTL]. clear CT CT'. cbn [tfirst] in CT0.
      destruct (proj1 (chain_cons L _ _ _ _) CTL) as [TLCELLS _]. clear CTL.
      destruct TLCELLS as (TLC & ETL & JTL & TCNT & TLEN & TRNG). cbn [fst snd tfirst] in TLC, ETL, JTL, TCNT, TLEN, TRNG.
      assert (INTL : In tl (G' ++ T)) by (rewrite ET; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
      destruct (OTH tl INTL) as (NTL & STL & GTL). apply bgeom_num in GTL. destruct GTL as (GT1 & GT2 & GT3 & GT4).
      pose proof (DJB tl INTL) as DBT.
      assert (RTL : rng RNG (baddr L tl) Q_BATCH_BYTES) by (eapply (proj1 (Forall_forall _ _) RB); right; exact INTL).
      unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in GT1, GT2, GT3, GT4.
      fold (baddr L tl) in TLC, ETL, JTL. set (TL := baddr L tl) in *.
      replace (tlast L T 0) with TL by (rewrite ET, tlast_app1; reflexivity).
      assert (OTT : forall x, In x (G' ++ T0) -> bslot x <> bslot tl).
      { intros x Hx. apply (nodup_mid bslot (b :: G' ++ T0) tl [] ); [| apply in_app_iff; left; right; exact Hx].
        cbn [app]. rewrite ET in ND. cbn [app] in ND. rewrite <- app_assoc. exact ND. }
      assert (DJT : forall x, In x (G' ++ T0) -> baddr L x + 8192 <= TL \/ TL + 8192 <= baddr L x).
      { intros x Hx. assert (Hx' : In x (G' ++ T)).
        { rewrite ET. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; apply in_app_iff; left; exact Hx]. }
        destruct (OTH x Hx') as (_ & S1 & _).
        pose proof (baddr_disj L x tl (OTT x Hx) S1 STL) as D. unfold Q_BATCH_BYTES in D. exact D. }
      assert (LENT : 0 < Z.of_nat (length T)) by (rewrite ET; clear; rewrite length_app; cbn [length]; lia).
      eapply evtF_cut.
      { eapply (deq_body_spec true B TL (tfirst L G' 0) (b_size (fst b)) (Z.of_nat (length (b :: G'))) (tlast L (b :: G') 0)
                  (b_size (fst b) + batches_bytes (map fst G')) (Z.of_nat (length T)) st1 (Z_to_bv 64 (tfirst L T 0)) st2 tb
                  (Z_to_bv 64 (b_count (fst b))) (Z_to_bv 64 0) (Z_to_bv 64 (b_size (fst tl))) (Z_to_bv 64 (b_count (fst tl)))).
        1: exact MI. 1: exact GC. 1: exact BC. 1: exact TM.
        1: { split; [exact TLC|]. split; [exact LENT| split; [| split; [| split; [clear -DBT; unfold Q_BATCH_BYTES; lia| unfold Q_BATCH_BYTES; exact RTL]]]].
             - clear -GT1; unfold AIMG_HI; lia.
             - clear -GT2; unfold Q_BATCH_BYTES; lia. }
        9: exact RBb.
        all: clear -GB1 GB2 GB3 GB4 NXN GL SZb SZR SZS LENG BRNG; unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *; lia. }
      cbv beta. intros ms1 (tb' & m1 & -> & MUc & WMc & MI1 & GC1 & BC1 & TM1 & TLC1). clear MI.
      rewrite E1, E2, E3 in GC1. unfold deq_W, AQ_GCACHE in MUc. unfold AQ_GCACHE in GC1.
      (* [comment removed for export] *)
      assert (REB : forall mf, munch [(SPP, SPP + 32); (0xcca10, 0xcca10 + 32); (B, B + 8); (TL, TL + 8)]%Z m mf -> wmono bsegs m mf ->
                rw_cells bsegs mf B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size (fst b))); C8 (Z_to_bv 64 (b_count (fst b)))] ->
                rw_cells bsegs mf TL [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 (b_size (fst tl))); C8 (Z_to_bv 64 (b_count (fst tl)))] ->
                chain L mf G' 0 /\ chain L mf (T ++ [b]) 0).
      { intros mf MUf WMf BCf TLCf. split.
        - eapply chain_frame; [exact CHR| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
          destruct (OTH x ltac:(apply in_app_iff; left; exact Hx)) as (Nx & Sx & Gx). apply bgeom_num in Gx. specialize (DJB x ltac:(apply in_app_iff; left; exact Hx)).
          pose proof (DJT x ltac:(apply in_app_iff; left; exact Hx)) as DxT.
          unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB DxT. lia.
        - pose proof EB as EBf. xport EBf MUf WMf ltac:(clear -BRNG BCNT BLEN GB3 GB4 DBT; rewrite length_map, qhdrs_length by exact BLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JB as [jb JBf]. xport JBf MUf WMf ltac:(clear -BRNG GB3 GB4 DBT; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          pose proof ETL as ETf. xport ETf MUf WMf ltac:(clear -TRNG TCNT TLEN GT3 GT4 DBT; rewrite length_map, qhdrs_length by exact TLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JTL as [jt JTf]. xport JTf MUf WMf ltac:(clear -TRNG GT3 GT4 DBT; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          rewrite ET. apply (proj2 (chain_app L _ _ _ _)). split.
          + apply (proj2 (chain_app L _ _ _ _)). cbn [tfirst]. fold TL. fold B. split.
            * eapply chain_frame; [exact CT0| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
              assert (HxT : In x (G' ++ T)) by (rewrite ET; apply in_app_iff; right; apply in_app_iff; left; exact Hx).
              destruct (OTH x HxT) as (_ & _ & Gx). apply bgeom_num in Gx.
              specialize (DJB x HxT). specialize (DJT x ltac:(apply in_app_iff; right; exact Hx)).
              unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB DJT. lia.
            * apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst fst snd]. fold TL. fold B.
              split; [exact TLCf|]. split; [exact ETf|]. split; [exists jt; exact JTf|]. clear -TCNT TLEN TRNG. tauto.
          + apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst]. fold B.
            split; [exact BCf|]. split; [exact EBf|]. split; [exists jb; exact JBf|]. clear -BCNT BLEN BRNG. tauto. }
      clear BC TLC.
      assert (TF : tfirst L (T ++ [b]) 0 = tfirst L T 0) by (apply tfirst_app; exact TNE).
      assert (TLN : Z.of_nat (length (T ++ [b])) = Z.of_nat (length T) + 1) by (clear; rewrite length_app; cbn [length]; lia).
      (* [comment removed for export] *)
      assert (SUB : sub_fp [(SPP, SPP + 32); (0xcca10, 0xcca10 + 32); (B, B + 8); (TL, TL + 8)]%Z (WL (b :: G') T)).
      { unfold WL, Q_BATCH_BYTES, AQ_GCACHE. apply sub_fp_by_incl'.
        constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; apply in_map_iff; exists b; split; [reflexivity| left; reflexivity]| cbn; fold B; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; apply in_map_iff; exists tl; split; [reflexivity| right; exact INTL]| cbn; fold TL; clear; lia]|].
        constructor. }
      unfold aqrec_lt. step. if_cases KX; zify_cond KX.          (* [comment removed for export] *)
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        step. step.                                             (* [comment removed for export] *)
        apply evtF_done. unfold deq_loop_post, aqrec_join.
        rewrite deq_bq_go by exact GO. rewrite E3'. rewrite deq_bq_stop by (clear -KX; lia).
        rewrite TF, TLN, tlast_app1. fold B.
        cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last].
        do 9 eexists. split; [reflexivity|].
        split; [eapply munch_weaken; [exact SUB| exact MUc]|].
        destruct (REB _ MUc WMc BC1 TLC1) as [CHR1 CHB].
        split; [exact WMc|]. split; [exact MI1|].
        split; [exact GC1|]. split; [exact CHR1|]. split; [exact TM1|]. split; [exact CHB|].
        split; [reflexivity| clear -KX; lia].
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        destruct (REB _ MUc WMc BC1 TLC1) as [CHR1 CHB].
        rewrite E1. rewrite <- TLN. rewrite <- TF in TM1.
        replace (Z_to_bv 64 B) with (Z_to_bv 64 (tlast L (T ++ [b]) 0)) by (rewrite tlast_app1; reflexivity).
        eapply evtF_mono.
        { eapply (IH G' (T ++ [b]) st1 st2 tb'); [cbn in HD; clear -HD; lia| exact KX| exact MI1| exact GC1| exact CHR1| exact TM1| exact CHB| ..].
          - exact (Forall_rot _ _ _ _ GEO).
          - exact (Forall_rot _ _ _ _ SL).
          - exact (NoDup_rot _ _ _ ND).
          - exact (Forall_inv_tail SZ).
          - clear -SZS SZb; unfold Q_BATCH_BYTES in SZb; lia.
          - revert LEN40; clear; rewrite !length_app; cbn [length]; intros; lia.
          - exact (Forall_rot _ _ _ _ RB). }
        cbv beta. unfold deq_loop_post, aqrec_join. intros ms' (y0 & y1 & y2 & y4 & y5 & y6 & y7 & tb'' & m' & POST).
        rewrite deq_bq_go by exact GO. rewrite E3'. destruct (deq_bq G' (batches_bytes (map fst G')) MIN) as [[tk rs] b2].
        destruct POST as (-> & MU' & WM' & MI' & GC' & CH' & TM' & CT' & HB2 & HB3).
        rewrite <- app_assoc in TM', CT'. cbn [app] in TM', CT'.
        do 9 eexists. split; [reflexivity|].
        split. { eapply (munch_trans_w _ _ _ _ _ _ MUc MU'); [exact SUB|].
                 unfold WL. apply sub_fp_incl. intros iv Hiv. apply in_app_iff in Hiv. apply in_app_iff. destruct Hiv as [Hiv|Hiv]; [left; exact Hiv| right].
                 rewrite !map_app in Hiv. rewrite map_app. cbn [map] in Hiv |- *. apply in_app_iff in Hiv. rewrite in_app_iff.
                 destruct Hiv as [Hiv|Hiv]; [left; right; exact Hiv|]. apply in_app_iff in Hiv. destruct Hiv as [Hiv|[Hiv|[]]]; [right; exact Hiv| left; left; exact Hiv]. }
        split; [eapply wmono_trans; [exact WMc| exact WM']|]. split; [exact MI'|].
        split; [exact GC'|]. split; [exact CH'|]. split; [exact TM'|]. split; [exact CT'|]. split; [exact HB2| exact HB3].
  Qed.
End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disj_objs_below : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> A + n <= AIMG_HI ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. right. unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
Qed.

Lemma bgeom_baddr : forall L LST TMP x y, baddr L y = baddr L x -> bgeom L LST TMP y -> bgeom L LST TMP x.
Proof. intros L LST TMP x y E H. unfold bgeom in *. rewrite <- E. exact H. Qed.

(* [comment removed for export] *)
Definition WQ (L : alayout) (sp : Z) (X : list bq) : list (Z * Z) :=
  ((sp - 96, sp) :: (AQ_MUTEX, AQ_MUTEX + 4) :: (AQ_GCACHE, AQ_GCACHE + 32) :: map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z.

Theorem qrec_front : qrec_front_stmt.
Proof.
  intros L RNG X bytes min_size lo. intros until m.
  intros ST CEIL LO SP47 MI -> -> MIN0 MX GC CH GEO SL ND SZ BY BY56 LEN40 RIMG RSTK RB.
  atop_facts. unfold AQUAR_Q, AQ_MUTEX, AQ_GCACHE in *.
  word_range sp SPR.
  pose proof (batches_bytes_lb (map fst X) ltac:(rewrite Forall_map; exact SZ)) as BYLB. rewrite length_map, <- BY in BYLB. unfold Q_BATCH_BYTES in BYLB.
  change (@length (abatch * qbatchc) X) with (@length bq X) in BYLB.
  assert (RT : rng RNG (bv_unsigned sp + -80) 32) by (eapply (rng_sub _ _ _ _ _ RSTK); clear -LO SPR; lia).
  assert (RG : rng RNG 0xcca10 32) by (eapply (rng_sub _ _ _ _ _ RIMG); clear; lia).
  assert (RMX : rng RNG 0xcca08 4) by (eapply (rng_sub _ _ _ _ _ RIMG); clear; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT2 : forall (m2 : amem) (rest T : list bq) (bytes2 : Z) (tb' rax t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a4 a5 a6 a7 u3 u4 u5 u6 : word),
    qrec_fun X bytes min_size = (rest, T, bytes2) ->
    mem_inv bsegs m2 -> boxed (munch (WQ L (bv_unsigned sp) X) m m2) -> wmono bsegs m m2 -> stk bsegs m2 lo (bv_unsigned sp + -80) ->
    rw_cells bsegs m2 0xcca08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs m2 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tb'] ->
    rw_cells bsegs m2 0xcca10 [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0)); C8 (Z_to_bv 64 bytes2)] ->
    chain L m2 rest 0 -> chain L m2 T 0 -> bytes2 = batches_bytes (map fst rest) -> bytes2 <= min_size ->
    Forall (bgeom L 0xcca10 (bv_unsigned sp + -80)) (rest ++ T) ->
    evtF bsegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0xcc970) (Z_to_bv 64 min_size) a2 a3 a4 a5 a6 a7
               xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 aqrec_join) fc None m2 (seg_rom bsegs))).
  { clear MI MU WM ST MX GC CH. intros m2 rest T bytes2 tb' rax x1 y1 y2 xs0 xs1 xs2 xs3 xs4 y4 y5 y6 y7 u3 u4 u5 u6 QF MI MUP WM ST MX FRS TM GC CHR CT HB2 HB3 GEO2.
    pose proof (munch_refl [(0xcca08, 0xcca08 + 4)]%Z m2) as MU.
    pose proof (wmono_refl bsegs m2) as WM2.
    unfold aqrec_join.
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. step.                               (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (CHR' : chain L mf rest 0) by (eapply chain_frame; [exact CHR| exact MU| exact WM2|]; apply Forall_forall; intros x Hx;
        pose proof (proj1 (Forall_forall _ _) GEO2 x ltac:(apply in_app_iff; left; exact Hx)) as (Gx & _); unfold AIMG_HI in Gx; cbn; clear -Gx; lia);
      assert (CT' : chain L mf T 0) by (eapply chain_frame; [exact CT| exact MU| exact WM2|]; apply Forall_forall; intros x Hx;
        pose proof (proj1 (Forall_forall _ _) GEO2 x ltac:(apply in_app_iff; right; exact Hx)) as (Gx & _); unfold AIMG_HI in Gx; cbn; clear -Gx; lia)
    end.
    apply evtF_done. unfold qrec_front_post. rewrite QF. unbox MUP.
    do 19 eexists. split; [reflexivity|].
    split; [eapply (munch_trans_w _ _ _ _ _ _ MUP MU); [intros z Hz; exact Hz| unfold WQ; solve_sub_fpw ltac:(clear; lia)]|].
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact TM|]. split; [exact FRS|]. split; [exact MX|].
    split; [exact GC|]. split; [exact CHR'|]. split; [exact CT'|]. split; [exact HB2| exact HB3]. }
  (* [comment removed for export] *)
  assert (CONT1 : forall (m1 : amem) (G T0 : list bq) (tb rax t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a4 a5 a7 u3 u4 u5 u6 : word),
    (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) = (G, T0) ->
    bytes - Q_BATCH_BYTES * Z.of_nat (length T0) = batches_bytes (map fst G) ->
    mem_inv bsegs m1 -> boxed (munch (WQ L (bv_unsigned sp) X) m m1) -> wmono bsegs m m1 -> stk bsegs m1 lo (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 0xcca08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (Z.of_nat (length T0))); C8 (Z_to_bv 64 (tfirst L T0 0)); C8 (Z_to_bv 64 (tlast L T0 0)); C8 tb] ->
    rw_cells bsegs m1 0xcca10 [C8 (Z_to_bv 64 (Z.of_nat (length G))); C8 (Z_to_bv 64 (tfirst L G 0)); C8 (Z_to_bv 64 (tlast L G 0)); C8 (Z_to_bv 64 (batches_bytes (map fst G)))] ->
    chain L m1 G 0 -> chain L m1 T0 0 ->
    Forall (bgeom L 0xcca10 (bv_unsigned sp + -80)) (G ++ T0) -> Forall (fun x => 0 <= bslot x) (G ++ T0) -> base.NoDup (map bslot (G ++ T0)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) G -> batches_bytes (map fst G) < 2^56 -> Z.of_nat (length (G ++ T0)) < 2^40 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (G ++ T0) ->
    (forall x, In x (G ++ T0) -> exists y, In y X /\ baddr L y = baddr L x) ->
    evtF bsegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0xcc970) (Z_to_bv 64 min_size) a2 a3 a4 a5
               (Z_to_bv 64 (Z.of_nat (length G))) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x35770) fc None m1 (seg_rom bsegs))).
  { clear MI MU WM ST MX GC CH. intros m1 G T0 tb rax x1 y1 y2 xs0 xs1 xs2 xs3 xs4 y4 y5 y7 u3 u4 u5 u6 QF HBY MI MUP WM ST MX FRS TM GC CHR CT GEO1 SL1 ND1 SZ1 SZS1 LEN1 RB1 INX.
    pose proof (batches_bytes_nonneg G SZ1) as GB0.
    pose proof (tfirst_range L (bv_unsigned sp + -80) G ltac:(apply Forall_app in GEO1 as [G1 _]; exact G1)) as [TF0 _].
    pose proof (tlast_range L (bv_unsigned sp + -80) T0 ltac:(apply Forall_app in GEO1 as [_ G1]; exact G1)) as TL0.
    assert (LENS : 0 <= Z.of_nat (length G) < 2^40 /\ 0 <= Z.of_nat (length T0) < 2^40) by (revert LEN1; clear; rewrite length_app; intros; lia).
    step. step. step.                          (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.           (* [comment removed for export] *)
    - rewrite ?Z.mod_small, ?unsigned_lit in KL by (clear -MIN0 GB0 SZS1; lia).
      eapply (CONT2 m1 G T0 (batches_bytes (map fst G)) tb); try eassumption.
      + unfold qrec_fun. rewrite QF, HBY, deq_bq_stop by (clear -KL; lia). rewrite app_nil_r. reflexivity.
      + reflexivity.
    - rewrite ?Z.mod_small, ?unsigned_lit in KL by (clear -MIN0 GB0 SZS1; lia).
      step. step.                              (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply deq_loop_spec with (d := length G) (G := G) (T := T0); [..| reflexivity| exact KL| exact MI| exact GC| exact CHR| exact TM| exact CT
          | exact GEO1| exact SL1| exact ND1| exact SZ1| exact SZS1| exact LEN1| exact RB1].
        all: try assumption. all: atop_facts; clear -CEIL LO SP47 SPR MIN0; lia. }
      cbv beta. unfold deq_loop_post. intros ms2 (z0 & z1 & z2 & z4 & z5 & z6 & z7 & tb' & m2 & POST).
      pose proof (deq_bq_split G (batches_bytes (map fst G)) min_size) as SPLIT.
      destruct (deq_bq G (batches_bytes (map fst G)) min_size) as [[tk rs] b2] eqn:DQ.
      destruct POST as (-> & MU' & WM' & MI' & GC' & CH' & TM' & CT' & HB2 & HB3). clear MI.
      assert (GEO2 : Forall (bgeom L 0xcca10 (bv_unsigned sp + -80)) (rs ++ T0 ++ tk)).
      { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) GEO1). rewrite <- SPLIT. rewrite <- app_assoc. apply in_app_iff in Hx. apply in_app_iff.
        destruct Hx as [Hx|Hx]; [right; apply in_app_iff; left; exact Hx|]. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [right; apply in_app_iff; right; exact Hx| left; exact Hx]. }
      (* [comment removed for export] *)
      xport MX MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear -LO CEIL; lia| split; [clear; lia| eapply disj_objs_below; [exact GEO1| unfold AIMG_HI; clear; lia]]]).
      xport FRS MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_above; [exact GEO1| atop_facts; clear -LO CEIL; lia]]]).
      xport ST MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_above; [exact GEO1| atop_facts; clear -LO CEIL; lia]]]).
      unbox MUP.
      eapply (CONT2 m2 rs (T0 ++ tk) b2 tb'); try eassumption.
      + unfold qrec_fun. rewrite QF, HBY, DQ. reflexivity.
      + apply Box. eapply (munch_trans_w _ _ _ _ _ _ MUP MU'); [intros z Hz; exact Hz|].
        unfold WL, WQ, AQ_GCACHE, AQ_MUTEX. cbn [app]. apply sub_fp_by_incl'.
        constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (x & <- & Hx). destruct (INX x Hx) as (y & Hy & EY).
        apply Exists_exists. eexists. split; [right; right; right; apply in_map_iff; exists y; split; [reflexivity| exact Hy]| cbn; rewrite EY; clear; lia].
      + eapply wmono_trans; [exact WM| exact WM']. }
  (* [comment removed for export] *)
  carve_frame 80%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  do 4 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step.                    (* [comment removed for export] *)
  apply (rw_C1x4_to_C4 _ _ 0 1 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 1) with 256 in MX.
  amo_step. lits.                              (* [comment removed for export] *)
  do 4 zstep.                                  (* [comment removed for export] *)
  amo_step.                                    (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. if_lit.                         (* [comment removed for export] *)
  apply (rw_C4_to_C1x4 _ _ 1 1 ltac:(lia) ltac:(lia)) in MX.
  step. step. zstep.                           (* [comment removed for export] *)
  setreg 14%Z (Z_to_bv 64 (8192 * Z.of_nat (length X))) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); try apply Z_to_bv_eqm; clear -LEN40; Z.div_mod_to_equations; lia).
  step. if_cases KC; zify_cond KC.             (* [comment removed for export] *)
  { exfalso. rewrite ?Z.mod_small, ?unsigned_lit in KC by (clear -BY56 BYLB LEN40; lia). clear -KC BYLB. lia. }
  clear KC.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR.
  destruct FR as [TM FRS].
  lazymatch type of FRS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -48) in FRS by (cbn; clear; lia) end.
  (* [comment removed for export] *)
  assert (SL' : Forall (fun x => 0 <= bslot x) (X ++ [])) by (rewrite app_nil_r; exact SL).
  assert (INX0 : forall x, In x (X ++ []) -> exists y, In y X /\ baddr L y = baddr L x) by (intros x Hx; rewrite app_nil_r in Hx; exists x; split; [exact Hx| reflexivity]).
  step. if_cases KM1; zify_cond KM1.           (* [comment removed for export] *)
  - rewrite ?Z.mod_small, ?unsigned_lit in KM1 by (clear -BY56 BYLB LEN40; lia).
    eapply (CONT1 _ X [] (Z_to_bv 64 0)); try eassumption.
    + unfold qrec_mergeb, Q_BATCH_BYTES. destruct (Z.ltb_spec (8192 * Z.of_nat (length X)) bytes) as [Hl|Hl]; [exfalso; clear -KM1 Hl; lia|]. reflexivity.
    + cbn [length]. rewrite <- BY. clear; lia.
    + apply Box. eapply munch_weaken; [| exact MU]. unfold WQ, AQ_MUTEX, AQ_GCACHE. solve_sub_fpw ltac:(clear; lia).
    + rewrite <- BY. exact GC.
    + eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
      pose proof (proj1 (Forall_forall _ _) GEO x Hx) as (G1 & G2 & G3 & G4). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
    + apply chain_nil.
    + rewrite app_nil_r. exact GEO.
    + rewrite app_nil_r. exact ND.
    + rewrite <- BY. exact BY56.
    + rewrite app_nil_r. exact LEN40.
    + rewrite app_nil_r. exact RB.
  - rewrite ?Z.mod_small, ?unsigned_lit in KM1 by (clear -BY56 BYLB LEN40; lia).
    step. step. zstep. zstep.                  (* [comment removed for export] *)
    step. if_cases KM2; zify_cond KM2.         (* [comment removed for export] *)
    + rewrite ?Z.mod_small, ?unsigned_lit in KM2 by (clear -BY56 BYLB LEN40; lia).
      eapply (CONT1 _ X [] (Z_to_bv 64 0)); try eassumption.
      * unfold qrec_mergeb, Q_BATCH_BYTES. destruct (Z.ltb_spec (bytes * 100) (8192 * Z.of_nat (length X) * 200)) as [Hl|Hl]; [exfalso; clear -KM2 Hl; lia|].
        rewrite andb_false_r. reflexivity.
      * cbn [length]. rewrite <- BY. clear; lia.
      * apply Box. eapply munch_weaken; [| exact MU]. unfold WQ, AQ_MUTEX, AQ_GCACHE. solve_sub_fpw ltac:(clear; lia).
      * rewrite <- BY. exact GC.
      * eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
        pose proof (proj1 (Forall_forall _ _) GEO x Hx) as (G1 & G2 & G3 & G4). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
      * apply chain_nil.
      * rewrite app_nil_r. exact GEO.
      * rewrite app_nil_r. exact ND.
      * rewrite <- BY. exact BY56.
      * rewrite app_nil_r. exact LEN40.
      * rewrite app_nil_r. exact RB.
    + rewrite ?Z.mod_small, ?unsigned_lit in KM2 by (clear -BY56 BYLB LEN40; lia).
      (* [comment removed for export] *)
      do 7 zstep.                              (* [comment removed for export] *)
      step.                                    (* [comment removed for export] *)
      destruct X as [|cur R]; [exfalso; cbn [length Z.of_nat] in KM1, KM2; clear -KM1 KM2; lia|].
      eapply evtF_cut.
      { eapply (amerge_spec L RNG 0xcca10 (bv_unsigned sp + -80) bytes 0 0 0 lo (cur :: R) []);
          rewrite ?unsigned_lit by (clear -SPR LO CEIL; lia); try eassumption; try reflexivity; try apply chain_nil; try (rewrite app_nil_r; eassumption).
        all: try (clear -CEIL LO SP47 SPR BY56 BYLB LEN40 MIN0; atop_facts; cbn [length]; lia).
        all: try (rewrite <- BY; clear -BY56; lia).
        - eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
          pose proof (proj1 (Forall_forall _ _) GEO x Hx) as (G1 & G2 & G3 & G4). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
        - unfold Q_BATCH_BYTES. clear -LEN40. lia.
        - eapply (rng_sub _ _ _ _ _ RSTK); clear -LO CEIL SPR; lia. }
      cbv beta. unfold amerge_post. cbn [amerge_fun].
      destruct (merge_bq cur R) as [l e] eqn:MB.
      intros ms1 (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m1 & -> & MU' & WM' & MI' & ST' & LS' & CH' & TM' & CT').
      rewrite ?unsigned_lit in MU' by (clear -SPR LO CEIL; lia). rewrite ?unsigned_lit in ST' by (clear -SPR LO CEIL; lia).
      replace (ret_pc (Z_to_bv 64 0x3575c)) with (Z_to_bv 64 0x3575c) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      clear MI. rewrite app_nil_r in MU'. cbn [app] in TM', CT'.
      pose proof (merge_bq_baddr_in L R cur) as INX1. rewrite MB in INX1. cbn [fst snd] in INX1.
      assert (GEO1 : Forall (bgeom L 0xcca10 (bv_unsigned sp + -80)) (l ++ e)).
      { apply Forall_forall. intros x Hx. destruct (INX1 x Hx) as (y & Hy & EY). eapply bgeom_baddr; [exact EY|]. exact (proj1 (Forall_forall _ _) GEO y Hy). }
      xport MX MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -LO CEIL; lia| split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_below; [exact GEO| unfold AIMG_HI; clear; lia]]]]).
      xport FRS MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| split; [clear; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -LO CEIL; lia]]]]).
      pose proof (merge_bq_bytes R cur) as MBY. rewrite MB in MBY. cbn [fst snd] in MBY. rewrite <- BY in MBY.
      replace (bytes - Q_BATCH_BYTES * Z.of_nat (length e)) with (batches_bytes (map fst l)) in LS' by (clear -MBY; lia).
      replace (tfirst L (cur :: R) 0) with (tfirst L l 0) in LS' by (pose proof (merge_bq_first L R cur 0) as E1; rewrite MB in E1; cbn [fst] in E1; rewrite E1; reflexivity).
      do 4 zstep.                              (* [comment removed for export] *)
      step.                                    (* [comment removed for export] *)
      eapply (CONT1 m1 l e); try eassumption.
      * unfold qrec_mergeb, Q_BATCH_BYTES. cbn [amerge_fun].
        destruct (Z.ltb_spec (8192 * Z.of_nat (length (cur :: R))) bytes) as [Hl|Hl]; [| exfalso; clear -KM1 Hl; lia].
        destruct (Z.ltb_spec (bytes * 100) (8192 * Z.of_nat (length (cur :: R)) * 200)) as [Hl2|Hl2]; [| exfalso; clear -KM2 Hl2; lia].
        cbn [andb]. exact MB.
      * clear -MBY; lia.
      * apply Box. eapply (munch_trans_w _ _ _ _ _ _ MU MU'); unfold WQ, AQ_MUTEX, AQ_GCACHE, Q_BATCH_BYTES; cbn [app].
        -- solve_sub_fpw ltac:(clear; lia).
        -- apply sub_fp_by_incl'.
           constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
           constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|].
           constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
           apply Forall_forall. intros iv Hiv. apply Exists_exists. exists iv. split; [right; right; right; exact Hiv| clear; lia].
      * eapply wmono_trans; [exact WM| exact WM'].
      * apply Forall_forall. intros x Hx. destruct (INX1 x Hx) as (y & Hy & EY). rewrite <- (baddr_inj L _ _ EY). exact (proj1 (Forall_forall _ _) SL y Hy).
      * refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND). pose proof (merge_bq_slots R cur) as P. rewrite MB in P. cbn [fst snd] in P.
        apply Permutation_sym. exact P.
      * pose proof (merge_bq_sizes R cur SZ) as S1. rewrite MB in S1. cbn [fst snd] in S1. apply Forall_app in S1 as [S1 _]. exact S1.
      * clear -MBY BY56. unfold Q_BATCH_BYTES in MBY. lia.
      * pose proof (merge_bq_length R cur) as L1. rewrite MB in L1. cbn [fst snd] in L1. rewrite L1. exact LEN40.
      * apply Forall_forall. intros x Hx. destruct (INX1 x Hx) as (y & Hy & EY). rewrite <- EY. exact (proj1 (Forall_forall _ _) RB y Hy).
Qed.

End CANSEC1.
