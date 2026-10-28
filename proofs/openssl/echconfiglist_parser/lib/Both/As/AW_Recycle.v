(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts2 AsAtomics AsDepotInv AllocWalkKit AW_IAInit AW_MergeBatches.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac litx := repeat match goal with
  | |- context [Z_to_bv 64 (bv_swrap ?n ?x)] => let v := eval vm_compute in (bv_swrap n x) in change (bv_swrap n x) with v
  | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v
  | |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
  | |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v
  | |- context [Z_to_bv 64 (Z.shiftr ?x ?y)] => let v := eval vm_compute in (Z.shiftr x y) in change (Z.shiftr x y) with v
  | |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.shiftl x y) in change (Z.shiftl x y) with v
  | |- context [Z_to_bv 64 (?x * ?y)] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (x * y) in change (x * y) with v
  | |- context [Z_to_bv 64 (?x + ?y)] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (x + y) in change (x + y) with v
  end.
(* [comment removed for export] *)
Ltac bytes_eq := cbn; repeat (first [reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsplit (g : qcache) (min_size : Z) : option (qcache * list qbatch * list qbatch) :=
  let overhead := zlen (qc_list g) * kBatchSize in
  if qc_bytes g <? overhead then None else
  let merged : option (qcache * list qbatch) :=
    if (overhead <? qc_bytes g) && (qc_bytes g * 100 <? overhead * 200)
    then match merge_batches g with None => None | Some (g', ex, _) => Some (g', ex) end
    else Some (g, []) in
  match merged with
  | None => None
  | Some (g1, extracted) =>
    match pop_while (S (length (qc_list g1))) (qc_list g1) (qc_bytes g1) min_size [] with
    | None => None
    | Some (l2, bytes2, rpopped) => Some (mkQC l2 bytes2, extracted, rpopped)
    end
  end.

Lemma quarantine_recycle_rsplit : forall st min_size,
  quarantine_recycle st min_size
  = match rsplit (as_gq st) min_size with
    | None => None
    | Some (g2, extracted, rpopped) =>
        match do_recycle (set_gq st g2) (extracted ++ rev rpopped) [] with
        | None => None
        | Some (st2, racc) => Some (st2, rev racc)
        end
    end.
Proof.
  intros st min_size. unfold quarantine_recycle, rsplit.
  destruct (qc_bytes (as_gq st) <? zlen (qc_list (as_gq st)) * kBatchSize); [reflexivity|].
  destruct ((zlen (qc_list (as_gq st)) * kBatchSize <? qc_bytes (as_gq st)) && (qc_bytes (as_gq st) * 100 <? zlen (qc_list (as_gq st)) * kBatchSize * 200)).
  - destruct (merge_batches (as_gq st)) as [[[g' ex] xb]|]; [| reflexivity].
    destruct (pop_while (S (length (qc_list g'))) (qc_list g') (qc_bytes g') min_size []) as [[[l2 b2] rp]|]; reflexivity.
  - destruct (pop_while (S (length (qc_list (as_gq st)))) (qc_list (as_gq st)) (qc_bytes (as_gq st)) min_size []) as [[[l2 b2] rp]|]; reflexivity.
Qed.

Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. intros l1 l2. induction l1 as [|b r IH]; [reflexivity|]. cbn [app]. rewrite !bsum_cons, IH. lia. Qed.
Lemma bsum_nil : bsum [] = 0. Proof. reflexivity. Qed.
Lemma bsum_rev : forall l, bsum (rev l) = bsum l.
Proof. intros l. induction l as [|b r IH]; [reflexivity|]. cbn [rev]. rewrite bsum_app, !bsum_cons, bsum_nil, IH. lia. Qed.
Lemma zlen_app' : forall (l1 l2 : list qbatch), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros l1 l2. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_rev' : forall (l : list qbatch), zlen (rev l) = zlen l.
Proof. intros l. unfold zlen. rewrite length_rev. reflexivity. Qed.

(* [comment removed for export] *)
Lemma merge_batches_aux_bsum : forall fuel cur rest rdone rex xb l' ex xb',
  merge_batches_aux fuel cur rest rdone rex xb = Some (l', ex, xb') ->
  bsum l' + xb' = bsum rdone + qb_size cur + bsum rest + xb /\ xb' - xb = kBatchSize * (zlen ex - zlen rex)
  /\ (Forall (fun b => qb_size b = kBatchSize) rex -> Forall (fun b => qb_size b = kBatchSize) ex).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb l' ex xb' H; [discriminate H|].
  cbn [merge_batches_aux] in H. destruct rest as [|nx rest'].
  - injection H as <- <- <-. rewrite bsum_app, bsum_rev, bsum_cons, !bsum_nil, zlen_rev'. split; [lia|]. split; [lia|].
    intros F. apply Forall_rev. exact F.
  - destruct (qb_count cur + qb_count nx <=? kBatchCount).
    + destruct (qb_size cur <? kBatchSize); [discriminate H|].
      apply IH in H. cbn [qb_size] in H. rewrite zlen_cons' in H. rewrite bsum_cons.
      destruct H as (H1 & H2 & H3). split; [lia|]. split; [lia|]. intros F. apply H3. constructor; [reflexivity| exact F].
    + apply IH in H. rewrite bsum_cons in H. rewrite bsum_cons. destruct H as (H1 & H2 & H3). split; [lia|]. split; [lia| exact H3].
Qed.
Lemma merge_batches_bsum : forall l qb l' qb' ex xb,
  merge_batches (mkQC l qb) = Some (mkQC l' qb', ex, xb) ->
  bsum l' + xb = bsum l /\ qb' = qb - xb /\ xb = kBatchSize * zlen ex /\ Forall (fun b => qb_size b = kBatchSize) ex.
Proof.
  intros l qb l' qb' ex xb H. unfold merge_batches in H. cbn [qc_list qc_bytes] in H. destruct l as [|b r].
  - injection H as <- <- <- <-. rewrite bsum_nil, zlen_nil'. repeat split; try lia. constructor.
  - destruct (merge_batches_aux (S (length r)) b r [] [] 0) as [[[l1 ex1] xb1]|] eqn:E; [| discriminate H].
    injection H as <- <- <- <-. apply merge_batches_aux_bsum in E. rewrite bsum_nil, zlen_nil' in E. rewrite bsum_cons.
    destruct E as (E1 & E2 & E3). split; [lia|]. split; [lia|]. split; [lia|]. apply E3. constructor.
Qed.

Lemma merge_batches_aux_zlen : forall fuel cur rest rdone rex xb l' ex xb',
  merge_batches_aux fuel cur rest rdone rex xb = Some (l', ex, xb') ->
  zlen l' + zlen ex = 1 + zlen rest + zlen rdone + zlen rex.
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb l' ex xb' H; [discriminate H|].
  cbn [merge_batches_aux] in H. destruct rest as [|nx rest'].
  - injection H as <- <- <-. rewrite zlen_app', !zlen_rev', zlen_cons', !zlen_nil'. lia.
  - destruct (qb_count cur + qb_count nx <=? kBatchCount).
    + destruct (qb_size cur <? kBatchSize); [discriminate H|]. apply IH in H. rewrite !zlen_cons' in *. lia.
    + apply IH in H. rewrite !zlen_cons' in *. lia.
Qed.
Lemma merge_batches_zlen : forall l qb l' qb' ex xb,
  merge_batches (mkQC l qb) = Some (mkQC l' qb', ex, xb) -> zlen l' + zlen ex = zlen l.
Proof.
  intros l qb l' qb' ex xb H. unfold merge_batches in H. cbn [qc_list qc_bytes] in H. destruct l as [|b r].
  - injection H as <- <- <- <-. rewrite zlen_nil'. lia.
  - destruct (merge_batches_aux (S (length r)) b r [] [] 0) as [[[l1 ex1] xb1]|] eqn:E; [| discriminate H].
    injection H as <- <- <- <-. apply merge_batches_aux_zlen in E. rewrite zlen_nil', zlen_cons' in *. lia.
Qed.

(* [comment removed for export] *)
Lemma outside_bextR : forall (L : list qbatch) x a, outside (map bext L) x -> In a (map qb_addr L) -> ~ (a <= x < a + kBatchSize).
Proof.
  intros L x a. induction L as [|b L IH]; cbn [map outside bext In]; [tauto|].
  intros [O1 O2] [E|Hin]; [subst a; exact O1| exact (IH O2 Hin)].
Qed.

Lemma nd_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [exact H1|].
  cbn [app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND]. destruct H1 as [<-|H1].
  - apply NI. apply in_or_app. right. exact H2.
  - exact (IH l2 x ND H1 H2).
Qed.

(* [comment removed for export] *)
Lemma outside_bext_hi `{HCEIL : HeapCeil} : forall (L : list qbatch) a, Forall bok L -> aceil <= a -> outside (map bext L) a.
Proof.
  intros L a OK Ha. induction L as [|b L IH]; [exact I|]. apply Forall_cons_iff in OK. destruct OK as [(_ & B2 & _) OK].
  cbn [map outside bext]. split; [clear - B2 Ha; lia| exact (IH OK)].
Qed.
Lemma outside_bext_lo `{HCEIL : HeapCeil} : forall (L : list qbatch) a, Forall bok L -> a < AIMG_TOP -> outside (map bext L) a.
Proof.
  intros L a OK Ha. induction L as [|b L IH]; [exact I|]. apply Forall_cons_iff in OK. destruct OK as [(B1 & _) OK].
  cbn [map outside bext]. split; [clear - B1 Ha; unfold AHI_LO, AIMG_TOP in *; lia| exact (IH OK)].
Qed.
Lemma bsum_all : forall ex, Forall (fun b => qb_size b = kBatchSize) ex -> bsum ex = kBatchSize * zlen ex.
Proof.
  intros ex F. induction ex as [|b ex IH]; [reflexivity|]. apply Forall_cons_iff in F. destruct F as [E F].
  rewrite bsum_cons, zlen_cons', E, (IH F). lia.
Qed.
Lemma last_map_qb : forall (r : list qbatch) x, last (map qb_addr r) (qb_addr x) = qb_addr (last r x).
Proof.
  intros r. induction r as [|c r IH]; intros x; [reflexivity|].
  destruct r as [|d r']; [reflexivity|]. exact (IH x).
Qed.
Lemma last_indep : forall (r : list Z) d d', r <> [] -> last r d = last r d'.
Proof.
  intros r. induction r as [|c r IH]; intros d d' NE; [exfalso; exact (NE eq_refl)|].
  destruct r as [|e r']; [reflexivity|]. apply IH. discriminate.
Qed.
Lemma thdr00 : forall ex, thdr (wz 0) (wz 0) ex = (wz (hd 0 (map qb_addr ex)), wz (last (map qb_addr ex) 0)).
Proof.
  intros [|b r]; [reflexivity|]. cbn [thdr map hd]. f_equal. f_equal.
  destruct r as [|c r']; [reflexivity|].
  change (last (qb_addr b :: map qb_addr (c :: r')) 0) with (last (map qb_addr (c :: r')) 0).
  rewrite (last_indep (map qb_addr (c :: r')) 0 (qb_addr b)) by discriminate. symmetry. exact (last_map_qb (c :: r') b).
Qed.

(* [comment removed for export] *)
Lemma pop_while_step : forall f l bytes min_size acc,
  pop_while (S f) l bytes min_size acc
  = if bytes <=? min_size then Some (l, bytes, acc)
    else match l with [] => None | b :: r => pop_while f r (bytes - qb_size b) min_size (b :: acc) end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pop_while_shape : forall fuel l bytes min_size acc l2 b2 racc2,
  pop_while fuel l bytes min_size acc = Some (l2, b2, racc2) ->
  exists popped, l = popped ++ l2 /\ racc2 = rev popped ++ acc /\ b2 = bytes - bsum popped /\ b2 <= min_size.
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros l bytes min_size acc l2 b2 racc2 H; [discriminate H|].
  cbn [pop_while] in H. destruct (Z.leb_spec bytes min_size) as [LE|GT].
  - injection H as <- <- <-. exists []. rewrite bsum_nil. cbn [app rev]. repeat split; lia.
  - destruct l as [|b r]; [discriminate H|]. apply IH in H. destruct H as (popped & -> & -> & -> & LE).
    exists (b :: popped). rewrite bsum_cons. cbn [app rev]. rewrite <- app_assoc. cbn [app]. repeat split; lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

  (* [comment removed for export] *)
  Definition rec_W (spv : Z) (l : list qbatch) : list ivl :=
    (spv + -96, spv) :: (AINST + OI_QMUTEX, AINST + OI_QMUTEX + 8) :: (AINST + OI_GQ, AINST + OI_GQ + 32) :: map bext l.

  (* [comment removed for export] *)
  Definition recycle_head_post (ra sp gp tp a2 a3 s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (lo : Z) (l l2 T : list qbatch) (b2 : Z) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 x4 t3 t4 t5 t6 : word) m',
      ms' = MS (mkR (wz 0x198ee4) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x0 x1 (wz (AINST + OI_Q)) (Z_to_bv 64 (bv_unsigned sp + -80)) a2 a3 a4 a5 a6 a7
                    x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1990dc) fc None m' (seg_rom asegs)
      /\ munch (rec_W (bv_unsigned sp) l) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells asegs m' (bv_unsigned sp + -80)
           [C8 (wz (zlen T)); C8 (wz (hd 0 (map qb_addr T))); C8 (wz (last (map qb_addr T) 0)); C8 (wz (bsum T));
            C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (AINST + OI_QMUTEX) [C8 (wz 0)]
      /\ rw_cells asegs m' (AINST + OI_GQ) [C8 (wz (zlen l2)); C8 (wz (hd 0 (map qb_addr l2))); C8 (wz (last (map qb_addr l2) 0)); C8 (wz b2)]
      /\ batches_rep m' l2 /\ batches_rep m' T
      /\ Forall bok l2 /\ Forall bok T
      /\ (forall b, In b (l2 ++ T) -> In (qb_addr b) (map qb_addr l)) /\ List.NoDup (map qb_addr (l2 ++ T))
      /\ b2 = bsum l2.
End HCW.

  Section Recycle.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
    Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
    Variables (lo qmin qbytes : Z) (l : list qbatch).
    (* [comment removed for export] *)
    Variables (l2F exF rpF : list qbatch) (b2F : Z).
    Hypothesis MI : mem_inv asegs m.
    Hypothesis ST : stk asegs m lo (bv_unsigned sp).
    Hypothesis LO : aceil <= lo. Hypothesis HI : lo + 96 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
    Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
    Hypothesis QMR : 0 <= qmin < 2^63.
    Hypothesis QBR : 0 <= qbytes < 2^40.
    Hypothesis QB : qbytes = bsum l.
    Hypothesis OKL : Forall bok l.
    Hypothesis NDL : List.NoDup (map qb_addr l).
    Hypothesis PW : forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.
    Hypothesis RS : rsplit (mkQC l qbytes) qmin = Some (mkQC l2F b2F, exF, rpF).
    (* [comment removed for export] *)
    Hypothesis QM : rw_cells asegs m (AINST + OI_QMUTEX) [C8 (wz 256)].
    Hypothesis GQ : rw_cells asegs m (AINST + OI_GQ) [C8 (wz (zlen l)); C8 (wz (hd 0 (map qb_addr l))); C8 (wz (last (map qb_addr l) 0)); C8 (wz qbytes)].
    Hypothesis BR : batches_rep m l.

    Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (AINST + OI_Q)) (wz qmin) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x198d74) fc None m (seg_rom asegs).
    Let POST := recycle_head_post ra sp gp tp a2 a3 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc m lo l l2F (exF ++ rev rpF) b2F.
    Let W := rec_W (bv_unsigned sp) l.

    (* [comment removed for export] *)
    Ltac rec_lits :=
      unfold AINST, OI_QMUTEX, OI_GQ, OI_Q, wz in *;
      replace (6976152 + 880) with 6977032 in * by reflexivity; replace (6977032 + 8) with 6977040 in * by reflexivity;
      replace (6976152 + 888) with 6977040 in * by reflexivity; replace (6977040 + 32) with 6977072 in * by reflexivity;
      replace (6976152 + 728) with 6976880 in * by reflexivity.

    Let FWI : forall L, Forall (ifar l L) [(6977032, 6977040)]%Z.
    Proof. intros L. constructor; [unfold ifar; left; unfold AIMG_TOP; clear; lia| constructor]. Qed.
    Let FPI : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(6977032, 6977040)]%Z.
    Proof. constructor; [cbn [fst snd]; left; unfold AIMG_TOP; clear; lia| constructor]. Qed.

    (* [comment removed for export] *)
    Lemma rec_finish : forall (rax t0' t1' t2' x0 x1 a4' a5' a6' a7' x2 x3 x4 t3' t4' t5' t6' : word) (m1 : mem) (l2 T : list qbatch),
      mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -80) ->
      rw_cells asegs m1 (bv_unsigned sp + -80)
        [C8 (wz (zlen T)); C8 (wz (hd 0 (map qb_addr T))); C8 (wz (last (map qb_addr T) 0)); C8 (wz (bsum T)); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 (AINST + OI_QMUTEX) [C4 (wz 257); C4 (wz 0)] ->
      rw_cells asegs m1 (AINST + OI_GQ) [C8 (wz (zlen l2)); C8 (wz (hd 0 (map qb_addr l2))); C8 (wz (last (map qb_addr l2) 0)); C8 (wz (bsum l2))] ->
      bseg m1 l2 0 -> bseg m1 T 0 -> Forall bok l2 -> Forall bok T ->
      (forall b, In b (l2 ++ T) -> In (qb_addr b) (map qb_addr l)) -> List.NoDup (map qb_addr (l2 ++ T)) ->
      l2 = l2F -> T = exF ++ rev rpF -> b2F = bsum l2 ->
      evt asegs POST
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' x0 x1 (wz (AINST + OI_Q)) (wz qmin) a2 a3 a4' a5' a6' a7'
                 x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x198ecc) fc None m1 (seg_rom asegs)).
    Proof.
      intros until T. intros MI1 MU WM ST1 FR QM1 GQ1 BS2 BST OK2 OKT SUB ND EL2 ET EB2.
      clear MI ST QM GQ BR. subst l2 T.
      clear QBR QB.   (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      assert (SUB2 : forall b, In b l2F -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
      assert (SUBT : forall b, In b (exF ++ rev rpF) -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply SUB; apply in_or_app; right; exact Hb).
      hide_hyp MU. pose proof (munch_refl [(AINST + OI_QMUTEX, AINST + OI_QMUTEX + 8)]%Z m1) as MUL. pose proof (wmono_refl asegs m1) as WML.
      unfold POST, recycle_head_post, W, rec_W in *. rec_lits. acb.
      (* [comment removed for export] *)
      apply (rw_cells_reshape _ _ _ [C1 (b8 1); C1 (b8 1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in QM1; [| bytes_eq| reflexivity| cbn; repeat split; exact I].
      step. st1f. step. st1f.
      apply (rw_cells_reshape _ _ _ [C8 (Z_to_bv 64 0)]) in QM1; [| bytes_eq| reflexivity| cbn; repeat split; exact I].
      (* [comment removed for export] *)
      step. step.
      pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU.
      lazymatch type of MUL with munch _ _ ?mN =>
        assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m mN)
          by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUL]; intros x Hx; cbn [outside] in Hx |- *; clear - Hx; tauto)
      end.
      apply evt_done. do 17 eexists. split; [reflexivity|].
      split; [exact MU2|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|]. split; [exact QM1|].
      split; [rewrite EB2; exact GQ1|].
      split; [apply bseg_batches; eapply (bseg_far l OKL PW _ m1); [apply FWI| exact OK2| exact SUB2| exact AGL| exact WML| exact BS2]|].
      split; [apply bseg_batches; eapply (bseg_far l OKL PW _ m1); [apply FWI| exact OKT| exact SUBT| exact AGL| exact WML| exact BST]|].
      split; [exact OK2|]. split; [exact OKT|]. split; [exact SUB|]. split; [exact ND| exact EB2].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition pl_mem (m1 : mem) (rem T : list qbatch) (zT zL : word) : Prop :=
         rw_cells asegs m1 (bv_unsigned sp + -80)
           [C8 zT; C8 (wz (hd 0 (map qb_addr T))); C8 zL; C8 (wz (bsum T)); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m1 (AINST + OI_QMUTEX) [C4 (wz 257); C4 (wz 0)]
      /\ rw_cells asegs m1 (AINST + OI_GQ) [C8 (wz (zlen rem)); C8 (wz (hd 0 (map qb_addr rem))); C8 (wz (last (map qb_addr rem) 0)); C8 (wz (bsum rem))]
      /\ bseg m1 rem 0 /\ bseg m1 T 0.
    Definition pl_pure (rem T racc : list qbatch) : Prop :=
         T = exF ++ rev racc
      /\ pop_while (S (length rem)) rem (bsum rem) qmin racc = Some (l2F, b2F, rpF)
      /\ Forall bok rem /\ Forall bok T
      /\ (forall b, In b (rem ++ T) -> In (qb_addr b) (map qb_addr l)) /\ List.NoDup (map qb_addr (rem ++ T))
      /\ bsum rem + bsum T = qbytes /\ zlen rem + zlen T = zlen l.

    Lemma last_map_ne : forall (r : list qbatch) (d : qbatch) z, r <> [] -> last (map qb_addr r) z = qb_addr (last r d).
    Proof.
      clear. intros r. induction r as [|x r IH]; intros d z NE; [exfalso; exact (NE eq_refl)|].
      destruct r as [|y r']; [reflexivity|]. cbn [map last]. cbn [map last] in IH. apply (IH d z). discriminate.
    Qed.
    Lemma nd_rot : forall (a : Z) (r t : list Z), List.NoDup (a :: r ++ t) -> List.NoDup (r ++ t ++ [a]).
    Proof.
      clear. intros a r t ND. rewrite app_assoc. eapply Permutation_NoDup; [| exact ND]. apply Permutation_cons_append.
    Qed.

    (* [comment removed for export] *)
    Definition pl_kont (k : nat) : Prop :=
      forall (rem T racc : list qbatch) (rax a5v a7v t1v t2v x0 x1 x2 x3 x4 t3' t4' t5' t6' zT zL : word) (m1 : mem),
      (length rem <= k)%nat -> pl_pure rem T racc -> qmin < bsum rem ->
      (T <> [] -> a5v = wz (last (map qb_addr T) 0)) ->
      mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -80) -> pl_mem m1 rem T zT zL ->
      evt asegs POST
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (wz (hd 0 (map qb_addr rem))) t1v t2v x0 x1 (wz (AINST + OI_Q)) (wz qmin) a2 a3
                 (wz (zlen T)) a5v (wz (zlen rem)) a7v x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x198e70) fc None m1 (seg_rom asegs)).

    (* [comment removed for export] *)
    Definition pl_memB (m2 : mem) (rem' T : list qbatch) (b : qbatch) (zT zL : word) : Prop :=
         rw_cells asegs m2 (bv_unsigned sp + -80)
           [C8 zT; C8 (wz (hd 0 (map qb_addr T))); C8 zL; C8 (wz (bsum T)); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m2 (AINST + OI_QMUTEX) [C4 (wz 257); C4 (wz 0)]
      /\ rw_cells asegs m2 (AINST + OI_GQ) [C8 (wz (zlen rem')); C8 (wz (hd 0 (map qb_addr rem'))); C8 (wz (last (map qb_addr rem') 0)); C8 (wz (bsum rem'))]
      /\ bseg m2 rem' 0 /\ bseg m2 T 0
      /\ rw_cells asegs m2 (qb_addr b) [C8 (wz 0); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
      /\ u64arr asegs m2 (qb_addr b + 24) (wlist (qb_chunks b))
      /\ stk asegs m2 (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize)
      /\ poisoned m2 (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.

    Lemma rec_popB : forall (k : nat), pl_kont k ->
      forall (rem' T racc : list qbatch) (b : qbatch) (rax a5v t2v x0 x1 x2 x3 x4 t3' t4' t5' t6' zT zL : word) (m2 : mem),
      (length rem' <= k)%nat -> pl_pure (b :: rem') T racc -> qmin < qb_size b + bsum rem' ->
      (T <> [] -> a5v = wz (last (map qb_addr T) 0)) ->
      mem_inv asegs m2 -> munch W m m2 -> wmono asegs m m2 -> stk asegs m2 lo (bv_unsigned sp + -80) -> pl_memB m2 rem' T b zT zL ->
      evt asegs POST
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (wz (qb_addr b)) (wz (qb_addr b)) t2v x0 x1 (wz (AINST + OI_Q)) (wz qmin) a2 a3
                 (wz (zlen T)) a5v (wz (zlen rem')) (wz (hd 0 (map qb_addr rem'))) x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x198ea4) fc None m2 (seg_rom asegs)).
    Proof.
      intros k KONT rem' T racc b rax a5v t2v x0 x1 x2 x3 x4 t3' t4' t5' t6' zT zL m2 LEN PURE GT A5 MI2 MU WM ST2 MEM.
      destruct PURE as (ET & POPW & OKR & OKT & SUB & ND & SUMS & LENS). destruct MEM as (FR & QM1 & GQ1 & BSR & BST & BC & BA & BJ & BP).
      clear MI ST QM GQ BR.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      apply Forall_cons_iff in OKR. destruct OKR as [OKB OKR']. pose proof OKB as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      assert (INB : In (qb_addr b) (map qb_addr l)) by (apply (SUB b); left; reflexivity).
      assert (SUBR : forall x, In x rem' -> In (qb_addr x) (map qb_addr l)) by (intros x Hx; apply SUB; right; apply in_or_app; left; exact Hx).
      assert (SUBT : forall x, In x T -> In (qb_addr x) (map qb_addr l)) by (intros x Hx; apply SUB; right; apply in_or_app; right; exact Hx).
      assert (Z0 : 0 <= zlen rem' /\ 0 <= zlen T) by (unfold zlen; clear; lia).
      pose proof (bsum_nonneg rem' OKR') as BS0. pose proof (bsum_nonneg T OKT) as BT0.
      assert (LENB : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in B5; clear - B5; lia).
      rewrite bsum_cons in POPW, SUMS. rewrite zlen_cons' in LENS.
      pose proof (bsum_len l OKL) as LLEN. assert (ZL : zlen l < 2^27) by (clear - LLEN QB QBR; unfold kBatchSize in LLEN; lia).
      change ((b :: rem') ++ T) with (b :: (rem' ++ T)) in ND. rewrite map_cons, map_app in ND.
      pose proof (proj1 (proj1 (NoDup_cons_iff _ _) ND)) as NIB. pose proof (NoDup_app_remove_l _ _ (proj2 (proj1 (NoDup_cons_iff _ _) ND))) as NDT.
      (* [comment removed for export] *)
      rewrite pop_while_step in POPW. replace (qb_size b + bsum rem' <=? qmin) with false in POPW by (symmetry; apply Z.leb_gt; exact GT).
      cbv iota in POPW. change (length (b :: rem')) with (S (length rem')) in POPW.
      replace (qb_size b + bsum rem' - qb_size b) with (bsum rem') in POPW by (clear; lia).
      set (lt := last T b) in *.
      assert (INLT : T <> [] -> In (qb_addr lt) (map qb_addr l)) by (intros NE; apply SUBT; subst lt; apply last_in; exact NE).
      assert (LTB : T <> [] -> qb_addr b + kBatchSize <= qb_addr lt \/ qb_addr lt + kBatchSize <= qb_addr b).
      { intros NE. apply (PW _ _ INB (INLT NE)). intros E. apply NIB. apply in_or_app. right. rewrite E. apply in_map. subst lt. apply last_in. exact NE. }
      assert (OKLT : T <> [] -> bok lt) by (intros NE; apply (proj1 (Forall_forall _ _) OKT); subst lt; apply last_in; exact NE).
      hide_hyp MU.
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp + -48); (qb_addr lt, qb_addr lt + 8)]%Z m2) as MUL.
      pose proof (wmono_refl asegs m2) as WML.
      unfold POST, recycle_head_post, W, rec_W in *. rec_lits. unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP in *. acb.
      (* [comment removed for export] *)
      Ltac pop_join := step; step; step; step; step; step; step; step.
      destruct T as [|tf Tr].
      - (* [comment removed for export] *)
        cbn [zlen length Z.of_nat map hd bsum fold_right app rev] in FR, ET, SUMS, LENS, NDT, SUB |- *. subst lt. cbn [last] in MUL.
        assert (FW : forall L, (forall x, In x L -> qb_addr x <> qb_addr b) -> Forall (ifar l L) [(bv_unsigned sp + -80, bv_unsigned sp + -48); (qb_addr b, qb_addr b + 8)]%Z).
        { intros L HL. constructor; [unfold ifar; right; left; clear - LO HI; lia|]. constructor; [| constructor].
          unfold ifar. right; right. exists (qb_addr b). split; [exact INB|]. split; [clear; lia|]. split; [unfold kBatchSize; clear; lia| exact HL]. }
        assert (FP : Forall (fun i : ivl => snd i <= 12599296 \/ 17594333495296 <= fst i) [(bv_unsigned sp + -80, bv_unsigned sp + -48); (qb_addr b, qb_addr b + 8)]%Z).
        { constructor; [cbn [fst snd]; right; clear - LO HI ACEILB; lia|]. constructor; [cbn [fst snd]; right; exact B1| constructor]. }
        assert (NRB : forall x, In x rem' -> qb_addr x <> qb_addr b) by (intros x Hx E; apply NIB; apply in_or_app; left; rewrite <- E; apply in_map; exact Hx).
        assert (SUB' : forall x, In x (rem' ++ [b]) -> In (qb_addr x) (map qb_addr l))
          by (intros x Hx; apply in_app_or in Hx; destruct Hx as [Hx|[<-|[]]]; [exact (SUBR x Hx)| exact INB]).
        assert (ND' : List.NoDup (map qb_addr (rem' ++ [b]))) by (rewrite map_app; cbn [map]; apply (nd_rot _ _ []); cbn [map] in ND; exact ND).
        step. if_cases Kt; zify_cond Kt. { exfalso. apply Kt. reflexivity. } clear Kt.
        step. step. step.
        pop_join.
        replace (0 + qb_size b) with (bsum [b]) in * by (rewrite bsum_cons, bsum_nil; clear; lia).
        step. if_cases Kx; zify_cond Kx.
        + (* [comment removed for export] *)
          assert (LE : bsum rem' <= qmin) by (revert Kx; rewrite ?unsigned_lit by (clear - QMR BS0 SUMS QBR BT0; lia); clear; intros Kx; lia). clear Kx.
          rewrite pop_while_step in POPW. replace (bsum rem' <=? qmin) with true in POPW by (symmetry; apply Z.leb_le; exact LE). injection POPW as EL2 EB2 ERP.
          step. step. replace (zlen [] + 1) with (zlen [b]) in FR by reflexivity.
          pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU.
          lazymatch type of MUL with munch _ _ ?mN =>
            assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m mN)
              by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUL]; intros x Hx; cbn [outside] in Hx |- *;
                  pose proof (outside_bextR l x (qb_addr b) ltac:(clear - Hx; tauto) INB) as OB; unfold kBatchSize in OB; clear - Hx OB; lia);
            assert (BSR2 : bseg mN rem' 0) by (eapply (bseg_far l OKL PW _ m2); [apply (FW rem' NRB)| exact OKR'| exact SUBR| exact AGL| exact WML| exact BSR]);
            assert (BSB : bseg mN [b] 0)
              by (cbn [bseg map hd]; split; [| exact I]; apply batch_close; [assumption| assumption| assumption|];
                  eapply (pois_far2 _ m2 _ b); [exact FP| exact OKB| exact AGL| exact WML| exact BP])
          end.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mN _) =>
            apply (rec_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mN rem' [b] ltac:(assumption) MU2 WM ltac:(assumption) FR ltac:(assumption) ltac:(assumption)
                     BSR2 BSB OKR' ltac:(constructor; [exact OKB| constructor]) SUB' ND' EL2
                     ltac:(rewrite <- ERP; cbn [rev]; destruct (app_eq_nil _ _ (eq_sym ET)) as [E1 E2]; rewrite E1, E2; reflexivity) (eq_sym EB2))
          end.
        + (* [comment removed for export] *)
          assert (GT' : qmin < bsum rem') by (revert Kx; rewrite ?unsigned_lit by (clear - QMR BS0 SUMS QBR BT0; lia); clear; intros Kx; lia). clear Kx.
          replace (zlen [] + 1) with (zlen [b]) by reflexivity.
          pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU.
          lazymatch type of MUL with munch _ _ ?mN =>
            assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m mN)
              by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUL]; intros x Hx; cbn [outside] in Hx |- *;
                  pose proof (outside_bextR l x (qb_addr b) ltac:(clear - Hx; tauto) INB) as OB; unfold kBatchSize in OB; clear - Hx OB; lia);
            assert (BSR2 : bseg mN rem' 0) by (eapply (bseg_far l OKL PW _ m2); [apply (FW rem' NRB)| exact OKR'| exact SUBR| exact AGL| exact WML| exact BSR]);
            assert (BSB : bseg mN [b] 0)
              by (cbn [bseg map hd]; split; [| exact I]; apply batch_close; [assumption| assumption| assumption|];
                  eapply (pois_far2 _ m2 _ b); [exact FP| exact OKB| exact AGL| exact WML| exact BP])
          end.
          eapply (KONT rem' [b] (b :: racc)); [exact LEN| | exact GT'| intros _; reflexivity| assumption| exact MU2| exact WM| assumption|].
          * split; [cbn [rev]; destruct (app_eq_nil _ _ (eq_sym ET)) as [E1 E2]; rewrite E1, E2; reflexivity|].
            split; [exact POPW|]. split; [exact OKR'|]. split; [constructor; [exact OKB| constructor]|].
            split; [exact SUB'|]. split; [exact ND'|]. clear - SUMS LENS. rewrite ?bsum_cons, ?bsum_nil, ?zlen_cons', ?zlen_nil' in *. lia.
          * split; [exact FR|]. split; [assumption|]. split; [assumption|]. split; [exact BSR2| exact BSB].
      - (* [comment removed for export] *)
        assert (TNE : tf :: Tr <> []) by discriminate.
        specialize (A5 TNE). specialize (INLT TNE). specialize (LTB TNE). specialize (OKLT TNE). subst a5v.
        pose proof OKLT as (L1 & L2 & L3 & L4 & L5 & L6 & L7). unfold kBatchSize, kBatchCount, AHI_LO in L1, L2, L4, L6.
        assert (LENLT : Z.of_nat (length (wlist (qb_chunks lt))) = qb_count lt) by (unfold wlist; rewrite length_map; unfold zlen in L5; clear - L5; lia).
        rewrite (last_map_ne (tf :: Tr) b 0 TNE). fold lt.
        (* [comment removed for export] *)
        pose proof BST as BST0. rewrite (app_removelast_last b TNE) in BST0. fold lt in BST0.
        apply bseg_app in BST0. destruct BST0 as [BSTi BLT]. cbn [bseg map hd] in BLT. destruct BLT as [BLT _].
        pose proof (batch_open m2 lt 0 OKLT BLT) as (LC & LA & LJ & LP). clear BLT. unfold kBatchSize in LJ, LP.
        pose proof NDT as NDTi. rewrite (app_removelast_last b TNE), map_app in NDTi. fold lt in NDTi. cbn [map] in NDTi.
        assert (NTI : forall x, In x (removelast (tf :: Tr)) -> qb_addr x <> qb_addr lt).
        { intros x Hx E. apply (NoDup_remove_2 _ [] _ NDTi). rewrite app_nil_r. rewrite <- E. apply in_map. exact Hx. }
        assert (INLTT : In lt (tf :: Tr)) by (subst lt; apply last_in; exact TNE).
        assert (NRL : forall x, In x rem' -> qb_addr x <> qb_addr lt).
        { intros x Hx E. apply (nd_app_disj _ _ (qb_addr lt) (proj2 (proj1 (NoDup_cons_iff _ _) ND))); [rewrite <- E; apply in_map; exact Hx| apply in_map; exact INLTT]. }
        assert (NRB : forall x, In x rem' -> qb_addr x <> qb_addr b) by (intros x Hx E; apply NIB; apply in_or_app; left; rewrite <- E; apply in_map; exact Hx).
        assert (NTB : forall x, In x (tf :: Tr) -> qb_addr x <> qb_addr b) by (intros x Hx E; apply NIB; apply in_or_app; right; rewrite <- E; apply in_map; exact Hx).
        assert (SUBTi : forall x, In x (removelast (tf :: Tr)) -> In (qb_addr x) (map qb_addr l)).
        { intros x Hx. apply SUBT. rewrite (app_removelast_last b TNE) at 1. apply in_or_app. left. exact Hx. }
        assert (OKTi : Forall bok (removelast (tf :: Tr))).
        { apply (proj2 (Forall_forall _ _)). intros x Hx. apply (proj1 (Forall_forall _ _) OKT). rewrite (app_removelast_last b TNE) at 1. apply in_or_app. left. exact Hx. }
        assert (FW : forall L, (forall x, In x L -> qb_addr x <> qb_addr lt) -> Forall (ifar l L) [(bv_unsigned sp + -80, bv_unsigned sp + -48); (qb_addr lt, qb_addr lt + 8)]%Z).
        { intros L HL. constructor; [unfold ifar; right; left; clear - LO HI; lia|]. constructor; [| constructor].
          unfold ifar. right; right. exists (qb_addr lt). split; [exact INLT|]. split; [clear; lia|]. split; [unfold kBatchSize; clear; lia| exact HL]. }
        assert (FP : Forall (fun i : ivl => snd i <= 12599296 \/ 17594333495296 <= fst i) [(bv_unsigned sp + -80, bv_unsigned sp + -48); (qb_addr lt, qb_addr lt + 8)]%Z).
        { constructor; [cbn [fst snd]; right; clear - LO HI ACEILB; lia|]. constructor; [cbn [fst snd]; right; exact L1| constructor]. }
        assert (SUB' : forall x, In x (rem' ++ (tf :: Tr) ++ [b]) -> In (qb_addr x) (map qb_addr l)).
        { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact (SUBR x Hx)|]. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [exact (SUBT x Hx)| exact INB]. }
        assert (ND' : List.NoDup (map qb_addr (rem' ++ (tf :: Tr) ++ [b]))) by (rewrite !map_app; cbn [map]; apply nd_rot; exact ND).
        assert (ET' : (tf :: Tr) ++ [b] = exF ++ rev (b :: racc)) by (cbn [rev]; rewrite app_assoc, <- ET; reflexivity).
        rewrite zlen_cons' in *.
        step. if_cases Kt; zify_cond Kt. 2: { exfalso. revert Kt. rewrite ?unsigned_lit by (clear - LENS ZL; unfold zlen in *; lia). clear. unfold zlen. intros Kt. lia. } clear Kt.
        (* [comment removed for export] *)
        step.
        pop_join.
        step. if_cases Kx; zify_cond Kx.
        + (* [comment removed for export] *)
          assert (LE : bsum rem' <= qmin) by (revert Kx; rewrite ?unsigned_lit by (clear - QMR BS0 SUMS QBR BT0; lia); clear; intros Kx; lia). clear Kx.
          rewrite pop_while_step in POPW. replace (bsum rem' <=? qmin) with true in POPW by (symmetry; apply Z.leb_le; exact LE). injection POPW as EL2 EB2 ERP.
          step. step.
          pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU.
          lazymatch type of MUL with munch _ _ ?mN =>
            assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m mN)
              by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUL]; intros x Hx; cbn [outside] in Hx |- *;
                  pose proof (outside_bextR l x (qb_addr lt) ltac:(clear - Hx; tauto) INLT) as OB; unfold kBatchSize in OB; clear - Hx OB; lia);
            assert (BSR2 : bseg mN rem' 0) by (eapply (bseg_far l OKL PW _ m2); [apply (FW rem' NRL)| exact OKR'| exact SUBR| exact AGL| exact WML| exact BSR]);
            assert (BST2 : bseg mN ((tf :: Tr) ++ [b]) 0)
              by (apply bseg_app; cbn [map hd]; split;
                  [ rewrite (app_removelast_last b TNE) at 1; fold lt; apply bseg_app; cbn [map hd bseg]; split;
                    [ eapply (bseg_far l OKL PW _ m2); [apply (FW _ NTI)| exact OKTi| exact SUBTi| exact AGL| exact WML| exact BSTi]
                    | split; [| exact I]; apply batch_close; [assumption| assumption| assumption| eapply (pois_far2 _ m2 _ lt); [exact FP| exact OKLT| exact AGL| exact WML| exact LP]]]
                  | cbn [bseg]; split; [| exact I]; apply batch_close; [assumption| assumption| assumption| eapply (pois_far2 _ m2 _ b); [exact FP| exact OKB| exact AGL| exact WML| exact BP]]]);
            assert (FR' : rw_cells asegs mN (bv_unsigned sp + -80)
                     [C8 (wz (zlen ((tf :: Tr) ++ [b]))); C8 (wz (hd 0 (map qb_addr ((tf :: Tr) ++ [b])))); C8 (wz (last (map qb_addr ((tf :: Tr) ++ [b])) 0));
                      C8 (wz (bsum ((tf :: Tr) ++ [b]))); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
              by (unfold wz; replace (zlen ((tf :: Tr) ++ [b])) with (1 + zlen Tr + 1) by (rewrite zlen_app1, zlen_cons'; clear; lia);
                  replace (hd 0 (map qb_addr ((tf :: Tr) ++ [b]))) with (hd 0 (map qb_addr (tf :: Tr))) by reflexivity; rewrite last_map_app1;
                  replace (bsum ((tf :: Tr) ++ [b])) with (bsum (tf :: Tr) + qb_size b) by (rewrite bsum_app, (bsum_cons b []), bsum_nil; clear; lia); exact FR)
          end.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mN _) =>
            apply (rec_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mN rem' ((tf :: Tr) ++ [b]) ltac:(assumption) MU2 WM ltac:(assumption) FR' ltac:(assumption) ltac:(assumption)
                     BSR2 BST2 OKR' ltac:(apply Forall_app; split; [exact OKT| constructor; [exact OKB| constructor]]) SUB' ND' EL2
                     ltac:(rewrite <- ERP; exact ET') (eq_sym EB2))
          end.
        + (* [comment removed for export] *)
          assert (GT' : qmin < bsum rem') by (revert Kx; rewrite ?unsigned_lit by (clear - QMR BS0 SUMS QBR BT0; lia); clear; intros Kx; lia). clear Kx.
          pose proof (munch_agree _ _ _ MUL) as AGL. unhide_hyp MU.
          lazymatch type of MUL with munch _ _ ?mN =>
            assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m mN)
              by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUL]; intros x Hx; cbn [outside] in Hx |- *;
                  pose proof (outside_bextR l x (qb_addr lt) ltac:(clear - Hx; tauto) INLT) as OB; unfold kBatchSize in OB; clear - Hx OB; lia);
            assert (BSR2 : bseg mN rem' 0) by (eapply (bseg_far l OKL PW _ m2); [apply (FW rem' NRL)| exact OKR'| exact SUBR| exact AGL| exact WML| exact BSR]);
            assert (BST2 : bseg mN ((tf :: Tr) ++ [b]) 0)
              by (apply bseg_app; cbn [map hd]; split;
                  [ rewrite (app_removelast_last b TNE) at 1; fold lt; apply bseg_app; cbn [map hd bseg]; split;
                    [ eapply (bseg_far l OKL PW _ m2); [apply (FW _ NTI)| exact OKTi| exact SUBTi| exact AGL| exact WML| exact BSTi]
                    | split; [| exact I]; apply batch_close; [assumption| assumption| assumption| eapply (pois_far2 _ m2 _ lt); [exact FP| exact OKLT| exact AGL| exact WML| exact LP]]]
                  | cbn [bseg]; split; [| exact I]; apply batch_close; [assumption| assumption| assumption| eapply (pois_far2 _ m2 _ b); [exact FP| exact OKB| exact AGL| exact WML| exact BP]]]);
            assert (FR' : rw_cells asegs mN (bv_unsigned sp + -80)
                     [C8 zT; C8 (wz (hd 0 (map qb_addr ((tf :: Tr) ++ [b])))); C8 zL; C8 (wz (bsum ((tf :: Tr) ++ [b]))); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
              by (unfold wz; replace (hd 0 (map qb_addr ((tf :: Tr) ++ [b]))) with (hd 0 (map qb_addr (tf :: Tr))) by reflexivity;
                  replace (bsum ((tf :: Tr) ++ [b])) with (bsum (tf :: Tr) + qb_size b) by (rewrite bsum_app, (bsum_cons b []), bsum_nil; clear; lia); exact FR)
          end.
          replace (1 + zlen Tr + 1) with (zlen ((tf :: Tr) ++ [b])) by (rewrite zlen_app1, zlen_cons'; clear; lia).
          eapply (KONT rem' ((tf :: Tr) ++ [b]) (b :: racc)); [exact LEN| | exact GT'| intros _; rewrite last_map_app1; reflexivity| assumption| exact MU2| exact WM| assumption|].
          * split; [exact ET'|]. split; [exact POPW|]. split; [exact OKR'|]. split; [apply Forall_app; split; [exact OKT| constructor; [exact OKB| constructor]]|].
            split; [exact SUB'|]. split; [exact ND'|]. clear - SUMS LENS. rewrite ?bsum_app, ?bsum_cons, ?bsum_nil, ?zlen_app1, ?zlen_cons', ?zlen_nil' in *. lia.
          * split; [exact FR'|]. split; [assumption|]. split; [assumption|]. split; [exact BSR2| exact BST2].
    Qed.

    (* [comment removed for export] *)
    Lemma rec_pop : forall k, pl_kont k.
    Proof.
      intros k. induction k as [|k IH]; unfold pl_kont; intros rem T racc rax a5v a7v t1v t2v x0 x1 x2 x3 x4 t3' t4' t5' t6' zT zL m1 LEN PURE GT A5 MI1 MU WM ST1 MEM.
      { exfalso. destruct rem; [rewrite bsum_nil in GT; clear - GT QMR; lia| cbn [length] in LEN; clear - LEN; lia]. }
      destruct rem as [|b rem']. { exfalso. rewrite bsum_nil in GT. clear - GT QMR. lia. }
      cbn [length] in LEN. apply le_S_n in LEN.
      pose proof PURE as (ET & POPW & OKR & OKT & SUB & ND & SUMS & LENS). destruct MEM as (FR & QM1 & GQ1 & BSR & BST).
      clear MI ST QM GQ BR.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      apply Forall_cons_iff in OKR. destruct OKR as [OKB OKR']. pose proof OKB as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      cbn [bseg] in BSR. destruct BSR as [BB BSR'].
      pose proof (batch_open m1 b _ OKB BB) as (BC & BA & BJ & BP). clear BB.
      assert (INB : In (qb_addr b) (map qb_addr l)) by (apply (SUB b); left; reflexivity).
      assert (SUBR : forall x, In x rem' -> In (qb_addr x) (map qb_addr l)) by (intros x Hx; apply SUB; right; apply in_or_app; left; exact Hx).
      assert (SUBT : forall x, In x T -> In (qb_addr x) (map qb_addr l)) by (intros x Hx; apply SUB; right; apply in_or_app; right; exact Hx).
      assert (Z0 : 0 <= zlen rem' /\ 0 <= zlen T) by (unfold zlen; clear; lia).
      pose proof (bsum_nonneg rem' OKR') as BS0. pose proof (bsum_nonneg T OKT) as BT0.
      assert (LENB : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in B5; clear - B5; lia).
      pose proof (bsum_len l OKL) as LLEN. assert (ZL : zlen l < 2^27) by (clear - LLEN QB QBR; unfold kBatchSize in LLEN; lia).
      pose proof GT as GT0. rewrite bsum_cons in GT0. pose proof SUMS as SUMS0. rewrite bsum_cons in SUMS0. pose proof LENS as LENS0. rewrite zlen_cons' in LENS0.
      rewrite bsum_cons, zlen_cons' in GQ1. rewrite zlen_cons'. cbn [map hd] in GQ1 |- *.
      pose proof ND as ND0. change ((b :: rem') ++ T) with (b :: (rem' ++ T)) in ND0. rewrite map_cons, map_app in ND0.
      pose proof (proj1 (proj1 (NoDup_cons_iff _ _) ND0)) as NIB.
      assert (NRB : forall x, In x rem' -> qb_addr x <> qb_addr b) by (intros x Hx E; apply NIB; apply in_or_app; left; rewrite <- E; apply in_map; exact Hx).
      assert (NTB : forall x, In x T -> qb_addr x <> qb_addr b) by (intros x Hx E; apply NIB; apply in_or_app; right; rewrite <- E; apply in_map; exact Hx).
      assert (FW : forall L, (forall x, In x L -> qb_addr x <> qb_addr b) -> Forall (ifar l L) [(6977040, 6977072); (qb_addr b, qb_addr b + 8)]%Z).
      { intros L HL. constructor; [unfold ifar; left; unfold AIMG_TOP; clear; lia|]. constructor; [| constructor].
        unfold ifar. right; right. exists (qb_addr b). split; [exact INB|]. split; [clear; lia|]. split; [unfold kBatchSize; clear; lia| exact HL]. }
      assert (FP : Forall (fun i : ivl => snd i <= AIMG_TOP \/ AHI_LO <= fst i) [(6977040, 6977072); (qb_addr b, qb_addr b + 8)]%Z).
      { constructor; [cbn [fst snd]; left; unfold AIMG_TOP; clear; lia|]. constructor; [cbn [fst snd]; right; exact B1| constructor]. }
      hide_hyp MU.
      pose proof (munch_refl [(6977040, 6977072); (qb_addr b, qb_addr b + 8)]%Z m1) as MUL. pose proof (wmono_refl asegs m1) as WML.
      unfold W, rec_W in *. rec_lits. unfold kBatchSize, kBatchCount, AHI_LO, AIMG_TOP in *. acb.
      (* [comment removed for export] *)
      step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - Z0 ZL LENS0; lia). clear - Z0. intros K. lia. } clear K.
      step. step.
      (* [comment removed for export] *)
      step. if_cases Kn; zify_cond Kn;
        [ destruct rem' as [|c rem'']; cbn [map hd last] in Kn, GQ1 |- *; [exfalso; apply Kn; reflexivity| clear Kn]
        | destruct rem' as [|c rem'']; cbn [map hd last] in Kn, GQ1 |- *;
          [ (* [comment removed for export] *) st1f; clear Kn
          | exfalso; apply Forall_cons_iff in OKR'; destruct OKR' as [(C1 & C2 & _) _]; unfold AHI_LO, kBatchSize in C1, C2;
            revert Kn; rewrite ?unsigned_lit, ?land64_id by (clear - C1 C2 ACEILB; lia); clear - C1; intros Kn; lia ] ].
      (* [comment removed for export] *)
      all: step; step; step; step; step; step; step; st1f.
      (* [comment removed for export] *)
      all: lazymatch type of GQ1 with rw_cells _ ?mm _ [C8 (Z_to_bv 64 (1 + zlen ?r + -1)); _; _; _] =>
             assert (GQ1' : rw_cells asegs mm 6977040 [C8 (Z_to_bv 64 (zlen r)); C8 (Z_to_bv 64 (hd 0 (map qb_addr r))); C8 (Z_to_bv 64 (last (map qb_addr r) 0)); C8 (Z_to_bv 64 (bsum r))])
               by (rewrite !unsigned_lit in GQ1 by (clear - SUMS0 QBR BS0 BT0 B6; rewrite ?bsum_cons in *; lia);
                   replace (zlen r) with (1 + zlen r + -1) by (clear; lia);
                   replace (bsum r) with (qb_size b + bsum r - qb_size b) by (clear; lia); exact GQ1);
             clear GQ1; replace (1 + zlen r + -1) with (zlen r) by (clear; lia);
             pose proof (munch_agree _ _ _ MUL) as AGL; unhide_hyp MU;
             assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m mm)
               by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUL]; intros x Hx; cbn [outside] in Hx |- *;
                   pose proof (outside_bextR l x (qb_addr b) ltac:(clear - Hx; tauto) INB) as OB; unfold kBatchSize in OB; clear - Hx OB; lia);
             assert (BSR2 : bseg mm r 0) by (eapply (bseg_far l OKL PW _ m1); [apply (FW r NRB)| exact OKR'| exact SUBR| exact AGL| exact WML| exact BSR']);
             assert (BST2 : bseg mm T 0) by (eapply (bseg_far l OKL PW _ m1); [apply (FW T NTB)| exact OKT| exact SUBT| exact AGL| exact WML| exact BST]);
             assert (BP2 : poisoned mm (qb_addr b) (Z.to_nat (8192 / 8)) kAsanHeapLeftRedzoneMagic) by (eapply (pois_far2 _ m1 _ b); [exact FP| exact OKB| exact AGL| exact WML| exact BP]);
             apply (rec_popB k IH r T racc b _ _ _ _ _ _ _ _ _ _ _ _ zT zL mm LEN PURE GT0 A5 ltac:(assumption) MU2 WM ltac:(assumption));
             split; [exact FR|]; split; [assumption|]; split; [exact GQ1'|]; split; [exact BSR2|]; split; [exact BST2|];
             split; [assumption|]; split; [assumption|]; split; [assumption| exact BP2]
           end.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma rec_join2 : forall (l1 T0 : list qbatch) (rax t0' t1' t2' x0 x1 a4' a5' a7' x2 x3 x4 t3' t4' t5' t6' : word) (m1 : mem),
      pop_while (S (length l1)) l1 (bsum l1) qmin [] = Some (l2F, b2F, rpF) -> exF = T0 ->
      Forall bok l1 -> Forall bok T0 -> (forall b, In b (l1 ++ T0) -> In (qb_addr b) (map qb_addr l)) -> List.NoDup (map qb_addr (l1 ++ T0)) ->
      bsum l1 + bsum T0 = qbytes -> zlen l1 + zlen T0 = zlen l ->
      mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -80) ->
      rw_cells asegs m1 (bv_unsigned sp + -80)
        [C8 (wz (zlen T0)); C8 (wz (hd 0 (map qb_addr T0))); C8 (wz (last (map qb_addr T0) 0)); C8 (wz (bsum T0)); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 (AINST + OI_QMUTEX) [C4 (wz 257); C4 (wz 0)] ->
      rw_cells asegs m1 (AINST + OI_GQ) [C8 (wz (zlen l1)); C8 (wz (hd 0 (map qb_addr l1))); C8 (wz (last (map qb_addr l1) 0)); C8 (wz (bsum l1))] ->
      bseg m1 l1 0 -> bseg m1 T0 0 ->
      evt asegs POST
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' x0 x1 (wz (AINST + OI_Q)) (wz qmin) a2 a3 a4' a5' (wz (zlen l1)) a7'
                 x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x198e30) fc None m1 (seg_rom asegs)).
    Proof.
      intros until m1. intros POPW EEX OK1 OKT SUB ND SUMS LENS MI1 MU WM ST1 FR QM1 GQ1 BS1 BST.
      clear MI ST QM GQ BR.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof (bsum_nonneg l1 OK1) as BS0. pose proof (bsum_nonneg T0 OKT) as BT0.
      unfold POST, W, rec_W in *. rec_lits. unfold kBatchSize, AHI_LO, AIMG_TOP in *. acb.
      (* [comment removed for export] *)
      step. step. step.
      step. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        assert (LE : bsum l1 <= qmin) by (revert K; rewrite ?unsigned_lit by (clear - QMR BS0 BT0 SUMS QBR; lia); clear; intros K; lia). clear K.
        rewrite pop_while_step in POPW. replace (bsum l1 <=? qmin) with true in POPW by (symmetry; apply Z.leb_le; exact LE). injection POPW as EL2 EB2 ERP.
        apply (rec_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 l1 T0 MI1 MU WM ST1 FR QM1 GQ1 BS1 BST OK1 OKT SUB ND EL2 ltac:(rewrite <- ERP, app_nil_r; symmetry; exact EEX) (eq_sym EB2)).
      - (* [comment removed for export] *)
        assert (GT : qmin < bsum l1) by (revert K; rewrite ?unsigned_lit by (clear - QMR BS0 BT0 SUMS QBR; lia); clear; intros K; lia). clear K.
        step. step.
        apply (rec_pop (length l1) l1 T0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz (zlen T0)) (wz (last (map qb_addr T0) 0)) m1 (le_n _)); [| exact GT| intros _; reflexivity| exact MI1| exact MU| exact WM| exact ST1|].
        + split; [rewrite app_nil_r; symmetry; exact EEX|]. split; [exact POPW|]. split; [exact OK1|]. split; [exact OKT|].
          split; [exact SUB|]. split; [exact ND|]. split; [exact SUMS| exact LENS].
        + split; [exact FR|]. split; [exact QM1|]. split; [exact GQ1|]. split; [exact BS1| exact BST].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Theorem recycle_head : evt asegs POST ENTRY.
    Proof.
      unfold ENTRY.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof SPA as R; destruct R as [SPA'].
      pose proof (bsum_len l OKL) as LLEN. assert (ZL : zlen l < 2^27) by (clear - LLEN QB QBR; unfold kBatchSize in LLEN; lia).
      assert (Z0 : 0 <= zlen l) by (unfold zlen; clear; lia).
      pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (AINST + OI_QMUTEX, AINST + OI_QMUTEX + 8); (AINST + OI_GQ, AINST + OI_GQ + 32)]%Z m) as MUL.
      assert (FWL : forall L, Forall (ifar l L) [(bv_unsigned sp + -96, bv_unsigned sp); (AINST + OI_QMUTEX, AINST + OI_QMUTEX + 8); (AINST + OI_GQ, AINST + OI_GQ + 32)]%Z).
      { intros L. constructor; [unfold ifar; right; left; clear - LO HI; lia|]. constructor; [unfold ifar; left; rec_lits; unfold AIMG_TOP; clear; lia|].
        constructor; [unfold ifar; left; rec_lits; unfold AIMG_TOP; clear; lia| constructor]. }
      assert (SUBl : forall b, In b l -> In (qb_addr b) (map qb_addr l)) by (intros b Hb; apply in_map; exact Hb).
      pose proof (proj2 (bseg_batches m l) BR) as BS.
      unfold POST, W, rec_W in *. rec_lits. unfold kBatchSize, AHI_LO, AIMG_TOP in *. acb.
      apply (rw_cells_reshape _ _ _ [C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 0)]) in QM; [| bytes_eq| reflexivity| cbn; repeat split; exact I].
      assert (MA : 6977032 mod 4 = 0) by reflexivity. assert (MR : 0 <= 6977032 < 2^64) by (clear; lia).
      (* [comment removed for export] *)
      step. carve_frame 80%nat ST.
      lazymatch goal with FRu : rw_cells _ _ (bv_unsigned sp + -80) [CB 80 ?j] |- _ =>
        let J := fresh "J" in remember j as J in FRu;
        apply (rw_cells_split_CB asegs _ _ [] 80 J [] [8;8;8;8;8;8;8;8;8;8]%nat) in FRu; [| reflexivity]; cbn [mk_CB_cells app] in FRu;
        repeat match type of FRu with context [CB ?k (take ?i ?l0)] => let X := fresh "jk" in remember (take i l0) as X in FRu end;
        repeat match type of FRu with context [CB ?k (drop ?i ?l0)] => let X := fresh "jk" in remember (drop i l0) as X in FRu end;
        repeat match goal with H' : _ = take _ _ |- _ => clear H' | H' : _ = drop _ _ |- _ => clear H' | H' : _ = J |- _ => clear H' end;
        rename FRu into FR
      end.
      step. step. step. step. step. step. st1f. st1f. st1f. st1f.
      (* [comment removed for export] *)
      step. step. step. step. litx.
      (* [comment removed for export] *)
      astep. step. step. step. step. litx. astep.
      step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
      step. litx. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
      (* [comment removed for export] *)
      step. step. step.
      rewrite (unsigned_lit (zlen l)) by (clear - Z0 ZL; lia). rewrite (Z.shiftl_mul_pow2 (zlen l) 13) by (clear; lia). change (2 ^ 13) with 8192.
      step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - Z0 ZL QBR; lia). clear - LLEN QB. intros K. lia. } clear K.
      (* [comment removed for export] *)
      apply (proj1 (rw_cells_app asegs _ _ [C8 _; C8 _; C8 _; C8 _] [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _])) in FR.
      cbn [cells_size csize Nat.add] in FR. change (Z.of_nat 32) with 32 in FR. destruct FR as [FT FS].
      replace (bv_unsigned sp + -80 + 32) with (bv_unsigned sp + -48) in FS by (clear; lia).
      (* [comment removed for export] *)
      pose proof RS as RS0. unfold rsplit in RS0. cbn [qc_list qc_bytes] in RS0. unfold kBatchSize in RS0.
      replace (qbytes <? zlen l * 8192) with false in RS0 by (symmetry; apply Z.ltb_ge; clear - LLEN QB; lia).
      (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.
      - assert (C1 : qbytes <= zlen l * 8192) by (revert K1; rewrite ?unsigned_lit by (clear - Z0 ZL QBR; lia); clear; intros K1; lia). clear K1.
        replace (zlen l * 8192 <? qbytes) with false in RS0 by (symmetry; apply Z.ltb_ge; exact C1). cbn [andb qc_list qc_bytes] in RS0.
        destruct (pop_while (S (length l)) l qbytes qmin []) as [[[l2 b2] rp]|] eqn:POPW; [| discriminate RS0].
        injection RS0 as E1 E2 E3 E4. subst l2 b2 rp. rewrite QB in POPW.
        pose proof (munch_agree _ _ _ MUL) as AGL.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mN _) =>
          apply (rec_join2 l [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mN POPW (eq_sym E3) OKL ltac:(constructor) ltac:(intros b Hb; rewrite app_nil_r in Hb; exact (SUBl b Hb))
                   ltac:(rewrite app_nil_r; exact NDL) ltac:(rewrite bsum_nil; clear - QB; lia) ltac:(rewrite zlen_nil'; clear; lia) ltac:(assumption) MU WM ltac:(assumption));
          [ apply (proj2 (rw_cells_app asegs _ _ [C8 _; C8 _; C8 _; C8 _] [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _])); split; [exact FT| cbn [cells_size csize Nat.add]; change (Z.of_nat 32) with 32; replace (bv_unsigned sp + -80 + 32) with (bv_unsigned sp + -48) by (clear; lia); exact FS]
          | assumption
          | rewrite <- QB; assumption
          | eapply (bseg_far l OKL PW _ m); [apply FWL| exact OKL| exact SUBl| exact AGL| exact WM| exact BS]
          | exact I ]
        end.
      - assert (C1 : zlen l * 8192 < qbytes) by (revert K1; rewrite ?unsigned_lit by (clear - Z0 ZL QBR; lia); clear; intros K1; lia). clear K1.
        replace (zlen l * 8192 <? qbytes) with true in RS0 by (symmetry; apply Z.ltb_lt; exact C1).
        (* [comment removed for export] *)
        step. step. step. step. litx. rewrite (unsigned_lit (zlen l)), (unsigned_lit qbytes) by (clear - Z0 ZL QBR; lia).
        step. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *)
          assert (C2 : zlen l * 1638400 <= qbytes * 100) by (revert K2; rewrite ?unsigned_lit by (clear - Z0 ZL QBR; lia); clear; intros K2; lia). clear K2.
          replace (qbytes * 100 <? zlen l * 8192 * 200) with false in RS0 by (symmetry; apply Z.ltb_ge; clear - C2; lia). cbn [andb qc_list qc_bytes] in RS0.
          destruct (pop_while (S (length l)) l qbytes qmin []) as [[[l2 b2] rp]|] eqn:POPW; [| discriminate RS0].
          injection RS0 as E1 E2 E3 E4. subst l2 b2 rp. rewrite QB in POPW.
          pose proof (munch_agree _ _ _ MUL) as AGL.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mN _) =>
            apply (rec_join2 l [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mN POPW (eq_sym E3) OKL ltac:(constructor) ltac:(intros b Hb; rewrite app_nil_r in Hb; exact (SUBl b Hb))
                     ltac:(rewrite app_nil_r; exact NDL) ltac:(rewrite bsum_nil; clear - QB; lia) ltac:(rewrite zlen_nil'; clear; lia) ltac:(assumption) MU WM ltac:(assumption));
            [ apply (proj2 (rw_cells_app asegs _ _ [C8 _; C8 _; C8 _; C8 _] [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _])); split; [exact FT| cbn [cells_size csize Nat.add]; change (Z.of_nat 32) with 32; replace (bv_unsigned sp + -80 + 32) with (bv_unsigned sp + -48) by (clear; lia); exact FS]
            | assumption
            | rewrite <- QB; assumption
            | eapply (bseg_far l OKL PW _ m); [apply FWL| exact OKL| exact SUBl| exact AGL| exact WM| exact BS]
            | exact I ]
          end.
        + (* [comment removed for export] *)
          assert (C2 : qbytes * 100 < zlen l * 1638400) by (revert K2; rewrite ?unsigned_lit by (clear - Z0 ZL QBR; lia); clear; intros K2; lia). clear K2.
          replace (qbytes * 100 <? zlen l * 8192 * 200) with true in RS0 by (symmetry; apply Z.ltb_lt; clear - C2; lia). cbn [andb qc_list qc_bytes] in RS0.
          destruct (merge_batches {| qc_list := l; qc_bytes := qbytes |}) as [[[[lF qbF] ex] xb]|] eqn:MB; [| discriminate RS0]. cbn [qc_list qc_bytes] in RS0.
          destruct (pop_while (S (length lF)) lF qbF qmin []) as [[[l2 b2] rp]|] eqn:POPW; [| discriminate RS0].
          injection RS0 as E1 E2 E3 E4. subst l2 b2 rp.
          pose proof (merge_batches_bsum _ _ _ _ _ _ MB) as (SB1 & SB2 & SB3 & SB4). pose proof (merge_batches_zlen _ _ _ _ _ _ MB) as ZB.
          pose proof (bsum_all ex SB4) as SBX. unfold kBatchSize in SB3, SBX.
          assert (QBF : qbF = bsum lF) by (clear - SB1 SB2 QB; lia). rewrite QBF in POPW.
          pose proof SPA' as SPk. apply Z.mod_divide in SPk; [| clear; lia]. destruct SPk as [k Hk].
          (* [comment removed for export] *)
          step. step. step. step. step. step. step. litx. step.
          pose proof (munch_agree _ _ _ MUL) as AGL.
          assert (BS0 : forall mX, agree_on (outside [(bv_unsigned sp + -96, bv_unsigned sp); (6977032, 6977040); (6977040, 6977072)]%Z) m mX -> wmono asegs m mX -> bseg mX l 0)
            by (intros mX AGX WMX; eapply (bseg_far l OKL PW _ m); [apply FWL| exact OKL| exact SUBl| exact AGX| exact WMX| exact BS]).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mN _) => specialize (BS0 mN AGL WM) end.
          eapply evt_cut.
          { eapply (merge_batches_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 6977040 (bv_unsigned sp + -80) qbytes 0 (Z_to_bv 64 0) (Z_to_bv 64 0) l lF ex xb qbF).
            * assumption.
            * rewrite unsigned_lit by (clear - SPR LO HI ACEILB; lia). assumption.
            * exact LO.
            * rewrite unsigned_lit by (clear - SPR LO HI ACEILB; lia). clear - HI; lia.
            * unfold AIMG_TOP; clear. split; [lia|]. split; [lia| reflexivity].
            * rewrite unsigned_lit by (clear - SPR LO HI ACEILB; lia). split; [clear; lia|]. split; [clear - SPT; lia|].
              rewrite Hk. replace (k * 16 + -80) with ((2 * k - 10) * 8) by (clear; lia). apply Z_mod_mult.
            * clear - QBR; lia.
            * clear - QBR; lia.
            * exact OKL.
            * exact NDL.
            * exact PW.
            * clear - QB; lia.
            * reflexivity.
            * reflexivity.
            * assumption.
            * apply bseg_batches; exact BS0.
            * exact FT.
            * exact MB. }
          cbv beta. intros ms' PO. unfold merge_batches_post in PO.
          destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & m1 & -> & MU1 & WM1 & MI1 & ST1 & HQ1 & BRF & HT1 & BRX & OKF & OKX & EXE & SUBL & XBE & NDX).
          rewrite ?unsigned_lit in MU1 by (clear - SPR LO HI ACEILB; lia). rewrite ?unsigned_lit in ST1 by (clear - SPR LO HI ACEILB; lia). rewrite ?unsigned_lit in HT1 by (clear - SPR LO HI ACEILB; lia).
          replace (ret_pc (Z_to_bv 64 1674780)) with (Z_to_bv 64 1674780) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
          (* [comment removed for export] *)
          pose proof (munch_agree _ _ _ MU1) as AG1.
          assert (FS1 : rw_cells asegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
          { eapply (rw_cells_transport_pt _ _ m1 AG1 WM1); [exact FS|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 48) with 48. intros a Ha. cbn [outside].
            split; [clear - Ha; lia|]. split; [clear - Ha LO HI ACEILB; lia|]. split; [clear - Ha; lia|]. apply (outside_bext_hi l a OKL). clear - Ha LO HI; lia. }
          lazymatch goal with H : rw_cells _ _ 6977032 _ |- _ =>
            assert (QM1 : rw_cells asegs m1 6977032 [C4 (Z_to_bv 64 257); C4 (Z_to_bv 64 0)])
              by (eapply (rw_cells_transport_pt _ _ m1 AG1 WM1); [exact H|]; cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; intros a Ha; cbn [outside];
                  split; [clear - Ha LO HI ACEILB; lia|]; split; [clear - Ha; lia|]; split; [clear - Ha LO HI ACEILB; lia|]; apply (outside_bext_lo l a OKL); unfold AIMG_TOP; clear - Ha; lia);
            clear H
          end.
          assert (MU2 : munch ((bv_unsigned sp + -96, bv_unsigned sp) :: (6977032, 6977040) :: (6977040, 6977072) :: map bext l)%Z m m1).
          { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4).
            split; [clear - X1; lia|]. split; [exact X3|]. split; [clear - X1; lia| exact X4]. }
          assert (WM2 : wmono asegs m m1) by (eapply wmono_trans; [exact WM| exact WM1]).
          clear MU WM MUL AGL FS FT BS0.
          (* [comment removed for export] *)
          step. step. step. step. step.
          rewrite thdr00 in HT1. cbn [fst snd] in HT1. replace (0 + xb) with (bsum ex) in HT1 by (clear - SBX SB3; lia).
          replace (qbytes - xb) with (bsum lF) in HQ1 by (clear - SB1 QB; lia).
          apply (rec_join2 lF ex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 POPW (eq_sym E3) OKF OKX SUBL NDX ltac:(clear - SB1 SB3 SBX QB; lia) ZB MI1 MU2 WM2 ST1);
            [ apply (proj2 (rw_cells_app asegs _ _ [C8 _; C8 _; C8 _; C8 _] [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _])); split; [exact HT1| cbn [cells_size csize Nat.add]; change (Z.of_nat 32) with 32; replace (bv_unsigned sp + -80 + 32) with (bv_unsigned sp + -48) by (clear; lia); exact FS1]
            | exact QM1
            | exact HQ1
            | apply bseg_batches; exact BRF
            | apply bseg_batches; exact BRX ].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition recycle_tail_post (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) : machine_state -> Prop :=
      fun ms' => ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m2 (seg_rom asegs)
                 /\ stk asegs m2 lo (bv_unsigned sp).
    Lemma recycle_tail : forall (rax t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 t3' t4' t5' t6' z0 z1 z2 z3 : word) (m2 : mem),
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -80) ->
      rw_cells asegs m2 (bv_unsigned sp + -80) [C8 z0; C8 z1; C8 z2; C8 z3; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt asegs (recycle_tail_post t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x198ee4) fc None m2 (seg_rom asegs)).
    Proof.
      intros until m2. intros MI2 ST2 FR. clear MI ST QM GQ BR.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR. acb.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      step.
      apply evt_done. split; [reflexivity| assumption].
    Qed.

  End Recycle.
