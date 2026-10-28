(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG CtWire.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApWalkTac W_prefix_create ApErrKit ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition osz32 (o : option bptr) : option (bptr * Z) := option_map (fun q => (q, 32)) o.      (* [comment removed for export] *)
Lemma fst_osz32 : forall o, option_map fst (osz32 o) = o. Proof. intros [q|]; reflexivity. Qed.

Definition lfree_sct {X} (s : sctr bptr) (k : lprog X) : lprog X :=
  lofree (sc_logid s) (lofree (option_map fst (sc_ext s)) (lofree (option_map fst (sc_sig s)) (lofree (option_map fst (sc_blob s)) (LFree (sc_blk s) k)))).
Fixpoint lfree_scts {X} (l : list (sctr bptr)) (k : lprog X) : lprog X :=
  match l with [] => k | s :: t => lfree_sct s (lfree_scts t k) end.

Definition oblk (adr : bptr -> Z) (o : option (bptr * Z)) : list block := match o with Some (q, n) => [(q, adr q, n)] | None => [] end.
Definition sct_blocks (adr : bptr -> Z) (s : sctr bptr) : list block :=
  oblk adr (osz32 (sc_logid s)) ++ oblk adr (sc_ext s) ++ oblk adr (sc_sig s) ++ oblk adr (sc_blob s) ++ [(sc_blk s, adr (sc_blk s), SCT_SIZE)].
Fixpoint scts_blocks (adr : bptr -> Z) (l : list (sctr bptr)) : list block :=
  match l with [] => [] | s :: t => sct_blocks adr s ++ scts_blocks adr t end.

(* [comment removed for export] *)
Definition remove_sct (s : sctr bptr) (L : list block) : list block :=
  lb_remove (sc_blk s) (lremove (sc_blob s) (lremove (sc_sig s) (lremove (sc_ext s) (lremove (osz32 (sc_logid s)) L)))).
Fixpoint remove_scts (l : list (sctr bptr)) (L : list block) : list block :=
  match l with [] => L | s :: t => remove_scts t (remove_sct s L) end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition sct_ptr_cells (m : mem) (adr : bptr -> Z) (s : sctr bptr) : Prop :=
  let A := adr (sc_blk s) in
  ro_cells ctusegs m (A + SCTO_SCT) [C8 (wz (optr adr (sc_blob s)))]
  /\ ro_cells ctusegs m (A + SCTO_LOG_ID) [C8 (wz (optr adr (osz32 (sc_logid s))))]
  /\ ro_cells ctusegs m (A + SCTO_EXT) [C8 (wz (optr adr (sc_ext s)))]
  /\ ro_cells ctusegs m (A + SCTO_SIG) [C8 (wz (optr adr (sc_sig s)))].

(* [comment removed for export] *)
Fixpoint data_cells (m : mem) (adr : bptr -> Z) (D i : Z) (l : list (sctr bptr)) : Prop :=
  match l with [] => True | s :: t => ro_cells ctusegs m (D + 8 * i) [C8 (wz (adr (sc_blk s)))] /\ data_cells m adr D (i + 1) t end.

(* [comment removed for export] *)
Lemma in_lb_remove_other : forall b q L, In b L -> blk_id b <> q -> In b (lb_remove q L).
Proof. intros b q L H Hq. apply lb_remove_In. split; [exact H| exact Hq]. Qed.
Lemma in_lremove_other : forall b od L, In b L -> (match od with Some (q, _) => blk_id b <> q | None => True end) -> In b (lremove od L).
Proof. intros b [[q n]|] L H Hq; cbn [lremove]; [apply in_lb_remove_other; assumption| exact H]. Qed.
Lemma remove_sct_incl : forall s L b, In b (remove_sct s L) -> In b L.
Proof. intros s L b H. unfold remove_sct in H. apply lb_remove_incl in H. do 4 (apply lremove_incl in H). exact H. Qed.
Lemma remove_scts_incl : forall l L b, In b (remove_scts l L) -> In b L.
Proof. induction l as [|s t IH]; intros L b H; [exact H|]. cbn [remove_scts] in H. apply remove_sct_incl with (s := s). apply IH. exact H. Qed.

(* [comment removed for export] *)
Lemma in_remove_sct : forall adr s L b, In b L -> ~ In (blk_id b) (map blk_id (sct_blocks adr s)) -> In b (remove_sct s L).
Proof.
  intros adr s L b H N. unfold remove_sct. unfold sct_blocks in N. rewrite !map_app, !in_app_iff in N. cbn [map blk_id fst snd] in N.
  apply in_lb_remove_other; [|intros E; apply N; right; right; right; right; left; first [exact E | symmetry; exact E]].
  apply in_lremove_other; [|destruct (sc_blob s) as [[q n]|]; [intros E; apply N; right; right; right; left; cbn; left; first [exact E | symmetry; exact E]| exact I]].
  apply in_lremove_other; [|destruct (sc_sig s) as [[q n]|]; [intros E; apply N; right; right; left; cbn; left; first [exact E | symmetry; exact E]| exact I]].
  apply in_lremove_other; [|destruct (sc_ext s) as [[q n]|]; [intros E; apply N; right; left; cbn; left; first [exact E | symmetry; exact E]| exact I]].
  apply in_lremove_other; [exact H|]. destruct (sc_logid s) as [q|]; [intros E; apply N; left; cbn; left; first [exact E | symmetry; exact E]| exact I].
Qed.

Lemma in_remove_scts_keep : forall adr l L b, In b L -> ~ In (blk_id b) (map blk_id (scts_blocks adr l)) -> In b (remove_scts l L).
Proof.
  induction l as [|x l IH]; intros L b H N; [exact H|]. cbn [remove_scts scts_blocks] in *. rewrite map_app, in_app_iff in N.
  apply IH; [apply in_remove_sct with (adr := adr); [exact H| intros I1; apply N; left; exact I1]| intros I2; apply N; right; exact I2].
Qed.

Lemma NoDup_lremove : forall od L, List.NoDup (map blk_id L) -> List.NoDup (map blk_id (lremove od L)).
Proof. intros [[q n]|] L ND; cbn; [apply NoDup_lb_remove; exact ND|exact ND]. Qed.

Lemma NoDup_app_split : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2 /\ (forall x, In x l1 -> ~ In x l2) /\ List.NoDup l1.
Proof.
  induction l1 as [|a l1 IH]; intros l2 H; cbn in H.
  - split; [exact H|]. split; [intros x []|constructor].
  - apply NoDup_cons_iff in H. destruct H as [Ha H]. destruct (IH l2 H) as (H2 & HX & H1).
    split; [exact H2|]. split.
    + intros x [<-|Hx]; [intros I2; apply Ha; apply in_app_iff; right; exact I2| apply HX; exact Hx].
    + constructor; [intros I1; apply Ha; apply in_app_iff; left; exact I1| exact H1].
Qed.


(* [comment removed for export] *)
Lemma ro_in_block_pres : forall L' SP mA mB p A n X cs,
  rheap_pres L' SP mA mB -> In (p, A, n) L' -> A <= X -> X + Z.of_nat (cells_size cs) <= A + n ->
  ro_cells ctusegs mA X cs -> ro_cells ctusegs mB X cs.
Proof.
  intros L' SP mA mB p A n X cs HP IN X1 X2 H. eapply (ro_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)); [exact H|].
  intros a Ha. right. right. exists (p, A, n). split; [exact IN|]. cbn. lia.
Qed.
Lemma sct_ptr_cells_pres : forall L' SP mA mB adr x,
  rheap_pres L' SP mA mB -> In (sc_blk x, adr (sc_blk x), SCT_SIZE) L' -> sct_ptr_cells mA adr x -> sct_ptr_cells mB adr x.
Proof.
  intros L' SP mA mB adr x HP IN H. unfold sct_ptr_cells in *. cbn zeta in *. unfold SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG, SCT_SIZE in *.
  destruct H as (C1 & C2 & C3 & C4).
  split; [|split; [|split]]; (eapply ro_in_block_pres; [exact HP| exact IN| lia| cbn; lia| assumption]).
Qed.
Lemma scts_blocks_struct_in : forall adr l x, In x l -> In (sc_blk x, adr (sc_blk x), SCT_SIZE) (scts_blocks adr l).
Proof.
  induction l as [|y l IH]; intros x H; [destruct H|]. cbn [scts_blocks]. apply in_app_iff. destruct H as [<-|H].
  - left. unfold sct_blocks. rewrite !in_app_iff. right. right. right. right. left. reflexivity.
  - right. apply IH. exact H.
Qed.
Lemma scts_ptr_cells_pres : forall L' SP mA mB adr l,
  rheap_pres L' SP mA mB -> Forall (fun b => In b L') (scts_blocks adr l) -> Forall (sct_ptr_cells mA adr) l -> Forall (sct_ptr_cells mB adr) l.
Proof.
  intros L' SP mA mB adr l HP HIN H. apply Forall_forall. intros x Hx. eapply sct_ptr_cells_pres; [exact HP| | exact (proj1 (Forall_forall _ _) H x Hx)].
  exact (proj1 (Forall_forall _ _) HIN _ (scts_blocks_struct_in adr l x Hx)).
Qed.
Lemma data_cells_pres : forall L' SP mA mB adr pd D dn l i,
  rheap_pres L' SP mA mB -> In (pd, D, dn) L' -> 0 <= i -> 8 * (i + zlength l) <= dn -> data_cells mA adr D i l -> data_cells mB adr D i l.
Proof.
  intros L' SP mA mB adr pd D dn l. revert l. induction l as [|x l IH]; intros i HP IN I0 BND H; [exact I|].
  cbn [data_cells] in *. destruct H as [H1 H2]. unfold zlength in BND. cbn [length] in BND. rewrite Nat2Z.inj_succ in BND.
  split; [eapply ro_in_block_pres; [exact HP| exact IN| lia| cbn; lia| exact H1]|].
  apply IH; [exact HP| exact IN| lia| unfold zlength; lia| exact H2].
Qed.
Lemma scts_blocks_in_remove : forall adr x l L,
  List.NoDup (map blk_id (sct_blocks adr x ++ scts_blocks adr l)) -> Forall (fun b => In b L) (scts_blocks adr l) ->
  Forall (fun b => In b (remove_sct x L)) (scts_blocks adr l).
Proof.
  intros adr x l L ND H. apply Forall_forall. intros b Hb. apply in_remove_sct with (adr := adr); [exact (proj1 (Forall_forall _ _) H b Hb)|].
  rewrite map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & HX & _). intros I1. exact (HX _ I1 (in_map _ _ _ Hb)).
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition SK_POP_FREE_STACK : Z := 48 + SCT_FREE_STACK.
  Definition PF_BODY : Z := 0xe76f0.      (* [comment removed for export] *)
  Definition PF_TAIL : Z := 0xe7750.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma SCT_free_walk' : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (adr : bptr -> Z) (x : sctr bptr)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SCT_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    Forall (fun b => In b L) (sct_blocks adr x) -> List.NoDup (map blk_id (sct_blocks adr x)) -> List.NoDup (map blk_id L) ->
    sct_ptr_cells m adr x ->
    a0 = wz (adr (sc_blk x)) ->
    (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (remove_sct x L) lo B errv m s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (lfree_sct x k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz SCT_FREE) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI TP CS HIN ND NDL (C1 & C2 & C3 & C4) HA0 K.
    unfold lfree_sct. rewrite <- (fst_osz32 (sc_logid x)).
    unfold sct_blocks in HIN, ND. rewrite !Forall_app in HIN. destruct HIN as (I1 & I2 & I3 & I4 & I5).
    apply Forall_inv in I5.
    rewrite !map_app in ND. cbn [map oblk blk_id fst snd app] in ND.
    eapply (SCT_free_walk HF) with (oL := osz32 (sc_logid x)) (oE := sc_ext x) (oS := sc_sig x) (oB := sc_blob x) (adr := adr);
      [exact HEAP| exact AUX| exact SPB| exact ST| exact CEIL| exact GLO| exact LO| exact ERR| exact MI| exact TP| exact CS
      | exact I5 | | | | | | exact C1| exact C2| exact C3| exact C4| exact HA0| exact K].
    - destruct (osz32 (sc_logid x)) as [[q n]|] eqn:EL; [|exact I]. apply Forall_inv in I1. exact I1.
    - destruct (sc_ext x) as [[q n]|] eqn:EE; [|exact I]. apply Forall_inv in I2. apply in_lremove_other; [exact I2|].
      destruct (osz32 (sc_logid x)) as [[q' n']|] eqn:EL; [|exact I]. cbn. cbn [oblk map blk_id fst snd app] in ND.
      apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. left. first [exact E | first [exact E | symmetry; exact E]].
    - destruct (sc_sig x) as [[q n]|] eqn:ES; [|exact I]. apply Forall_inv in I3.
      apply in_lremove_other; [apply in_lremove_other; [exact I3|]|].
      + destruct (osz32 (sc_logid x)) as [[q' n']|]; [|exact I]. cbn. cbn [oblk map blk_id fst snd app] in ND.
        apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. rewrite in_app_iff. right. left. first [exact E | first [exact E | symmetry; exact E]].
      + destruct (sc_ext x) as [[q' n']|]; [|exact I]. cbn. cbn [oblk map blk_id fst snd app] in ND.
        destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x)))) _ ND) as (N2 & _ & _). apply NoDup_cons_iff in N2. destruct N2 as [N2 _].
        intros E. apply N2. left. first [exact E | first [exact E | symmetry; exact E]].
    - destruct (sc_blob x) as [[q n]|] eqn:EB; [|exact I]. apply Forall_inv in I4.
      apply in_lremove_other; [apply in_lremove_other; [apply in_lremove_other; [exact I4|]|]|].
      + destruct (osz32 (sc_logid x)) as [[q' n']|]; [|exact I]. cbn. cbn [oblk map blk_id fst snd app] in ND.
        apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. rewrite !in_app_iff. right. right. left. first [exact E | first [exact E | symmetry; exact E]].
      + destruct (sc_ext x) as [[q' n']|]; [|exact I]. cbn. cbn [oblk map blk_id fst snd app] in ND.
        destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x)))) _ ND) as (N2 & _ & _). apply NoDup_cons_iff in N2. destruct N2 as [N2 _].
        intros E. apply N2. rewrite in_app_iff. right. left. first [exact E | first [exact E | symmetry; exact E]].
      + destruct (sc_sig x) as [[q' n']|]; [|exact I]. cbn. cbn [oblk map blk_id fst snd app] in ND.
        destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x))) ++ map blk_id (oblk adr (sc_ext x))) _ ltac:(rewrite <- app_assoc; exact ND)) as (N3 & _ & _).
        apply NoDup_cons_iff in N3. destruct N3 as [N3 _]. intros E. apply N3. left. first [exact E | first [exact E | symmetry; exact E]].
    - (* [comment removed for export] *)
      apply in_lremove_other; [apply in_lremove_other; [apply in_lremove_other; [apply in_lremove_other; [exact I5|]|]|]|]; cbn [blk_id fst snd].
      + destruct (osz32 (sc_logid x)) as [[q' n']|]; [|exact I]. cbn [oblk map blk_id fst snd app] in ND.
        apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. rewrite !in_app_iff. right. right. right. left. first [exact E | first [exact E | symmetry; exact E]].
      + destruct (sc_ext x) as [[q' n']|]; [|exact I]. cbn [oblk map blk_id fst snd app] in ND.
        destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x)))) _ ND) as (N2 & _ & _). apply NoDup_cons_iff in N2. destruct N2 as [N2 _].
        intros E. apply N2. rewrite !in_app_iff. right. right. left. first [exact E | first [exact E | symmetry; exact E]].
      + destruct (sc_sig x) as [[q' n']|]; [|exact I]. cbn [oblk map blk_id fst snd app] in ND.
        destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x))) ++ map blk_id (oblk adr (sc_ext x))) _ ltac:(rewrite <- app_assoc; exact ND)) as (N3 & _ & _).
        apply NoDup_cons_iff in N3. destruct N3 as [N3 _]. intros E. apply N3. rewrite in_app_iff. right. left. first [exact E | first [exact E | symmetry; exact E]].
      + destruct (sc_blob x) as [[q' n']|]; [|exact I]. cbn [oblk map blk_id fst snd app] in ND.
        destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x))) ++ map blk_id (oblk adr (sc_ext x)) ++ map blk_id (oblk adr (sc_sig x))) _
                    ltac:(rewrite <- !app_assoc; exact ND)) as (N4 & _ & _).
        apply NoDup_cons_iff in N4. destruct N4 as [N4 _]. intros E. apply N4. left. first [exact E | first [exact E | symmetry; exact E]].
  Qed.

  (* [comment removed for export] *)
  Definition pf_frame (m : mem) (sp ra s0 s1 s2 s3 s4 : word) : Prop :=
    rw_cells ctusegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition st_cells (m : mem) (SA num D : Z) : Prop :=
    ro_cells ctusegs m SA [C4 (wz num)] /\ ro_cells ctusegs m (SA + SKO_DATA) [C8 (wz D)] /\ ro_cells ctusegs m (SA + SKO_FREE_THUNK) [C8 (wz SK_SCT_FREEFUNC_THUNK)].

  Definition pf_tail_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L' : list block) (lo B : Z) (errv : word) (m : mem) (SA num D : Z) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (wz SA) a0 a1 a2 a3 a4 a5 a6 a7 (wz SCT_FREE) x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PF_TAIL) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres L' (bv_unsigned sp + -48) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' L' m' /\ crypto_statics m' /\ pf_frame m' sp ra s0 s1 s2 s3 s4 /\ st_cells m' SA num D.

  (* [comment removed for export] *)
  Lemma pop_free_loop : forall {X : Type} (rest : list (sctr bptr))
      (ra x1 sp gp t0 t1 t2 x8 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (adr : bptr -> Z) (pst pd : bptr) (SA D dn num i : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    rest <> [] ->
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SK_POP_FREE_STACK -> bv_unsigned sp mod 16 = 0 ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> crypto_statics m ->
    pf_frame m sp ra s0 s1 s2 s3 s4 -> st_cells m SA num D ->
    In (pst, SA, STACK_SIZE) L -> In (pd, D, dn) L -> 8 * num <= dn ->
    0 <= i -> i + zlength rest = num -> num < 2 ^ 31 ->
    data_cells m adr D i rest -> Forall (sct_ptr_cells m adr) rest ->
    Forall (fun b => In b L) (scts_blocks adr rest) ->
    List.NoDup (map blk_id (scts_blocks adr rest ++ [(pd, D, dn); (pst, SA, STACK_SIZE)])) -> List.NoDup (map blk_id L) ->
    (forall s' ms', pf_tail_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (remove_scts rest L) lo B errv m SA num D s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (lfree_scts rest k)) s Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (wz SA) a0 a1 a2 a3 a4 a5 a6 a7 (wz SCT_FREE) (wz (8 * i)) (wz i) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PF_BODY) fc None m (seg_rom ctusegs)).
  Proof using HF.
    induction rest as [|x rest IH]; [intros; congruence|].
    intros until Q. intros _ HEAP AUX SPB STK CEIL GLO LO SP16 ERR MI CS PFR (SC1 & SC2 & SC3) HST HD DN I0 NUM N31 (DC & DCS) PC HIN ND NDL K.
    apply Forall_cons_iff in PC. destruct PC as [PCx PC].
    unfold SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, PF_BODY, PF_TAIL, GLOBALS_TOP, MallocRep.wz in *.
    unfold SKO_DATA, SKO_FREE_THUNK, STACK_SIZE, SCT_SIZE, SK_SCT_FREEFUNC_THUNK, SCT_FREE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HST) as (BS0 & BS1 & BS2 & BS3 & BS4).
    pose proof (LH_block_range _ _ _ _ HEAP HD) as (BD0 & BD1 & BD2 & BD3 & BD4). cbn [blk_addr blk_size fst snd] in *.
    assert (NUM' : i + 1 + zlength rest = num) by (unfold zlength in *; cbn [length] in NUM; rewrite Nat2Z.inj_succ in NUM; lia). clear NUM. rename NUM' into NUM.
    pose proof (Zle_0_nat (length rest)) as LR0. unfold zlength in NUM.
    cbn [scts_blocks] in HIN, ND. rewrite Forall_app in HIN. destruct HIN as [HINx HIN].
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    unfold pf_frame in PFR. unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    pose proof HINx as HINx'. unfold sct_blocks in HINx'. rewrite !Forall_app in HINx'. destruct HINx' as (_ & _ & _ & _ & I5). apply Forall_inv in I5.
    pose proof (LH_block_range _ _ _ _ HEAP I5) as (BX0 & BX1 & BX2 & BX3 & BX4). cbn [blk_addr blk_size fst snd] in BX0, BX1, BX2, BX3, BX4.
    step. step. ub. remember (D + 8 * i) as Di eqn:EDi. step. subst Di.
    step. if_cases K0; zify_cond K0; [exfalso; try rewrite <- unsigned_lit_land, ?unsigned_lit in K0 by lia; lia|]. clear K0.
    (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; revert K1; vm_compute; congruence|]. clear K1.
    step. step.
    replace (ret_pc (Z_to_bv 64 1691848)) with (Z_to_bv 64 1691848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 48)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    carve_frame 16%nat STK. do 4 step. step. step. do 3 step. release_frame FR STK (bv_unsigned sp + -48). step.
    replace (ret_pc (Z_to_bv 64 1692940)) with (Z_to_bv 64 1692940) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp + -48) a -> outside [(bv_unsigned sp - 64, bv_unsigned sp - 48)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp + -48) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    (* [comment removed for export] *)
    apply (sct_ptr_cells_pres _ _ _ _ _ _ HP0 I5) in PCx.
    apply (scts_ptr_cells_pres _ _ _ _ _ _ HP0 HIN) in PC.
    apply (data_cells_pres _ _ _ _ _ _ _ _ _ _ HP0 HD) in DCS; [| lia| unfold zlength; lia].
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    cbn [lfree_scts].
    eapply (SCT_free_walk' ) with (B := B) (lo := lo) (errv := errv) (adr := adr) (L := L);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact STK | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | exact HINx | | exact NDL | exact PCx | reflexivity | ].
    { rewrite map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & _ & NDx). rewrite map_app in NDx. destruct (NoDup_app_split _ _ NDx) as (_ & _ & NDx1). exact NDx1. }
    intros st1 ms1 PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP1 & FA1 & SO1 & HEAP2).
    replace (ret_pc (Z_to_bv 64 948020)) with (Z_to_bv 64 948020) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof ND as ND0. rewrite map_app in ND0. destruct (NoDup_app_split _ _ ND0) as (_ & _ & NDxr).          (* [comment removed for export] *)
    rewrite <- app_assoc, map_app in ND. destruct (NoDup_app_split _ _ ND) as (NDrt & NXx & NDx).                (* [comment removed for export] *)
    assert (HST2 : In (pst, SA, 56) (remove_sct x L)).
    { apply in_remove_sct with (adr := adr); [exact HST|]. intros I1. refine (NXx _ I1 _). rewrite map_app, in_app_iff. right. cbn. right. left. reflexivity. }
    assert (HD2 : In (pd, D, dn) (remove_sct x L)).
    { apply in_remove_sct with (adr := adr); [exact HD|]. intros I1. refine (NXx _ I1 _). rewrite map_app, in_app_iff. right. cbn. left. reflexivity. }
    assert (HIN2 : Forall (fun b => In b (remove_sct x L)) (scts_blocks adr rest)) by (apply scts_blocks_in_remove; [exact NDxr| exact HIN]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP1)) in PFR; [| intros a Ha; left; cbn in Ha; lia].
    apply (ro_in_block_pres _ _ _ _ _ _ _ _ _ HP1 HST2) in SC1; [|lia|cbn; lia]. apply (ro_in_block_pres _ _ _ _ _ _ _ _ _ HP1 HST2) in SC2; [|lia|cbn; lia].
    apply (ro_in_block_pres _ _ _ _ _ _ _ _ _ HP1 HST2) in SC3; [|lia|cbn; lia].
    apply (scts_ptr_cells_pres _ _ _ _ _ _ HP1 HIN2) in PC.
    apply (data_cells_pres _ _ _ _ _ _ _ _ _ _ HP1 HD2) in DCS; [| lia| unfold zlength; lia].
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP1)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
    assert (HP01 : rheap_pres (remove_sct x L) (bv_unsigned sp + -48) m m2).
    { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply remove_sct_incl; exact Hb]| exact HP1]. }
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. step.
    step. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      destruct rest as [|y rest']; [exfalso; unfold zlength in NUM; cbn [length] in NUM; rewrite ?sx32_small, ?signed_small in K2 by lia; lia|].
      replace (Z_to_bv 64 (8 * i + 8)) with (Z_to_bv 64 (8 * (i + 1))) by (f_equal; lia).
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
      eapply (IH) with (B := B) (lo := lo) (errv := errv) (L := remove_sct x L) (pst := pst) (pd := pd) (dn := dn) (num := num);
        [congruence| exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact SP16
        | unfold LX_ERRNO, RATP; exact ERR2| exact MI2| exact CS2| exact PFR| split; [exact SC1| split; [exact SC2| exact SC3]]
        | exact HST2| exact HD2| exact DN| lia| unfold zlength in *; cbn [length] in *; lia| exact N31| exact DCS| exact PC| exact HIN2
        | exact NDrt| | ].
      { unfold remove_sct. apply NoDup_lb_remove. do 4 (apply NoDup_lremove). exact NDL. }
      intros s' ms' PO. apply K. unfold pf_tail_post in *.
      destruct PO as (ux1 & u0 & u1 & u2 & u8 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u19 & u20 & u3 & u4 & u5 & u6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3 & CS3 & PFR3 & SC3').
      do 19 eexists. exists m3. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
      split; [eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP01| lia| intros b Hb; cbn [remove_scts] in Hb; apply (remove_scts_incl (y :: rest')); cbn [remove_scts]; exact Hb]| exact HP3]|].
      split; [congruence|]. split; [congruence|]. split; [exact HEAP3|]. split; [exact CS3|]. split; [exact PFR3| exact SC3'].
    - (* [comment removed for export] *)
      destruct rest as [|y rest']; [| exfalso; unfold zlength in NUM; cbn [length] in NUM; rewrite ?sx32_small, ?signed_small in K2 by lia; lia].
      apply evt_done. apply K. unfold pf_tail_post. cbn [remove_scts].
      do 19 eexists. exists m2. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
      split; [exact HP01|]. split; [congruence|]. split; [congruence|]. split; [exact HEAP2|]. split; [exact CS2|].
      split; [exact PFR| split; [exact SC1| split; [exact SC2| exact SC3]]].
  Qed.

  (* [comment removed for export] *)
  Lemma pop_free_tail : forall {X : Type}
      (ra x1 sp gp t0 t1 t2 x8 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (adr : bptr -> Z) (pst : bptr) (odata : option (bptr * Z)) (SA num : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SK_POP_FREE_STACK -> bv_unsigned sp mod 16 = 0 ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> crypto_statics m ->
    pf_frame m sp ra s0 s1 s2 s3 s4 -> st_cells m SA num (optr adr odata) ->
    In (pst, SA, STACK_SIZE) L -> match odata with Some (q, n) => In (q, adr q, n) L /\ q <> pst | None => True end ->
    (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pst (lremove odata L)) lo B errv m s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (lofree (option_map fst odata) (LFree pst k))) s Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 x8 (wz SA) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PF_TAIL) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. intros HEAP AUX SPB STK CEIL GLO LO SP16 ERR MI CS PFR (SC1 & SC2 & SC3) HST HOD K.
    unfold SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, PF_TAIL, GLOBALS_TOP, MallocRep.wz in *.
    unfold SKO_DATA, SKO_FREE_THUNK, STACK_SIZE, SK_SCT_FREEFUNC_THUNK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HST) as (BS0 & BS1 & BS2 & BS3 & BS4). cbn [blk_addr blk_size fst snd] in BS0, BS1, BS2, BS3, BS4.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (SEPS : SA + 56 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= SA) by lia.
    unfold pf_frame in PFR. unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. do 6 step. step. release_frame PFR STK (bv_unsigned sp). step.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    carve_frame 32%nat STK. do 6 step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. uchk.
    step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv) (od := odata) (adr := adr);
      [exact HEAP1 | destruct odata as [[q n]|]; [exact (proj1 HOD)| exact I] | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact STK | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | ].
    intros st1 ms1 PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP1 & FA1 & SO1 & HEAP2).
    replace (ret_pc (Z_to_bv 64 945412)) with (Z_to_bv 64 945412) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP1)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP1)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (HST2 : In (pst, SA, 56) (lremove odata L)).
    { destruct odata as [[q n]|]; cbn [lremove]; [apply in_lb_remove_other; [exact HST| cbn; intros E; apply (proj2 HOD); symmetry; exact E]| exact HST]. }
    unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. do 4 step. step. release_frame FR ST2 (bv_unsigned sp). step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := SA) (n := 56);
      [exact HEAP2 | exact HST2 | exact AUX2 | lia | exact ST2 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI2 | reflexivity
      | exact CS2 | reflexivity | ].
    intros st2 ms2 PO. apply K. unfold cfree_post in PO. unfold ofree_post.
    destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP2 & FA2 & SO2 & HEAP3).
    do 15 eexists. exists m3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lremove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP1| lia| intros b Hb; eapply lb_remove_incl; exact Hb]| exact HP2]. }
    split; [congruence|]. split; [congruence|]. exact HEAP3.
  Qed.

  Definition SCT_LIST_FREE_STACK : Z := SK_POP_FREE_STACK.

  (* [comment removed for export] *)
  Theorem SCT_LIST_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (adr : bptr -> Z) (sk : skr bptr)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    let SA := adr (sk_blk sk) in let items := sk_items sk in let num := zlength items in
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SCT_LIST_FREE_STACK -> bv_unsigned sp mod 16 = 0 ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP -> crypto_statics m ->
    ro_cells ctusegs m SCT_FREE_GOT [C8 (wz SCT_FREE_VA)] ->
    st_cells m SA num (optr adr (sk_data sk)) ->
    In (sk_blk sk, SA, STACK_SIZE) L ->
    match sk_data sk with Some (q, na) => In (q, adr q, 8 * na) L /\ num <= na | None => items = [] end ->      (* [comment removed for export] *)
    num < 2 ^ 31 ->
    data_cells m adr (optr adr (sk_data sk)) 0 items -> Forall (sct_ptr_cells m adr) items ->
    Forall (fun b => In b L) (scts_blocks adr items) ->
    List.NoDup (map blk_id (scts_blocks adr items ++ oblk adr (sk_data sk) ++ [(sk_blk sk, SA, STACK_SIZE)])) -> List.NoDup (map blk_id L) ->
    a0 = wz SA ->
    (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove (sk_blk sk) (lremove (sk_data sk) (remove_scts items L))) lo B errv m s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (lfree_scts items (lofree (option_map fst (sk_data sk)) (LFree (sk_blk sk) k)))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz SCT_LIST_FREE) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. cbn zeta. intros HEAP AUX SPB STK CEIL GLO LO SP16 ERR MI -> CS GOT (SC1 & SC2 & SC3) HST HOD N31 DCS PC HIN ND NDL -> K.
    unfold SCT_LIST_FREE_STACK, SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, SCT_LIST_FREE, GLOBALS_TOP, MallocRep.wz in *.
    unfold SKO_DATA, SKO_FREE_THUNK, STACK_SIZE, SK_SCT_FREEFUNC_THUNK, SCT_FREE_GOT, SCT_FREE_VA in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HST) as (BS0 & BS1 & BS2 & BS3 & BS4). cbn [blk_addr blk_size fst snd] in BS0, BS1, BS2, BS3, BS4.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (Zle_0_nat (length (sk_items sk))) as LR0.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat STK. do 4 step. step. step. do 3 step. release_frame FR STK (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat STK. do 8 step. step. if_cases K0; zify_cond K0; [exfalso; try rewrite <- unsigned_lit_land, ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. uchk. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    apply (scts_ptr_cells_pres _ _ _ _ _ _ HP0 HIN) in PC.
    assert (DCS1 : data_cells m1 adr (optr adr (sk_data sk)) 0 (sk_items sk)).
    { destruct (sk_data sk) as [[pd dn]|] eqn:ED; cbn [optr] in *.
      - apply (data_cells_pres _ _ _ _ _ _ _ _ _ _ HP0 (proj1 HOD)) in DCS; [exact DCS| lia| lia].
      - rewrite HOD. exact I. }
    clear DCS.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    - assert (E0 : sk_items sk = []).
      { destruct (sk_items sk) as [|y r]; [reflexivity| exfalso]. unfold zlength in K1, N31, LR0. cbn [length] in K1, N31, LR0.
        rewrite ?sx32_small, ?unsigned_lit, ?signed_small in K1 by lia. apply Bool.andb_false_iff in K1. destruct K1 as [K1|K1]; apply Z.ltb_ge in K1; lia. }
      rewrite E0 in *. cbn [lfree_scts remove_scts scts_blocks app] in *.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
      set (ODATA := match sk_data sk with Some (q, na) => Some (q, 8 * na) | None => None end).
      replace (option_map fst (sk_data sk)) with (option_map fst ODATA) by (subst ODATA; destruct (sk_data sk) as [[? ?]|]; reflexivity).
      replace (optr adr (sk_data sk)) with (optr adr ODATA) in SC2 by (subst ODATA; destruct (sk_data sk) as [[? ?]|]; reflexivity).
      eapply pop_free_tail with (B := B) (lo := lo) (errv := errv) (adr := adr) (num := zlength (@nil (sctr bptr))) (odata := ODATA);
        [exact HEAP1| exact AUX1| lia| exact STK| exact CEIL| unfold GLOBALS_TOP; lia| unfold SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia| exact SP16
        | unfold LX_ERRNO, RATP; exact ERR| exact MI| exact CS1| exact FR| split; [exact SC1| split; [exact SC2| exact SC3]]| exact HST| | ].
      { subst ODATA. destruct (sk_data sk) as [[pd dn]|]; [|exact I]. split; [exact (proj1 HOD)|].
        cbn [oblk map blk_id fst snd app] in ND. apply NoDup_cons_iff in ND. destruct ND as [ND _]. intros E. apply ND. left. symmetry. exact E. }
      intros s' ms' PO. apply K. unfold ofree_post in *.
      replace (lremove (sk_data sk)) with (lremove ODATA) by (subst ODATA; destruct (sk_data sk) as [[? ?]|]; reflexivity).
      destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP2 & FA2 & SO2 & HEAP3).
      do 15 eexists. exists m3. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
      split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lremove_incl; eapply lb_remove_incl; exact Hb]|].
               eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; exact Hb]. }
      split; [congruence|]. split; [congruence|]. exact HEAP3.
    - (* [comment removed for export] *)
      assert (NE : sk_items sk <> []).
      { intros E0. exfalso.
        repeat match goal with H : context [sx32 (Z_to_bv 64 (zlength (sk_items sk)))] |- _ =>
          rewrite E0 in H; unfold zlength in H; cbn [length] in H; rewrite ?sx32_small, ?unsigned_lit, ?signed_small in H by lia end. lia. }
      step. step. step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
      destruct (sk_data sk) as [[pd dn]|] eqn:ED; [| exfalso; exact (NE HOD)]. destruct HOD as [HDin HDn]. cbn [optr oblk] in *.
      assert (ND8 : List.NoDup (map blk_id (scts_blocks adr (sk_items sk) ++ [(pd, adr pd, 8 * dn); (sk_blk sk, adr (sk_blk sk), 56)]))).
      { revert ND. rewrite !map_app. cbn [map blk_id app fst snd]. intros ND. exact ND. }
      eapply pop_free_loop with (B := B) (lo := lo) (errv := errv) (adr := adr) (L := L) (pst := sk_blk sk) (i := 0) (num := zlength (sk_items sk))
                                 (pd := pd) (dn := 8 * dn) (D := adr pd) (SA := adr (sk_blk sk));
        [exact NE| exact HEAP1| exact AUX1| lia| exact STK| exact CEIL| unfold GLOBALS_TOP; lia| unfold SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia| exact SP16
        | unfold LX_ERRNO, RATP; exact ERR| exact MI| exact CS1| exact FR| split; [exact SC1| split; [exact SC2| exact SC3]]| exact HST| exact HDin| lia| lia| lia| exact N31
        | exact DCS1| exact PC| exact HIN| exact ND8| exact NDL| ].
      intros s' ms' PO. unfold pf_tail_post in PO.
        destruct PO as (ux1 & u0 & u1 & u2 & u8 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u19 & u20 & u3 & u4 & u5 & u6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3 & CS3 & PFR3 & SC3').
        eapply pop_free_tail with (B := B) (lo := lo) (errv := errv) (adr := adr) (odata := Some (pd, 8 * dn));
          [exact HEAP3| exact AUX3| lia| exact ST3| exact CEIL| unfold GLOBALS_TOP; lia| unfold SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia| exact SP16
          | exact ERR3| exact MI3| exact CS3| exact PFR3| exact SC3'| | | ].
        * apply (in_remove_scts_keep adr); [exact HST|]. rewrite !map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & NX & _).
          intros I1. refine (NX _ I1 _). apply in_app_iff. right. cbn. left. reflexivity.
        * split.
          -- apply (in_remove_scts_keep adr); [exact HDin|]. rewrite !map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & NX & _).
             intros I1. refine (NX _ I1 _). apply in_app_iff. left. cbn. left. reflexivity.
          -- rewrite !map_app in ND. destruct (NoDup_app_split _ _ ND) as (N2 & _ & _). cbn [oblk map blk_id fst snd app] in N2.
             apply NoDup_cons_iff in N2. destruct N2 as [N2 _]. intros E. apply N2. left. symmetry. exact E.
        * intros s'' ms'' PO. apply K. unfold ofree_post in *. cbn [lremove].
          destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
          do 15 eexists. exists m4. split; [reflexivity|].
          split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
          split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply remove_scts_incl; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]|].
                   eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP3| lia| intros b Hb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]|].
                   eapply rheap_pres_weaken; [exact HP4| lia| intros b Hb; exact Hb]. }
          split; [congruence|]. split; [congruence|]. exact HEAP4.
  Qed.
End Proofs.
End WithCeiling0.
