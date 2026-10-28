(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_obj_free ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt O2iKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtWire CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA W_sct_freeA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.


Definition SK_POP_FREE_A : Z := 0x1fc864.
Definition PF_BODY_A : Z := 0x1fc8f8.      (* [comment removed for export] *)
Definition PF_TAIL_A : Z := 0x1fc96c.      (* [comment removed for export] *)
Definition SCT_FREE_GOT_A : Z := 0x5aa228.  (* [comment removed for export] *)
Definition SK_POP_FREE_STACK_A : Z := 112 + 16 + SCT_FREE_STACK_A.   (* [comment removed for export] *)

Local Notation E_lf_tail := (E_SCT_LIST_free_34bb64 : uk_tail 0x3376b8 0x1fc864).            (* [comment removed for export] *)
Local Notation E_pf_item := (E_OPENSSL_sk_pop_free_1f8294 : uk_call 0x1fc864 0x1fc938 0x337578). (* [comment removed for export] *)
Local Notation E_pf_skfree := (E_OPENSSL_sk_pop_free_1f8308 : uk_tail 0x1fc864 0x1fd334).      (* [comment removed for export] *)
Local Notation E_skf_data := (E_OPENSSL_sk_pop_free_1fc990 : uk_call 0x1fc864 0x1fc994 0x1fd334).  (* [comment removed for export] *)

Notation in_remove_sct := CtSctP.W_sct_list_free.in_remove_sct.
Notation scts_blocks_in_remove := CtSctP.W_sct_list_free.scts_blocks_in_remove.
Notation scts_blocks_struct_in := CtSctP.W_sct_list_free.scts_blocks_struct_in.
Notation remove_scts_incl := CtSctP.W_sct_list_free.remove_scts_incl.
Notation in_remove_scts_keep := CtSctP.W_sct_list_free.in_remove_scts_keep.
Notation remove_sct_incl := CtSctP.W_sct_list_free.remove_sct_incl.
Notation NoDup_app_split := CtSctP.W_sct_list_free.NoDup_app_split.
Notation NoDup_lremove := CtSctP.W_sct_list_free.NoDup_lremove.
Notation in_lremove_other := CtSctP.W_sct_list_free.in_lremove_other.
Notation fst_osz32 := CtSctP.W_sct_list_free.fst_osz32.

(* [comment removed for export] *)
Lemma sct_ptr_cellsA_of_cells : forall m adr s et vs,
  rw_cells ctasegs m (adr (sc_blk s)) (sct_cells adr s et vs) -> sct_ptr_cellsA m adr s.
Proof.
  intros m adr s et vs H. unfold sct_ptr_cellsA. cbn zeta. unfold SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG.
  assert (SPLIT : forall k pre c post, sct_cells adr s et vs = pre ++ c :: post -> Z.of_nat (cells_size pre) = k ->
                  ro_cells ctasegs m (adr (sc_blk s) + k) [c]).
  { intros k pre c post E Hk. rewrite E in H. apply rw_cells_app in H. destruct H as [_ H2]. rewrite Hk in H2.
    change (c :: post) with ([c] ++ post) in H2. apply rw_cells_app in H2. destruct H2 as [H3 _]. exact (proj1 H3). }
  split; [|split; [|split]].
  - apply (SPLIT 8 [C4 (wz (u32 (sc_version s))); C4 (wz 0)] _ _ eq_refl eq_refl).
  - eapply (SPLIT 24 (firstn 4 (sct_cells adr s et vs))); [reflexivity| reflexivity].
  - eapply (SPLIT 48 (firstn 7 (sct_cells adr s et vs))); [reflexivity| reflexivity].
  - eapply (SPLIT 72 (firstn 12 (sct_cells adr s et vs))); [reflexivity| reflexivity].
Qed.

Lemma sct_repA_ptr_cells : forall m L adr x, sct_repA m L adr x -> sct_ptr_cellsA m adr x.
Proof. intros m L adr x (_ & _ & H & _). eapply sct_ptr_cellsA_of_cells. exact H. Qed.

(* [comment removed for export] *)
Lemma ro_in_block_presA : forall (L' LB : list block) SP mA mB p A n X cs,
  agree_on (aclient_addr (L' ++ LB) SP) mA mB -> In (p, A, n) L' -> A <= X -> X + Z.of_nat (cells_size cs) <= A + n ->
  ro_cells ctasegs mA X cs -> ro_cells ctasegs mB X cs.
Proof.
  intros L' LB SP mA mB p A n X cs AG IN X1 X2 H. eapply (ro_cells_agree _ _ _ _ _ AG); [exact H|].
  intros a Ha. right. right. exists (p, A, n). split; [apply in_or_app; left; exact IN|]. cbn. lia.
Qed.

Lemma sct_ptr_cellsA_pres : forall (L' LB : list block) SP mA mB adr x,
  agree_on (aclient_addr (L' ++ LB) SP) mA mB -> In (sc_blk x, adr (sc_blk x), SCT_SIZE) L' -> sct_ptr_cellsA mA adr x -> sct_ptr_cellsA mB adr x.
Proof.
  intros L' LB SP mA mB adr x AG IN (H1 & H2 & H3 & H4). unfold sct_ptr_cellsA, SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG, SCT_SIZE in *.
  cbn zeta in *. split; [| split; [| split]]; (eapply ro_in_block_presA; [exact AG| exact IN| lia| cbn; lia| assumption]).
Qed.

Lemma scts_ptr_cellsA_pres : forall (L' LB : list block) SP mA mB adr l,
  agree_on (aclient_addr (L' ++ LB) SP) mA mB -> Forall (fun b => In b L') (scts_blocks adr l) -> Forall (sct_ptr_cellsA mA adr) l -> Forall (sct_ptr_cellsA mB adr) l.
Proof.
  intros L' LB SP mA mB adr l AG HIN H. apply Forall_forall. intros x Hx. eapply sct_ptr_cellsA_pres; [exact AG| | exact (proj1 (Forall_forall _ _) H x Hx)].
  exact (proj1 (Forall_forall _ _) HIN _ (scts_blocks_struct_in adr l x Hx)).
Qed.

Lemma sk_data_cellsA_pres : forall (L' LB : list block) SP mA mB adr pd D dn l i,
  agree_on (aclient_addr (L' ++ LB) SP) mA mB -> In (pd, D, dn) L' -> 0 <= i -> 8 * (i + zlength l) <= dn -> sk_data_cellsA mA adr D i l -> sk_data_cellsA mB adr D i l.
Proof.
  intros L' LB SP mA mB adr pd D dn l. revert l. induction l as [|x l IH]; intros i AG IN I0 BND H; [exact I|].
  cbn [sk_data_cellsA] in *. destruct H as [H1 H2]. unfold zlength in BND. cbn [length] in BND. rewrite Nat2Z.inj_succ in BND.
  split; [eapply ro_in_block_presA; [exact AG| exact IN| lia| cbn; lia| exact H1]|].
  apply IH; [exact AG| exact IN| lia| unfold zlength; lia| exact H2].
Qed.

(* [comment removed for export] *)
Definition afree_sct {X} (s : sctr bptr) (k : aprog bptr X) : aprog bptr X :=
  ofree (sc_logid s) (ofree (option_map fst (sc_ext s)) (ofree (option_map fst (sc_sig s)) (ofree (option_map fst (sc_blob s)) (AFree (sc_blk s) k)))).
Fixpoint afree_scts {X} (l : list (sctr bptr)) (k : aprog bptr X) : aprog bptr X :=
  match l with [] => k | s :: t => afree_sct s (afree_scts t k) end.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma got_sct_freeA : forall Σ OW LB m, AHEAP Σ OW LB m -> ro_cells ctasegs m SCT_FREE_GOT_A [C8 (Z_to_bv 64 SCT_FREE_A)].
Proof.
  intros Σ OW LB m H. pose proof (af_relro RT AF Σ m (AH_art _ _ _ _ H)) as R. unfold SCT_FREE_GOT_A, SCT_FREE_A.
  apply (relro_ro_cells m 0x5aa228 [C8 (Z_to_bv 64 0x337578)]); [exact R| cbn; auto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma SCT_free_walkA' : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (adr : bptr -> Z) (x : sctr bptr) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SCT_FREE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  Forall (fun b => In b OW) (sct_blocks adr x) -> List.NoDup (map blk_id (sct_blocks adr x)) -> List.NoDup (map blk_id OW) ->
  sct_ptr_cellsA m adr x ->
  a0 = wz (adr (sc_blk x)) ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_FREE_A (bv_unsigned ra :: ras) ->
  (forall Σ' ms', ofree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (remove_sct x OW) LB lo m Σ' ms' -> implAp k Σ' Q ms') ->
  implAp (afree_sct x k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_FREE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP CS HIN ND NDL (C1 & C2 & C3 & C4) HA0 UW CTX K.
  unfold afree_sct. rewrite <- (fst_osz32 (sc_logid x)).
  unfold CtSctP.W_sct_list_free.sct_blocks in HIN, ND. rewrite !Forall_app in HIN. destruct HIN as (I1 & I2 & I3 & I4 & I5).
  apply Forall_inv in I5.
  rewrite !map_app in ND. cbn [map CtSctP.W_sct_list_free.oblk blk_id fst snd app] in ND.
  eapply (SCT_free_walkA) with (oL := osz32 (sc_logid x)) (oE := sc_ext x) (oS := sc_sig x) (oB := sc_blob x) (adr := adr);
    [exact HEAP| exact ST| exact CEIL| exact LO| exact SPT| exact SP16| exact MI| exact TP| exact CS
    | exact I5 | | | | | | exact C1| exact C2| exact C3| exact C4| exact HA0| exact UW| exact CTX| exact K].
  - destruct (osz32 (sc_logid x)) as [[q n]|] eqn:EL; [|exact I]. apply Forall_inv in I1. exact I1.
  - destruct (sc_ext x) as [[q n]|] eqn:EE; [|exact I]. apply Forall_inv in I2. apply in_lremove_other; [exact I2|].
    destruct (osz32 (sc_logid x)) as [[q' n']|] eqn:EL; [|exact I]. cbn. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
    apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. left. first [exact E | first [exact E | symmetry; exact E]].
  - destruct (sc_sig x) as [[q n]|] eqn:ES; [|exact I]. apply Forall_inv in I3.
    apply in_lremove_other; [apply in_lremove_other; [exact I3|]|].
    + destruct (osz32 (sc_logid x)) as [[q' n']|]; [|exact I]. cbn. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. rewrite !in_app_iff. right. left. first [exact E | first [exact E | symmetry; exact E]].
    + destruct (sc_ext x) as [[q' n']|]; [|exact I]. cbn. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x)))) _ ND) as (N2 & _ & _). apply NoDup_cons_iff in N2. destruct N2 as [N2 _].
      intros E. apply N2. left. first [exact E | first [exact E | symmetry; exact E]].
  - destruct (sc_blob x) as [[q n]|] eqn:EB; [|exact I]. apply Forall_inv in I4.
    apply in_lremove_other; [apply in_lremove_other; [apply in_lremove_other; [exact I4|]|]|].
    + destruct (osz32 (sc_logid x)) as [[q' n']|]; [|exact I]. cbn. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. rewrite !in_app_iff. right. right. left. first [exact E | first [exact E | symmetry; exact E]].
    + destruct (sc_ext x) as [[q' n']|]; [|exact I]. cbn. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x)))) _ ND) as (N2 & _ & _). apply NoDup_cons_iff in N2. destruct N2 as [N2 _].
      intros E. apply N2. rewrite in_app_iff. right. left. first [exact E | first [exact E | symmetry; exact E]].
    + destruct (sc_sig x) as [[q' n']|]; [|exact I]. cbn. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x))) ++ map blk_id (oblk adr (sc_ext x))) _ ltac:(rewrite <- app_assoc; exact ND)) as (N3 & _ & _).
      apply NoDup_cons_iff in N3. destruct N3 as [N3 _]. intros E. apply N3. left. first [exact E | first [exact E | symmetry; exact E]].
  - (* [comment removed for export] *)
    apply in_lremove_other; [apply in_lremove_other; [apply in_lremove_other; [apply in_lremove_other; [exact I5|]|]|]|]; cbn [blk_id fst snd].
    + destruct (osz32 (sc_logid x)) as [[q' n']|]; [|exact I]. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      apply NoDup_cons_iff in ND. destruct ND as [N1 _]. intros E. apply N1. rewrite !in_app_iff. right. right. right. left. first [exact E | first [exact E | symmetry; exact E]].
    + destruct (sc_ext x) as [[q' n']|]; [|exact I]. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x)))) _ ND) as (N2 & _ & _). apply NoDup_cons_iff in N2. destruct N2 as [N2 _].
      intros E. apply N2. rewrite !in_app_iff. right. right. left. first [exact E | first [exact E | symmetry; exact E]].
    + destruct (sc_sig x) as [[q' n']|]; [|exact I]. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x))) ++ map blk_id (oblk adr (sc_ext x))) _ ltac:(rewrite <- app_assoc; exact ND)) as (N3 & _ & _).
      apply NoDup_cons_iff in N3. destruct N3 as [N3 _]. intros E. apply N3. rewrite in_app_iff. right. left. first [exact E | first [exact E | symmetry; exact E]].
    + destruct (sc_blob x) as [[q' n']|]; [|exact I]. cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND.
      destruct (NoDup_app_split (map blk_id (oblk adr (osz32 (sc_logid x))) ++ map blk_id (oblk adr (sc_ext x)) ++ map blk_id (oblk adr (sc_sig x))) _
                  ltac:(rewrite <- !app_assoc; exact ND)) as (N4 & _ & _).
      apply NoDup_cons_iff in N4. destruct N4 as [N4 _]. intros E. apply N4. left. first [exact E | first [exact E | symmetry; exact E]].
Qed.


(* [comment removed for export] *)
Lemma aclient_agree_of_munch : forall Σ OW LB (L' : list block) m mX m1 lo1 hi1 SP,
  AHEAP Σ OW LB m -> (forall b, In b L' -> In b OW) -> munch [(lo1, hi1)] mX m1 -> ACEIL <= lo1 -> hi1 <= SP ->
  agree_on (aclient_addr (L' ++ LB) SP) mX m1.
Proof.
  intros Σ OW LB L' m mX m1 lo1 hi1 SP HEAP HL MU H1 H2. pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3).
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A in Cq1. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - assert (Hb' : In b (OW ++ LB)). { apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (HL b Hb)| right; exact Hb]. }
    pose proof (AH_range_gen _ _ _ _ b HEAP Hb') as (_ & _ & _ & B3 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma frame_presA : forall (L' LB : list block) SP' mA mB FA cs,
  agree_on (aclient_addr (L' ++ LB) SP') mA mB -> SP' <= FA -> FA + Z.of_nat (cells_size cs) <= USTACK_TOP ->
  rw_cells ctasegs mA FA cs -> rw_cells ctasegs mB FA cs.
Proof. intros L' LB SP' mA mB FA cs AG H1 H2 H. eapply (rw_cells_agree _ _ _ _ _ AG); [exact H|]. intros a Ha. left. lia. Qed.

Lemma crypto_statics_presA : forall (L' LB : list block) SP' mA mB,
  agree_on (aclient_addr (L' ++ LB) SP') mA mB -> crypto_statics mA -> crypto_statics mB.
Proof.
  intros L' LB SP' mA mB AG H. eapply crypto_statics_agree; [exact AG| | exact H].
  intros a Ha. right; left; apply client_static_intro. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. lia.
Qed.

Lemma uw_chain_presA : forall (L' LB : list block) SP' mA mB sp fp ras,
  agree_on (aclient_addr (L' ++ LB) SP') mA mB -> SP' <= sp -> uw_chain USTACK_TOP mA sp fp ras -> uw_chain USTACK_TOP mB sp fp ras.
Proof. intros L' LB SP' mA mB sp fp ras AG LE H. eapply uw_chain_agreeP; [exact AG| exact H|]. intros a H1 Ha. left. lia. Qed.

(* [comment removed for export] *)
Ltac step_hoisted_chk ACC MU :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch type of ACC with acc _ ?mb ?a ?n =>
    lazymatch type of MU with munch ?W mb mc =>
      let RD := fresh "RDsh" in
      first [ pose proof (acc_rdG segs W mb mc a n a (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 a)) 3 + SHB)) ACC MU
                            ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr)) as RD;
              OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; clear RD
            | (* [comment removed for export] *)
              pose proof (acc_rdG segs W mb mc a n a (Z_to_bv 64 (Z.shiftr a 3 + SHB)) ACC MU
                            ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr)) as RD;
              OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; clear RD ];
      OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true]
    end end end.

(* [comment removed for export] *)
Definition pf_frameA (m : mem) (sp : word) (jk : list (bv 8)) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  rw_cells ctasegs m (bv_unsigned sp + -112) [CB 8 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma afree_sct_afrees : forall {X} (x : sctr bptr) (t : aprog bptr X), afree_sct x t = CtSctP.O2iKit.afrees (CtSctP.O2iKit.sct_ids x) t.
Proof.
  intros X x t. unfold afree_sct, CtSctP.O2iKit.sct_ids. rewrite !CtSctP.O2iKit.afrees_app.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|]; reflexivity.
Qed.
Lemma afree_scts_afrees : forall {X} (l : list (sctr bptr)) (t : aprog bptr X), afree_scts l t = CtSctP.O2iKit.afrees (CtSctP.O2iKit.scts_ids l) t.
Proof. intros X l t. induction l as [|x r IH]; cbn [afree_scts CtSctP.O2iKit.scts_ids]; [reflexivity|]. rewrite IH, afree_sct_afrees, CtSctP.O2iKit.afrees_app. reflexivity. Qed.
Lemma sk_free_all_atree : forall (k : skr bptr) (st0 : ap_st bptr),
  sk_free_all k st0 = afree_scts (sk_items k) (ofree (option_map fst (sk_data k)) (AFree (sk_blk k) (ARet (tt, st0)))).
Proof.
  intros k st0. rewrite CtSctP.O2iKit.sk_free_all_tree, !CtSctP.O2iKit.afrees_app, afree_scts_afrees.
  destruct (sk_data k) as [[q n]|]; reflexivity.
Qed.

(* [comment removed for export] *)
Definition pf_tail_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jk : list (bv 8))
    (Σ : rts RT) (L' LB : list block) (lo : Z) (m : mem) (SA num D : Z) (ras : list Z) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x24 x25 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (wz SA) a0 a1 a2 a3 a4 a5 a6 a7
                  (wz SCT_FREE_A) (wz (SA + 8)) (wz (SA + 40)) (wz SHB) (Z_to_bv 64 (Z.shiftr SA 3 + SHB))
                  x23 x24 (Z_to_bv 64 (Z.shiftr (SA + 8) 3 + SHB)) x25
                  (Z_to_bv 64 (Z.shiftr (SA + 40) 3 + SHB)) t3 t4 t5 t6)      (* [comment removed for export] *)
             F' (wz PF_TAIL_A) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp + -112)
    /\ agree_on (aclient_addr (L' ++ LB) (bv_unsigned sp + -112)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' L' LB m' /\ crypto_statics m'
    /\ pf_frameA m' sp jk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 /\ st_cellsA m' SA num D
    /\ uw_chain USTACK_TOP m' (bv_unsigned sp) (bv_unsigned s0) ras.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pop_free_loopA : forall {X : Type} (rest : list (sctr bptr))
    (ra x1 sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x25 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (jk : list (bv 8))
    (adr : bptr -> Z) (pst pd : bptr) (SA D dn num i : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  rest <> [] ->
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp + -112) -> ACEIL <= lo -> lo <= bv_unsigned sp - SK_POP_FREE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> crypto_statics m ->
  pf_frameA m sp jk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> st_cellsA m SA num D ->
  In (pst, SA, STACK_SIZE) OW -> SA mod 16 = 0 -> In (pd, D, dn) OW -> D mod 16 = 0 -> 8 * num <= dn ->
  0 <= i -> i + zlength rest = num -> num < 2 ^ 31 ->
  sk_data_cellsA m adr D i rest -> Forall (sct_ptr_cellsA m adr) rest ->
  Forall (fun b => In b OW) (scts_blocks adr rest) ->
  List.NoDup (map blk_id (scts_blocks adr rest ++ [(pd, D, dn); (pst, SA, STACK_SIZE)])) ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SK_POP_FREE_A (bv_unsigned ra :: ras) ->
  (forall Σ' ms', pf_tail_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 jk Σ (remove_scts rest OW) LB lo m SA num D ras Σ' ms' ->
                  implAp k Σ' Q ms') ->
  implAp (afree_scts rest k) Σ Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (wz SA) a0 a1 a2 a3 a4 a5 a6 a7
              (wz SCT_FREE_A) (wz (SA + 8)) (wz (SA + 40)) (wz SHB) (Z_to_bv 64 (Z.shiftr SA 3 + SHB))
             (wz (8 * i)) (wz i) (Z_to_bv 64 (Z.shiftr (SA + 8) 3 + SHB)) x25
              (Z_to_bv 64 (Z.shiftr (SA + 40) 3 + SHB)) t3 t4 t5 t6)
        F (wz PF_BODY_A) fc None m (seg_rom ctasegs)).
Proof.
  induction rest as [|x rest IH]; [intros; congruence|].
  intros until Q. intros _ HEAP ST CEIL LO SPT SP16 MI CS PFR (SC1 & SC2 & SC3) HST ALS HD ALD DN I0 NUM N31 (DC & DCS) PC HIN ND UW CTX K.
  apply Forall_cons_iff in PC. destruct PC as [PCx PC].
  unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK, PF_BODY_A, PF_TAIL_A, SK_POP_FREE_A, SCT_FREE_A, MallocRep.wz in *.
  unfold SKO_DATA, SKO_FREE_THUNK, STACK_SIZE, SCT_SIZE, SK_SCT_FREEFUNC_THUNK_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HST' : In (pst, SA, 56) (OW ++ LB)) by (apply in_or_app; left; exact HST).
  assert (HD' : In (pd, D, dn) (OW ++ LB)) by (apply in_or_app; left; exact HD).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HST') as (BS0 & _ & _ & BS3 & BS4). cbn [blk_addr blk_size fst snd] in BS0, BS3, BS4.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HD') as (BD0 & _ & _ & BD3 & BD4). cbn [blk_addr blk_size fst snd] in BD0, BD3, BD4.
  assert (NUM' : i + 1 + zlength rest = num) by (unfold zlength in *; cbn [length] in NUM; rewrite Nat2Z.inj_succ in NUM; lia). clear NUM. rename NUM' into NUM.
  pose proof (Zle_0_nat (length rest)) as LR0. unfold zlength in NUM.
  cbn [CtSctP.W_sct_list_free.scts_blocks] in HIN, ND. rewrite Forall_app in HIN. destruct HIN as [HINx HIN].
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  assert (ESA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESA8 : bv_unsigned (Z_to_bv 64 (SA + 8)) = SA + 8) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESA40 : bv_unsigned (Z_to_bv 64 (SA + 40)) = SA + 40) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  unfold pf_frameA in PFR.
  (* [comment removed for export] *)
  pose proof HINx as HINx'. unfold CtSctP.W_sct_list_free.sct_blocks in HINx'. rewrite !Forall_app in HINx'. destruct HINx' as (_ & _ & _ & _ & I5). apply Forall_inv in I5.
  assert (I5' : In (sc_blk x, adr (sc_blk x), 104) (OW ++ LB)) by (apply in_or_app; left; exact I5).
  pose proof (AH_range_gen _ _ _ _ _ HEAP I5') as (BX0 & _ & _ & BX3 & BX4). cbn [blk_addr blk_size fst snd] in BX0, BX3, BX4.
  ablock HEAP HST' ACCS OFFS. ablock HEAP HD' ACCD OFFD.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp - 112)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 128, bv_unsigned sp - 112)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. apre. remember (D + 8 * i) as Di eqn:EDi. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. subst Di.
  step. if_cases K0; zify_cond K0; [exfalso; try rewrite <- unsigned_lit_land, ?unsigned_lit in K0 by lia; lia|]. clear K0.
  (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1; [exfalso; revert K1; vm_compute; congruence|]. clear K1.
  step. step.
  try rewrite (ret_pc_even 0x336b54) by (clear; lia).
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step. step. step. do 3 step. release_frame FR ST (bv_unsigned sp + -112). step.
  try rewrite (ret_pc_even 0x337578) by (clear; lia).
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp + -112)) m m1).
  { eapply (aclient_agree_of_munch _ _ _ OW m m m1); [exact HEAP| intros b Hb; exact Hb| exact MU1| alia| lia]. }
  pose proof (crypto_statics_presA _ _ _ _ _ AG1 CS) as CS1.
  apply (sct_ptr_cellsA_pres _ _ _ _ _ _ _ AG1 I5) in PCx.
  apply (scts_ptr_cellsA_pres _ _ _ _ _ _ _ AG1 HIN) in PC.
  apply (sk_data_cellsA_pres _ _ _ _ _ _ _ _ _ _ _ AG1 HD) in DCS; [| lia| unfold zlength; lia].
  (* [comment removed for export] *)
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [CB 8 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; uchk_open; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact PFR.
    - eapply (uw_chain_presA OW LB); [exact AG1| lia| exact UW]. }
  apply evt_done. cbn [afree_scts].
  eapply (SCT_free_walkA') with (lo := lo) (adr := adr) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras);
    [exact HEAP1 | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; lia | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia
    | exact MI | reflexivity | exact CS1 | exact HINx | | exact (AH_nodup_l _ _ _ _ HEAP1) | exact PCx | reflexivity
    | rewrite ESP; exact UW1 | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_pf_item CTX) | ].
  { rewrite map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & _ & NDx). rewrite map_app in NDx. destruct (NoDup_app_split _ _ NDx) as (_ & _ & NDx1). exact NDx1. }
  intros Σ2 ms2 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F2 & fc2 & m2
                  & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
  try rewrite (ret_pc_even 0x1fc938) by (clear; lia).
  (* [comment removed for export] *)
  pose proof ND as ND0. rewrite map_app in ND0. destruct (NoDup_app_split _ _ ND0) as (_ & _ & NDxr).          (* [comment removed for export] *)
  rewrite <- app_assoc, map_app in ND. destruct (NoDup_app_split _ _ ND) as (NDrt & NXx & NDx).                (* [comment removed for export] *)
  assert (HST2 : In (pst, SA, 56) (remove_sct x OW)).
  { apply in_remove_sct with (adr := adr); [exact HST|]. intros I1. refine (NXx _ I1 _). rewrite map_app, in_app_iff. right. cbn. right. left. reflexivity. }
  assert (HD2 : In (pd, D, dn) (remove_sct x OW)).
  { apply in_remove_sct with (adr := adr); [exact HD|]. intros I1. refine (NXx _ I1 _). rewrite map_app, in_app_iff. right. cbn. left. reflexivity. }
  assert (HIN2 : Forall (fun b => In b (remove_sct x OW)) (scts_blocks adr rest)) by (apply scts_blocks_in_remove; [exact NDxr| exact HIN]).
  apply (frame_presA _ _ _ _ _ _ _ AG2) in PFR; [| lia| cbn; unfold USTACK_TOP; lia].
  apply (ro_in_block_presA _ _ _ _ _ _ _ _ _ _ AG2 HST2) in SC1; [|lia|cbn; lia]. apply (ro_in_block_presA _ _ _ _ _ _ _ _ _ _ AG2 HST2) in SC2; [|lia|cbn; lia].
  apply (ro_in_block_presA _ _ _ _ _ _ _ _ _ _ AG2 HST2) in SC3; [|lia|cbn; lia].
  apply (scts_ptr_cellsA_pres _ _ _ _ _ _ _ AG2 HIN2) in PC.
  apply (sk_data_cellsA_pres _ _ _ _ _ _ _ _ _ _ _ AG2 HD2) in DCS; [| lia| unfold zlength; lia].
  pose proof (crypto_statics_presA _ _ _ _ _ AG2 CS1) as CS2.
  assert (UW2 : uw_chain USTACK_TOP m2 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply (uw_chain_presA (remove_sct x OW) LB); [exact AG2| lia|]. eapply (uw_chain_presA OW LB); [exact AG1| lia| exact UW]. }
  assert (AG02 : agree_on (aclient_addr (remove_sct x OW ++ LB) (bv_unsigned sp + -112)) m m2).
  { eapply agree_on_trans; [| exact AG2]. eapply agree_on_mono; [exact AG1|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
    intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply remove_sct_incl; exact Hb| right; exact Hb]. }
  assert (HST2' : In (pst, SA, 56) (remove_sct x OW ++ LB)) by (apply in_or_app; left; exact HST2).
  assert (HD2' : In (pd, D, dn) (remove_sct x OW ++ LB)) by (apply in_or_app; left; exact HD2).
  ablock HEAP2 HST2' ACCS2 OFFS2. ablock HEAP2 HD2' ACCD2 OFFD2.
  destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  clear HEAP1 CS1 UW1 ACCS ACCD SHB1 SHB2 MU1 WM1 AG1 HEAP ST MI CS.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp - 112)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. step_hoisted_chk ACCS2 MU2. step. step. step.
  step. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    destruct rest as [|y rest']; [exfalso; unfold zlength in NUM; cbn [length] in NUM; rewrite ?usx32_small, ?ab_signed_small in K2 by lia; lia|].
    replace (Z_to_bv 64 (8 * i + 8)) with (Z_to_bv 64 (8 * (i + 1))) by (f_equal; lia).
    apply evt_done.
    rewrite ?ESA, ?ESA8, ?ESA40.
    eapply (IH) with (lo := lo) (OW := remove_sct x OW) (LB := LB) (pst := pst) (pd := pd) (dn := dn) (num := num);
      [congruence| exact HEAP2| exact ST2| exact CEIL| lia| unfold USTACK_TOP; lia| exact SP16| exact MI2| exact CS2| exact PFR
      | split; [exact SC1| split; [exact SC2| exact SC3]]| exact HST2| exact ALS| exact HD2| exact ALD| exact DN| lia
      | unfold zlength in *; cbn [length] in *; lia| exact N31| exact DCS| exact PC| exact HIN2| exact NDrt| exact UW2| exact CTX| ].
    intros Σ3 ms3 PO. apply K. unfold pf_tail_postA in *.
    destruct PO as (ux1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u23 & u24 & u25 & u3 & u4 & u5 & u6 & F3 & fc3 & m3
                    & -> & MI3 & ST3 & AG3 & CR3 & HEAP3 & CS3 & PFR3 & SC3' & UW3).
    do 21 eexists. exists m3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { eapply agree_on_trans; [| exact AG3]. eapply agree_on_mono; [exact AG02|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
             intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
             cbn [CtSctP.W_sct_list_free.remove_scts] in Hb. apply (remove_scts_incl (y :: rest')). cbn [CtSctP.W_sct_list_free.remove_scts]. exact Hb. }
    split; [rewrite CR3, CR2; reflexivity|]. split; [exact HEAP3|]. split; [exact CS3|]. split; [exact PFR3|]. split; [exact SC3'| exact UW3].
  - (* [comment removed for export] *)
    destruct rest as [|y rest']; [| exfalso; unfold zlength in NUM; cbn [length] in NUM; rewrite ?usx32_small, ?ab_signed_small in K2 by lia; lia].
    step. apply evt_done. rewrite ?ESA, ?ESA8, ?ESA40. apply K. unfold pf_tail_postA. cbn [CtSctP.W_sct_list_free.remove_scts].
    do 21 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact AG02|]. split; [exact CR2|]. split; [exact HEAP2|]. split; [exact CS2|].
    split; [exact PFR| split; [split; [exact SC1| split; [exact SC2| exact SC3]]| exact UW2]].
Qed.

(* [comment removed for export] *)
Lemma pop_free_tailA : forall {X : Type}
    (ra x1 sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x18 x20 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (L LB : list block) (lo : Z) (jk : list (bv 8))
    (adr : bptr -> Z) (pst : bptr) (odata : option (bptr * Z)) (SA num : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ L LB m ->
  stk ctasegs m lo (bv_unsigned sp + -112) -> ACEIL <= lo -> lo <= bv_unsigned sp - SK_POP_FREE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> crypto_statics m ->
  pf_frameA m sp jk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> st_cellsA m SA num (optr adr odata) ->
  In (pst, SA, STACK_SIZE) L -> SA mod 16 = 0 -> match odata with Some (q, n) => In (q, adr q, n) L /\ q <> pst | None => True end ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SK_POP_FREE_A (bv_unsigned ra :: ras) ->
  (forall Σ' ms', ofree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove pst (lremove odata L)) LB lo m Σ' ms' -> implAp k Σ' Q ms') ->
  implAp (ofree (option_map fst odata) (AFree pst k)) Σ Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (wz SA) a0 a1 a2 a3 a4 a5 a6 a7
              x18 (wz (SA + 8)) x20 (wz SHB) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)      (* [comment removed for export] *)
        F (wz PF_TAIL_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI CS PFR (SC1 & SC2 & SC3) HST ALS HOD UW CTX K.
  unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK, PF_TAIL_A, SK_POP_FREE_A, MallocRep.wz in *.
  unfold SKO_DATA, SKO_FREE_THUNK, STACK_SIZE, SK_SCT_FREEFUNC_THUNK_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HST' : In (pst, SA, 56) (L ++ LB)) by (apply in_or_app; left; exact HST).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HST') as (BS0 & _ & _ & BS3 & BS4). cbn [blk_addr blk_size fst snd] in BS0, BS3, BS4.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  assert (ESA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESA8 : bv_unsigned (Z_to_bv 64 (SA + 8)) = SA + 8) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESA40 : bv_unsigned (Z_to_bv 64 (SA + 40)) = SA + 40) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  unfold pf_frameA in PFR.
  ablock HEAP HST' ACCS OFFS.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  ual.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  do 6 step.
  (* [comment removed for export] *)
  assert (UW1 : uw_chain USTACK_TOP m (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m _ (bv_unsigned sp) 112 [CB 8 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; uchk_open; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact PFR.
    - exact UW. }
  apply evt_done.
  eapply CRYPTO_free_opt_walkAp with (od := odata) (adr := adr) (lo := lo) (OW := L) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity;
    [exact HEAP| destruct odata as [[q n]|]; [exact (proj1 HOD)| exact I]| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; lia| rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI| exact CS| rewrite ESP; exact UW1
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_skf_data CTX)|].
  intros Σ2 ms2 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F2 & fc2 & m2
                  & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
  try rewrite (ret_pc_even 0x1fc994) by (clear; lia).
  apply (frame_presA _ _ _ _ _ _ _ AG2) in PFR; [| lia| cbn; unfold USTACK_TOP; lia].
  pose proof (crypto_statics_presA _ _ _ _ _ AG2 CS) as CS2.
  assert (UW2 : uw_chain USTACK_TOP m2 (bv_unsigned sp) (bv_unsigned s0) ras) by (eapply (uw_chain_presA (lremove odata L) LB); [exact AG2| lia| exact UW]).
  assert (HST2 : In (pst, SA, 56) (lremove odata L)).
  { destruct odata as [[q n]|]; cbn [CtRepP.ApErrKit.lremove]; [| exact HST]. apply CtSctP.W_sct_list_free.in_lb_remove_other; [exact HST| cbn; intros E; apply (proj2 HOD); symmetry; exact E]. }
  clear ACCS SHB1 SHB2 MU WM HEAP ST MI CS UW1.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. step. step. do 13 step. release_frame PFR ST2 (bv_unsigned sp). step. step.
  apply evt_done.
  eapply CRYPTO_free_walkAp with (p := pst) (A := SA) (n := 56) (lo := lo) (OW := lremove odata L) (LB := LB) (ras := ras); try reflexivity;
    [exact HEAP2| exact HST2| exact ST2| exact CEIL| unfold CRYPTO_FREE_STACK, RT_STACK; lia| unfold USTACK_TOP; lia| clear - SP16; uchk_open; lia| exact MI2| exact CS2
    | exact UW2 | exact (uk_ctx_tail _ _ _ E_pf_skfree CTX)|].
  intros Σ3 ms3 PO. apply K. unfold cfree_postA in PO. unfold ofree_postA.
  destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & F3 & fc3 & m3
                  & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
  do 17 eexists. exists m3. split; [reflexivity|].
  split; [exact MI3|]. split; [exact ST3|].
  split. { eapply agree_on_trans.
           - eapply agree_on_mono; [exact AG2|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
             intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply lb_remove_incl; exact Hb| right; exact Hb].
           - rewrite (BnHeapA.lb_remove_app_l pst _ LB (AH_nodup _ _ _ _ HEAP2) ltac:(change pst with (blk_id (pst, SA, 56)); apply in_map; exact HST2)) in AG3. exact AG3. }
  split; [rewrite CR3, CR2; reflexivity| exact HEAP3].
Qed.
(* [comment removed for export] *)

Theorem SCT_LIST_free_walkA : sct_list_free_specA SK_POP_FREE_STACK_A.
Proof.
  unfold sct_list_free_specA. intros until k. intros HEAP ST CEIL LO SPT SP16 MI -> CS UW CTX NE SK N31 ->.
  pose proof (sk_repA_free_view _ _ _ _ SK) as ((SC1 & SC2 & SC3) & HST & HOD & DCS & HIN & ND).
  pose proof (proj1 (sk_repA_scts _ _ _ _ SK)) as PCF.
  assert (PC : Forall (sct_ptr_cellsA m adr) (sk_items k)).
  { apply Forall_forall. intros x Hx. eapply sct_repA_ptr_cells. exact (proj1 (Forall_forall _ _) PCF x Hx). }
  pose proof (proj2 (proj1 SK)) as ALS.
  assert (ALD : match sk_data k with Some (q, na) => adr q mod 16 = 0 | None => True end).
  { destruct SK as (_ & _ & HD & _). destruct (sk_data k) as [[q na]|]; [exact (proj1 (proj2 HD))| exact I]. }
  clear PCF.
  rewrite sk_free_all_atree.
  unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK, SCT_LIST_FREE_A, MallocRep.wz in *.
  unfold SKO_DATA, SKO_FREE_THUNK, STACK_SIZE, SK_SCT_FREEFUNC_THUNK_A in *. unfold sk_num in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HST' : In (sk_blk k, adr (sk_blk k), 56) (OW ++ LB)) by (apply in_or_app; left; exact HST).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HST') as (BS0 & _ & _ & BS3 & BS4). cbn [blk_addr blk_size fst snd] in BS0, BS3, BS4.
  remember (adr (sk_blk k)) as SA eqn:ESA.
  assert (ESAu : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESA8 : bv_unsigned (Z_to_bv 64 (SA + 8)) = SA + 8) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESA40 : bv_unsigned (Z_to_bv 64 (SA + 40)) = SA + 40) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof (got_sct_freeA _ _ _ _ HEAP) as GOT. unfold SCT_FREE_GOT_A, SCT_FREE_A in GOT.
  ablock HEAP HST' ACCS OFFS.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (Zle_0_nat (length (sk_items k))) as LR0.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step. step. step. step. step. release_frame FR ST (bv_unsigned sp). step. step.
  (* [comment removed for export] *)
  carve_frame 112%nat ST. do 15 step.
  step. if_cases K0; zify_cond K0; [exfalso; try rewrite <- unsigned_lit_land, ?unsigned_lit in K0 by lia; lia|]. clear K0.
  (* [comment removed for export] *)
  step. step.
  step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (aclient_agree_of_munch _ _ _ OW m m m1); [exact HEAP| intros b Hb; exact Hb| exact MU1| alia| lia]. }
  pose proof (crypto_statics_presA _ _ _ _ _ AG1 CS) as CS1.
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras) by (eapply (uw_chain_presA OW LB); [exact AG1| lia| exact UW]).
  apply (scts_ptr_cellsA_pres _ _ _ _ _ _ _ AG1 HIN) in PC.
  assert (DCS1 : sk_data_cellsA m1 adr (optr adr (sk_data k)) 0 (sk_items k)).
  { destruct (sk_data k) as [[pd na]|] eqn:ED; cbn [optr] in *.
    - apply (sk_data_cellsA_pres _ _ _ _ _ _ _ _ _ _ _ AG1 (proj1 HOD)) in DCS; [exact DCS| lia| lia].
    - rewrite HOD. exact I. }
  clear DCS.
  (* [comment removed for export] *)
  pose proof (uk_ctx_tail _ _ _ E_lf_tail CTX) as CTXpf.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.
  - assert (E0 : sk_items k = []).
    { destruct (sk_items k) as [|y r]; [reflexivity| exfalso]. unfold zlength in K1, N31, LR0. cbn [length] in K1, N31, LR0.
      rewrite ?usx32_small, ?unsigned_lit, ?ab_signed_small in K1 by lia. apply Bool.andb_false_iff in K1. destruct K1 as [K1|K1]; apply Z.ltb_ge in K1; lia. }
    rewrite E0 in *. cbn [afree_scts CtSctP.W_sct_list_free.remove_scts CtSctP.W_sct_list_free.scts_blocks app] in *.
    apply evt_done.
    set (ODATA := match sk_data k with Some (q, na) => Some (q, 8 * na) | None => None end).
    replace (option_map fst (sk_data k)) with (option_map fst ODATA) by (subst ODATA; destruct (sk_data k) as [[? ?]|]; reflexivity).
    replace (optr adr (sk_data k)) with (optr adr ODATA) in SC2 by (subst ODATA; destruct (sk_data k) as [[? ?]|]; reflexivity).
    rewrite ?ESAu, ?ESA8, ?ESA40.
    eapply pop_free_tailA with (lo := lo) (adr := adr) (num := zlength (@nil (sctr bptr))) (odata := ODATA) (L := OW) (LB := LB) (ras := ras);
      [exact HEAP1| exact ST| exact CEIL| unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK; lia| unfold USTACK_TOP; lia| exact SP16
      | exact MI| exact CS1| exact FR| split; [exact SC1| split; [exact SC2| exact SC3]]| exact HST| exact ALS| | exact UW1| exact CTXpf| ].
    { subst ODATA. destruct (sk_data k) as [[pd na]|]; [|exact I]. split; [exact (proj1 HOD)|].
      cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in ND. apply NoDup_cons_iff in ND. destruct ND as [ND _]. intros E. apply ND. left. symmetry. exact E. }
    intros Σ3 ms3 PO. unfold ofree_postA, sct_list_free_postA, remove_sk in *. rewrite E0. cbn [CtSctP.W_sct_list_free.remove_scts].
    replace (lremove (sk_data k)) with (lremove ODATA) by (subst ODATA; destruct (sk_data k) as [[? ?]|]; reflexivity).
    destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & F3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
    apply implAp_ret.
    do 17 eexists. exists m3. split; [subst SA; reflexivity|]. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { eapply agree_on_trans; [| exact AG3]. eapply agree_on_mono; [exact AG1|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
             intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply lremove_incl; eapply lb_remove_incl; exact Hb| right; exact Hb]. }
    split; [exact CR3| exact HEAP3].
  - (* [comment removed for export] *)
    assert (NE0 : sk_items k <> []).
    { intros E0. exfalso.
      repeat match goal with H : context [sx32 (Z_to_bv 64 (zlength (sk_items k)))] |- _ =>
        rewrite E0 in H; unfold zlength in H; cbn [length] in H; rewrite ?usx32_small, ?unsigned_lit, ?ab_signed_small in H by lia end. lia. }
    do 9 step.
    apply evt_done.
    destruct (sk_data k) as [[pd na]|] eqn:ED; [| exfalso; exact (NE0 HOD)]. destruct HOD as [HDin HDn]. cbn [optr CtSctP.W_sct_list_free.oblk] in *.
    assert (ND8 : List.NoDup (map blk_id (scts_blocks adr (sk_items k) ++ [(pd, adr pd, 8 * na); (sk_blk k, SA, 56)]))).
    { revert ND. rewrite !map_app. cbn [map blk_id app fst snd]. intros ND. exact ND. }
    rewrite ?ESAu, ?ESA8, ?ESA40.
    eapply pop_free_loopA with (lo := lo) (adr := adr) (OW := OW) (LB := LB) (pst := sk_blk k) (i := 0) (num := zlength (sk_items k))
                               (pd := pd) (dn := 8 * na) (D := adr pd) (SA := SA) (ras := ras);
      [exact NE0| exact HEAP1| exact ST| exact CEIL| unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK; lia| unfold USTACK_TOP; lia| exact SP16
      | exact MI| exact CS1| exact FR| split; [exact SC1| split; [exact SC2| exact SC3]]| subst SA; exact HST| exact ALS| exact HDin| exact ALD| lia| lia| lia| exact N31
      | exact DCS1| exact PC| exact HIN| exact ND8| exact UW1| exact CTXpf| ].
    intros Σ3 ms3 PO. unfold pf_tail_postA in PO.
    destruct PO as (ux1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u23 & u24 & u25 & u3 & u4 & u5 & u6 & F3 & fc3 & m3
                    & -> & MI3 & ST3 & AG3 & CR3 & HEAP3 & CS3 & PFR3 & SC3' & UW3).
    eapply pop_free_tailA with (lo := lo) (adr := adr) (odata := Some (pd, 8 * na)) (L := remove_scts (sk_items k) OW) (LB := LB) (ras := ras);
      [exact HEAP3| exact ST3| exact CEIL| unfold SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK; lia| unfold USTACK_TOP; lia| exact SP16
      | exact MI3| exact CS3| exact PFR3| exact SC3'| | exact ALS| | exact UW3| exact CTXpf| ].
    + apply (in_remove_scts_keep adr); [subst SA; exact HST|]. rewrite !map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & NX & _).
      intros I1. refine (NX _ I1 _). apply in_app_iff. right. cbn. left. reflexivity.
    + split.
      * apply (in_remove_scts_keep adr); [exact HDin|]. rewrite !map_app in ND. destruct (NoDup_app_split _ _ ND) as (_ & NX & _).
        intros I1. refine (NX _ I1 _). apply in_app_iff. left. cbn. left. reflexivity.
      * rewrite !map_app in ND. destruct (NoDup_app_split _ _ ND) as (N2 & _ & _). cbn [CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in N2.
        apply NoDup_cons_iff in N2. destruct N2 as [N2 _]. intros E. apply N2. left. symmetry. exact E.
    + intros Σ4 ms4 PO. unfold ofree_postA, sct_list_free_postA, remove_sk in *. rewrite ED. cbn [CtRepP.ApErrKit.lremove].
      destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
      apply implAp_ret.
      do 17 eexists. exists m4. split; [subst SA; reflexivity|]. split; [reflexivity|].
      split; [exact MI4|]. split; [exact ST4|].
      split. { eapply agree_on_trans; [| exact AG4]. eapply agree_on_trans.
               - eapply agree_on_mono; [exact AG1|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
                 intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
                 eapply remove_scts_incl. eapply lb_remove_incl. eapply lb_remove_incl. exact Hb.
               - eapply agree_on_mono; [exact AG3|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
                 intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
                 eapply lb_remove_incl. eapply lb_remove_incl. exact Hb. }
      split; [rewrite CR4, CR3; reflexivity| exact HEAP4].
Qed.

End WithRT.
