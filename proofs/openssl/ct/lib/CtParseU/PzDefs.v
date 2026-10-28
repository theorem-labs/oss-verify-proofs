(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApObj ApParse2 ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApErrKit W_prefix_create W_obj_free ApObjRep.
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
Definition PZ_ENTRY : Z := 0x13e114.      (* [comment removed for export] *)
Definition PZ_LOOP : Z := 0x13e218.       (* [comment removed for export] *)
Definition PZ_KINF : Z := 0x13e528.       (* [comment removed for export] *)
Definition PZ_KDEF : Z := 0x13e584.       (* [comment removed for export] *)
Definition PZ_NEXT : Z := 0x13ebec.       (* [comment removed for export] *)
Definition PZ_END1 : Z := 0x13ecdc.       (* [comment removed for export] *)
Definition PZ_END0 : Z := 0x13ed40.       (* [comment removed for export] *)
Definition PZ_ENDC : Z := 0x13ed50.       (* [comment removed for export] *)
Definition PZ_FRAME : Z := 384.
(* [comment removed for export] *)
Definition PZ_CALLEE : Z := 15360.
Definition PZ_STACK (depth : Z) : Z := (130 - depth) * PZ_FRAME + PZ_CALLEE.

Definition ASN1_PARSE_DUMP : Z := 0x13edf4.
Definition FUZZER_TEST_ONE : Z := 0xe2514.  (* [comment removed for export] *)
Definition ASN1_GET_OBJECT : Z := 0xfd87c.
Definition D2I_ASN1_OBJECT : Z := 0xfd374.
Definition I2A_ASN1_OBJECT : Z := 0xfd1c4.
Definition D2I_ASN1_OCTET_STRING : Z := 0x115088.
Definition D2I_ASN1_INTEGER : Z := 0x115144.
Definition D2I_ASN1_ENUMERATED : Z := 0x1151d8.
Definition ERR_CLEAR_ERROR : Z := 0xe8a10.

(* [comment removed for export] *)
Definition A_BADREC : Z := 0x32a12.    (* [comment removed for export] *)
Definition A_F1 : Z := 0x39975.        (* [comment removed for export] *)
Definition A_F2 : Z := 0x2ea96.        (* [comment removed for export] *)
Definition A_CONS : Z := 0x1862e.      (* [comment removed for export] *)
Definition A_PRIM : Z := 0x132f7.      (* [comment removed for export] *)
Definition A_F3 : Z := 0x1c514.        (* [comment removed for export] *)
Definition A_F4 : Z := 0x1c521.        (* [comment removed for export] *)
Definition A_F5 : Z := 0x18635.        (* [comment removed for export] *)
Definition A_F6 : Z := 0x315d2.        (* [comment removed for export] *)
Definition A_F7 : Z := 0x35544.        (* [comment removed for export] *)
Definition A_UNKNOWN : Z := 0x25550.   (* [comment removed for export] *)
Definition A_NL : Z := 0x2a387.        (* [comment removed for export] *)
Definition A_COLON : Z := 0x2552e.     (* [comment removed for export] *)
Definition A_MINUS : Z := 0x300ba.     (* [comment removed for export] *)
Definition A_F11 : Z := 0x2c010.       (* [comment removed for export] *)
Definition A_00 : Z := 0x24123.        (* [comment removed for export] *)
Definition A_BADBOOL : Z := 0x14862.   (* [comment removed for export] *)
Definition A_F10 : Z := 0x1dc58.       (* [comment removed for export] *)
Definition A_BADOBJ : Z := 0x1aee5.    (* [comment removed for export] *)
Definition A_BADENUM : Z := 0x34132.   (* [comment removed for export] *)
Definition A_BADINT : Z := 0x19b0d.    (* [comment removed for export] *)
Definition A_LBR : Z := 0x2555a.       (* [comment removed for export] *)
Definition A_RBR : Z := 0x294bb.       (* [comment removed for export] *)
Definition A_HEXDUMP : Z := 0x21899.   (* [comment removed for export] *)
Definition A_ERRENC : Z := 0x36ba6.    (* [comment removed for export] *)
Definition A_F9 : Z := 0x3801b.        (* [comment removed for export] *)
Definition TAG2STR : Z := 0x2d37a0.    (* [comment removed for export] *)
Definition JTAB : Z := 0x42180.        (* [comment removed for export] *)
Definition PMASK : Z := 0x2600.        (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pz_saved (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word) : list cell :=
  [C8 s11_; C8 s10_; C8 s9_; C8 s8_; C8 s7_; C8 s6_; C8 s5_; C8 s4_; C8 s3_; C8 s2_; C8 s1_; C8 s0_; C8 ra_].

(* [comment removed for export] *)
Definition pz_frame (pad opj j32j hlj xcj tgj lenj oppj str : list byte) (tot depth PP oadr pcur : Z)
    (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word) : list cell :=
  [CB 8 pad; C8 (wz PMASK); C8 (wz tot); C8 (wz 0); C8 (wz (depth + 1)); C8 (wz 0); C8 (wz A_F2);
   CB 8 opj; C8 (wz depth); C8 (wz A_CONS); C8 (wz 0); C8 (wz PP); CB 8 j32j; CB 8 hlj; C8 (wz oadr);
   CB 4 xcj; CB 4 tgj; CB 8 lenj; CB 8 oppj; C8 (wz pcur); CB 128 str]
  ++ pz_saved ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_.

Lemma pz_saved_size ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ :
  cells_size (pz_saved ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_) = 104%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition pz_pre (s : PState) (st : ap_st bptr) (m : mem) (OW LB : list block) (E : ap_env) (bo : Z * Z)
    (q lo B : Z) (errv canary : word) : Prop :=
  RHEAP s (OW ++ LB) m /\ ap_state st m OW E bo /\ ids_ok E st /\ data_cells m OW st
  /\ rauxv_ok m B /\ q <= B /\ B < 2^63
  /\ stk ctusegs m lo q /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
  /\ rw_cells ctusegs m (errno_addr (wz RATP)) [C4 errv] /\ ssp_cells m canary
  /\ mem_inv ctusegs m /\ q mod 16 = 0
  /\ e_stage E = CnfInit.      (* [comment removed for export] *)

Lemma pz_pre_of_ap : forall s st m OW LB E bo sp lo B errv canary stack,
  ap_pre s st m OW LB E bo sp lo B errv canary stack -> e_stage E = CnfInit ->
  pz_pre s st m OW LB E bo (bv_unsigned sp) lo B errv canary /\ lo <= bv_unsigned sp - stack.
Proof.
  intros until stack. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15) ECNF.
  split; [|exact A11]. repeat (split; [assumption|]). exact ECNF.
Qed.

Lemma ap_pre_of_pz : forall s st m OW LB E bo (sp : word) lo B errv canary stack,
  pz_pre s st m OW LB E bo (bv_unsigned sp) lo B errv canary -> lo <= bv_unsigned sp - stack ->
  ap_pre s st m OW LB E bo sp lo B errv canary stack.
Proof.
  intros until stack. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A12 & A13 & A14 & A15 & A16) LO.
  repeat (split; [assumption|]). exact A15.
Qed.

Lemma pz_pre_ecnf : forall s st m OW LB E bo q lo B errv canary,
  pz_pre s st m OW LB E bo q lo B errv canary -> e_stage E = CnfInit.
Proof. intros until canary. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A16). exact A16. Qed.

(* [comment removed for export] *)
Lemma ap_pre_of_pz_lit : forall s st m OW LB E bo q lo B errv canary stack,
  pz_pre s st m OW LB E bo q lo B errv canary -> 0 <= q -> lo <= q - stack ->
  ap_pre s st m OW LB E bo (Z_to_bv 64 q) lo B errv canary stack.
Proof.
  intros until stack. intros PRE Hq LO.
  assert (E1 : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; destruct PRE as (_ & _ & _ & _ & _ & A6 & A7 & _); lia).
  apply ap_pre_of_pz; rewrite E1; assumption.
Qed.

Lemma pz_pre_of_ap_lit : forall s st m OW LB E bo q lo B errv canary stack,
  ap_pre s st m OW LB E bo (Z_to_bv 64 q) lo B errv canary stack -> e_stage E = CnfInit -> 0 <= q < 2^64 ->
  pz_pre s st m OW LB E bo q lo B errv canary.
Proof.
  intros until stack. intros PRE ECNF Hq. pose proof (pz_pre_of_ap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE ECNF) as [P _].
  rewrite (unsigned_lit q) in P by lia. exact P.
Qed.

(* [comment removed for export] *)
Definition pz_acc (LB : list block) (SP : Z) (X : list (Z * Z)) (K : list block) (E : ap_env) (m0 m : mem) (OW : list block) (st : ap_st bptr) : Prop :=
  lx_pres LB SP X m0 m /\ kept K m0 m /\ (forall b, In b K -> In b OW) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)).

Lemma pz_acc_init : forall LB SP X K E m OW st,
  (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) -> pz_acc LB SP X K E m m OW st.
Proof. intros. split; [apply lx_pres_refl|]. split; [apply kept_refl|]. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma badr_cons_other : forall OW p A n q, p <> q -> badr ((p, A, n) :: OW) q = badr OW q.
Proof. intros. rewrite badr_cons. destruct (bptr_eqb p q) eqn:E; [|reflexivity]. apply bptr_eqb_eq in E. contradiction. Qed.

Lemma in_ids : forall (OW : list block) q A n, In (q, A, n) OW -> In q (map blk_id OW).
Proof. intros OW q A n H. change q with (blk_id (q, A, n)). apply in_map. exact H. Qed.

(* [comment removed for export] *)
Lemma optb_ok_cons_fresh : forall OW p A n o, ~ In p (map blk_id OW) -> optb_ok OW o -> optb_ok ((p, A, n) :: OW) o.
Proof.
  intros OW p A n [[q k]|] NI H; [|exact I]. unfold optb_ok in *. destruct H as [HIn Hpos].
  assert (Hpq : p <> q) by (intros ->; apply NI; eapply in_ids; exact HIn).
  rewrite (badr_cons_other OW p A n q Hpq). split; [right; exact HIn|exact Hpos].
Qed.

Lemma map_optr_cons_fresh : forall OW p A n (l : list (option (bptr * Z))),
  ~ In p (map blk_id OW) -> Forall (optb_ok OW) l -> map (optr (badr ((p, A, n) :: OW))) l = map (optr (badr OW)) l.
Proof.
  intros OW p A n l NI HF. induction HF as [|o l Ho HF IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  destruct o as [[q k]|]; [|reflexivity]. unfold optb_ok in Ho. destruct Ho as [HIn _]. unfold optr.
  apply badr_cons_other. intros ->. apply NI. eapply in_ids. exact HIn.
Qed.

Lemma optb_ok_remove_other : forall OW p o, List.NoDup (map blk_id OW) ->
  (forall q k, o = Some (q, k) -> q <> p) -> optb_ok OW o -> optb_ok (lb_remove p OW) o.
Proof.
  intros OW p [[q k]|] ND Ho H; [|exact I]. unfold optb_ok in *. destruct H as [HIn Hpos]. specialize (Ho q k eq_refl).
  rewrite (badr_remove_other OW q p Ho). split; [|exact Hpos]. apply lb_remove_In. split; [exact HIn|]. cbn. exact Ho.
Qed.

Lemma map_optr_remove_other : forall OW p (l : list (option (bptr * Z))),
  (forall q k, In (Some (q, k)) l -> q <> p) -> map (optr (badr (lb_remove p OW))) l = map (optr (badr OW)) l.
Proof.
  intros OW p l Hl. induction l as [|o l IH]; [reflexivity|]. cbn [map]. rewrite IH by (intros q k H; apply (Hl q k); right; exact H). f_equal.
  destruct o as [[q k]|]; [|reflexivity]. unfold optr. apply badr_remove_other. apply (Hl q k). left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma g_of_adr_ext : forall (st : ap_st bptr) adr adr',
  map (optr adr') (as_data st) = map (optr adr) (as_data st) -> map (optr adr') (as_file st) = map (optr adr) (as_file st) ->
  map (optr adr') (as_func st) = map (optr adr) (as_func st) -> g_of st adr' = g_of st adr.
Proof. intros st adr adr' E1 E2 E3. unfold g_of. rewrite E1, E2, E3. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ap_state_cons_fresh : forall st m OW E bo q A0 n0,
  ap_state st m OW E bo -> ~ In q (map blk_id OW) -> 0 < A0 -> A0 + n0 < 2^63 -> A0 mod 16 = 0 ->
  ap_state st m ((q, A0, n0) :: OW) E bo.
Proof.
  intros st m OW E bo q A0 n0 AS NI HA Hn H16.
  pose proof (proj1 (ap_state_split _ _ _ _ _) AS) as [AR ER]. destruct ER as (SH & EAT & F1 & F2 & F3).
  apply ap_state_join.
  - apply rest_OW_cons; assumption.
  - exact SH.
  - rewrite (g_of_adr_ext st (badr OW) (badr ((q, A0, n0) :: OW)));
      [apply es_at_raw; exact EAT| apply map_optr_cons_fresh; assumption| apply map_optr_cons_fresh; assumption| apply map_optr_cons_fresh; assumption].
  - eapply Forall_impl; [|exact F1]. intros o Ho. apply optb_ok_cons_fresh; assumption.
  - eapply Forall_impl; [|exact F2]. intros o Ho. apply optb_ok_cons_fresh; assumption.
  - eapply Forall_impl; [|exact F3]. intros o Ho. apply optb_ok_cons_fresh; assumption.
Qed.

Lemma ids_ok_OW : forall E st, ids_ok E st -> forall OW : list block, ids_ok E st.
Proof. intros E st H _. exact H. Qed.

Lemma data_cells_cons_fresh : forall m OW st q A0 n0,
  data_cells m OW st -> Forall (optb_ok OW) (as_data st) -> ~ In q (map blk_id OW) -> data_cells m ((q, A0, n0) :: OW) st.
Proof.
  intros m OW st q A0 n0 DC F3 NI. eapply data_cells_OW; [exact DC|]. intros i p k Hd.
  pose proof (optb_ok_nth OW _ i p k F3 Hd) as [HIn _]. apply badr_cons_other. intros ->. apply NI. eapply in_ids. exact HIn.
Qed.

(* [comment removed for export] *)
Lemma in_fm_es_ids : forall (st : ap_st bptr) q k,
  (In (Some (q, k)) (as_file st) \/ In (Some (q, k)) (as_func st) \/ In (Some (q, k)) (as_data st)) -> In q (es_ids st).
Proof.
  intros st q k H. unfold es_ids, st_blocks. rewrite !map_app, !in_app_iff.
  assert (FM : forall l, In (Some (q, k)) l -> In q (map fst (fm l))).
  { intros l Hl. induction l as [|o l IH]; [destruct Hl|]. destruct Hl as [->|Hl]; cbn; [left; reflexivity|].
    destruct o as [[q' k']|]; cbn; [right|]; apply IH; exact Hl. }
  destruct H as [H|[H|H]]; [left|right; left|right; right; left]; apply FM; exact H.
Qed.

Lemma ap_state_remove_other : forall st m OW E bo q,
  ap_state st m OW E bo -> ~ In q (env_ids E) -> ~ In q (es_ids st) -> ap_state st m (lb_remove q OW) E bo.
Proof.
  intros st m OW E bo q AS NE NS.
  pose proof (proj1 (ap_state_split _ _ _ _ _) AS) as [AR ER]. destruct ER as (SH & EAT & F1 & F2 & F3).
  pose proof AR as (HE & _). destruct HE as (_ & ND & _).
  assert (NR : ~ In q (map blk_id (rest_blocks OW E (as_cnf st)))).
  { rewrite rest_ids. rewrite in_app_iff. intros [H|H]; [apply NE; rewrite env_ids_unfold; cbn [In] in H |- *; tauto|].
    apply NS. apply cnf_ids_in_es_ids. exact H. }
  assert (NEs : q <> p_es E) by (intros ->; apply NE; rewrite env_ids_unfold; cbn; tauto).
  assert (OTH : forall l, (forall o, In o l -> In o (as_file st) \/ In o (as_func st) \/ In o (as_data st)) -> forall q' k, In (Some (q', k)) l -> q' <> q).
  { intros l Hl q' k HIn ->. apply NS. eapply in_fm_es_ids. apply Hl. exact HIn. }
  apply ap_state_join.
  - apply rest_OW_remove; assumption.
  - exact SH.
  - rewrite (g_of_adr_ext st (badr OW) (badr (lb_remove q OW)));
      [apply es_at_raw; exact EAT| apply map_optr_remove_other; apply OTH; tauto| apply map_optr_remove_other; apply OTH; tauto| apply map_optr_remove_other; apply OTH; tauto].
  - apply Forall_forall. intros o Ho. apply optb_ok_remove_other; [exact ND| intros q' k ->; eapply OTH; [|exact Ho]; tauto| exact (proj1 (Forall_forall _ _) F1 o Ho)].
  - apply Forall_forall. intros o Ho. apply optb_ok_remove_other; [exact ND| intros q' k ->; eapply OTH; [|exact Ho]; tauto| exact (proj1 (Forall_forall _ _) F2 o Ho)].
  - apply Forall_forall. intros o Ho. apply optb_ok_remove_other; [exact ND| intros q' k ->; eapply OTH; [|exact Ho]; tauto| exact (proj1 (Forall_forall _ _) F3 o Ho)].
Qed.

Lemma data_cells_remove_other : forall m OW st q,
  data_cells m OW st -> ~ In q (es_ids st) -> data_cells m (lb_remove q OW) st.
Proof.
  intros m OW st q DC NS. eapply data_cells_OW; [exact DC|]. intros i p k Hd. apply badr_remove_other.
  intros ->. apply NS. eapply es_ids_data. exact Hd.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition obj_ids (o : aobj bptr) : list bptr :=
  match o with ODyn blk data _ _ => [blk; data] | _ => [] end.
Definition pz_obj (m : mem) (OW K : list block) (st : ap_st bptr) (E : ap_env) (o : aobj bptr) (oadr : Z) : Prop :=
  obj_rep m OW o oadr /\ (forall q, In q (obj_ids o) -> ~ In q (map blk_id K ++ es_ids st ++ env_ids E)).

(* [comment removed for export] *)
Definition pz_ret_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word)
    (s0e : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m0 : mem) (K : list block)
    (D PP p length : Z) (r : (Z * Z) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (OW' : list block) (errv' : word) (nw' : Z),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz (fst (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F0 k)
    /\ pz_pre s' (snd r) m' OW' LB E (0, nw') (bv_unsigned sp) lo B errv' canary
    /\ lx_pres LB (bv_unsigned sp) ((PP, PP + 8) :: LIBW_AP) m0 m'
    /\ ps_so s' = ps_so s0e /\ ps_fa s' = ps_fa s0e
    /\ blocks_kept K (snd r) OW' m0 m'
    /\ rw_cells ctusegs m' PP [C8 (wz (D + snd (fst r)))] /\ 0 <= nw' < 2^64
    /\ p <= snd (fst r) <= p + length /\ (fst (fst r) = 0 \/ fst (fst r) = 1 \/ fst (fst r) = 2).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MP_parse (fuel : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (nw : Z)
         (lo B : Z) (errv canary : word) (K : list block) (D : Z) (d : list Z) (p length offset depth PP : Z),
    pz_pre s st m OW LB E (0, nw) (bv_unsigned sp) lo B errv canary -> lo <= bv_unsigned sp - PZ_STACK depth -> 0 <= nw < 2^64 ->
    tp = wz RATP -> frm0 fc ->
    payload_ok m LB D d ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    0 <= p -> 0 <= length -> p + length <= zlength d -> 0 <= depth <= 129 -> 0 <= offset <= p ->
    rw_cells ctusegs m PP [C8 (wz (D + p))] -> bv_unsigned sp <= PP -> PP + 8 <= B ->
    a0 = wz (e_bio E) -> a1 = wz PP -> a2 = wz length -> a3 = wz offset -> a4 = wz depth -> a5 = wz 0 -> a6 = wz 0 ->
    implM ctusegs (interp (ap_embed (parse2 d fuel p length offset depth st))) s
          (pz_ret_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB E lo B canary m K D PP p length)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz PZ_ENTRY) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition MP_loop (fuel : nat) : Prop :=
  forall (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word)
         (sp gp x1 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x23 x25 t0 t1 t2 t3 t4 t5 t6 : word)
         (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0e s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (nw : Z)
         (lo B : Z) (errv canary : word) (K : list block) (D : Z) (d : list Z) (PP : Z)
         (pad opj j32j hlj xcj tgj lenj oppj str : list byte) (o : aobj bptr) (oadr : Z)
         (p length offset depth pp0 tot length0 : Z),
    let q := bv_unsigned sp + -384 in
    pz_pre s st m OW LB E (0, nw) q lo B errv canary -> lo <= bv_unsigned sp - PZ_STACK depth -> 0 <= nw < 2^64 ->
    frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
    ps_so s = ps_so s0e -> ps_fa s = ps_fa s0e ->
    pz_acc LB (bv_unsigned sp) ((PP, PP + 8) :: LIBW_AP) K E m0 m OW st ->
    payload_ok m LB D d ->
    rw_cells ctusegs m q (pz_frame pad opj j32j hlj xcj tgj lenj oppj str (D + tot) depth PP oadr (D + p) ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_) ->
    rw_cells ctusegs m PP [C8 (wz (D + pp0))] -> bv_unsigned sp <= PP -> PP + 8 <= B ->
    pz_obj m OW K st E o oadr ->
    0 <= pp0 <= p -> 0 < length -> tot = p + length -> tot <= zlength d -> 0 <= depth <= 128 -> 0 <= offset <= pp0 -> tot = pp0 + length0 ->
    implM ctusegs (interp (ap_embed (ploop d fuel p length offset depth pp0 tot o st))) s
          (pz_ret_post ra_ sp gp s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ F0 s0e LB E lo B canary m0 K D PP pp0 length0)
          (MS (mkR x1 (wz q) gp (wz RATP) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7
                   (wz depth) x19 x20 x21 (wz PP) x23 (wz offset) x25 (wz (e_bio E)) (wz length) t3 t4 t5 t6)
              F (wz PZ_LOOP) fc None m (seg_rom ctusegs)).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pz_mid (s0e : PState) (F0 : bvmap 5 word) (m0 : mem) (LB : list block) (E : ap_env) (lo B : Z) (canary : word)
    (K : list block) (D : Z) (d : list Z) (PP SP : Z)
    (s : PState) (st : ap_st bptr) (m : mem) (OW : list block) (nw : Z) (errv : word) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  pz_pre s st m OW LB E (0, nw) (SP - 384) lo B errv canary /\ 0 <= nw < 2^64
  /\ frm0 fc /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k)
  /\ ps_so s = ps_so s0e /\ ps_fa s = ps_fa s0e
  /\ pz_acc LB SP ((PP, PP + 8) :: LIBW_AP) K E m0 m OW st
  /\ payload_ok m LB D d.

(* [comment removed for export] *)
Definition pz_frame2 (pad oppj str : list byte) (tot depth PP op j32 hl oadr cls tag len pcur : Z)
    (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word) : list cell :=
  [CB 8 pad; C8 (wz PMASK); C8 (wz tot); C8 (wz 0); C8 (wz (depth + 1)); C8 (wz 0); C8 (wz A_F2);
   C8 (wz op); C8 (wz depth); C8 (wz A_CONS); C8 (wz 0); C8 (wz PP); C8 (wz j32); C8 (wz hl); C8 (wz oadr);
   C4 (wz cls); C4 (wz tag); C8 (wz len); CB 8 oppj; C8 (wz pcur); CB 128 str]
  ++ pz_saved ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_.

(* [comment removed for export] *)
Definition obj_blocks (OW : list block) (o : aobj bptr) : list block :=
  match o with ODyn blk data alloc _ => [(blk, badr OW blk, ASN1_OBJECT_SIZE); (data, badr OW data, alloc)] | _ => [] end.

Definition PZ_KFAIL : Z := 0x13ed44.       (* [comment removed for export] *)
Definition PZ_KINF_DONE : Z := 0x13e658.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kids_post (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word) (sp gp : word)
    (s0e : PState) (F0 : bvmap 5 word) (m0 : mem) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block) (D : Z) (d : list Z) (PP : Z)
    (pad oppj str : list byte) (tot depth op j32 lsave oadr cls tag len pp0 offset : Z) (o : aobj bptr)
    (pc_ok : Z) (x9v x18v x27v : word) (X21 : word -> Prop) (POK PANY : Z -> Prop)
    (r : (bool * Z) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (x1 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
                    (m : mem) (OW : list block) (nw : Z) (errv : word),
    let q := bv_unsigned sp + -384 in
    ms' = MS (mkR x1 (wz q) gp (wz RATP) t0 t1 t2 sp x9v x10 x11 x12 x13 x14 x15 x16 x17
                  x18v x19 (wz 0) x21 (wz PP) (wz (depth + 1)) (wz offset) (wz 0) (wz (e_bio E)) x27v t3 t4 t5 t6)
             F (wz (if fst (fst r) then pc_ok else PZ_KFAIL)) fc None m (seg_rom ctusegs)
    /\ (if fst (fst r) then x19 = wz (D + snd (fst r)) /\ X21 x21 /\ POK (snd (fst r)) else x21 = wz 0) /\ PANY (snd (fst r))
    /\ pz_mid s0e F0 m0 LB E lo B canary K D d PP (bv_unsigned sp) s' (snd r) m OW nw errv F fc
    /\ rw_cells ctusegs m q (pz_frame2 pad oppj str (D + tot) depth PP (D + op) j32 lsave oadr cls tag len (D + snd (fst r))
                              ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_)
    /\ rw_cells ctusegs m PP [C8 (wz (D + pp0))]
    /\ pz_obj m OW K (snd r) E o oadr.

(* [comment removed for export] *)
Definition MP_kinf (fuel : nat) : Prop :=
  forall (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word)
         (sp gp x1 x10 x11 x12 x13 x14 x15 x16 x17 x21 t0 t1 t2 t3 t4 t5 t6 : word)
         (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0e s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (nw : Z)
         (lo B : Z) (errv canary : word) (K : list block) (D : Z) (d : list Z) (PP : Z)
         (pad oppj str : list byte) (o : aobj bptr) (oadr : Z)
         (p tot offset depth pp0 spos plow op j32 lsave cls tag len : Z),
    let q := bv_unsigned sp + -384 in
    pz_mid s0e F0 m0 LB E lo B canary K D d PP (bv_unsigned sp) s st m OW nw errv F fc -> lo <= bv_unsigned sp - PZ_STACK depth ->
    rw_cells ctusegs m q (pz_frame2 pad oppj str (D + tot) depth PP (D + op) j32 lsave oadr cls tag len (D + p)
                              ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_) ->
    rw_cells ctusegs m PP [C8 (wz (D + pp0))] -> bv_unsigned sp <= PP -> PP + 8 <= B ->
    pz_obj m OW K st E o oadr ->
    0 <= pp0 <= spos -> spos <= p <= tot -> plow <= p -> tot <= zlength d -> 0 <= depth <= 128 -> 0 <= offset <= pp0 ->
    implM ctusegs (interp (ap_embed (kids_inf d fuel p tot offset depth pp0 st))) s
          (kids_post ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ sp gp s0e F0 m0 LB E lo B canary K D d PP
                     pad oppj str tot depth op j32 lsave oadr cls tag len pp0 offset o
                     PZ_KINF_DONE (wz (D + spos)) (wz (D + tot)) (wz 2) (fun _ => True) (fun _ => True) (fun p' => plow <= p' <= tot))
          (MS (mkR x1 (wz q) gp (wz RATP) t0 t1 t2 sp (wz (D + spos)) x10 x11 x12 x13 x14 x15 x16 x17
                   (wz (D + tot)) (wz (D + p)) (wz 0) x21 (wz PP) (wz (depth + 1)) (wz offset) (wz 0) (wz (e_bio E)) (wz 2) t3 t4 t5 t6)
              F (wz PZ_KINF) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition MP_kdef (fuel : nat) : Prop :=
  forall (ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ : word)
         (sp gp x1 x10 x11 x12 x13 x14 x15 x16 x17 x27 t0 t1 t2 t3 t4 t5 t6 : word)
         (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0e s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (nw : Z)
         (lo B : Z) (errv canary : word) (K : list block) (D : Z) (d : list Z) (PP : Z)
         (pad oppj str : list byte) (o : aobj bptr) (oadr : Z)
         (p ep tmp offset depth pp0 tot plow op j32 hl cls tag len lcur : Z),
    let q := bv_unsigned sp + -384 in
    pz_mid s0e F0 m0 LB E lo B canary K D d PP (bv_unsigned sp) s st m OW nw errv F fc -> lo <= bv_unsigned sp - PZ_STACK depth ->
    rw_cells ctusegs m q (pz_frame2 pad oppj str (D + tot) depth PP (D + op) j32 hl oadr cls tag len (D + p)
                              ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_) ->
    rw_cells ctusegs m PP [C8 (wz (D + pp0))] -> bv_unsigned sp <= PP -> PP + 8 <= B ->
    pz_obj m OW K st E o oadr ->
    0 <= pp0 <= p -> p < ep -> ep <= tot -> tot <= zlength d -> p + tmp = ep -> plow <= p -> 0 <= depth <= 128 -> 0 <= offset <= pp0 -> 0 <= lcur < 2^63 ->
    implM ctusegs (interp (ap_embed (kids_def d fuel p ep tmp offset depth pp0 st))) s
          (fun r s' ms' => exists tmp', kids_post ra_ s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ sp gp s0e F0 m0 LB E lo B canary K D d PP
                     pad oppj str tot depth op j32 hl oadr cls tag len pp0 offset o
                     PZ_NEXT (wz (D + ep)) (wz tmp') x27 (fun w => w = wz lcur) (fun p' => p' = ep) (fun p' => plow <= p' <= ep) r s' ms')
          (MS (mkR x1 (wz q) gp (wz RATP) t0 t1 t2 sp (wz (D + ep)) x10 x11 x12 x13 x14 x15 x16 x17
                   (wz tmp) (wz (D + p)) (wz 0) (wz lcur) (wz PP) (wz (depth + 1)) (wz offset) (wz 0) (wz (e_bio E)) x27 t3 t4 t5 t6)
              F (wz PZ_KDEF) fc None m (seg_rom ctusegs)).
End WithCeiling0.
