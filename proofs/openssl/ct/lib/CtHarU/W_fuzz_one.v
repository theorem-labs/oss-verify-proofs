(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg LibOps CtSizes CtWire CtModel CtBridge ApBase ApState ApInv ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad Stdio ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Stdio_iface Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts HxpLaws HxpInstAp.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_err_clear_error W_bio_new W_bio_free W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_free W_sct_list_free SctRep W_sct_leaves W_sk_leaves SctStmt O2iKit W_o2i_sct_list.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import W_sct_print W_sct_list_print.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncStmt EncKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarU Require Import HarKit W_bio_null.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
Ltac xmu H MU WM := apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU WM) in H; [| cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; cbn; lia].
Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ct_lib_inv3 (ls : ap_ls bptr) (m : word -> option byte) (OW : list block) : Prop :=
  exists E, (e_stage E = CnfInit /\ exists nw, ap_state (st_of_ls ls) m OW E (0, nw)) /\ ids_ok E (st_of_ls ls) /\ ApIface.data_cells m OW (st_of_ls ls).

Lemma ct_lib_inv3_of2 : forall ls m OW, ap_lib_inv2 ls m OW -> ct_lib_inv3 ls m OW.
Proof.
  intros ls m OW (E & (Hwf & HSG & nw & HS) & HI & HD). exists E. split; [split; [exact HSG| exists nw; exact HS]|]. split; [exact HI| exact HD].
Qed.
Lemma ct_lib_inv3_init_of2 : forall m OW, ap_lib_inv ap_ls0 m OW -> ct_lib_inv3 ap_ls0 m OW.
Proof. intros m OW H. apply ct_lib_inv3_of2. apply ap_lib_inv2_init. exact H. Qed.
Lemma ct_lib_inv3_agree : forall ls OW m m',
  ct_lib_inv3 ls m OW -> agree_on (fun a => rin_ivs LIBW_HX a \/ in_block OW a) m m' -> ct_lib_inv3 ls m' OW.
Proof.
  intros ls OW m m' (E & (HSG & nw & HS) & HI & HD) AG.
  exists E. split; [split; [exact HSG| exists nw; eapply ApRep.ap_state_agree; [exact HS| exact AG]]|]. split; [exact HI|].
  destruct HD as [HD DF]. split; [|exact DF].
  intros i p n Hd. destruct (HD i p n Hd) as [Hn [junk HC]]. split; [exact Hn|]. exists junk.
  eapply rw_cells_agree; [exact AG|exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r in Ha.
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & FD)).
  assert (HIn : In (Some (p, n)) (as_data (st_of_ls ls))).
  { unfold get_data in Hd. rewrite <- Hd. apply nth_In. destruct (Nat.lt_ge_cases i (length (as_data (st_of_ls ls)))) as [L|L]; [exact L|]. rewrite (nth_overflow _ None L) in Hd. discriminate. }
  pose proof (proj1 (Forall_forall _ _) FD _ HIn) as [HB _]. cbn in HB. right. exists (p, badr OW p, n). split; [exact HB|]. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma ap_state_bo : forall st m OW E bo bo', ap_state st m OW E bo -> ap_state st m OW E bo'.
Proof. intros st m OW E bo bo' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact I| exact A8]. Qed.

(* [comment removed for export] *)
Lemma ap_embed_sk_free_all0 : forall (k : skr bptr) (st0 : ap_st bptr),
  ap_embed (sk_free_all k st0) = lfree_scts (sk_items k) (lofree (option_map fst (sk_data k)) (LFree (sk_blk k) (LRet (tt, st0)))).
Proof.
  intros k st0. rewrite sk_free_all_tree, ap_embed_afrees, !lfrees_app, lfree_scts_lfrees. cbn [apbind fst snd lfrees ap_embed].
  destruct (sk_data k) as [[q n]|]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma implM_ap_assoc' {CE__ : Ceiling} : forall {A B C} (t : aprog bptr A) (f : A -> aprog bptr B) (g : B -> aprog bptr C) s Q ms,
  implM ctusegs (interp (ap_embed (apbind t (fun a => apbind (f a) g)))) s Q ms ->
  implM ctusegs (interp (ap_embed (apbind (apbind t f) g))) s Q ms.
Proof.
  intros A B C t f g. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros s Q ms H; cbn [apbind ap_embed interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
Qed.

(* [comment removed for export] *)
Lemma implM_ap_assoc_r {CE__ : Ceiling} : forall {A B C} (t : aprog bptr A) (f : A -> aprog bptr B) (g : B -> aprog bptr C) s Q ms,
  implM ctusegs (interp (ap_embed (apbind (apbind t f) g))) s Q ms ->
  implM ctusegs (interp (ap_embed (apbind t (fun a => apbind (f a) g)))) s Q ms.
Proof.
  intros A B C t f g. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros s Q ms H; cbn [apbind ap_embed interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
Qed.

Lemma implM_apbind_cont {CE__ : Ceiling} : forall {A B} (t : aprog bptr A) (f g : A -> aprog bptr B) s Q ms,
  (forall a s' ms', implM ctusegs (interp (ap_embed (f a))) s' Q ms' -> implM ctusegs (interp (ap_embed (g a))) s' Q ms') ->
  implM ctusegs (interp (ap_embed (apbind t f))) s Q ms -> implM ctusegs (interp (ap_embed (apbind t g))) s Q ms.
Proof.
  intros A B t f g s Q ms Hfg. revert s ms. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros s ms H; cbn [apbind ap_embed interp] in *; try exact H.
  - apply Hfg. exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
Qed.

(* [comment removed for export] *)
Lemma exit_cells_of_fixed {CE__ : Ceiling} : forall m E, ap_statics_fixed m E -> ossl_exit_cells m.
Proof.
  intros m E FX. unfold ap_statics_fixed in FX.
  do 23 (apply proj2 in FX). destruct FX as ([b0 HB0] & HCL & _). exists b0. split; [exact HB0| exact HCL].
Qed.

(* [comment removed for export] *)
Lemma held_ids_OW {CE__ : Ceiling} : forall st m OW E bo q, ap_state st m OW E bo -> In q (es_ids st ++ env_ids E) -> In q (map blk_id OW).
Proof.
  intros st m OW E bo q AS Hq.
  pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3).
  pose proof (proj1 (proj1 (ap_state_split _ _ _ _ _) AS)) as AR.
  assert (FM : forall l, Forall (optb_ok OW) l -> In q (map fst (fm l)) -> In q (map blk_id OW)).
  { intros l Hl Hin. apply in_map_iff in Hin. destruct Hin as ([q' n] & E0 & Hin). cbn in E0. subst q'.
    unfold fm in Hin. apply in_flat_map in Hin. destruct Hin as (o & Ho & Hn). destruct o as [[p' n']|]; cbn in Hn; [| destruct Hn].
    destruct Hn as [Hn|[]]. injection Hn; intros; subst. pose proof (proj1 (Forall_forall _ _) Hl _ Ho) as [HIn _]. eapply in_ids. exact HIn. }
  apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
  - unfold es_ids, st_blocks in Hq. rewrite !map_app, !in_app_iff in Hq.
    destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [exact (FM _ F1 Hq)| exact (FM _ F2 Hq)| exact (FM _ F3 Hq)|].
    assert (HR : In q (map blk_id (rest_blocks OW E (as_cnf st)))) by (rewrite rest_ids; apply in_app_iff; right; exact Hq).
    apply in_map_iff in HR. destruct HR as (b & <- & Hb). apply in_map. eapply rest_blocks_OW; [exact AR| exact Hb].
  - unfold env_ids in Hq. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map. pose proof AS as ((HF & _ & _) & _).
    exact (proj1 (Forall_forall _ _) HF b Hb).
Qed.

Definition HAR_ENTRY : Z := 0xe2514.     (* [comment removed for export] *)
Definition HAR_RET1 : Z := 0xe253c.      (* [comment removed for export] *)
Definition HAR_I2D : Z := 0xe2578.       (* [comment removed for export] *)
Definition HAR_FREE : Z := 0xe2598.      (* [comment removed for export] *)
Definition HAR_CLR : Z := 0xe25a0.       (* [comment removed for export] *)
Definition BIO_S_NULL : Z := 0x194320.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable TSTK : Z.
  Hypothesis TSTK_RANGE : 0 <= TSTK <= 30000.
  Hypothesis HD2I : d2i_sct_list_spec.
  Hypothesis HPRINT : SCT_LIST_print_spec TSTK.
  Hypothesis HI2D : i2d_sct_list_spec.
  Hypothesis HCLR : ERR_clear_error_spec.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st0 : ap_st bptr) (OW LB : list block) (E : ap_env).
  Variables (lo B : Z) (errv canary : word) (D : Z) (d : list Z).
  Variables (ra0 e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LOB : lo <= bv_unsigned sp - 65536.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ECNF : e_stage E = CnfInit.
  Hypothesis HEAP0 : RHEAP s (OW ++ LB) m.
  Hypothesis PAY0 : payload_ok m LB D d.
  Hypothesis LXS0 : lx_statics m.
  Hypothesis SE0 : stderr_wfile m.

  Local Notation HINV := (einv sp m s LB E lo B canary [] []).
  Let h_facts := @einv_facts CE__ RN__ sp m s LB E lo B canary [] [].
  Let h_call := @einv_call CE__ RN__ sp m s LB E lo B canary [] [] CEIL GLO SPB B63.
  Let h_munch := @einv_munch CE__ RN__ sp m s LB E lo B canary [] [] CEIL GLO SPB (@Forall_nil _ _).
  Let h_exit := @einv_exit CE__ RN__ sp m s LB E lo B canary [] [] CEIL GLO SPB B63.
  Let h_ap_pre := @einv_ap_pre CE__ RN__ sp m s LB E lo B canary [] [] CEIL GLO SPB B63.
  Let h_after := @einv_after CE__ RN__ sp m s LB E lo B canary [] [] CEIL GLO SPB B63.
  Let h_alloc := @einv_alloc CE__ RN__ sp m s LB E lo B canary [] [].
  Let h_heap := @einv_heap CE__ RN__ sp m s LB E lo B canary [] [].

  Lemma SPR' : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma OWN0 : forall NEW lo' hi', lo <= lo' -> hi' <= bv_unsigned sp -> Forall (own_iv sp lo [] NEW) [(lo', hi')]%Z.
  Proof. intros. constructor; [left; cbn; lia| constructor]. Qed.
  Lemma BK0 : forall st' OW' mX mY, blocks_kept [] st' OW' mX mY.
  Proof. intros. split; [intros b []|]. split; [intros b []|]. intros a _ (b & [] & _). Qed.

  (* [comment removed for export] *)
  Definition mid_post (r : unit * ap_st bptr) (s2 : PState) : machine_state -> Prop :=
    fun ms2 => exists (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32) m2 OW2 (errv2 : word) bo2,
      ms2 = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
               F2 (Z_to_bv 64 HAR_CLR) fc2 None m2 (seg_rom ctusegs)
      /\ frm0 fc2 /\ HINV (bv_unsigned sp + -48) s2 (snd r) m2 OW2 errv2 bo2 []
      /\ exists j (dv pv : word), rw_cells ctusegs m2 (bv_unsigned sp + -48) [CB 8%nat j; C8 dv; C8 pv; C8 e9; C8 e8; C8 ra0].

  (* [comment removed for export] *)
  Definition fin_post (r : Z * ap_st bptr) (s2 : PState) : machine_state -> Prop :=
    fun ms2 => fst r = 0 /\
      rfuzz_one_post (LM := @LM_ap (ap_ls bptr) ct_ls0 ct_lib_one) (LSP := @LSP_ap (ap_ls bptr) ct_ls0 ct_lib_one ct_lib_inv3)
                     ra0 sp gp (wz RATP) e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 s LB D d lo B canary m (ls_of_st (snd r), 0) s2 ms2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_clr : forall (r : unit * ap_st bptr) s2 ms2,
    mid_post r s2 ms2 ->
    implM ctusegs (interp (ap_embed (abind err_clear_error (fun _ => aret 0) (snd r)))) s2 fin_post ms2.
  Proof.
    intros [u stX] s2 ms2 PO. unfold mid_post in PO. cbn [fst snd] in *.
    destruct PO as (x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F2 & fc2 & m2 & OW2 & errv2 & bo2 & -> & FRM2 & EI & (j & dv & pv & FRT)).
    pose proof SPR' as SPR. unfold HAR_CLR.
    pose proof (h_call _ _ _ _ _ _ _ _ EI) as (_ & _ & _ & ST & _ & _ & _ & MI & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
    (* [comment removed for export] *)
    zstep. ihere. to_implM.
    unfold abind.
    pose proof (HCLR bo2) as HE7. unfold ap_stmt in HE7.
    destruct (h_ap_pre _ _ _ _ _ _ _ _ ERR_CLEAR_ERROR_STACK EI ltac:(rewrite <- Zplus_mod_idemp_l, SP16; reflexivity) ltac:(unfold ERR_CLEAR_ERROR_STACK; lia)) as (PRE & _ & _).
    eapply implM_apbind.
    { eapply HE7 with (K := []); [exact PRE| reflexivity| exact FRM2| reflexivity| intros b Hb0; destruct Hb0| intros b Hb0; destruct Hb0]. }
    clear HE7. cbv beta. intros [[] st''] s'' ms'' PO. cbn [fst snd] in PO.
    unfold ap_post in PO. cbn [fst snd] in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & b0' & b1' & b2' & b3' & b4' & b5' & b6' & b7' & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & OW3 & errv3 & bo3
                    & -> & FRM3 & FREG3 & PRE3 & LX3 & SO3 & FA3 & BK3 & Ebo & NF).
    replace (ret_pc (Z_to_bv 64 0xe25a4)) with (Z_to_bv 64 0xe25a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (EI3 : HINV (bv_unsigned sp + -48) s'' st'' m3 OW3 errv3 bo3 ([] ++ [])).
    { eapply (h_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] []); [exact EI| exact PRE3| rewrite ESP; exact LX3| intros a Ha; destruct Ha| exact SO3| exact FA3| exact BK3]. }
    cbn [app] in EI3.
    apply (rw_cells_lx _ _ _ _ _ _ _ LX3) in FRT; [| lia| intros a Ha Hin; apply rin_ivs_LIBW_AP in Hin; cbn [cells_size csize Nat.add] in Ha; lia].
    pose proof (h_call _ _ _ _ _ _ _ _ EI3) as (_ & _ & _ & ST3 & _ & _ & _ & MI3 & _).
    clear MU WM ST MI EI PRE LX3 BK3.
    (* [comment removed for export] *)
    cbn [apbind aret ap_embed interp fst snd]. apply implM_ret.
    pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl ctusegs m3) as WM.
    zstep. zstep. zstep. zstep. zstep. release_frame FRT ST3 (bv_unsigned sp). zstep.
    apply evt_done.
    assert (EI4 : HINV (bv_unsigned sp) s'' st'' m3 OW3 errv3 bo3 []).
    { eapply h_munch; [exact EI3| exact MU| exact WM| exact MI3| exact ST3| lia| constructor]. }
    destruct (h_exit _ _ _ _ _ _ _ EI4 SP16) as (PRE4 & LX4 & _ & SO4 & FA4 & _). cbn [app] in PRE4, LX4.
    pose proof PRE4 as (HEAP4 & AS4 & IDS4 & DC4 & AUX4 & _ & _ & ST4 & _ & _ & _ & ERR4 & SSP4 & MI4 & _).
    assert (LX5 : lx_pres LB (bv_unsigned sp) LIBW_HX m m3) by (eapply lx_pres_weaken; [exact LX4| lia| intros b Hb; exact Hb| exact LIBW_AP_HX]).
    pose proof (agree_of_lx_pres _ _ _ _ _ LX5) as AG.
    unfold fin_post, rfuzz_one_post. cbn [fst snd]. split; [reflexivity|]. split; [|reflexivity].
    unfold rlib_post. do 15 eexists. exists F3, fc3, m3, OW3.
    split; [reflexivity|].
    split.
    { split.
      { exists errv3. unfold lx_env. split; [exact HEAP4|].
        split; [eapply lx_statics_agree; [exact AG | intros a Ha; apply drv_cells_client; left; exact Ha | exact LXS0]|].
        split; [eapply stderr_wfile_agree; [exact AG | intros a Ha; apply drv_cells_client; right; exact Ha | exact SE0]|].
        split; [exact SSP4|]. split; [exact AUX4|]. split; [exact SPB|]. split; [exact B63|]. split; [exact ST4|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|].
        split; [exact ERR4|]. split; [reflexivity| exact MI4]. }
      split; [exact FRM3|]. split; [cbn [LIBW LSP_ap]; exact LX5|].
      split; [exact SO4| exact FA4]. }
    split.
    { change (ct_lib_inv3 (ls_of_st st'') m3 OW3). exists E. rewrite <- NF.
      split; [split; [exact ECNF| exists 0; eapply ap_state_bo; exact AS4]|]. split; [exact IDS4| exact DC4]. }
    split; [exact (exit_cells_of_fixed _ _ (proj1 (proj2 (proj2 AS4))))|].
    split; [reflexivity|].
    eapply (payload_ok_lx s OW LB m m3 D d (bv_unsigned sp) [] lo); [exact HEAP0| exact PAY0| exact LX4| exact CEIL| constructor].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_free : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) NEWk (adr : bptr -> Z) (k : skr bptr) j (dv pv : word),
    HINV (bv_unsigned sp + -48) sX stX mX OWX errvX boX NEWk -> Permutation NEWk (sk_blocks adr k) -> sk_rep mX (NEWk ++ LB) adr k ->
    frm0 fcX -> rw_cells ctusegs mX (bv_unsigned sp + -48) [CB 8%nat j; C8 dv; C8 pv; C8 e9; C8 e8; C8 ra0] ->
    implM ctusegs (interp (ap_embed (sk_free_all k stX))) sX mid_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) x5 x6 x7 (wz (adr (sk_blk k))) x9 x10 x11 x12 x13 x14 x15 x16 x17
               e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 HAR_FREE) fcX None mX (seg_rom ctusegs)).
  Proof.
    intros until pv. intros EI PM SK FRM FR. pose proof SPR' as SPR. unfold HAR_FREE.
    pose proof (h_call _ _ _ _ _ _ _ _ EI) as (HEAP & AUX & _ & ST & _ & _ & ERR & MI & CS & _ & AS & _).
    pose proof (h_facts _ _ _ _ _ _ _ _ EI) as (_ & ND & BND & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (SKL : sk_rep mX (OWX ++ NEWk ++ LB) adr k).
    { eapply sk_rep_relist; [exact SK|]. intros b Hb. apply in_app_iff. right. exact (sk_allblocks_in _ _ _ _ _ SK Hb). }
    pose proof (sk_rep_free_view _ _ _ _ SKL) as (STC & HIN & HDAT & DCS & PCS & HINS & NDK).
    pose proof SKL as (_ & _ & HD3 & _).
    assert (N31 : zlength (sk_items k) < 2 ^ 31).
    { unfold sk_num in HD3. destruct (sk_data k) as [[q na]|]; [destruct HD3 as (_ & Hn & Hna & _); lia| rewrite HD3; unfold zlength; cbn; lia]. }
    unfold MallocRep.wz. unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    zstep. zstep. ihere. to_implM.
    rewrite ap_embed_sk_free_all0.
    eapply (SCT_LIST_free_walk HF) with (L := OWX ++ NEWk ++ LB) (lo := lo) (B := B) (adr := adr) (sk := k); rewrite ?ESP;
      [ exact HEAP| exact AUX| lia| exact ST| exact CEIL| unfold GLOBALS_TOP; lia
      | unfold SCT_LIST_FREE_STACK, SK_POP_FREE_STACK, SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
      | rewrite <- Zplus_mod_idemp_l, SP16; reflexivity
      | exact ERR| exact MI| reflexivity| exact CS| exact (got_of_state _ _ _ _ _ AS)
      | exact STC| exact HIN| | exact N31| exact DCS| exact PCS| exact HINS| | exact ND| reflexivity|].
    { destruct (sk_data k) as [[q na]|]; [| exact HDAT]. destruct HDAT as [H1 H2]. split; [exact H1| unfold sk_num in H2; exact H2]. }
    { revert NDK. unfold sk_blocks. destruct (sk_data k) as [[q na]|]; cbn [dblk oblk]; rewrite !map_app; cbn [map blk_id fst snd app]; intros ND0; exact ND0. }
    intros sG msG PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (g0 & g1 & g2 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g3 & g4 & g5 & g6 & mG
                    & -> & MIG & STG & ERRG & AUXG & HPG & FAG & SOG & HEAPG).
    replace (ret_pc (Z_to_bv 64 HAR_CLR)) with (Z_to_bv 64 HAR_CLR) by (symmetry; apply ret_pc_even; [unfold HAR_CLR; lia| reflexivity]).
    pose proof (remove_sk_perm adr k OWX NEWk LB PM ND) as PMR.
    assert (EIG : HINV (bv_unsigned sp + -48) sG stX mG OWX errvX boX []).
    { eapply (h_heap _ _ _ _ _ _ _ NEWk sG mG errvX _ _ []); [exact EI| exact HPG| | exact HEAPG| cbn [app]; exact PMR| exact MIG| exact STG| exact ERRG| exact AUXG| exact FAG| exact SOG].
      intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PMR|]. apply in_app_iff. exact Hb. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HPG)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    cbn [interp]. apply implM_ret. apply evt_done.
    unfold mid_post. cbn [fst snd]. do 18 eexists. exists FX, fcX, mG, OWX, errvX, boX.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact EIG|]. exists j, dv, pv. exact FR.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_pre (NEWk : list block) (adr : bptr -> Z) (k : skr bptr) (r : unit * ap_st bptr) (s3 : PState) : machine_state -> Prop :=
    fun ms3 => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F3 : bvmap 5 word) (fc3 : bv 32) m3 OW3 (errv3 : word) bo3 j (dv pv : word),
      ms3 = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) x5 x6 x7 (wz (adr (sk_blk k))) x9 x10 x11 x12 x13 x14 x15 x16 x17
                    e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
               F3 (Z_to_bv 64 HAR_FREE) fc3 None m3 (seg_rom ctusegs)
      /\ frm0 fc3 /\ HINV (bv_unsigned sp + -48) s3 (snd r) m3 OW3 errv3 bo3 NEWk /\ sk_rep m3 (NEWk ++ LB) adr k
      /\ rw_cells ctusegs m3 (bv_unsigned sp + -48) [CB 8%nat j; C8 dv; C8 pv; C8 e9; C8 e8; C8 ra0].

  Lemma har_i2d : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) NEWk (adr : bptr -> Z) (k : skr bptr) j (pv : word),
    HINV (bv_unsigned sp + -48) sX stX mX OWX errvX boX NEWk -> Permutation NEWk (sk_blocks adr k) -> sk_rep mX (NEWk ++ LB) adr k ->
    frm0 fcX -> rw_cells ctusegs mX (bv_unsigned sp + -48) [CB 8%nat j; C8 (wz 0); C8 pv; C8 e9; C8 e8; C8 ra0] ->
    implM ctusegs (interp (ap_embed (abind (i2d_sct_list k) (fun _ => sk_free_all k) stX))) sX mid_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) x5 x6 x7 (wz (adr (sk_blk k))) x9 x10 x11 x12 x13 x14 x15 x16 x17
               e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 HAR_I2D) fcX None mX (seg_rom ctusegs)).
  Proof.
    intros until pv. intros EI PM SK FRM FR. pose proof SPR' as SPR. unfold HAR_I2D.
    pose proof (h_call _ _ _ _ _ _ _ _ EI) as (HEAP & _ & _ & ST & _ & _ & _ & MI & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    unfold MallocRep.wz in *. unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ihere. to_implM.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app mX _ [CB 8%nat j] _) FR) as [FRA FRb]. cbn [cells_size csize Nat.add] in FRb.
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FRb by lia.
    pose proof (proj1 (rw_cells_app mX _ [C8 (Z_to_bv 64 0)] _) FRb) as [FRD FRS]. cbn [cells_size csize Nat.add] in FRS. clear FR FRb.
    replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) in FRS by lia.
    destruct (h_ap_pre _ _ _ _ _ _ _ _ I2D_SCT_LIST_STACK EI ltac:(rewrite <- Zplus_mod_idemp_l, SP16; reflexivity) ltac:(unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK; lia)) as (PRE & _ & _).
    unfold abind at 1. rewrite (i2d_sct_list_cps_eq k stX).
    eapply (implM_apbind _ _ sX (free_pre NEWk adr k)).
    { pose proof HI2D as W. unfold i2d_sct_list_spec in W.
      eapply W with (K := []) (DER := bv_unsigned sp + -40); clear W; rewrite ?ESP;
        [exact PRE| reflexivity| exact FRM| intros b Hb0; destruct Hb0| intros b Hb0; destruct Hb0| exact SK| lia| lia| exact FRD| clear - SP16; Z.div_mod_to_equations; lia| reflexivity| reflexivity| |].
      - (* [comment removed for export] *)
        intros st' s' ms' PO. unfold i2d_post in PO. rewrite ?ESP in PO. cbn [fst snd] in PO.
        destruct PO as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & OW2 & errv2 & bo2 & NEW2
                        & -> & FRM2 & FE2 & PRE2 & LX2 & SO2 & FA2 & BK2 & FRESH2 & SK2 & ENEW & HDER2). subst NEW2. cbn [app] in PRE2.
        replace (ret_pc (Z_to_bv 64 0xe2584)) with (Z_to_bv 64 0xe2584) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (EI2 : HINV (bv_unsigned sp + -48) s' st' m2 OW2 errv2 bo2 ([] ++ NEWk)).
        { eapply (h_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ [(bv_unsigned sp + -40, bv_unsigned sp + -40 + 8)] []);
            [exact EI| exact PRE2| rewrite ESP; exact LX2| | exact SO2| exact FA2| exact BK2].
          intros a Ha. left. cbn [rin_ivs fst snd] in Ha. lia. }
        cbn [app] in EI2.
        apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FRA; [| lia| intros a Ha [Hin|Hin]; [cbn [fst snd] in Hin; cbn in Ha; lia| apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia]].
        apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FRS; [| lia| intros a Ha [Hin|Hin]; [cbn [fst snd] in Hin; cbn in Ha; lia| apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia]].
        pose proof (h_call _ _ _ _ _ _ _ _ EI2) as (_ & _ & _ & ST2 & _ & _ & _ & MI2 & CS2 & _).
        clear MU WM ST MI EI PRE LX2 BK2 SK.
        cbn [afree_opt ap_embed interp]. apply implM_ret.
        pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply CRYPTO_free_null_spec with (lo := lo); rewrite ?ESP; [exact ST2| unfold GLOBALS_TOP; lia| lia| exact MI2| exact CS2| reflexivity]. }
        cbv beta. intros ms3 PO. rewrite ?ESP in PO.
        destruct PO as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
        replace (ret_pc (Z_to_bv 64 HAR_FREE)) with (Z_to_bv 64 HAR_FREE) by (symmetry; apply ret_pc_even; [unfold HAR_FREE; lia| reflexivity]).
        unfold MallocRep.wz in HDER2. xmu FRA MU3 WM3. xmu HDER2 MU3 WM3. xmu FRS MU3 WM3.
        assert (EI3 : HINV (bv_unsigned sp + -48) s' st' m3 OW2 errv2 bo2 NEWk).
        { eapply h_munch; [exact EI2| exact MU3| exact WM3| exact MI3| exact ST3| lia| apply OWN0; lia]. }
        assert (SK3 : sk_rep m3 (NEWk ++ LB) adr k).
        { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU3 WM3)| | exact SK2]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
          pose proof (h_facts _ _ _ _ _ _ _ _ EI2) as (_ & _ & BND2 & _).
          pose proof (BND2 qb Ab nb ltac:(apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK2 Hb))) as (_ & _ & B3 & _). cbn. lia. }
        apply evt_done. unfold free_pre. cbn [fst snd]. do 17 eexists. exists F2, fc2, m3, OW2, errv2, bo2, j, (Z_to_bv 64 0), pv.
        split; [reflexivity|]. split; [exact FRM2|]. split; [exact EI3|]. split; [exact SK3|].
        apply (proj2 (rw_cells_app m3 _ [CB 8%nat j] _)). split; [exact FRA|]. cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) by lia.
        apply (proj2 (rw_cells_app m3 _ [C8 (Z_to_bv 64 0)] _)). split; [exact HDER2|]. cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia. exact FRS.
      - (* [comment removed for export] *)
        intros dd st' s' ms' PO. unfold i2d_post in PO. rewrite ?ESP in PO. cbn [fst snd] in PO.
        destruct PO as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & OW2 & errv2 & bo2 & NEW2
                        & -> & FRM2 & FE2 & PRE2 & LX2 & SO2 & FA2 & BK2 & FRESH2 & SK2 & (AD & n & ENEW & N0 & HDER2)). subst NEW2. cbn [app] in PRE2.
        replace (ret_pc (Z_to_bv 64 0xe2584)) with (Z_to_bv 64 0xe2584) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (EI2 : HINV (bv_unsigned sp + -48) s' st' m2 OW2 errv2 bo2 ([(dd, AD, n)] ++ NEWk)).
        { eapply (h_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ [(bv_unsigned sp + -40, bv_unsigned sp + -40 + 8)] [(dd, AD, n)]);
            [exact EI| exact PRE2| rewrite ESP; exact LX2| | exact SO2| exact FA2| exact BK2].
          intros a Ha. left. cbn [rin_ivs fst snd] in Ha. lia. }
        cbn [app] in EI2.
        apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FRA; [| lia| intros a Ha [Hin|Hin]; [cbn [fst snd] in Hin; cbn in Ha; lia| apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia]].
        apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FRS; [| lia| intros a Ha [Hin|Hin]; [cbn [fst snd] in Hin; cbn in Ha; lia| apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia]].
        pose proof (h_call _ _ _ _ _ _ _ _ EI2) as (HEAP2 & AUX2 & _ & ST2 & _ & _ & ERR2 & MI2 & CS2 & _).
        pose proof (h_facts _ _ _ _ _ _ _ _ EI2) as (_ & ND2 & BND2 & FRESHD & _).
        pose proof (BND2 dd AD n ltac:(apply in_app_iff; right; left; reflexivity)) as (AD0 & _ & ADC & _).
        clear MU WM ST MI EI PRE LX2 BK2 SK.
        unfold MallocRep.wz in HDER2. unfold implM. iprefix.
        pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. ihere. to_implM.
        cbn [afree_opt afree ap_embed].
        eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv2) (A := AD) (n := n) (L := OW2 ++ (dd, AD, n) :: NEWk ++ LB); rewrite ?ESP;
          [ exact HEAP2| apply in_app_iff; right; left; reflexivity| exact AUX2| lia| exact ST2| exact CEIL| unfold GLOBALS_TOP; lia
          | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia| exact ERR2| exact MI2| reflexivity| exact CS2| reflexivity|].
        intros s3 ms3 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
        destruct PO as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3).
        replace (ret_pc (Z_to_bv 64 HAR_FREE)) with (Z_to_bv 64 HAR_FREE) by (symmetry; apply ret_pc_even; [unfold HAR_FREE; lia| reflexivity]).
        assert (FRdd : ~ In dd (map blk_id (OW2 ++ LB))) by (apply (FRESHD dd AD n); left; reflexivity).
        rewrite map_app, in_app_iff in FRdd.
        rewrite !map_app in ND2. cbn [map blk_id fst snd app] in ND2.
        pose proof (NoDup_app_split _ _ ND2) as (N23 & _ & _). apply NoDup_cons_iff in N23. destruct N23 as [NDN _]. rewrite in_app_iff in NDN.
        assert (LEQ : lb_remove dd (OW2 ++ (dd, AD, n) :: NEWk ++ LB) = OW2 ++ NEWk ++ LB).
        { rewrite lb_remove_app, lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl, lb_remove_app.
          rewrite !lb_remove_notin by tauto. reflexivity. }
        rewrite LEQ in HP3, HEAP3.
        assert (EI3 : HINV (bv_unsigned sp + -48) s3 st' m3 OW2 errv2 bo2 NEWk).
        { eapply (h_heap _ _ _ _ _ _ _ _ s3 m3 errv2 _ _ NEWk); [exact EI2| exact HP3| | exact HEAP3| apply Permutation_refl| exact MI3| exact ST3| exact ERR3| exact AUX3| exact FA3| exact SO3].
          intros b Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_app_iff; right; exact Hb]. }
        pose proof (agree_of_heap_pres _ _ _ _ HP3) as AG3.
        apply (rw_cells_agree _ _ _ _ _ AG3) in FRA; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG3) in FRS; [| intros a Ha; left; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG3) in HDER2; [| intros a Ha; left; cbn in Ha; lia].
        assert (SK3 : sk_rep m3 (NEWk ++ LB) adr k).
        { eapply sk_rep_agree; [exact AG3| | exact SK2]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
          right. right. exists (qb, Ab, nb). split; [apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK2 Hb)| cbn; lia]. }
        cbn [interp]. apply implM_ret. apply evt_done.
        unfold free_pre. cbn [fst snd]. do 17 eexists. exists F2, fc2, m3, OW2, errv2, bo2, j, (Z_to_bv 64 AD), pv.
        split; [reflexivity|]. split; [exact FRM2|]. split; [exact EI3|]. split; [exact SK3|].
        apply (proj2 (rw_cells_app m3 _ [CB 8%nat j] _)). split; [exact FRA|]. cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) by lia.
        apply (proj2 (rw_cells_app m3 _ [C8 (Z_to_bv 64 AD)] _)). split; [exact HDER2|]. cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia. exact FRS. }
    (* [comment removed for export] *)
    cbv beta. intros [u st3] s3 ms3 PO. cbn [fst snd].
    unfold free_pre in PO. cbn [fst snd] in PO.
    destruct PO as (y1 & y5 & y6 & y7 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F3 & fc3 & m3 & OW3 & errv3 & bo3 & j3 & dv3 & pv3
                    & -> & FRM3 & EI3 & SK3 & FR3).
    eapply har_free; [exact EI3| exact PM| exact SK3| exact FRM3| exact FR3].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_some : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) NEWk (adr : bptr -> Z) (k : skr bptr) j (pv : word),
    HINV (bv_unsigned sp + -48) sX stX mX OWX errvX boX NEWk -> Permutation NEWk (sk_blocks adr k) -> sk_rep mX (NEWk ++ LB) adr k ->
    frm0 fcX -> rw_cells ctusegs mX (bv_unsigned sp + -48) [CB 8%nat j; C8 (wz 0); C8 pv; C8 e9; C8 e8; C8 ra0] ->
    implM ctusegs (interp (ap_embed (abind (amalloc SZ_BIO) (fun bio =>
                                      abind (sct_list_print k) (fun _ => abind (afree bio) (fun _ =>
                                      abind (i2d_sct_list k) (fun _ => sk_free_all k)))) stX))) sX mid_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) x5 x6 x7 x8 x9 (wz (adr (sk_blk k))) x11 x12 x13 x14 x15 x16 x17
               e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 HAR_RET1) fcX None mX (seg_rom ctusegs)).
  Proof.
    intros until pv. intros EI PM SK FRM FR. pose proof SPR' as SPR. unfold HAR_RET1.
    pose proof (h_call _ _ _ _ _ _ _ _ EI) as (HEAP & AUX & _ & ST & _ & _ & ERR & MI & CS & _ & AS & IMG & _).
    pose proof (h_facts _ _ _ _ _ _ _ _ EI) as (_ & ND & BND & FRESH & _).
    pose proof (BND (sk_blk k) (adr (sk_blk k)) STACK_SIZE ltac:(apply in_app_iff; right; exact (proj1 SK))) as (SA0 & _ & SAC & _). unfold STACK_SIZE in SAC.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    pose proof AS as ((HEF & _ & _) & _ & SF & _ & _ & HXL & _).
    pose proof (proj1 (Forall_forall _ _) HEF (p_xl E, e_xl E, MUTEX_SIZE) ltac:(unfold env_blocks; cbn; tauto)) as HXLIN.
    unfold MallocRep.wz in *. clear ERR. unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep.
    carve_frame 16%nat ST. do 4 zstep. zstep. zstep. do 2 zstep. zstep. release_frame FR0 ST (bv_unsigned sp + -48). zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : mem_inv ctusegs m1 |- _ => rename H into MI1 end.
    assert (EI1 : HINV (bv_unsigned sp + -48) sX stX m1 OWX errvX boX NEWk).
    { eapply h_munch; [exact EI| exact MU| exact WM| exact MI1| exact ST| lia| apply OWN0; lia]. }
    assert (SK1 : sk_rep m1 (NEWk ++ LB) adr k).
    { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (BND qb Ab nb ltac:(apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK Hb))) as (_ & _ & B3 & _). cbn. lia. }
    pose proof (h_call _ _ _ _ _ _ _ _ EI1) as (HEAP1 & AUX1 & _ & ST1 & _ & _ & ERR1 & _ & CS1 & _ & AS1 & IMG1 & _).
    pose proof AS1 as (_ & _ & SF1 & _ & _ & HXL1 & _).
    clear MU WM HEAP AUX ST CS AS IMG SF HXL EI SK.
    (* [comment removed for export] *)
    ihere. cbn [abind apbind amalloc afree aret ap_embed fst snd]. to_implM.
    eapply BIO_new_null_walk with (lo := lo) (B := B) (errv := errvX) (E := E) (L := OWX ++ NEWk ++ LB); rewrite ?ESP;
      [ exact HM| exact HEAP1| exact AUX1| lia| exact ST1| exact CEIL| unfold GLOBALS_TOP; lia
      | unfold BIO_NEW_STACK, PREFIX_CREATE_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | exact ERR1| exact MI1| reflexivity| exact SF1| exact HXL1| apply in_app_iff; left; exact HXLIN| apply null_meth_create; exact IMG1| reflexivity| reflexivity|].
    intros pb sB msB PO. unfold bio_null_post in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mB & A & errvB
                    & -> & MIB & STB & ERRB & AUXB & HPB & FAB & SOB & BRA & HEAPB & HBIO).
    replace (ret_pc (Z_to_bv 64 0xe254c)) with (Z_to_bv 64 0xe254c) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
    pose proof BRA as (A0 & A16 & _ & AC & _). unfold BIO_SIZE in AC.
    assert (EIB : HINV (bv_unsigned sp + -48) sB stX mB OWX errvB boX ((pb, A, BIO_SIZE) :: NEWk)).
    { eapply h_alloc; [exact EI1| exact HPB| exact HEAPB| exact MIB| exact STB| exact ERRB| exact AUXB| exact FAB| exact SOB]. }
    pose proof (agree_of_heap_pres _ _ _ _ HPB) as AGB.
    apply (rw_cells_agree _ _ _ _ _ AGB) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (SKB : sk_rep mB (NEWk ++ LB) adr k).
    { eapply sk_rep_agree; [exact AGB| | exact SK1]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      right. right. exists (qb, Ab, nb). split; [apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK1 Hb)| cbn; lia]. }
    pose proof (h_facts _ _ _ _ _ _ _ _ EIB) as (_ & _ & _ & FRESHB & _).
    assert (NPB : ~ In pb (es_ids stX ++ env_ids E)).
    { intros Hin. apply (FRESHB pb A BIO_SIZE ltac:(left; reflexivity)). rewrite map_app, in_app_iff. left.
      pose proof (h_call _ _ _ _ _ _ _ _ EIB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ASB & _). eapply held_ids_OW; [exact ASB| exact Hin]. }
    (* [comment removed for export] *)
    apply (einv_adopt sp m s LB E lo B canary CEIL SPB B63) in EIB.
    pose proof (h_call _ _ _ _ _ _ _ _ EIB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ASB & _).
    clear HEAP1 AUX1 ST1 ERR1 CS1 AS1 IMG1 SF1 HXL1 MI1 EI1 SK1 AGB HPB HEAPB.
    unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctusegs mB) as WM.
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    ihere. to_implM.
    destruct (h_ap_pre _ _ _ _ _ _ _ _ (SCT_LIST_PRINT_STACK TSTK) EIB ltac:(rewrite <- Zplus_mod_idemp_l, SP16; reflexivity)
                ltac:(unfold SCT_LIST_PRINT_STACK, SCT_PRINT_STACK; lia)) as (PRE & _ & _).
    eapply implM_abind.
    { pose proof HPRINT as W. unfold SCT_LIST_print_spec in W.
      eapply W with (K := []) (pbio := pb) (pv := 0) (nw := 0); clear W;
        [exact PRE| reflexivity| exact FRM| reflexivity| reflexivity| reflexivity| unfold A_SEP; reflexivity| reflexivity
        | exact SKB| left; reflexivity| exact NPB| exact HBIO| lia| intros b Hb0; destruct Hb0| intros b Hb0; destruct Hb0| intros b Hb0; destruct Hb0]. }
    cbv beta. intros [[] st2] s2 ms2 PO. cbn [fst snd] in PO |- *.
    unfold ap_post in PO. rewrite ?ESP in PO. cbn [fst snd] in PO.
    destruct PO as (v0 & v1 & v2 & b0' & b1' & b2' & b3' & b4' & b5' & b6' & b7' & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & OW2 & errv2 & bo2
                    & -> & FRM2 & FE2 & PRE2 & LX2 & SO2 & FA2 & BK2 & (ER & EOW & nw2 & NW2 & HBIO2)).
    injection ER. intros EST. subst st2 OW2.
    replace (ret_pc (Z_to_bv 64 0xe2570)) with (Z_to_bv 64 0xe2570) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (EI2 : HINV (bv_unsigned sp + -48) s2 stX m2 ((pb, A, BIO_SIZE) :: OWX) errv2 bo2 ([] ++ NEWk)).
    { eapply (h_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] []); [exact EIB| exact PRE2| rewrite ESP; exact LX2| intros a Ha; destruct Ha| exact SO2| exact FA2| exact BK2]. }
    cbn [app] in EI2.
    apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FR; [| lia| intros a Ha Hin; apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia].
    assert (SK2 : sk_rep m2 (NEWk ++ LB) adr k).
    { eapply sk_rep_agree; [apply (agree_of_lx_pres _ _ _ _ _ LX2)| | exact SKB]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (h_facts _ _ _ _ _ _ _ _ EIB) as (_ & _ & BNDB & _).
      pose proof (BNDB qb Ab nb ltac:(apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SKB Hb))) as (_ & _ & B3 & B4 & _).
      split; [intros Hin; apply rin_ivs_LIBW_AP in Hin; lia|]. right. left. exists (qb, Ab, nb). split; [exact (sk_allblocks_in _ _ _ _ _ SKB Hb)| cbn; lia]. }
    (* [comment removed for export] *)
    apply (einv_release sp m s LB E lo B canary) in EI2; [| exact NPB].
    pose proof (h_call _ _ _ _ _ _ _ _ EI2) as (HEAP2 & AUX2 & _ & ST2 & _ & _ & ERR2 & MI2 & CS2 & _ & AS2 & IMG2 & _).
    pose proof AS2 as ((HEF2 & _ & _) & _ & SF2 & _ & _ & HXL2 & _).
    pose proof (h_facts _ _ _ _ _ _ _ _ EI2) as (_ & ND2 & _ & FRESH2 & _).
    assert (NXB : p_xl E <> pb).
    { intros EQ. apply (FRESH2 pb A BIO_SIZE ltac:(left; reflexivity)). rewrite map_app, in_app_iff. left. rewrite <- EQ.
      apply in_map_iff. exists (p_xl E, e_xl E, MUTEX_SIZE). split; [reflexivity| exact HXLIN]. }
    clear PRE EIB SKB LX2 BK2 PRE2 ASB MU WM.
    unfold MallocRep.wz in HBIO2. unfold implM. iprefix.
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. ihere. cbn [abind apbind amalloc afree aret ap_embed fst snd]. to_implM.
    eapply BIO_free_null_walk with (lo := lo) (B := B) (errv := errv2) (E := E) (L := OWX ++ (pb, A, BIO_SIZE) :: NEWk ++ LB)
                                    (pb := pb) (A := A) (nxt := 0) (prev := 0) (nw := nw2); rewrite ?ESP;
      [ exact HF| exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL| unfold GLOBALS_TOP; lia
      | unfold BIO_FREE_STACK, PREFIX_DESTROY_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
      | exact ERR2| exact MI2| reflexivity| exact SF2| exact HXL2| apply in_app_iff; left; exact HXLIN
      | apply null_meth_destroy; exact IMG2| apply in_app_iff; right; left; reflexivity| exact NXB
      | unfold bio_null_cells in HBIO2; exact HBIO2| reflexivity| clear - SP16; Z.div_mod_to_equations; lia|].
    intros s3 ms3 PO. unfold free2_post in PO. rewrite ?ESP in PO.
    destruct PO as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3 & _).
    replace (ret_pc (Z_to_bv 64 HAR_I2D)) with (Z_to_bv 64 HAR_I2D) by (symmetry; apply ret_pc_even; [unfold HAR_I2D; lia| reflexivity]).
    assert (FRpb : ~ In pb (map blk_id (OWX ++ LB))) by (apply (FRESH2 pb A BIO_SIZE); left; reflexivity).
    rewrite map_app, in_app_iff in FRpb.
    assert (LEQ : lb_remove pb (OWX ++ (pb, A, BIO_SIZE) :: NEWk ++ LB) = OWX ++ NEWk ++ LB).
    { rewrite !map_app in ND2. cbn [map blk_id fst snd app] in ND2.
      pose proof (NoDup_app_split _ _ ND2) as (N23 & _ & _). apply NoDup_cons_iff in N23. destruct N23 as [NDN _]. rewrite in_app_iff in NDN.
      rewrite lb_remove_app, lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl, lb_remove_app.
      rewrite !lb_remove_notin by tauto. reflexivity. }
    rewrite LEQ in HP3, HEAP3.
    assert (EI3 : HINV (bv_unsigned sp + -48) s3 stX m3 OWX errv2 bo2 NEWk).
    { eapply (h_heap _ _ _ _ _ _ _ _ s3 m3 errv2 _ _ NEWk); [exact EI2| exact HP3| | exact HEAP3| apply Permutation_refl| exact MI3| exact ST3| exact ERR3| exact AUX3| exact FA3| exact SO3].
      intros b Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_app_iff; right; exact Hb]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP3) as AG3.
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (SK3 : sk_rep m3 (NEWk ++ LB) adr k).
    { eapply sk_rep_agree; [exact AG3| | exact SK2]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      right. right. exists (qb, Ab, nb). split; [apply in_app_iff; right; exact (sk_allblocks_in _ _ _ _ _ SK2 Hb)| cbn; lia]. }
    eapply har_i2d; [exact EI3| exact PM| exact SK3| exact FRM2| exact FR].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_none : forall sX stX mX OWX (errvX : word) boX (FX : bvmap 5 word) (fcX : bv 32)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j (dv pv : word),
    HINV (bv_unsigned sp + -48) sX stX mX OWX errvX boX [] ->
    frm0 fcX -> rw_cells ctusegs mX (bv_unsigned sp + -48) [CB 8%nat j; C8 dv; C8 pv; C8 e9; C8 e8; C8 ra0] ->
    implM ctusegs (interp (ap_embed (aret tt stX))) sX mid_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) x5 x6 x7 x8 x9 (wz 0) x11 x12 x13 x14 x15 x16 x17
               e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 x28 x29 x30 x31)
          FX (Z_to_bv 64 HAR_RET1) fcX None mX (seg_rom ctusegs)).
  Proof.
    intros until pv. intros EI FRM FR. pose proof SPR' as SPR. unfold HAR_RET1, MallocRep.wz.
    pose proof (h_call _ _ _ _ _ _ _ _ EI) as (_ & _ & _ & ST & _ & _ & _ & MI & _).
    cbn [aret ap_embed interp]. apply implM_ret.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    zstep. btaken. apply evt_done.
    unfold mid_post. cbn [fst snd]. do 18 eexists. exists FX, fcX, mX, OWX, errvX, boX.
    split; [unfold HAR_CLR; reflexivity|]. split; [exact FRM|]. split; [exact EI|]. exists j, dv, pv. exact FR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fuzz_act : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ls : ap_ls bptr) (nw : Z),
    st0 = st_of_ls ls ->
    ap_state st0 m OW E (0, nw) -> ids_ok E st0 -> ApIface.data_cells m OW st0 ->
    ssp_cells m canary -> rauxv_ok m B -> stk ctusegs m lo (bv_unsigned sp) -> rw_cells ctusegs m (errno_addr (wz RATP)) [C4 errv] -> mem_inv ctusegs m ->
    frm0 fc ->
    implM ctusegs (interp (ap_embed (ct_one ls d))) s
      (rfuzz_one_post (LM := @LM_ap (ap_ls bptr) ct_ls0 ct_lib_one) (LSP := @LSP_ap (ap_ls bptr) ct_ls0 ct_lib_one ct_lib_inv3)
                      ra0 sp gp (wz RATP) e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 s LB D d lo B canary m)
      (MS (mkR ra0 sp gp (wz RATP) t0 t1 t2 e8 e9 (wz D) (wz (zlength d)) a2 a3 a4 a5 a6 a7 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 t3 t4 t5 t6)
          F (wz LX_FUZZ) fc None m (seg_rom ctusegs)).
  Proof.
    intros until nw. intros EST AS IDS DC SSP AUX ST ERR MI FRM. pose proof SPR' as SPR.
    pose proof PAY0 as (_ & PF & D0 & DN & DN30 & _). unfold zlength in DN, DN30.
    unfold ct_one. rewrite (ct_bytes_id d PF), <- EST.
    assert (PRE0 : ap_pre s st0 m OW LB E (0, nw) sp lo B errv canary 65536).
    { unfold ap_pre. split; [exact HEAP0|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact AUX|]. split; [exact SPB|]. split; [exact B63|].
      split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|]. split; [exact ERR|]. split; [exact SSP|]. split; [exact MI| exact SP16]. }
    destruct (einv_entry sp m s LB E lo B canary [] [] st0 OW (0, nw) errv 65536 PRE0 ltac:(lia) ltac:(intros b Hb0; destruct Hb0) ltac:(intros b Hb0; destruct Hb0)) as (EI0 & _ & _).
    pose proof (LH_nodup _ _ _ HEAP0) as ND0. rewrite map_app in ND0. pose proof (NoDup_app_split _ _ ND0) as (NDLB & _ & _).
    unfold LX_FUZZ, MallocRep.wz in *. rewrite EA in ERR. unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    (* [comment removed for export] *)
    zstep. carve_frame 48%nat ST. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : mem_inv ctusegs m1 |- _ => rename H into MI1 end.
    assert (EI1 : HINV (bv_unsigned sp + -48) s st0 m1 OW errv (0, nw) []).
    { eapply h_munch; [exact EI0| exact MU| exact WM| exact MI1| exact ST| lia| apply OWN0; lia]. }
    assert (PAY1 : payload_ok m1 LB D d).
    { eapply (payload_ok_munch s OW LB m m1); [exact HEAP0| exact PAY0| exact MU| exact CEIL|]. constructor; [left; cbn; lia| constructor]. }
    clear MU WM ERR EI0 PRE0.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] =>
      pose proof (proj1 (rw_cells_app m1 _ [c0; c1] [c2; c3; c4; c5]) FR) as [FRA FRb];
      cbn [cells_size csize Nat.add] in FRb; replace (bv_unsigned sp + -48 + Z.of_nat 16) with (bv_unsigned sp + -32) in FRb by lia;
      pose proof (proj1 (rw_cells_app m1 _ [c2] [c3; c4; c5]) FRb) as [FRP FRS]; clear FRb;
      cbn [cells_size csize Nat.add] in FRS; replace (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -24) in FRS by lia end.
    ihere. to_implM.
    lazymatch goal with |- implM _ _ _ _ ?msx => set (ms1 := msx) end.
    destruct (h_ap_pre _ _ _ _ _ _ _ _ D2I_SCT_LIST_STACK EI1 ltac:(rewrite <- Zplus_mod_idemp_l, SP16; reflexivity)
                ltac:(let v := eval vm_compute in D2I_SCT_LIST_STACK in change D2I_SCT_LIST_STACK with v; lia)) as (PRE & _ & _).
    (* [comment removed for export] *)
    set (KK := fun ok : option (skr bptr) =>
           abind (match ok with
                  | None => aret tt
                  | Some k0 => abind (amalloc SZ_BIO) (fun bio => abind (sct_list_print k0) (fun _ => abind (afree bio) (fun _ =>
                               abind (i2d_sct_list k0) (fun _ => sk_free_all k0))))
                  end) (fun _ => abind err_clear_error (fun _ => aret 0))).
    assert (SRC : implM ctusegs (interp (ap_embed (apbind (d2i_list_tree d KK st0) (fun r => ARet (ls_of_st (snd r), fst r))))) s
                    (rfuzz_one_post (LM := @LM_ap (ap_ls bptr) ct_ls0 ct_lib_one) (LSP := @LSP_ap (ap_ls bptr) ct_ls0 ct_lib_one ct_lib_inv3)
                                    ra0 sp gp (wz RATP) e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 s LB D d lo B canary m) ms1).
    2:{ unfold d2i_list_tree in SRC. unfold abind at 1 in SRC. apply implM_ap_assoc_r in SRC.
        unfold ct_call. unfold abind at 1. apply implM_ap_assoc'.
        eapply implM_apbind_cont; [| exact SRC]. clear SRC.
        intros [[os|] st'] s' ms' H; cbn [fst snd] in H |- *.
        - (* [comment removed for export] *)
          apply implM_ap_assoc_r in H. apply implM_ap_assoc'. apply implM_ap_assoc'.
          eapply implM_apbind_cont; [| exact H]. clear H. intros [ok st2] s2 ms2 H; cbn [fst snd] in H |- *.
          apply implM_ap_assoc_r in H. apply implM_ap_assoc'.
          eapply implM_apbind_cont; [| exact H]. clear H. intros [[] st3] s3 ms3 H; cbn [fst snd] in H |- *.
          subst KK. cbv beta in H. unfold abind at 1 in H. apply implM_ap_assoc_r in H. exact H.
        - subst KK. cbv beta in H. exact H. }
    eapply (implM_apbind _ _ s fin_post).
    2:{ intros [rz stF] sF msF [RZ PO]. cbn [fst snd] in RZ, PO |- *. subst rz. cbn [ap_embed interp]. apply implM_ret. apply evt_done. exact PO. }
    pose proof HD2I as W. unfold d2i_sct_list_spec in W.
    eapply (W Z KK fin_post) with (K := []) (D := D) (PIN := bv_unsigned sp + -32) (adr := badr LB); clear W; rewrite ?ESP;
      [exact PRE| reflexivity| exact FRM| intros b Hb0; destruct Hb0| intros b Hb0; destruct Hb0| exact PAY1
      | intros [[qb Ab] nb] Hb; cbn [blk_id blk_addr fst snd]; exact (badr_in _ _ _ _ NDLB Hb)
      | lia| lia| clear - SP16; Z.div_mod_to_equations; lia| exact FRP| reflexivity| reflexivity| reflexivity|].
    intros ok st' s' ms' PO. subst KK. cbv beta.
    eapply implM_abind; [| intros r s2 ms2 PO2; eapply har_clr; exact PO2].
    unfold d2i_list_post in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & OW2 & errv2 & bo2 & adr2 & NEW2
                    & -> & FRM2 & FE2 & PRE2 & LX2 & SO2 & FA2 & BK2 & ADR2 & FRESH2 & RES).
    replace (ret_pc (Z_to_bv 64 HAR_RET1)) with (Z_to_bv 64 HAR_RET1) by (symmetry; apply ret_pc_even; [unfold HAR_RET1; lia| reflexivity]).
    assert (EI2 : HINV (bv_unsigned sp + -48) s' st' m2 OW2 errv2 bo2 (NEW2 ++ [])).
    { eapply (h_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ [(bv_unsigned sp + -32, bv_unsigned sp + -32 + 8)] NEW2);
        [exact EI1| exact PRE2| rewrite ESP; exact LX2| | exact SO2| exact FA2| exact BK2].
      intros a Ha. left. cbn [rin_ivs fst snd] in Ha. lia. }
    rewrite app_nil_r in EI2.
    apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FRA; [| lia| intros a Ha [Hin|Hin]; [cbn [fst snd] in Hin; cbn in Ha; lia| apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia]].
    apply (rw_cells_lx _ _ _ _ _ _ _ LX2) in FRS; [| lia| intros a Ha [Hin|Hin]; [cbn [fst snd] in Hin; cbn in Ha; lia| apply rin_ivs_LIBW_AP in Hin; cbn in Ha; lia]].
    unfold MallocRep.wz in *.
    destruct ok as [k|].
    - destruct RES as (PM & SK & HPIN).
      assert (SK2 : sk_rep m2 (NEW2 ++ LB) adr2 k).
      { eapply sk_rep_relist; [exact SK|]. intros b Hb. apply in_app_iff. left. eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]. }
      cbv iota beta. eapply har_some; [exact EI2| exact PM| exact SK2| exact FRM2|].
      lazymatch type of FRA with rw_cells _ _ _ [?c0; ?c1] =>
        apply (proj2 (rw_cells_app m2 _ [c0; c1] _)) end. split; [exact FRA|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned sp + -48 + Z.of_nat 16) with (bv_unsigned sp + -32) by lia.
      apply (proj2 (rw_cells_app m2 _ [C8 (Z_to_bv 64 (D + zlength d))] _)). split; [exact HPIN|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -24) by lia. exact FRS.
    - destruct RES as [ENEW [pv HPIN]]. subst NEW2.
      cbv iota beta. eapply har_none; [exact EI2| exact FRM2|].
      lazymatch type of FRA with rw_cells _ _ _ [?c0; ?c1] =>
        apply (proj2 (rw_cells_app m2 _ [c0; c1] _)) end. split; [exact FRA|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned sp + -48 + Z.of_nat 16) with (bv_unsigned sp + -32) by lia.
      apply (proj2 (rw_cells_app m2 _ [C8 pv] _)). split; [exact HPIN|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned sp + -32 + Z.of_nat 8) with (bv_unsigned sp + -24) by lia. exact FRS.
  Qed.
  End Act.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem rfuzz_one_ct :
    rfuzz_one_stmt (LM := @LM_ap (ap_ls bptr) ct_ls0 ct_lib_one) (LSP := @LSP_ap (ap_ls bptr) ct_ls0 ct_lib_one ct_lib_inv3).
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HEAP LI LXS SE SSP AUX SPB B63 ST CEIL GLO LO ERR Etp MI SP16 PAY FRM Ea0 Ea1.
    change (ct_lib_inv3 ls m OW) in LI. destruct LI as (E & (ECNF & nw & AS) & IDS & DC).
    subst tp a0 a1. unfold GLOBALS_TOP in GLO. cbn [LX_FUZZ_STACK LIB_STACK LSP_ap] in LO.
    change (lib_one_prog ls d) with (interp (ap_embed (ct_one ls d))).
    eapply (fuzz_act sp gp F fc m s (st_of_ls ls) OW LB E lo B errv canary D d) with (ls := ls) (nw := nw);
      first [eassumption| reflexivity| lia].
  Qed.
End Proofs.
End WithCeiling0.
