(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge ApPrim.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA UnwindA UnwindX UnwindRecA EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame I_strcpyA W_err_newA W_err_set_debugA W_err_vsetA W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA EncKitA EncActA Fr_i2o_SCT Fr_i2o_SCT_LIST W_sct_completeA W_i2o_sctA W_i2o_sct_failA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

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

Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

(* [comment removed for export] *)
Fixpoint i2o_sum (l : list (sctr bptr)) : Z := match l with [] => 0 | x :: t => 2 + i2o_sct_len x + i2o_sum t end.
Lemma i2o_sum_ge0 : forall adr l, Forall (sct_ok adr) l -> 0 <= i2o_sum l <= 196702 * zlength l.
Proof.
  intros adr l. induction l as [|x t IH]; intros H; cbn [i2o_sum]; [unfold zlength; cbn; lia|]. apply Forall_cons_iff in H. destruct H as [Hx Ht].
  specialize (IH Ht). unfold zlength in *. cbn [length].
  destruct Hx as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
  unfold i2o_sct_len. destruct (sc_version x =? 0); lia.
Qed.
Lemma i2o_sum_app : forall a b, i2o_sum (a ++ b) = i2o_sum a + i2o_sum b.
Proof. induction a as [|y t IH]; intros b; cbn [i2o_sum app]; [lia| rewrite IH; lia]. Qed.
Lemma zlength_app_l : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_ge0 : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

(* [comment removed for export] *)
Lemma i2o_len_pass_ok : forall (l : list (sctr bptr)) acc st, Forall (fun x => sct_complete x = true) l -> i2o_len_pass l acc st = ARet (Some (acc + i2o_sum l), st).
Proof.
  induction l as [|x t IH]; intros acc st H; cbn [i2o_len_pass i2o_sum].
  - unfold aret. rewrite Z.add_0_r. reflexivity.
  - apply Forall_cons_iff in H as [Hx Ht]. rewrite Hx. rewrite (IH _ _ Ht). replace (acc + 2 + i2o_sct_len x + i2o_sum t) with (acc + (2 + i2o_sct_len x + i2o_sum t)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sk_data_cellsA_app : forall (m : mem) adr D i done rest,
  sk_data_cellsA m adr D i (done ++ rest) -> sk_data_cellsA m adr D (i + zlength done) rest.
Proof.
  intros m adr D i done. revert i. induction done as [|y d IH]; intros i rest H.
  - unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact H.
  - cbn [sk_data_cellsA app] in H. destruct H as [_ H]. pose proof (IH _ _ H) as H'. unfold zlength in *. cbn [length].
    replace (i + Z.of_nat (S (length d))) with (i + 1 + Z.of_nat (length d)) by lia. exact H'.
Qed.

(* [comment removed for export] *)
Definition IOL_LEN_STACK_A : Z := 176 + I2O_SCT_FAIL_STACK_A.
(* [comment removed for export] *)
Definition IOL_LEN_COST_A (n : Z) : Z := 1 + n + I2O_SCT_FAIL_COST_A.
Definition IOL_LEN_FRAMES_A : Z := 1 + I2O_SCT_FAIL_FRAMES_A.
(* [comment removed for export] *)
Definition IOL_NESTED_RET : Z := 0x336e4c.   (* [comment removed for export] *)
Definition IOL_REC_DEPTH : nat := 6.          (* [comment removed for export] *)
Definition IOL_LOOP : Z := 0x336ce8.
Definition IOL_AFTER : Z := 0x336dac.      (* [comment removed for export] *)
Definition IOL_ERR : Z := 0x336db4.
Definition IOL_OK : Z := 0x336dcc.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec I2O_SCT_LIST_A IOL_NESTED_RET IOL_REC_DEPTH}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ios := (E_i2o_SCT_LIST_34b11c : uk_call 3369852 3370336 3367120).

(* [comment removed for export] *)
Hypothesis STRCPY : strcpy_icontract RT.

Local Ltac ecu := unfold IOL_LEN_STACK_A, IOL_LEN_COST_A, IOL_LEN_FRAMES_A, I2O_SCT_FAIL_STACK_A, I2O_SCT_FAIL_COST_A, I2O_SCT_FAIL_FRAMES_A, I2O_SCT_LEN_STACK_A, IOS_FRAME,
                         ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK,
                         ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, CRYPTO_FREE_STACK, RT_STACK in *.

(* [comment removed for export] *)
Definition lenpost_ok (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (k : skr bptr) (tot : Z) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (if 65535 <? tot then -1 else tot)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' st m' OW LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K st OW m m'
    /\ sk_repA m' LB adr k
    /\ Forall (fun x => sct_complete x = true) (sk_items k).

(* [comment removed for export] *)
Definition lenpost_fail (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (k : skr bptr) (st1 : ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' st1 m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K st1 OW' m m'
    /\ sk_repA m' LB adr k.

Section ActLen.
  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z).
  Variables (lo : Z) (K : list block) (ras : list Z) (STK CST FRMb : Z) (adr : bptr -> Z) (k : skr bptr).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo STK CST FRMb.
  Hypothesis STKB : IOL_LEN_STACK_A <= STK.
  Hypothesis CSTB : IOL_LEN_COST_A (zlength (sk_items k)) <= CST.
  Hypothesis FRMB : IOL_LEN_FRAMES_A <= FRMb.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  (* [comment removed for export] *)
  Variables (j : nat) (X0 : list Z).
  Hypothesis ERAS : bv_unsigned ra :: ras = repeat IOL_NESTED_RET j ++ X0.
  Hypothesis CTXJ : uk_ctxJ j X0.
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis SK : sk_repA m LB adr k.
  (* [comment removed for export] *)
  Variables (Σ1 : rts RT) (m4 : mem) (f spa : Z) (g : nat) (junk gj j0 j8 j32 j40 : list byte).
  Hypothesis HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m4.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 0 b.
  Hypothesis GEO : fr_geo f 0.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis EL1 : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis ST4 : stk ctasegs m4 lo spa.
  Hypothesis MI4 : mem_inv ctasegs m4.
  Hypothesis AG4 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m4.
  Hypothesis FRL4 : rw_cells ctasegs m4 spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 f); CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk].   (* [comment removed for export] *)
  Hypothesis FRH4 : rw_cells ctasegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 176 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 160.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 72.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Variables (B0 : Type) (G : option Z -> @AM bptr B0) (Q : B0 * ap_st bptr -> rts RT -> machine_state -> Prop).
  Hypothesis KS : forall Σ' ms',
    lenpost_ok ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB E bo lo m K (IOL_LEN_COST_A (zlength (sk_items k))) adr k (2 + i2o_sum (sk_items k)) Σ' ms' ->
    implAp (G (Some (2 + i2o_sum (sk_items k))) st) Σ' Q ms'.
  Hypothesis KN : forall st1 Σ' ms',
    lenpost_fail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (IOL_LEN_COST_A (zlength (sk_items k))) adr k st1 Σ' ms' ->
    implAp (abind (abind (err_raise RS_i2o_list) (fun _ => aret None)) G st1) Σ' Q ms'.

  Let STKb : Z := STK - 176.
  Let CSTb : Z := CST - 1.
  Let FRMb' : Z := FRMb - 1.
  (* [comment removed for export] *)
  Let linv : rts RT -> ap_st bptr -> mem -> list block -> Z * Z -> list block -> Z -> Prop :=
    @oinv (push AR f 0) (Z_to_bv 64 spa) spa m4 Σ1 LB E lo K [] STKb CSTb FRMb'.
  (* [comment removed for export] *)
  Let frameL (mX : mem) : Prop := rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 f); CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk].
  Let frameH (mX : mem) : Prop := rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition bst (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mX : mem) (pc : Z) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 0) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (adr (sk_blk k))) x22 x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 SHB) x27 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mX (seg_rom ctasegs).

  Lemma base_facts :
    0 <= bv_unsigned sp < 2 ^ 64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo /\ 0 <= lo
    /\ lo <= bv_unsigned sp - STK /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
    /\ 0 < f /\ f mod 64 = 0 /\ f + 64 <= ACEIL /\ SEGTOP_A <= f /\ (f + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f /\ CST <= rt_credit RT Σ /\ Z.of_nat (length FRM) + FRMb <= Z.of_nat FRAMES_MAX.
  Proof.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
    pose proof STKB as STKu. ecu.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LOSP SPAL SPAH SPR LO0 STKu; plia).
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; plia).
    split; [exact SPR|]. split; [exact CE1|]. split; [exact CE2|]. split; [exact CE3|]. split; [exact CEIL|]. split; [exact LO0|]. split; [exact LOSP|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact ESPA|]. split; [exact Ef|]. split; [clear - CRED; lia| clear - FRM0; lia].
  Qed.

  Lemma OKALL : Forall (sct_ok adr) (sk_items k).
  Proof.
    pose proof PRE as (HEAP & _). pose proof SK as (_ & _ & _ & HF & _).
    apply Forall_forall. intros x Hx. eapply (sct_ok_of_repA _ _ _ _ _ _ HEAP). exact (proj1 (Forall_forall _ _) HF x Hx).
  Qed.

  Lemma KH : @kit_hyps (push AR f 0) (Z_to_bv 64 spa) spa LB lo [] STKb.
  Proof.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & _).
    pose proof STKB as STKu. ecu.
    unfold kit_hyps. rewrite ESPA. split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL|]. split; [exact LO0|]. split; [subst STKb; clear - LOSP SPAL; lia|].
    split; [subst STKb; clear - STKu; plia|]. split; [clear; lia|]. split; [clear - TOP SPAH; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    split; [clear - SPA32; Z.div_mod_to_equations; lia| constructor].
  Qed.

  Lemma AG04 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m4.
  Proof. exact AG4. Qed.

  (* [comment removed for export] *)
  Lemma linv0 : linv Σ1 st m4 OW bo [] CSTb.
  Proof.
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu. pose proof (zlength_ge0 (sk_items k)) as Z0.
    apply (oinv_entry _ _ _ _ _ _ _ _ _ _ _ _ KH).
    - subst STKb CSTb FRMb'. replace (STK - 176) with (STK - 160 - 16) by (clear; lia).
      eapply (pro_closeA Σ st m OW LB E bo sp lo STK CST FRMb f 0%nat Σ1 m4 spa 160);
        [exact PRE| exact HEAP4| exact ST4| exact MI4| exact AG4| exact CR1| exact SPA32| clear - SPAL; lia| clear - SPAH; lia| clear; lia| clear - STKu; lia| clear - CSTu Z0; lia| clear - FRMu; lia].
    - exact KOW.
    - exact KIDS.
  Qed.

  (* [comment removed for export] *)
  Lemma keep_frame : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX ->
    frameL mX /\ frameH mX /\ uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras) /\ agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX.
  Proof.
    intros until CX. intros (_ & AX & _).
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & _).
    pose proof STKB as STKu. ecu. nrm. rewrite ESPA in AX. cbn [app] in AX.
    assert (AXS : forall a, spa <= a < USTACK_TOP -> mX (wa a) = m4 (wa a)).
    { intros a Ha. unfold USTACK_TOP in Ha. apply AX; [clear - Ha SPR CEIL LOSP STKu SPAL LO0; lia|]. split; [| left; unfold USTACK_TOP; exact Ha].
      unfold LIBW_A. cbn [rin_ivs fst snd]. clear - Ha CEIL CE1 LOSP STKu SPAL. lia. }
    assert (AGS : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX).
    { intros a Ha Hr. unfold USTACK_TOP in Hr. rewrite (AXS a ltac:(unfold USTACK_TOP; clear - Hr SPAH; lia)). apply AG4; [exact Ha| left; unfold USTACK_TOP; exact Hr]. }
    split; [| split; [| split; [| exact AGS]]].
    - eapply rw_cells_agree; [| exact FRL4|]; [intros wa' Hr Hc; exact (AXS wa' Hc)|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold USTACK_TOP. clear - Ha TOP GSZ SPAH. lia.
    - eapply rw_cells_agree; [| exact FRH4|]; [intros wa' Hr Hc; exact (AXS wa' Hc)|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold USTACK_TOP. clear - Ha TOP SPAH. lia.
    - eapply (uw_call m mX spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [exact UW| exact AGS| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| unfold USTACK_TOP; clear - TOP; lia| apply bv_unsigned_in_range|].
      rewrite !Z_to_bv_bv_unsigned. cbn [app]. eapply rw_cells_agree; [| exact FRH4|]; [intros wa' Hr Hc; exact (AXS wa' Hc)|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold USTACK_TOP. clear - Ha TOP SPAH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma keep_sk : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX -> sk_repA mX LB adr k.
  Proof.
    intros until CX. intros (PREX & AX & _). pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 spa)) as SPR'.
    pose proof PREX as (HEAPX & _). pose proof PRE as (HEAP & _).
    assert (SK4 : sk_repA m4 LB adr k).
    { eapply sk_repA_agree; [exact AG4| | exact SK]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha]. }
    eapply sk_repA_agree; [exact AX| | exact SK4]. intros b a Hb Ha. pose proof (sk_repA_blocks_in _ _ _ _ _ SK Hb) as HbL.
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror HbL))) as (B1 & _ & _ & _ & B5).
    split.
    - unfold LIBW_A. cbn [app rin_ivs fst snd]. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Ha, B1, B5. clear - Ha B1 B5. lia.
    - right; right. exists b. split; [exact HbL| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma item_factsA : forall ΣX stX mX OWX boX CX done x t,
    linv ΣX stX mX OWX boX [] CX -> sk_repA mX LB adr k -> sk_items k = done ++ x :: t ->
    let SA := adr (sk_blk k) in let D := optr adr (sk_data k) in let num := sk_num k in let i := zlength done in
    exists q na,
      sk_data k = Some (q, na) /\ D = adr q /\ In (sk_blk k, SA, STACK_SIZE) (OWX ++ LB) /\ SA mod 16 = 0 /\ In (q, adr q, 8 * na) (OWX ++ LB) /\ adr q mod 16 = 0 /\ num <= na
      /\ 0 <= i < num /\ num < 2^23
      /\ ro_cells ctasegs mX SA [C4 (wz num)] /\ ro_cells ctasegs mX (SA + SKO_DATA) [C8 (wz D)] /\ ro_cells ctasegs mX (D + 8 * i) [C8 (wz (adr (sc_blk x)))]
      /\ sct_repA mX LB adr x /\ sct_ok adr x /\ In (sc_blk x, adr (sc_blk x), SCT_SIZE) (OWX ++ LB) /\ adr (sc_blk x) mod 16 = 0
      /\ rw_cells ctasegs mX (adr (sc_blk x)) (sct_cells adr x (-1) 0).
  Proof.
    intros until t. intros LI SKX EQ. cbn zeta.
    destruct LI as (PREX & _). destruct PREX as (HEAP & _). cbn [app] in HEAP.
    pose proof (sk_repA_free_view _ _ _ _ SKX) as ((HN & HD & _) & HIN & HDB & DCS & _ & _).
    pose proof SKX as ((_ & ALS) & _ & HDD & HF & _).
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; lia).
    pose proof (zlength_ge0 done) as D0. pose proof (zlength_ge0 t) as T0.
    destruct (sk_data k) as [[q na]|] eqn:ED; [| exfalso; rewrite HDD in EQ; destruct done; discriminate].
    destruct HDD as (HQ & ALQ & HNA & HNA2 & _). destruct HDB as [_ _].
    exists q, na. split; [reflexivity|]. split; [reflexivity|].
    split; [apply in_or_app; right; exact HIN|]. split; [exact ALS|]. split; [apply in_or_app; right; exact HQ|]. split; [exact ALQ|]. split; [exact HNA|].
    split; [clear - LEN D0 T0; lia|]. split; [clear - HNA HNA2; lia|].
    split; [exact HN|]. split; [exact HD|].
    rewrite EQ in DCS. cbn [optr] in DCS. pose proof (sk_data_cellsA_app _ _ _ _ _ _ DCS) as [DX _]. rewrite Z.add_0_l in DX.
    split; [exact DX|].
    assert (HX : sct_repA mX LB adr x) by (apply (proj1 (Forall_forall _ _) HF); rewrite EQ; apply in_or_app; right; left; reflexivity).
    split; [exact HX|]. split; [exact (sct_ok_of_repA _ _ _ _ _ _ HEAP HX)|].
    pose proof HX as (XIN & XAL & XC & _). split; [apply in_or_app; right; exact XIN|]. split; [exact XAL| exact XC].
  Qed.

  (* [comment removed for export] *)
  Lemma close_post : forall ΣX stX mX OWX CX Σ' m',
    linv ΣX stX mX OWX bo [] CX -> CSTb - zlength (sk_items k) - I2O_SCT_FAIL_COST_A <= CX ->
    AHEAP Σ' OWX LB m' -> rt_credit RT Σ' = rt_credit RT ΣX -> stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
    agree_on (aclient_addr (OWX ++ LB) spa) mX m' ->
    ap_preA Σ' stX m' OWX LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m m'
    /\ rt_credit RT Σ - IOL_LEN_COST_A (zlength (sk_items k)) <= rt_credit RT Σ'
    /\ blocks_kept K stX OWX m m'.
  Proof.
    intros until m'. intros LI HCX HEAP' CR' ST' MI' AG'.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & _).
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & CRED & FRM0).
    destruct LI as (PREX & AX & KO & KI & KP & CR & LBOK). cbn [app] in PREX, AX.
    pose proof PREX as (HEAPX & ASX & IDSX & DCX & STX & _ & _ & _ & _ & MIX & CREDX & _). rewrite ESPA in AX. cbn [ar_RT ar_FR push amb] in CREDX, CR.
    split; [| split; [| split]].
    - unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASX | exact AG']|]. split; [exact IDSX|].
      split; [eapply data_cells_rt; [exact ASX | exact DCX | exact AG']|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSP STKB; ecu; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [clear - CREDX CR'; lia|]. clear - FRM0. lia.
    - eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [exact AG4 | clear; lia]|].
      eapply ax_pres_trans; [eapply ax_pres_lower; [exact AX | clear - SPAH; lia]|].
      eapply (ax_pres_of_aclient OWX LB); [exact AG' | clear - SPAH; lia].
    - subst CSTb. clear - CR CR1 CR' HCX. ecu. lia.
    - eapply (blocks_kept_post K stX OWX LB); [| exact AG']. eapply (blocks_kept_pre K stX OW OWX LB); [exact KOW | exact AG4 |].
      split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP].
  Qed.

  (* [comment removed for export] *)
  Lemma len_ret : forall ΣX mX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x28 x29 x30 x31 : word) FX fcX (tot r : Z),
    linv ΣX st mX OW bo [] (CSTb - zlength (sk_items k)) -> Forall (fun x => sct_complete x = true) (sk_items k) ->
    tot = 2 + i2o_sum (sk_items k) -> r = (if 65535 <? tot then -1 else tot) ->
    implAp (G (Some tot) st) ΣX Q
      (bst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 r) x28 x29 x30 x31 FX fcX mX IOL_EXIT).   (* [comment removed for export] *)
  Proof.
    intros until r. intros LI CPL Etot Er. subst tot r. pose proof (keep_sk _ _ _ _ _ _ _ LI) as SKX.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & _).
    pose proof STKB as STKu. ecu.
    pose proof (keep_frame _ _ _ _ _ _ _ LI) as (FRL & FRH & UWX & AGS).
    pose proof LI as (PREX & _). cbn [app] in PREX. pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & _). rewrite ESPA in STX.
    intros XX Φ DD SAFE LINK.
    unfold bst. change (Z_to_bv 64 IOL_EXIT) with (wz IOL_EXIT).
    eapply (@iol_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAPX| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STX| exact CEIL| clear - LOSP STKu SPAL; lia
      | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIX| exact (rw_cells_cb_first mX spa _ 4 FRL)| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply (implAp_elim (G (Some _) st) ΣX Σ' _ _ XX Φ DD); [| exact SAFE| exact LINK| exact LIVE'].
    apply KS.
    assert (SM : -2^31 <= (if 65535 <? 2 + i2o_sum (sk_items k) then -1 else 2 + i2o_sum (sk_items k)) < 2^31).
    { pose proof (i2o_sum_ge0 adr (sk_items k) OKALL) as B. destruct (65535 <? 2 + i2o_sum (sk_items k)) eqn:EB; [clear; lia|]. apply Z.ltb_ge in EB. clear - EB B. lia. }
    rewrite (v_addiw0_int _ SM).
    destruct (close_post _ _ _ _ _ _ _ LI ltac:(clear; ecu; lia) HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK').
    unfold lenpost_ok. do 16 eexists. exists m'. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
    split; [| exact CPL]. eapply sk_repA_agree; [exact AG'| | exact SKX]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SKX Hb)| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma linv_munch : forall ΣX stX mX OWX boX CX mY W,
    linv ΣX stX mX OWX boX [] CX -> munch W mX mY -> wmono ctasegs mX mY -> mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    Forall (fun iv => lo <= fst iv /\ snd iv <= spa) W -> linv ΣX stX mY OWX boX [] CX.
  Proof.
    intros until W. intros LI MU WM MI ST HW. pose proof base_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESPA & _).
    eapply (oinv_munch _ _ _ _ _ _ _ _ _ _ _ _ KH); [exact LI| exact MU| exact WM| exact MI| exact ST|].
    eapply Forall_impl; [| exact HW]. intros [u v] [H1 H2]. left. cbn [fst snd] in *. rewrite ESPA. split; [exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma len_loop : forall rest done acc ΣC mC (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) FC fcC,
    sk_items k = done ++ rest -> rest <> [] -> Forall (fun x => sct_complete x = true) done -> acc = 2 + i2o_sum done ->
    linv ΣC st mC OW bo [] (CSTb - zlength done) ->
    implAp (abind (i2o_len_pass rest acc) G st) ΣC Q
      (bst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-1)) (Z_to_bv 64 (zlength done)) x23 (Z_to_bv 64 f) (Z_to_bv 64 acc) x28 x29 x30 x31 FC fcC mC IOL_LOOP).   (* [comment removed for export] *)
  Proof.
    induction rest as [|x t IH]; intros until fcC; intros EQ NEr CPLD Eacc LI; [exfalso; exact (NEr eq_refl)|]. pose proof (keep_sk _ _ _ _ _ _ _ LI) as SKC.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0).
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu.
    pose proof (keep_frame _ _ _ _ _ _ _ LI) as (FRL & FRH & UWC & AGS).
    destruct (item_factsA _ _ _ _ _ _ done x t LI SKC EQ) as (q & na & ED & EDQ & KIN & KAL & QIN & QAL & NA & IR & NR & RNUM & RDAT & RITEM & REPX & OKX & XIN & XAL & HX).
    pose proof LI as (PREX & AX & KO & KI & KP & CR & LBOK). cbn [app] in PREX.
    pose proof PREX as (HEAPC & ASC & IDSC & DCC & STC & _ & _ & _ & _ & MIC & CREDC & FRMC). rewrite ESPA in STC. cbn [ar_RT ar_FR push amb length] in CREDC, FRMC, CR.
    pose proof (zlength_ge0 done) as D0. pose proof (zlength_ge0 t) as T0.
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; clear; lia).
    pose proof (AH_range_gen _ _ _ _ _ HEAPC KIN) as (KB0 & _ & _ & KBC & _). pose proof (AH_range_gen _ _ _ _ _ HEAPC QIN) as (QB0 & _ & _ & QBC & _).
    pose proof (AH_range_gen _ _ _ _ _ HEAPC XIN) as (XB0 & _ & _ & XBC & _). cbn [blk_addr blk_size fst snd] in KB0, KBC, QB0, QBC, XB0, XBC. nrm.
    rewrite EDQ in RDAT, RITEM. unfold SKO_DATA, MallocRep.wz in RNUM, RDAT, RITEM.
    destruct (sct_complete x) eqn:CPLx.
    - (* [comment removed for export] *)
      replace (abind (i2o_len_pass (x :: t) acc) G st) with (abind (i2o_len_pass t (acc + 2 + i2o_sct_len x)) G st) by (cbn [i2o_len_pass]; rewrite CPLx; reflexivity).
      intros XX Φ DD SAFE LINK. unfold bst, IOL_LOOP.
      pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. btaken. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply (@OPENSSL_sk_value_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (q := q) (SA := adr (sk_blk k)) (num := sk_num k) (D := adr q) (na := na) (i := zlength done) (V := adr (sc_blk x));
          rewrite ?ESPA; [exact HEAPC| exact STC| exact MIC| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
          | exact KIN| exact KAL| exact QIN| exact QAL| exact NA| exact RNUM| exact RDAT| exact IR| clear - NR; lia| exact RITEM| reflexivity| reflexivity]. }
      cbv beta. intros ms2 PO.
      destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mD & -> & MUD & WMD & MID & STD & _). rewrite ?ESPA in MUD, STD.
      rewrite (ret_pc_even 0x336d58) by (clear; lia).
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in FRL; [| cbn; clear; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in FRH; [| cbn; clear - SPAH; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in HX; [| rewrite SctRep.sct_cells_size; cbn; clear - XBC CEIL LOSP STKu SPAL; lia].
      pose proof (linv_munch _ _ _ _ _ _ _ _ LI MUD WMD MID STD ltac:(constructor; [cbn [fst snd]; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LID.
      pose proof LID as (PRED & _). cbn [app] in PRED. pose proof PRED as (HEAPD & _).
      apply evt_done. pose proof (munch_refl (@nil (Z * Z)) mD) as MU2. pose proof (wmono_refl ctasegs mD) as WM2.
      apply cps_from_evt'. unfold MallocRep.wz.
      (* [comment removed for export] *)
      zstep. zstep.
      apply evt_done. change (Z_to_bv 64 3367120) with (wz I2O_SCT_A).
      eapply (@i2o_sct_len_cpsA (push AR f 0) _) with (lo := lo) (STK := STKb) (OW := OW) (LB := LB) (adr := adr) (sc := x) (vs := 0); rewrite ?ESPA;
        [exact HEAPD| exact STD| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP SPAL; lia| unfold I2O_SCT_LEN_STACK_A, IOS_FRAME, RT_STACK; subst STKb; clear - STKu; lia
        | clear - TOP SPAH; plia| clear - SPA32; Z.div_mod_to_equations; lia| exact MID| reflexivity| cbn [ar_FR push amb length]; clear - FRM0 FRMu; lia
        | cbn [ar_RT push amb]; clear - CR CRED0 CR1 CSTu D0 T0 LEN; subst CSTb; unfold sk_num in *; lia| exact XIN| exact XAL| exact HX| exact OKX| exact CPLx| reflexivity| reflexivity|].
      intros ΣE mE y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 FE fcE HEAPE CRE ELE STE MIE AGE.
      rewrite (ret_pc_even 0x336d60) by (clear; lia). cbn [ar_RT ar_PMc push amb] in CRE, ELE |- *. rewrite ?ESPA in STE, AGE.
      assert (LIE : linv ΣE st mE OW bo [] (CSTb - zlength done - 1)).
      { eapply (oinv_heap _ _ _ _ _ _ _ _ _ _ _ _ KH) with (L1 := OW ++ LB) (NEW' := []) (cst := 1);
          [exact LID| eapply agree_on_mono; [exact AGE| intros a [Ha _]; exact Ha]| intros b Hb; apply in_app_iff; exact Hb| cbn [app]; exact HEAPE| constructor
          | exact MIE| exact STE| cbn [ar_RT push amb]; clear - CRE; lia| subst CSTb; clear - CSTu D0 T0 LEN; unfold sk_num in *; lia]. }
      pose proof (keep_frame _ _ _ _ _ _ _ LIE) as (FRLE & FRHE & UWE & AGSE). clear FRL FRH.
      pose proof OKX as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
      assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q' n']|] eqn:ES; [pose proof (SIGP q' n' eq_refl); clear - H; lia| clear; lia]).
      assert (LXR : 0 <= i2o_sct_len x <= 196702) by (unfold i2o_sct_len; destruct (sc_version x =? 0); clear - ELR BLR SL; lia).
      clear VR HR GR SIGP BLOBP LOGP ELR BLR EXTP EXTL BLBL SL.
      pose proof (i2o_sum_ge0 adr (sk_items k) OKALL) as SUMB.
      assert (ACCB : 0 <= acc /\ acc + 2 + i2o_sct_len x <= 2 + i2o_sum (sk_items k) /\ 2 + i2o_sum (sk_items k) < 2 ^ 62).
      { pose proof OKALL as OK3. rewrite EQ in OK3. apply Forall_app in OK3 as [OKd OKr]. apply Forall_cons_iff in OKr as [_ OKt].
        pose proof (i2o_sum_ge0 adr done OKd) as Bd. pose proof (i2o_sum_ge0 adr t OKt) as Bt.
        assert (ES : i2o_sum (sk_items k) = i2o_sum done + (2 + i2o_sct_len x + i2o_sum t)) by (rewrite EQ, i2o_sum_app; reflexivity).
        pose proof SUMB as SB. rewrite ES in SB |- *. subst acc. unfold sk_num in LEN, NR. clear - Bd Bt LXR NR LEN SB. lia. }
      clear MU2 WM2 MU WM MUD WMD STD MID HEAPD PRED LID STC MIC HEAPC.
      pose proof (munch_refl (@nil (Z * Z)) mE) as MU. pose proof (wmono_refl ctasegs mE) as WM.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 LXR; lia| clear K0].
      zstep. zstep. zstep. zstep. zstep. rewrite (swrap32_small (zlength done + 1)) by (unfold sk_num in LEN, NR; clear - D0 T0 LEN NR; lia).
      pose proof LIE as (PREE & _). cbn [app] in PREE. pose proof PREE as (HEAPE' & _ & _ & _ & _ & _ & _ & _ & _ & MIE' & _).
      pose proof (keep_sk _ _ _ _ _ _ _ LIE) as SKE. destruct (sk_repA_free_view _ _ _ _ SKE) as ((RNUME & _ & _) & _). unfold MallocRep.wz in RNUME.
      eapply evt_cut.
      { eapply (@OPENSSL_sk_num_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (SA := adr (sk_blk k)) (num := sk_num k);
          rewrite ?ESPA; [exact HEAPE'| exact STE| exact MIE'| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
          | exact KIN| exact KAL| exact RNUME| unfold sk_num in *; clear - NR D0 T0 LEN; lia| reflexivity]. }
      cbv beta. intros ms3 PO.
      destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & mF & -> & MUF & WMF & MIF & STF & _). rewrite ?ESPA in MUF, STF.
      rewrite (ret_pc_even 0x336d7c) by (clear; lia).
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in FRLE; [| cbn; clear; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in FRHE; [| cbn; clear - SPAH; lia].
      pose proof (linv_munch _ _ _ _ _ _ _ _ LIE MUF WMF MIF STF ltac:(constructor; [cbn [fst snd]; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LIF.
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctasegs mF) as WM.
      (* [comment removed for export] *)
      destruct t as [|x2 t2].
      + (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?signed_small, ?unsigned_lit by (unfold sk_num in *; clear - NR D0 T0 LEN; lia); unfold sk_num, zlength in *; cbn [length] in *; clear - LEN; lia| clear K1].
        assert (ETOT : acc + 2 + i2o_sct_len x = 2 + i2o_sum (sk_items k)) by (subst acc; rewrite EQ, i2o_sum_app; cbn [i2o_sum]; clear; lia).
        cbn [abind i2o_len_pass aret apbind fst snd] in SAFE. rewrite ETOT in SAFE.
        replace (acc + i2o_sct_len x + 2) with (2 + i2o_sum (sk_items k)) by (clear - ETOT; lia).
        assert (LIX : linv ΣE st mF OW bo [] (CSTb - zlength (sk_items k))).
        { replace (zlength (sk_items k)) with (zlength done + 1) by (rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; clear; lia). rewrite Z.sub_add_distr. exact LIF. }
        assert (CPLA : Forall (fun y => sct_complete y = true) (sk_items k)) by (rewrite EQ; apply Forall_app; split; [exact CPLD| constructor; [exact CPLx| constructor]]).
        zstep. zstep. rewrite (Z.shiftr_div_pow2 _ 16) by (clear; lia).
        destruct (Z.lt_ge_cases (2 + i2o_sum (sk_items k)) 65536) as [SMALL|BIG].
        * rewrite Z.div_small by (clear - SMALL SUMB; lia). zstep. btaken.
          (* [comment removed for export] *)
          zstep. zstep. btaken.
          apply evt_done. eapply (implAp_elim _ ΣC ΣE _ _ XX Φ DD); [| exact SAFE| exact LINK| exact ELE].
          eapply len_ret; [exact LIX| exact CPLA| reflexivity| replace (65535 <? 2 + i2o_sum (sk_items k)) with false by (symmetry; apply Z.ltb_ge; clear - SMALL; lia); reflexivity].
        * zstep. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by (clear - BIG ACCB; Z.div_mod_to_equations; lia); clear - BIG ACCB; Z.div_mod_to_equations; lia| clear K2].
          (* [comment removed for export] *)
          zstep. zstep. zstep. bnot. zstep. zstep.
          apply evt_done. eapply (implAp_elim _ ΣC ΣE _ _ XX Φ DD); [| exact SAFE| exact LINK| exact ELE].
          eapply len_ret; [exact LIX| exact CPLA| reflexivity| replace (65535 <? 2 + i2o_sum (sk_items k)) with true by (symmetry; apply Z.ltb_lt; clear - BIG; lia); reflexivity].
      + (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1; [clear K1| exfalso; revert K1; rewrite ?signed_small, ?unsigned_lit by (unfold sk_num in *; clear - NR D0 T0 LEN; lia); unfold sk_num, zlength in *; cbn [length] in *; clear - LEN; lia].
        apply evt_done. eapply (implAp_elim _ ΣC ΣE _ _ XX Φ DD); [| exact SAFE| exact LINK| exact ELE].
        replace (zlength done + 1) with (zlength (done ++ [x])) by (rewrite zlength_app_l; unfold zlength; cbn [length]; clear; lia).
        replace (acc + i2o_sct_len x + 2) with (acc + 2 + i2o_sct_len x) by (clear; lia).
        eapply (IH (done ++ [x])).
        * rewrite EQ, <- app_assoc. reflexivity.
        * discriminate.
        * apply Forall_app. split; [exact CPLD| constructor; [exact CPLx| constructor]].
        * subst acc. rewrite i2o_sum_app. cbn [i2o_sum]. clear; lia.
        * rewrite zlength_app_l. unfold zlength at 2. cbn [length]. rewrite Z.sub_add_distr. exact LIF.
    - (* [comment removed for export] *)
      replace (abind (i2o_len_pass (x :: t) acc) G st) with (abind (err_raise RS_i2o_notset) (fun _ => abind (abind (err_raise RS_i2o_list) (fun _ => aret None)) G) st)
        by (cbn [i2o_len_pass]; rewrite CPLx, abind_assoc; reflexivity).
      intros XX Φ DD SAFE LINK. unfold bst, IOL_LOOP.
      pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. btaken. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply (@OPENSSL_sk_value_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (q := q) (SA := adr (sk_blk k)) (num := sk_num k) (D := adr q) (na := na) (i := zlength done) (V := adr (sc_blk x));
          rewrite ?ESPA; [exact HEAPC| exact STC| exact MIC| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
          | exact KIN| exact KAL| exact QIN| exact QAL| exact NA| exact RNUM| exact RDAT| exact IR| clear - NR; lia| exact RITEM| reflexivity| reflexivity]. }
      cbv beta. intros ms2 PO.
      destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mD & -> & MUD & WMD & MID & STD & _). rewrite ?ESPA in MUD, STD.
      rewrite (ret_pc_even 0x336d58) by (clear; lia).
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in HX; [| rewrite SctRep.sct_cells_size; cbn; clear - XBC CEIL LOSP STKu SPAL; lia].
      pose proof (linv_munch _ _ _ _ _ _ _ _ LI MUD WMD MID STD ltac:(constructor; [cbn [fst snd]; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LID.
      pose proof (keep_frame _ _ _ _ _ _ _ LID) as (FRLD & FRHD & UWD & AGSD). clear FRL FRH.
      pose proof LID as (PRED & AXD & KOD & KID & _). cbn [app] in PRED.
      apply evt_done. pose proof (munch_refl (@nil (Z * Z)) mD) as MU2. pose proof (wmono_refl ctasegs mD) as WM2.
      apply cps_from_evt'. unfold MallocRep.wz.
      (* [comment removed for export] *)
      zstep. zstep.
      apply evt_done. eapply (implAp_elim _ ΣC ΣC _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
      eapply implAp_abind.
      { change (Z_to_bv 64 3367120) with (wz I2O_SCT_A).
        eapply (@i2o_sct_failA (push AR f 0) UK BE STRCPY) with (lo := lo) (K := K) (ras := bv_unsigned ra :: ras) (STK := STKb) (CST := CSTb - zlength done) (FRMb := FRMb') (adr := adr) (sc := x) (vs := 0);
          rewrite ?ESPA.
        - exact PRED.
        - reflexivity.
        - subst STKb. ecu. clear - STKu. lia.
        - subst CSTb. ecu. clear - CSTu D0 T0 LEN. unfold sk_num in *. lia.
        - subst FRMb'. ecu. clear - FRMu. lia.
        - exact UWD.
        - rewrite unsigned_lit by (clear; lia). rewrite ERAS. refine (uk_ctxJ_call j X0 _ _ E_ios _ CTXJ). unfold IOL_NESTED_RET. clear. lia.
        - apply cons_ne.
        - exact KOD.
        - exact KID.
        - exact (proj1 REPX).
        - exact XAL.
        - exact HX.
        - exact OKX.
        - exact CPLx.
        - reflexivity. }
      intros r1 Σa ms1 PO1. cbv beta in PO1.
      destruct PO1 as (o0 & o1 & o2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & o3 & o4 & o5 & o6 & Fa & fca & mA & OWa & boa & -> & PREa & AXa & CRa & BKa & -> & ->).
      rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x336d60) by (clear; lia).
      (* [comment removed for export] *)
      assert (LIA : linv Σa (snd r1) mA OWa bo [] (CSTb - zlength done - I2O_SCT_FAIL_COST_A)).
      { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := []) (NEW2 := []) (cst := I2O_SCT_FAIL_COST_A);
          [exact LID| cbn [app]; exact PREa| cbn [app]; exact AXa| intros a []| cbn [ar_RT push amb]; exact CRa| subst CSTb; ecu; clear - CSTu D0 T0 LEN; unfold sk_num in *; lia| exact BKa| constructor]. }
      pose proof (keep_frame _ _ _ _ _ _ _ LIA) as (FRLA & FRHA & UWA & AGSA). unfold frameL, frameH in FRLA, FRHA.
      pose proof LIA as (PREA' & _). cbn [app] in PREA'. pose proof PREA' as (HEAPA & _ & _ & _ & STA & _ & _ & _ & _ & MIA & _). rewrite ESPA in STA.
      intros X2 Φ2 D2 SAFE2 LINK2.
      pose proof (munch_refl (@nil (Z * Z)) mA) as MU3. pose proof (wmono_refl ctasegs mA) as WM3.
      apply cps_from_evt'. unfold MallocRep.wz.
      (* [comment removed for export] *)
      zstep. btaken. zstep. zstep. zstep. bnot. zstep. zstep.
      apply evt_done. change (Z_to_bv 64 3370740) with (wz IOL_EXIT).
      eapply (@iol_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
        [exact HEAPA| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STA| exact CEIL| clear - LOSP STKu SPAL; lia
        | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIA| exact (rw_cells_cb_first mA spa _ 4 FRLA)| exact FRHA| reflexivity|].
      intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
      eapply (implAp_elim _ Σa Σ' _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| exact LIVE'].
      apply KN. rewrite (v_addiw0_int (-1)) by (clear; lia).
      destruct (close_post _ _ _ _ _ _ _ LIA ltac:(clear - D0 T0 LEN; unfold sk_num in *; lia) HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK').
      unfold lenpost_fail. do 16 eexists. exists m', OWa. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
      eapply sk_repA_agree; [exact AG'| | exact (keep_sk _ _ _ _ _ _ _ LIA)]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma len_start : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) F1 fc1,
    implAp (abind (i2o_len_pass (sk_items k) 2) G st) Σ1 Q
      (bst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 (Z_to_bv 64 f) x27 x28 x29 x30 x31 F1 fc1 m4 0x336ccc).
  Proof.
    intros.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0).
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu.
    pose proof linv0 as LI. pose proof (keep_sk _ _ _ _ _ _ _ LI) as SK4.
    pose proof LI as (PREX & _). cbn [app] in PREX. pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & _). rewrite ESPA in STX.
    pose proof (sk_repA_free_view _ _ _ _ SK4) as ((RNUM & _ & _) & KINL & _). unfold MallocRep.wz in RNUM.
    pose proof SK4 as ((_ & KAL) & _ & HDD & _).
    assert (KIN : In (sk_blk k, adr (sk_blk k), STACK_SIZE) (OW ++ LB)) by (apply in_or_app; right; exact KINL).
    pose proof (zlength_ge0 (sk_items k)) as N0.
    assert (NR : sk_num k < 2 ^ 23) by (unfold sk_num; destruct (sk_data k) as [[q na]|]; [destruct HDD as (_ & _ & HNA & HNA2 & _); unfold sk_num in HNA; clear - HNA HNA2; lia| rewrite HDD; unfold zlength; cbn; lia]).
    intros XX Φ DD SAFE LINK. unfold bst.
    pose proof FRL4 as FRL. pose proof FRH4 as FRH.
    pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_cut.
    { eapply (@OPENSSL_sk_num_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (SA := adr (sk_blk k)) (num := sk_num k);
        rewrite ?ESPA; [exact HEAPX| exact STX| exact MIX| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
        | exact KIN| exact KAL| exact RNUM| unfold sk_num in *; clear - NR N0; lia| reflexivity]. }
    cbv beta. intros ms3 PO.
    destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & mF & -> & MUF & WMF & MIF & STF & _). rewrite ?ESPA in MUF. rewrite ?ESPA in STF.
    rewrite (ret_pc_even 0x336cd8) by (clear; lia).
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in FRL; [| cbn; clear; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in FRH; [| cbn; clear - SPAH; lia].
    pose proof (linv_munch _ _ _ _ _ _ _ _ LI MUF WMF MIF STF ltac:(constructor; [cbn [fst snd]; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LIF.
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctasegs mF) as WM.
    (* [comment removed for export] *)
    assert (EI' : exists l, sk_items k = l) by (eexists; reflexivity). destruct EI' as [[|x t] EI].
    - (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [clear K0| exfalso; match goal with K1 : 0 < Z.land (sk_num k) _ |- _ => unfold sk_num, zlength in K1; rewrite EI in K1; cbn [length] in K1; change (Z.land (Z.of_nat 0) 18446744073709551615) with 0 in K1; clear - K1; lia end].
      zstep. zstep. zstep. zstep. btaken.
      assert (E2 : 2 = 2 + i2o_sum (sk_items k)) by (rewrite EI; cbn [i2o_sum]; clear; lia).
      replace (abind (i2o_len_pass (sk_items k) 2) G st) with (G (Some 2) st) in SAFE by (rewrite EI; reflexivity).
      rewrite E2 in SAFE.
      apply evt_done. eapply (implAp_elim _ Σ1 Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
      change (Z_to_bv 64 3370740) with (Z_to_bv 64 IOL_EXIT).
      eapply len_ret; [rewrite EI; unfold zlength; cbn [length Z.of_nat]; rewrite Z.sub_0_r; exact LIF| rewrite EI; constructor| reflexivity| rewrite <- E2; reflexivity].
    - (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0;
        [exfalso; unfold sk_num in K0, NR; rewrite EI in K0, NR; rewrite land64_small in K0 by (clear - NR; unfold zlength in *; cbn [length] in *; lia);
         apply Bool.andb_false_iff in K0; destruct K0 as [K0|K0]; apply Z.ltb_ge in K0; clear - K0 NR; unfold zlength in *; cbn [length] in *; lia
        | try clear K1 K2].
      zstep. zstep. zstep.
      apply evt_done. eapply (implAp_elim _ Σ1 Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
      change (Z_to_bv 64 3370216) with (Z_to_bv 64 IOL_LOOP).
      eapply (len_loop (sk_items k) []); [reflexivity| rewrite EI; discriminate| constructor| reflexivity| unfold zlength; cbn [length Z.of_nat]; rewrite Z.sub_0_r; exact LIF].
  Qed.
End ActLen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem i2o_list_len_walkA : forall (B0 : Type) (G : option Z -> @AM bptr B0) (Q : B0 * ap_st bptr -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
    (lo : Z) (K : list block) (ras : list Z) (j : nat) (X0 : list Z) (STK CST FRMb : Z) (adr : bptr -> Z) (k : skr bptr),
  ap_preA Σ st m OW LB E bo sp lo STK CST FRMb -> tp = wz TP_A ->
  IOL_LEN_STACK_A <= STK -> IOL_LEN_COST_A (zlength (sk_items k)) <= CST -> IOL_LEN_FRAMES_A <= FRMb ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> bv_unsigned ra :: ras = repeat IOL_NESTED_RET j ++ X0 -> uk_ctxJ j X0 -> ras <> nil ->
  (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
  sk_repA m LB adr k ->
  a0 = wz (adr (sk_blk k)) -> a1 = wz 0 ->
  (forall Σ' ms',
     lenpost_ok ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st OW LB E bo lo m K (IOL_LEN_COST_A (zlength (sk_items k))) adr k (2 + i2o_sum (sk_items k)) Σ' ms' ->
     implAp (G (Some (2 + i2o_sum (sk_items k))) st) Σ' Q ms') ->
  (forall st1 Σ' ms',
     lenpost_fail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (IOL_LEN_COST_A (zlength (sk_items k))) adr k st1 Σ' ms' ->
     implAp (abind (abind (err_raise RS_i2o_list) (fun _ => aret None)) G st1) Σ' Q ms') ->
  implAp (abind (i2o_len_pass (sk_items k) 2) G st) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz I2O_SCT_LIST_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until k. intros PRE TP STKB CSTB FRMB UW ERAS CTXJ NE KOW KIDS SK -> -> KS KN.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
  pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). pose proof (zlength_ge0 (sk_items k)) as N0.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  intros XX Φ DD SAFE LINK.
  change (wz I2O_SCT_LIST_A) with (wz IOL_ENTRY).
  eapply (iol_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold IOL_FRAME, RT_STACK; clear - LOSP STKu; lia| exact TOP| exact AL16| exact MI| exact TP
    | clear - FRM0 FRMu; lia| clear - CRED CSTu N0; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AG3 FRL FRH HF FRS SPA32 SPAL SPAH GSZ SAVJ.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  pose proof (munch_refl [(spa + 16, spa + 32)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  apply cps_from_evt'. unfold IOL_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  zstep. btaken. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
  assert (ST4 : stk ctasegs m4 lo spa) by (first [assumption| eapply stk_transport; [exact ST3| exact MU4| exact WM4| cbn; clear; lia]]).
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m4).
  { eapply (@AH_frame (push AR f 0)); [exact HEAP3| exact MU4| exact WM4|]. constructor; [left; cbn [fst snd]; clear - CEIL LOSP STKu SPAL SPAH TOP LO0; plia| constructor]. }
  assert (AG4 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m4).
  { eapply agree_on_trans; [exact AG3|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)|]. intros a Ha. cbn [outside fst snd].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; split; [lia| exact I]| |].
    - destruct Ha as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; clear - Hlh CE1 CEIL LOSP STKu SPAL; (split; [lia| exact I]).
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, B3. clear - Hr B3 CEIL LOSP STKu SPAL. nrm. split; [lia| exact I]. }
  apply evt_done. eapply (implAp_elim _ Σ Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| exact EL1].
  eapply len_start; [exact PRE| exact STKB| exact CSTB| exact FRMB| exact UW| exact ERAS| exact CTXJ| exact KOW| exact KIDS| exact SK| exact HEAP4| exact FRESH| exact GEO| exact CR1
    | exact ST4| exact MI4| exact AG4| exact FRL| exact FRH| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact KS| exact KN].
Qed.
End WithRT.
