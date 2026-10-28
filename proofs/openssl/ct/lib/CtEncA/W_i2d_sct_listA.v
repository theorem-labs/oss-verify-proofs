(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain I_lkit.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_asn1_stringA W_obj_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA EncKitA EncActA Fr_asn1_ex_i2c Fr_asn1_i2d_ex_primitive Fr_ASN1_item_ex_i2d Fr_asn1_item_flags_i2d Fr_i2o_SCT Fr_i2o_SCT_LIST Fr_i2d_SCT_LIST W_asn1_enc_leavesA W_sct_completeA W_i2o_sigA W_i2o_sctA W_i2o_sct_failA W_i2o_sct_writeA W_asn1_ex_i2cA W_asn1_i2d_primA W_asn1_item_exA W_asn1_flagsA W_i2o_list_lenA W_i2o_list_outA.
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
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.
(* [comment removed for export] *)
Ltac step_until tgt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [constr_eq pc tgt | (apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep); step_until tgt]
  end.



(* [comment removed for export] *)
Definition IDL_STACK_A : Z := 112 + IOL_OUT_STACK_A.
(* [comment removed for export] *)
Definition IDL_COST_A (n : Z) : Z := 1 + IOL_OUT_COST_A n + 8 + (2 * (65535 + 8) + 16384) + 16.
Definition IDL_FRAMES_A : Z := 1 + IOL_OUT_FRAMES_A + 4.
(* [comment removed for export] *)
Definition IDL_RET1 : Z := 0x3373cc.       (* [comment removed for export] *)
Definition IDL_THUNK_NEW : Z := 0x246e5c.  (* [comment removed for export] *)
Definition IDL_CALL_I2D : Z := 0x3373f4.   (* [comment removed for export] *)
Definition IDL_AFTER_I2D : Z := 0x337400.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma idl_open_data {AR : ARun} : forall Σ1 OW LB m f q,
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m -> (forall b, In b LB -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m (shad f) idl_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) m.
Proof.
  intros Σ1 OW LB m f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 0) Σ1 OW LB m f 0%nat q (f + 32) 8 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 0) with 64; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m (shad f) idl_shadow_pro 4%nat (f + 32) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b Hb) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 0) with 64 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec I2O_SCT_LIST_A IOL_NESTED_RET IOL_REC_DEPTH}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_iol := (E_i2d_SCT_LIST_34b82c : uk_call 3371716 3371980 3369852).
Local Notation E_onew := (E_i2d_SCT_LIST_34b840 : uk_call 3371716 3371996 2387548).
Local Notation E_onew_tail := (E_ASN1_OCTET_STRING_new_249fb0 : uk_tail 2387548 2247428).
Local Notation E_i2d := (E_i2d_SCT_LIST_34b868 : uk_call 3371716 3372032 2387508).
Local Notation E_ofree := (E_i2d_SCT_LIST_34b878 : uk_call 3371716 3372044 2387584).

(* [comment removed for export] *)
Hypothesis STRCPY : strcpy_icontract RT.

Local Ltac ecu := unfold IDL_STACK_A, IDL_COST_A, IDL_FRAMES_A, IOL_OUT_STACK_A, IOL_OUT_COST_A, IOL_OUT_FRAMES_A, IOL_MALLOC_COST_A, IOL_LEN_STACK_A, IOL_LEN_COST_A, IOL_LEN_FRAMES_A,
                         I2O_SCT_FAIL_STACK_A, I2O_SCT_FAIL_COST_A, I2O_SCT_FAIL_FRAMES_A, I2O_SCT_LEN_STACK_A, I2O_SCT_W_STACK_A, I2O_SIG_STACK_A, IOS_FRAME,
                         I2D_OCTET_STACK_A, I2D_OCTET_COST_A, ASN1_ITEM_EX_I2D_STACK_A, ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AFI_FRAME, AIE_FRAME, AIP_FRAME, AEI_FRAME,
                         ASN1_STRING_FREE_STACK, ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, ASN1_STRING_SET0_STACK_A,
                         ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK,
                         ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, CRYPTO_FREE_STACK,
                         CRYPTO_MALLOC_STACK, RT_STACK in *.

Section ActIdl.
  (* [comment removed for export] *)
  Variables (B0 : Type) (kont : option bptr -> @AM bptr B0) (Q : B0 * ap_st bptr -> rts RT -> machine_state -> Prop).
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z).
  Variables (lo : Z) (K : list block) (ras : list Z) (adr : bptr -> Z) (k : skr bptr) (DER : Z) (bO : block).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo IDL_STACK_A (IDL_COST_A (zlength (sk_items k))) IDL_FRAMES_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx I2D_SCT_LIST_A (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis SK : sk_repA m LB adr k.
  Hypothesis OIN : In bO LB.
  Hypothesis OLO : blk_addr bO <= DER.
  Hypothesis OHI : DER + 8 <= blk_addr bO + blk_size bO.
  Hypothesis O8 : DER mod 8 = 0.
  Hypothesis OAP : forall b, In b (sk_blocks adr k) -> DER + 8 <= blk_addr b \/ blk_addr b + blk_size b <= DER.
  Hypothesis HO : rw_cells ctasegs m DER [C8 (wz 0)].
  Hypothesis KN : forall st' Σ' ms',
    i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (IDL_COST_A (zlength (sk_items k))) adr k DER (None, st') Σ' ms' -> implAp (kont None st') Σ' Q ms'.
  Hypothesis KS : forall d st' Σ' ms',
    i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (IDL_COST_A (zlength (sk_items k))) adr k DER (Some d, st') Σ' ms' -> implAp (kont (Some d) st') Σ' Q ms'.
  (* [comment removed for export] *)
  Variables (Σ1 : rts RT) (m3 : mem) (f spa : Z) (g : nat) (junk gj j0 : list byte) (qd : bptr).
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3.
  Hypothesis HEAPp : @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((qd, f + 32, 8) :: LB) m3.
  Hypothesis QDF : ~ In qd (map blk_id (OW ++ LB)).
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 0 b.
  Hypothesis GEO : fr_geo f 0.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis EL1 : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AG3 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis FRL3 : rw_cells ctasegs m3 spa [CB 8 j0; C8 (Z_to_bv 64 f); CB g junk].
  Hypothesis FRH3 : rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis HDATA3 : rw_cells ctasegs m3 (f + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 112 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 96.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 32.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

  Let STKb : Z := IDL_STACK_A - 112.
  Let CSTb : Z := IDL_COST_A (zlength (sk_items k)) - 1.
  Let FRMb' : Z := IDL_FRAMES_A - 1.
  Let LB' : list block := (qd, f + 32, 8) :: LB.
  Let XP : list (Z * Z) := [(f + 32, f + 40); (DER, DER + 8)]%Z.
  (* [comment removed for export] *)
  Let CN : @AM bptr B0 := kont None.
  Let CS : Z -> bptr -> @AM bptr B0 := fun len2 data =>
    abind (amalloc SZ_ASN1_STRING) (fun oct => abind (amalloc (der_hl len2 + len2)) (fun der => abind (afree data) (fun _ => abind (afree oct) (fun _ => kont (Some der))))).
  (* [comment removed for export] *)
  Let linv : rts RT -> ap_st bptr -> mem -> list block -> Z * Z -> list block -> Z -> Prop :=
    @oinv (push AR f 0) (Z_to_bv 64 spa) spa m3 Σ1 LB' E lo K XP STKb CSTb FRMb'.
  Let frameH (mX : mem) : Prop := rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition dst (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mX : mem) (pc : Z) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) (Z_to_bv 64 DER) x20 x21 x22 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mX (seg_rom ctasegs).

  Lemma base_facts :
    0 <= bv_unsigned sp < 2 ^ 64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo /\ 0 <= lo
    /\ lo <= bv_unsigned sp - IDL_STACK_A /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
    /\ 0 < f /\ f mod 64 = 0 /\ f + 64 <= ACEIL /\ SEGTOP_A <= f /\ (f + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f /\ IDL_COST_A (zlength (sk_items k)) <= rt_credit RT Σ /\ Z.of_nat (length FRM) + IDL_FRAMES_A <= Z.of_nat FRAMES_MAX
    /\ 0 < blk_addr bO /\ blk_addr bO + blk_size bO <= ACEIL /\ 0 < DER < 2 ^ 64 /\ (blk_addr bO + blk_size bO <= 65536 \/ 12365824 <= blk_addr bO).
  Proof.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
    pose proof LOSP as LOSPu. ecu.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LOSPu SPAL SPAH SPR LO0; plia).
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; plia).
    pose proof (AH_range_gen _ _ _ _ bO HEAP (in_or_app _ _ _ (or_intror OIN))) as (B1 & _ & _ & B4 & B5).
    split; [exact SPR|]. split; [exact CE1|]. split; [exact CE2|]. split; [exact CE3|]. split; [exact CEIL|]. split; [exact LO0|]. split; [exact LOSP|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact ESPA|]. split; [exact Ef|]. split; [clear - CRED; lia|]. split; [clear - FRM0; lia|]. split; [exact B1|]. split; [exact B4|].
    split; [clear - B1 B4 OLO OHI CE3; plia| exact B5].
  Qed.

  Lemma OKALL : Forall (sct_ok adr) (sk_items k).
  Proof.
    pose proof PRE as (HEAP & _). pose proof SK as (_ & _ & _ & HF & _).
    apply Forall_forall. intros x Hx. eapply (sct_ok_of_repA _ _ _ _ _ _ HEAP). exact (proj1 (Forall_forall _ _) HF x Hx).
  Qed.

  Lemma KH : @kit_hyps (push AR f 0) (Z_to_bv 64 spa) spa LB' lo XP STKb.
  Proof.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & _).
    pose proof LOSP as LOSPu. ecu.
    unfold kit_hyps. rewrite ESPA. split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL|]. split; [exact LO0|]. split; [subst STKb; clear - LOSPu SPAL; ecu; lia|].
    split; [subst STKb; clear; ecu; lia|]. split; [clear; lia|]. split; [clear - TOP SPAH; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    subst XP LB'. constructor; [| constructor; [| constructor]]; cbn [fst snd].
    - exists (qd, f + 32, 8). split; [left; reflexivity| cbn; clear; lia].
    - exists bO. split; [right; exact OIN| clear - OLO OHI; lia].
  Qed.

  Lemma linv0 : linv Σ1 st m3 OW bo [] CSTb.
  Proof.
    pose proof base_facts as (_ & _ & _ & _ & _ & _ & LOSP & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRED0 & FRM0 & _).
    pose proof (zlength_ge0 (sk_items k)) as Z0. pose proof (mcost_le 0 ltac:(clear; lia)) as MC.
    apply (oinv_entry _ _ _ _ _ _ _ _ _ _ _ _ KH).
    - subst STKb CSTb FRMb'. replace (IDL_STACK_A - 112) with (IDL_STACK_A - 96 - 16) by (clear; lia).
      pose proof (pro_closeA Σ st m OW LB E bo sp lo IDL_STACK_A (IDL_COST_A (zlength (sk_items k))) IDL_FRAMES_A f 0%nat Σ1 m3 spa 96 PRE HEAP3 ST3 MI3 AG3 CR1 SPA32
                    ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(clear; ecu; lia) ltac:(clear - Z0 MC; ecu; lia) ltac:(clear; ecu; lia)) as P3.
      destruct P3 as (_ & REST). split; [subst LB'; exact HEAPp| exact REST].
    - exact KOW.
    - exact KIDS.
  Qed.

  (* [comment removed for export] *)
  Lemma keep_idl : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX ->
    frameH mX /\ uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras) /\ agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX
    /\ rw_cells ctasegs mX spa [CB 8 j0; C8 (Z_to_bv 64 f); CB g junk].
  Proof.
    intros until CX. intros (_ & AX & _).
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu. nrm. rewrite ESPA in AX.
    assert (FHI : f + 64 <= spa) by (clear - G3 CEIL LOSPu SPAL; lia).
    assert (DHI' : DER + 8 <= spa) by (clear - BD2 OHI CEIL LOSPu SPAL; lia).
    assert (AXS : forall a, spa <= a < USTACK_TOP -> mX (wa a) = m3 (wa a)).
    { intros a Ha. unfold USTACK_TOP in Ha. apply AX; [clear - Ha SPR CEIL LOSPu SPAL LO0; lia|]. split; [| left; unfold USTACK_TOP; exact Ha].
      subst XP. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha FHI DHI' CEIL CE1 LOSPu SPAL. lia. }
    assert (AGS : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX).
    { intros a Ha Hr. unfold USTACK_TOP in Hr. rewrite (AXS a ltac:(unfold USTACK_TOP; clear - Hr SPAH; lia)). apply AG3; [exact Ha| left; unfold USTACK_TOP; exact Hr]. }
    assert (FRH : frameH mX).
    { unfold frameH. eapply rw_cells_agree; [| exact FRH3|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. apply AXS. unfold USTACK_TOP. clear - Ha TOP SPAH. lia. }
    split; [exact FRH|]. split; [| split; [exact AGS|]].
    - eapply (uw_call m mX spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [exact UW| exact AGS| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| unfold USTACK_TOP; clear - TOP; lia| apply bv_unsigned_in_range|].
      rewrite !Z_to_bv_bv_unsigned. cbn [app]. exact FRH.
    - eapply rw_cells_agree; [| exact FRL3|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbv beta. cbn [cells_size csize Nat.add] in Ha. apply AXS. unfold USTACK_TOP. clear - Ha TOP SPAH GSZ. lia.
  Qed.

  Lemma keep_sk : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX -> sk_repA mX LB adr k.
  Proof.
    intros until CX. intros (PREX & AX & _). pose proof base_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _ & _ & ESPA & _). rewrite ESPA in AX.
    pose proof PRE as (HEAP & _).
    assert (SK3 : sk_repA m3 LB adr k).
    { eapply sk_repA_agree; [exact AG3| | exact SK]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha]. }
    eapply sk_repA_agree; [exact AX| | exact SK3]. intros b a Hb Ha. pose proof (sk_repA_blocks_in _ _ _ _ _ SK Hb) as HbL.
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror HbL))) as (B1 & _ & _ & B4 & B5). pose proof (FRESH b (in_or_app _ _ _ (or_intror HbL))) as O.
    unfold off_fr in O. change (fs_size 0) with 64 in O. pose proof (OAP b Hb) as DA.
    split.
    - subst XP. unfold LIBW_A. cbn [app rin_ivs fst snd]. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Ha, B1, B5, O, DA. clear - Ha B1 B5 O DA. lia.
    - right; right. exists b. split; [subst LB'; right; exact HbL| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma close_idl : forall ΣX stX mX OWX NEW CX Σ' m',
    linv ΣX stX mX OWX bo NEW CX -> 0 <= CX ->
    AHEAP Σ' OWX (NEW ++ LB) m' -> rt_credit RT Σ' = rt_credit RT ΣX -> stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
    agree_on (aclient_addr (OWX ++ (NEW ++ LB)) spa) mX m' ->
    ap_preA Σ' stX m' OWX (NEW ++ LB) E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(DER, DER + 8)]%Z ++ LIBW_A) m m'
    /\ rt_credit RT Σ - IDL_COST_A (zlength (sk_items k)) <= rt_credit RT Σ'
    /\ blocks_kept K stX OWX m m'.
  Proof.
    intros until m'. intros LI HCX HEAP' CR' ST' MI' AG'.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & CRED & _).
    destruct LI as (PREX & AX & KO & KI & KP & CR & LBOK).
    pose proof PREX as (HEAPX & ASX & IDSX & DCX & STX & _ & _ & _ & _ & MIX & CREDX & _). rewrite ESPA in AX. cbn [ar_RT ar_FR push amb] in CREDX, CR.
    split; [| split; [| split]].
    - unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASX | exact AG']|]. split; [exact IDSX|].
      split; [eapply data_cells_rt; [exact ASX | exact DCX | exact AG']|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSPu; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [clear - CREDX CR'; lia|]. clear - FRM0. ecu. lia.
    - eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [exact AG3 | clear; lia]|].
      eapply ax_pres_trans.
      + unfold ax_pres. eapply agree_on_mono; [exact AX|]. intros a [HXa Ha]. split.
        * subst XP. intros HIN. apply HXa. cbn [app]. cbn [app rin_ivs fst snd] in HIN |- *.
          destruct HIN as [HIN|HIN]; [| exact HIN]. exfalso.
          destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha HIN G3 CEIL LOSPu; lia| |].
          -- destruct Ha as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; clear - Hlh HIN G4; unfold SEGTOP_A in G4; lia.
          -- pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
             destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O HIN. lia.
        * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [subst LB'; right; exact Hb| exact Hr]].
      + eapply (ax_pres_of_aclient (OWX ++ NEW) LB); [rewrite <- app_assoc; exact AG' | clear - SPAH; lia].
    - subst CSTb. clear - CR CR1 CR' HCX. lia.
    - eapply (blocks_kept_post K stX OWX (NEW ++ LB)); [| exact AG']. eapply (blocks_kept_pre K stX OW OWX LB); [exact KOW | exact AG3 |].
      split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP].
  Qed.

  Lemma close_pb : forall ΣX OWX NEW mX, @BnHeapA.AHEAP (push AR f 0) ΣX OWX (NEW ++ LB') mX -> @BnHeapA.AHEAP (push AR f 0) ΣX OWX (NEW ++ LB) mX.
  Proof.
    intros ΣX OWX NEW mX H. subst LB'.
    eapply (@frame_obj_close (push AR f 0)) with (f := f) (k := 0%nat) (b := (qd, f + 32, 8)); [left; reflexivity| | unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
    eapply AHEAP_permLB; [exact H|]. symmetry. apply Permutation_middle.
  Qed.

  (* [comment removed for export] *)
  Lemma idl_exit : forall ΣX stX mX OWX NEW CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) FX fcX (r : Z) (od : option bptr),
    linv ΣX stX mX OWX bo NEW CX -> 0 <= CX -> -2^31 <= r < 2^31 ->
    (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB))) ->
    match od with
    | None => NEW = [] /\ rw_cells ctasegs mX DER [C8 (wz 0)]
    | Some d => exists AD n, NEW = [(d, AD, n)] /\ 0 < n /\ rw_cells ctasegs mX DER [C8 (wz AD)] /\ off_fr f 0 (d, AD, n)
    end ->
    (forall st' Σ' ms', i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (IDL_COST_A (zlength (sk_items k))) adr k DER (od, st') Σ' ms' -> implAp (kont od st') Σ' Q ms') ->
    implAp (kont od stX) ΣX Q (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x21 x22 s9 s10 s11 x28 x29 x30 x31 FX fcX mX IDL_EXIT).
  Proof.
    intros until od. intros LI HCX RR NFR RES KK.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu.
    pose proof (keep_idl _ _ _ _ _ _ _ LI) as (FRH & UWX & AGS & FRL). unfold frameH in FRH.
    pose proof LI as (PREX & _ & _ & _ & _ & _ & LBOK). cbn [app] in PREX. pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & _). rewrite ESPA in STX.
    intros XX Φ DD SAFE LINK. unfold dst. change (Z_to_bv 64 IDL_EXIT) with (wz IDL_EXIT).
    eapply (@idl_epi_cps AR _) with (lo := lo) (LB := NEW ++ LB) (gj := gj) (hrest := []);
      [exact (close_pb _ _ _ _ HEAPX)| | exact STX| exact CEIL| clear - LOSPu SPAL; lia| exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIX| exact FRL| exact FRH| reflexivity|].
    { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [| exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))].
      destruct od as [d|]; [destruct RES as (AD & n & -> & _ & _ & OFD); destruct Hb as [<-|[]]; exact OFD| destruct RES as [-> _]; destruct Hb]. }
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply (implAp_elim _ ΣX Σ' _ _ XX Φ DD); [| exact SAFE| exact LINK| exact LIVE'].
    apply KK.
    destruct (close_idl _ _ _ _ NEW CX _ _ LI HCX HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK').
    assert (SK' : sk_repA m' LB adr k).
    { eapply sk_repA_agree; [exact AG'| | exact (keep_sk _ _ _ _ _ _ _ LI)]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha]. }
    assert (KDER : forall v, rw_cells ctasegs mX DER [C8 (wz v)] -> rw_cells ctasegs m' DER [C8 (wz v)]).
    { intros v H. eapply rw_cells_agree; [exact AG'| exact H|]. intros a Ha. cbn in Ha. right; right. exists bO. split; [apply in_or_app; right; apply in_or_app; right; exact OIN| clear - Ha OLO OHI; lia]. }
    unfold i2d_postA. do 17 eexists. exists m', OWX, bo, NEW. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
    split; [exact NFR|]. split; [eapply Forall_impl; [| exact LBOK]; intros b Hb; exact (lbokA_pop _ _ _ Hb)|]. split; [exact SK'|].
    cbn [fst]. destruct od as [d|].
    - destruct RES as (AD & n & E1 & N1 & HD & _). exists AD, n. split; [exact E1|]. split; [exact N1| exact (KDER _ HD)].
    - destruct RES as [E1 HD]. split; [exact E1| exact (KDER _ HD)].
  Qed.
  (* [comment removed for export] *)
  Lemma linv_munch : forall ΣX stX mX OWX boX NEW CX mY W,
    linv ΣX stX mX OWX boX NEW CX -> munch W mX mY -> wmono ctasegs mX mY -> mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    Forall (fun iv => (lo <= fst iv /\ snd iv <= spa) \/ (exists b, In b NEW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    linv ΣX stX mY OWX boX NEW CX.
  Proof.
    intros until W. intros LI MU WM MI ST HW. pose proof base_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESPA & _).
    eapply (oinv_munch _ _ _ _ _ _ _ _ _ _ _ _ KH); [exact LI| exact MU| exact WM| exact MI| exact ST|].
    eapply Forall_impl; [| exact HW]. intros [u v] [[H1 H2]|(b & Hb & H1 & H2)]; cbn [fst snd] in *.
    - left. cbn [fst snd]. rewrite ESPA. split; [exact H1| exact H2].
    - right; right. exists b. split; [exact Hb| cbn; split; [exact H1| exact H2]].
  Qed.

  (* [comment removed for export] *)
  Lemma der_keep : forall (L : list block) mX mY v (P : Z -> Prop),
    agree_on P mX mY -> (forall a, in_block L a -> P a) -> In bO L ->
    rw_cells ctasegs mX DER [C8 v] -> rw_cells ctasegs mY DER [C8 v].
  Proof.
    intros L mX mY v P AG HP HIN H. eapply rw_cells_agree; [exact AG| exact H|].
    intros a Ha. cbn in Ha. apply HP. exists bO. split; [exact HIN| clear - Ha OLO OHI; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma idl_none : forall ΣX stX mX OWX (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word) FX fcX CX,
    linv ΣX stX mX OWX bo [] CX -> 0 <= CX -> rw_cells ctasegs mX DER [C8 (wz 0)] ->
    implAp (CN stX) ΣX Q (dst x1 x5 x6 x7 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 s9 s10 s11 x28 x29 x30 x31 FX fcX mX IDL_RET1).
  Proof.
    intros until CX. intros LI HCX HOX.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & _).
    pose proof LI as (PREX & _). cbn [app] in PREX. pose proof PREX as (_ & _ & _ & _ & STX & _ & _ & _ & _ & MIX & _). rewrite ESPA in STX.
    intros XX Φ DD SAFE LINK. unfold dst, IDL_RET1.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    apply cps_from_evt'. zstep. zstep. btaken.
    apply evt_done. eapply (implAp_elim _ ΣX ΣX _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    change (Z_to_bv 64 3372076) with (Z_to_bv 64 IDL_EXIT).
    eapply (idl_exit _ _ _ _ [] CX) with (od := None); [exact LI| exact HCX| clear; lia| intros b []| split; [reflexivity| exact HOX]| exact KN].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma idl_free : forall ΣX stX mX (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) FX fcX CX
      (d poct pder : bptr) (AD tot A ADR nd : Z),
    linv ΣX stX mX OW bo [(pder, ADR, nd); (poct, A, ASN1_STRING_SIZE); (d, AD, tot)] CX -> 0 <= CX ->
    2 <= tot <= 65535 -> nd = der_hl tot + tot -> poct <> d ->
    ~ In pder (map blk_id (OW ++ LB)) -> off_fr f 0 (pder, ADR, nd) ->
    rw_cells ctasegs mX A (asn1_string_cells tot V_ASN1_OCTET_STRING AD 0) ->
    rw_cells ctasegs mX DER [C8 (wz ADR)] ->
    implAp (abind (afree d) (fun _ => abind (afree poct) (fun _ => kont (Some pder))) stX) ΣX Q
      (dst x1 x5 x6 x7 (Z_to_bv 64 nd) x11 x12 x13 x14 x15 x16 x17 x20 (Z_to_bv 64 A) (Z_to_bv 64 tot) s9 s10 s11 x28 x29 x30 x31 FX fcX mX IDL_AFTER_I2D).
  Proof.
    intros until nd. intros LI HCX TOT ND NPD DFR OFD HS HOX.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu.
    pose proof (keep_idl _ _ _ _ _ _ _ LI) as (FRH & UWX & AGS & FRL). unfold frameH in FRH.
    pose proof (oinv_call _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & LOX & SPT & SPA16 & MIX & CSX & ASX & CXR & _). rewrite ?ESPA in STX.
    pose proof LI as (_ & _ & _ & _ & _ & _ & LBOK). apply Forall_cons_iff in LBOK as [LBder LBOK2].
    pose proof (der_hl_range tot ltac:(clear - TOT; lia)) as HLR.
    (* [comment removed for export] *)
    assert (HEAPq : @BnHeapA.AHEAP (push AR f 0) ΣX OW ([(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] ++ ((pder, ADR, nd) :: LB')) mX).
    { eapply (@AH_lb_perm (push AR f 0)); [exact HEAPX|]. cbn [app]. apply (@Permutation_middle block [(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] LB' (pder, ADR, nd)). }
    pose proof (@AH_adopt_list (push AR f 0) ΣX [(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] OW ((pder, ADR, nd) :: LB') mX HEAPq LBOK2) as HEAPa. cbn [app] in HEAPa.
    pose proof (@AH_nodup_l (push AR f 0) _ _ _ _ HEAPa) as NDl.
    pose proof NDl as NDl'. cbn [map app blk_id fst snd] in NDl'. apply NoDup_cons_iff in NDl' as [NI1 ND2]. pose proof ND2 as ND2'. apply NoDup_cons_iff in ND2' as [NI2 ND3].
    assert (ND1 : List.NoDup (map blk_id ((poct, A, ASN1_STRING_SIZE) :: OW))) by (cbn [map blk_id fst snd]; constructor; [intros Hin; apply NI1; right; exact Hin| exact ND3]).
    assert (ER : lb_remove poct (lb_remove d ((poct, A, ASN1_STRING_SIZE) :: (d, AD, tot) :: OW)) = OW).
    { rewrite (lb_remove_cons d (poct, A, ASN1_STRING_SIZE)). cbn [blk_id fst snd]. rewrite (bptr_eqb_neq poct d NPD).
      rewrite (lb_remove_head (d, AD, tot) OW ND2). exact (lb_remove_head (poct, A, ASN1_STRING_SIZE) OW ND1). }
    intros XX Φ DD SAFE LINK. unfold dst, IDL_AFTER_I2D.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply evt_done. eapply (implAp_elim _ ΣX ΣX _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    change (abind (afree d) (fun _ => abind (afree poct) (fun _ => kont (Some pder))) stX) with (AFree d (AFree poct (kont (Some pder) stX))).
    change (Z_to_bv 64 2387584) with (wz ASN1_OCTET_STRING_FREE_A).
    eapply (@ASN1_pfree_walkA (push AR f 0) UK BE _) with (lo := lo) (OW := (poct, A, ASN1_STRING_SIZE) :: (d, AD, tot) :: OW) (LB := (pder, ADR, nd) :: LB')
        (pblk := poct) (pdata := d) (len := tot) (ty := V_ASN1_OCTET_STRING) (D := AD) (alloc := tot) (ras := bv_unsigned ra :: ras); rewrite ?ESPA.
    - reflexivity.
    - exact HEAPa.
    - exact STX.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    - subst STKb. clear - LOX. ecu. lia.
    - clear - TOP SPAH. plia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MIX.
    - reflexivity.
    - exact CSX.
    - left. reflexivity.
    - right. left. reflexivity.
    - exact NPD.
    - exact HS.
    - reflexivity.
    - exact UWX.
    - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_ofree CTX).
    - intros Σ' ms' PO. unfold vfree_postA in PO.
      destruct PO as (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4 & _).
      rewrite ?ESPA in ST4. rewrite ?ESPA in AG4. cbn [ar_RT push amb] in CR4. rewrite (ret_pc_even 0x33740c) by (clear; lia). unfold MallocRep.wz.
      rewrite ER in HEAP4, AG4. unfold apres in AG4.
      assert (LI4 : linv Σ' stX m4 OW bo [(pder, ADR, nd)] (CX - 0)).
      { eapply (oinv_heapN _ _ _ _ _ _ _ _ _ _ _ _ KH) with (L1 := OW ++ (pder, ADR, nd) :: LB') (NEW' := [(pder, ADR, nd)]) (cst := 0);
          [exact LI| | intros b [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]| cbn [app]; exact HEAP4| constructor; [exact LBder| constructor]
          | exact MI4| exact ST4| cbn [ar_RT push amb]; clear - CR4; lia| clear - HCX; lia].
        eapply agree_on_mono; [exact AG4|]. intros a (Ha & _ & _). exact Ha. }
      replace (CX - 0) with CX in LI4 by (clear; lia).
      pose proof LI4 as (PRE4 & _). cbn [app] in PRE4. pose proof PRE4 as (_ & _ & _ & _ & ST4' & _ & _ & _ & _ & MI4' & _). rewrite ESPA in ST4'.
      pose proof (der_keep (OW ++ (pder, ADR, nd) :: LB') _ _ _ _ AG4 ltac:(intros a Ha; right; right; exact Ha) ltac:(apply in_or_app; right; right; subst LB'; right; exact OIN) HOX) as HO4.
      intros X2 Φ2 D2 SAFE2 LINK2. clear MU WM. pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
      apply cps_from_evt'. zstep.
      apply evt_done. eapply (implAp_elim _ Σ' Σ' _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| reflexivity].
      change (Z_to_bv 64 3372076) with (Z_to_bv 64 IDL_EXIT).
      eapply (idl_exit _ _ _ _ [(pder, ADR, nd)] CX) with (od := Some pder); [exact LI4| exact HCX| subst nd; clear - TOT HLR; lia| intros b [<-|[]]; exact DFR| | exact (KS pder)].
      exists ADR, nd. split; [reflexivity|]. split; [subst nd; clear - TOT HLR; lia|]. split; [exact HO4| exact OFD].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma idl_der : forall ΣX stX mX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) FX fcX CX
      (d poct : bptr) (AD tot A : Z) (bs : list byte),
    linv ΣX stX mX OW bo [(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] CX -> 8 + (2 * (65535 + 8) + 16384) <= CX ->
    2 <= tot <= 65535 -> poct <> d -> A mod 16 = 0 ->
    rw_cells ctasegs mX A (asn1_string_cells tot V_ASN1_OCTET_STRING AD 0) ->
    bytes_at ctasegs mX AD bs -> length bs = Z.to_nat tot ->
    rw_cells ctasegs mX DER [C8 (wz 0)] ->
    implAp (abind (amalloc (der_hl tot + tot)) (fun der => abind (afree d) (fun _ => abind (afree poct) (fun _ => kont (Some der)))) stX) ΣX Q
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 (Z_to_bv 64 A) (Z_to_bv 64 tot) s9 s10 s11 x28 x29 x30 x31 FX fcX mX IDL_CALL_I2D).
  Proof.
    intros until bs. intros LI HCX TOT NPD A16 HS SRC SLEN HOX.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu.
    pose proof (keep_idl _ _ _ _ _ _ _ LI) as (FRH & UWX & AGS & FRL). unfold frameH in FRH.
    pose proof (oinv_call _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & LOX & SPT & SPA16 & MIX & CSX & ASX & CXR & FR0 & FRMX). rewrite ?ESPA in STX.
    pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (_ & _ & BND & FRSH & DJL & DJO).
    pose proof (DJL (poct, A, ASN1_STRING_SIZE) bO ltac:(left; reflexivity) ltac:(subst LB'; right; exact OIN)) as DJAO.
    pose proof (DJL (d, AD, tot) bO ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact OIN)) as DJDO.
    unfold ASN1_STRING_SIZE in DJAO. cbn [blk_addr blk_size fst snd] in DJAO, DJDO.
    pose proof (der_hl_range tot ltac:(clear - TOT; lia)) as HLR.
    assert (MCB : 0 <= mcost (der_hl tot + tot) <= 2 * (65535 + 8) + 16384) by (unfold mcost; destruct (_ <=? _); clear - TOT HLR; lia).
    intros XX Φ DD SAFE LINK. unfold dst, IDL_CALL_I2D.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply evt_done. eapply (implAp_elim _ ΣX ΣX _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    eapply (implAp_abind (amalloc (der_hl tot + tot)) (fun der => abind (afree d) (fun _ => abind (afree poct) (fun _ => kont (Some der)))) stX ΣX
              (fun r Σ' ms' => snd r = stX /\ ~ In (fst r) (map blk_id (OW ++ ([(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] ++ LB'))) /\
                 @i2d_octet_postA (push AR f 0) (Z_to_bv 64 0x337400) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 f) (Z_to_bv 64 DER) x20 (Z_to_bv 64 A) (Z_to_bv 64 tot) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s9 s10 s11
                    ΣX OW ([(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] ++ LB') lo DER tot mX (fst r) Σ' ms')).
    { unfold amalloc. change (Z_to_bv 64 2387508) with (wz I2D_ASN1_OCTET_STRING_A).
      eapply (@i2d_octet_walkA (push AR f 0) UK BE _) with (lo := lo) (OW := OW) (LB := [(poct, A, ASN1_STRING_SIZE); (d, AD, tot)] ++ LB') (ras := bv_unsigned ra :: ras)
          (A := A) (len := tot) (D := AD) (fl := 0) (OUT := DER) (src := bs) (bA := (poct, A, ASN1_STRING_SIZE)) (bD := (d, AD, tot)) (bO := bO); rewrite ?ESPA.
      - exact HEAPX.
      - exact STX.
      - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      - subst STKb. clear - LOX. ecu. lia.
      - clear - TOP SPAH. plia.
      - clear - SPA32. Z.div_mod_to_equations. lia.
      - exact MIX.
      - reflexivity.
      - unfold fr_depth_ok. subst FRMb'. clear - FR0 FRMX. ecu. lia.
      - unfold I2D_OCTET_COST_A. clear - CXR HCX MCB. lia.
      - exact CSX.
      - exact UWX.
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_i2d CTX).
      - apply in_or_app. right. left. reflexivity.
      - cbn [blk_addr fst snd]. clear; lia.
      - cbn [blk_addr blk_size fst snd]. clear; lia.
      - clear - A16. unfold al16 in *. Z.div_mod_to_equations. lia.
      - exact HS.
      - clear - TOT; lia.
      - clear; lia.
      - apply in_or_app. right. right. left. reflexivity.
      - cbn [blk_addr fst snd]. clear; lia.
      - cbn [blk_addr blk_size fst snd]. clear; lia.
      - exact SRC.
      - exact SLEN.
      - apply in_or_app. right. right. right. subst LB'. right. exact OIN.
      - exact OLO.
      - exact OHI.
      - exact O8.
      - exact HOX.
      - clear - DJAO OLO OHI. unfold ASN1_STRING_SIZE in *. lia.
      - clear - DJDO TOT OLO OHI. lia.
      - reflexivity.
      - reflexivity.
      - intros p Σ' ms' Hp PO. apply implAp_ret. split; [reflexivity|]. split; [exact Hp| exact PO]. }
    intros [pder st'] Σb msb (Est & Hp & POb). cbn [fst snd] in Est, Hp, POb. subst st'. cbv beta.
    destruct POb as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fb & fcb & mB & ADR & -> & MIB & STB & HEAPB & BRB & CRB & AGB & HOB).
    unfold MallocRep.wz in *. rewrite ?ESPA in STB. rewrite ?ESPA in AGB. cbn [ar_RT push amb] in CRB. rewrite (ret_pc_even 0x337400) by (clear; lia).
    pose proof (@AH_ow_off_fr (push AR f 0) _ _ _ _ f 0%nat _ HEAPB (or_introl eq_refl) (or_introl eq_refl)) as OFD.
    assert (LIB : linv Σb stX mB OW bo [(pder, ADR, der_hl tot + tot); (poct, A, ASN1_STRING_SIZE); (d, AD, tot)] (CX - I2D_OCTET_COST_A (der_hl tot + tot))).
    { eapply (oinv_allocX _ _ _ _ _ _ _ _ _ _ _ _ KH); [exact LI| | cbn [app]; exact HEAPB| exact MIB| exact STB| cbn [ar_RT push amb]; clear - CRB; lia| unfold I2D_OCTET_COST_A; clear - HCX MCB; lia].
      eapply agree_on_mono; [exact AGB|]. intros a [Ha HXa]. split; [exact Ha|]. intros Hr. apply HXa. subst XP. cbn [rin_ivs fst snd]. right. left. exact Hr. }
    assert (HSB : rw_cells ctasegs mB A (asn1_string_cells tot V_ASN1_OCTET_STRING AD 0)).
    { eapply rw_cells_agree; [exact AGB| exact HS|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha. split; [| clear - Ha DJAO OLO OHI; lia].
      right; right. exists (poct, A, ASN1_STRING_SIZE). split; [apply in_or_app; right; left; reflexivity| cbn; unfold ASN1_STRING_SIZE; clear - Ha; lia]. }
    assert (DFR : ~ In pder (map blk_id (OW ++ LB))).
    { intros Hin. apply Hp. rewrite map_app in Hin |- *. apply in_app_iff in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right]. cbn [map app]. right; right. subst LB'. right. exact Hin. }
    change (Z_to_bv 64 3372032) with (Z_to_bv 64 IDL_AFTER_I2D).
    eapply idl_free; [exact LIB| unfold I2D_OCTET_COST_A; clear - HCX MCB; lia| exact TOT| reflexivity| exact NPD| exact DFR| exact OFD| exact HSB| exact HOB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma idl_some : forall ΣX stX mX (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 : word) FX fcX CX (d : bptr) (AD tot : Z) (bs : list byte),
    linv ΣX stX mX OW bo [(d, AD, tot)] CX -> 8 + (2 * (65535 + 8) + 16384) <= CX ->
    2 <= tot <= 65535 ->
    rw_cells ctasegs mX (f + 32) [C8 (wz AD)] -> bytes_at ctasegs mX AD bs -> length bs = Z.to_nat tot ->
    rw_cells ctasegs mX DER [C8 (wz 0)] ->
    implAp (CS tot d stX) ΣX Q (dst x1 x5 x6 x7 (Z_to_bv 64 tot) x11 x12 x13 x14 x15 x16 x17 x20 (Z_to_bv 64 (f + 32)) x22 s9 s10 s11 x28 x29 x30 x31 FX fcX mX IDL_RET1).
  Proof.
    intros until bs. intros LI HCX TOT HD SRC SLEN HOX.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu.
    pose proof (oinv_call _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & LOX & SPT & SPA16 & MIX & CSX & ASX & CXR & FR0 & FRMX). rewrite ?ESPA in STX.
    pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (_ & _ & BND & FRSH & DJL & DJO).
    pose proof (BND (d, AD, tot) ltac:(apply in_or_app; right; left; reflexivity)) as (D1 & _ & D3 & D5). cbn [blk_addr blk_size fst snd] in D1, D3, D5.
    pose proof (DJL (d, AD, tot) bO ltac:(left; reflexivity) ltac:(subst LB'; right; exact OIN)) as DJDO. cbn [blk_addr blk_size fst snd] in DJDO.
    pose proof (DJL (d, AD, tot) (qd, f + 32, 8) ltac:(left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJDQ. cbn [blk_addr blk_size fst snd] in DJDQ.
    nrm.
    intros XX Φ DD SAFE LINK. unfold dst, IDL_RET1. subst CS. cbv beta.
    pose proof (munch_refl [(spa - 16, spa)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - TOT; lia); clear - K0 TOT; lia| clear K0].
    zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 16%nat STX. do 5 zstep. do 2 zstep. release_frame FR STX spa. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : munch _ mX m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs mX m1 |- _ => rename H into WM1 end.
    match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
    assert (ST1 : stk ctasegs m1 lo spa) by (first [assumption| eapply stk_transport; [exact STX| exact MU1| exact WM1| cbn; clear; lia]]).
    assert (LI1 : linv ΣX stX m1 OW bo [(d, AD, tot)] CX).
    { eapply (linv_munch _ _ _ _ _ _ _ _ _ LI MU1 WM1 MI1 ST1). constructor; [cbn [fst snd]; left; subst STKb; clear - LOX; ecu; lia| constructor]. }
    pose proof (oinv_call _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI1) as (HEAP1 & ST1' & _ & _ & _ & _ & MI1' & CS1 & _). rewrite ?ESPA in ST1'.
    pose proof (keep_idl _ _ _ _ _ _ _ LI1) as (FRH1 & UW1 & AGS1 & FRL1). unfold frameH in FRH1.
    assert (K1 : forall A' cs, rw_cells ctasegs mX A' cs -> A' + Z.of_nat (cells_size cs) <= spa - 16 -> rw_cells ctasegs m1 A' cs).
    { intros A' cs H HA. eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact H|]. intros a Ha. cbn [outside fst snd]. split; [clear - Ha HA; lia| exact I]. }
    (* [comment removed for export] *)
    first [apply K1 in HD; [| cbn; clear - G3 CEIL LOSPu SPAL; lia] | idtac]. first [apply K1 in HOX; [| cbn; clear - BD2 OHI CEIL LOSPu SPAL; lia] | idtac].
    assert (SRC1 : bytes_at ctasegs m1 AD bs).
    { first [exact SRC | (eapply bytes_at_agree; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact SRC|]; intros a Ha; rewrite SLEN in Ha; cbn [outside fst snd]; split; [clear - Ha D3 CEIL LOSPu SPAL TOT; lia| exact I])]. }
    clear K1 SRC.
    apply evt_done. eapply (implAp_elim _ ΣX ΣX _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    eapply (implAp_abind (amalloc SZ_ASN1_STRING) (fun oct => abind (amalloc (der_hl tot + tot)) (fun der => abind (afree d) (fun _ => abind (afree oct) (fun _ => kont (Some der))))) stX ΣX
              (fun r Σ' ms' => snd r = stX /\ ~ In (fst r) (map blk_id (OW ++ ([(d, AD, tot)] ++ LB'))) /\
                 @calloc_postA (push AR f 0) (Z_to_bv 64 0x3373dc) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 f) (Z_to_bv 64 DER) (Z_to_bv 64 (-1)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 tot) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s9 s10 s11
                    ΣX OW ([(d, AD, tot)] ++ LB') 24 lo m1 (fun A' m' => rw_cells ctasegs m' A' (asn1_string_cells 0 V_ASN1_OCTET_STRING 0 0)) (fst r) Σ' ms')).
    { unfold amalloc, SZ_ASN1_STRING. change (Z_to_bv 64 2247428) with (wz ASN1_STRING_TYPE_NEW_A).
      eapply (@ASN1_STRING_type_new_walkA (push AR f 0) UK BE _) with (lo := lo) (OW := OW) (LB := [(d, AD, tot)] ++ LB') (ty := V_ASN1_OCTET_STRING) (ras := bv_unsigned ra :: ras); rewrite ?ESPA; try reflexivity.
      - exact HEAP1.
      - exact ST1'.
      - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      - subst STKb. clear - LOX. ecu. lia.
      - clear - TOP SPAH. plia.
      - clear - SPA32. Z.div_mod_to_equations. lia.
      - exact MI1'.
      - exact CS1.
      - unfold V_ASN1_OCTET_STRING. clear; lia.
      - exact UW1.
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_tail _ _ _ E_onew_tail (uk_ctx_call _ _ _ _ E_onew CTX)).
      - intros p Σ' ms' Hp PO. apply implAp_ret. split; [reflexivity|]. split; [exact Hp| exact PO]. }
    intros [poct st'] Σb msb (Est & Hp & POb). cbn [fst snd] in Est, Hp, POb. subst st'. cbv beta.
    destruct POb as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fb & fcb & mB & A & -> & MIB & STB & AGB & CRB & BRB & HEAPB & ACCB & HSB).
    unfold MallocRep.wz in *. rewrite ?ESPA in STB. rewrite ?ESPA in AGB. cbn [ar_RT push amb] in CRB. rewrite (ret_pc_even 0x3373dc) by (clear; lia).
    pose proof BRB as (A0 & A16 & _ & ACE & AIMG). unfold BnHeapA.ACEIL in ACE. cbn [ar_SP0 push amb] in ACE.
    replace (mcost 24) with 0 in CRB by reflexivity.
    assert (LIB : linv Σb stX mB OW bo [(poct, A, 24); (d, AD, tot)] (CX - 0)).
    { eapply (oinv_alloc _ _ _ _ _ _ _ _ _ _ _ _ KH); [exact LI1| cbn [app]; exact AGB| cbn [app]; exact HEAPB| exact MIB| exact STB| cbn [ar_RT push amb]; clear - CRB; lia| clear - HCX; lia]. }
    replace (CX - 0) with CX in LIB by (clear; lia).
    pose proof LIB as (PREB & _). cbn [app] in PREB. pose proof PREB as (HEAPB' & _ & _ & _ & STB' & _ & _ & _ & _ & MIB' & _). rewrite ESPA in STB'.
    pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LIB) as (_ & _ & _ & _ & DJLb & _).
    pose proof (DJLb (poct, A, 24) bO ltac:(left; reflexivity) ltac:(subst LB'; right; exact OIN)) as DJAO. cbn [blk_addr blk_size fst snd] in DJAO.
    assert (NPD : poct <> d).
    { intros E0. apply Hp. rewrite E0. rewrite map_app. apply in_or_app. right. left. reflexivity. }
    pose proof (@AH_disjoint_gen (push AR f 0) _ _ _ _ (poct, A, 24) (d, AD, tot) HEAPB' ltac:(apply in_or_app; right; left; reflexivity) ltac:(apply in_or_app; right; right; left; reflexivity) NPD) as DJAD.
    cbn [blk_addr blk_size fst snd] in DJAD.
    assert (KB : forall A' cs, rw_cells ctasegs m1 A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> aclient_addr (OW ++ [(d, AD, tot)] ++ LB') spa a) -> rw_cells ctasegs mB A' cs).
    { intros A' cs H HA. eapply rw_cells_agree; [exact AGB| exact H| exact HA]. }
    apply KB in HD; [| intros a Ha; cbn in Ha; right; right; exists (qd, f + 32, 8); split; [apply in_or_app; right; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia]].
    apply KB in HOX; [| intros a Ha; cbn in Ha; right; right; exists bO; split; [apply in_or_app; right; right; subst LB'; right; exact OIN| clear - Ha OLO OHI; lia]].
    assert (SRCB : bytes_at ctasegs mB AD bs).
    { eapply bytes_at_agree; [exact AGB| exact SRC1|]. intros a Ha. rewrite SLEN in Ha. right; right. exists (d, AD, tot). split; [apply in_or_app; right; left; reflexivity| cbn; clear - Ha TOT; lia]. }
    clear KB SRC1.
    intros X2 Φ2 D2 SAFE2 LINK2. try clear MU; try clear WM; try clear MU1; try clear WM1. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?land64_small, ?unsigned_lit in K1 by (clear - A0 ACE CE3; plia); clear - K1 A0; lia| clear K1].
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (@ASN1_STRING_set0_walkA (push AR f 0)) with (lo := lo) (OW := OW) (LB := [(poct, A, 24); (d, AD, tot)] ++ LB') (q := poct) (ty := V_ASN1_OCTET_STRING) (len := tot) (D := AD);
        rewrite ?ESPA; [exact HEAPB'| exact STB'| exact MIB'| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOX; ecu; lia
          | apply in_or_app; right; left; reflexivity| exact A16| clear - D1 D3 CE3 TOT; plia| clear - TOT; lia| unfold V_ASN1_OCTET_STRING; clear; lia| exact HSB| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros ms3 PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & HS5).
    rewrite ?ESPA in MU5. rewrite ?ESPA in ST5. rewrite (ret_pc_even 0x3373f4) by (clear; lia). unfold ASN1_STRING_SET0_STACK_A, ASN1_STRING_SIZE in MU5.
    assert (LI5 : linv Σb stX m5 OW bo [(poct, A, 24); (d, AD, tot)] CX).
    { eapply (linv_munch _ _ _ _ _ _ _ _ _ LIB MU5 WM5 MI5 ST5).
      constructor; [cbn [fst snd]; left; subst STKb; clear - LOX; ecu; lia| constructor; [cbn [fst snd]; right; exists (poct, A, 24); split; [left; reflexivity| cbn; clear; lia]| constructor]]. }
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU5 WM5) in HOX; [| cbn; clear - DJAO BD2 OLO OHI CEIL LOSPu SPAL; lia].
    assert (SRC5 : bytes_at ctasegs m5 AD bs).
    { eapply bytes_at_agree; [apply (agree_on_of_munch_nw _ _ _ MU5)| exact SRCB|]. intros a Ha. rewrite SLEN in Ha. cbn [outside fst snd].
      split; [clear - Ha D3 CEIL LOSPu SPAL TOT; lia|]. split; [clear - Ha DJAD TOT; lia| exact I]. }
    apply evt_done. eapply (implAp_elim _ Σb Σb _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| reflexivity].
    change (Z_to_bv 64 3372020) with (Z_to_bv 64 IDL_CALL_I2D).
    eapply idl_der; [exact LI5| exact HCX| exact TOT| exact NPD| exact A16| exact HS5| exact SRC5| exact SLEN| exact HOX].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma idl_body : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) F1 fc1,
    implAp (i2d_sct_list_cps k kont st) Σ1 Q
      (dst x1 x5 x6 x7 (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (f + 32)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (f + 32)) x22 s9 s10 s11 x28 x29 x30 x31 F1 fc1 m3 IDL_BODY).
  Proof.
    intros.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & BD5).
    pose proof LOSP as LOSPu. ecu. pose proof (zlength_ge0 (sk_items k)) as N0. pose proof (mcost_le 0 ltac:(clear; lia)) as MC0.
    pose proof linv0 as LI. pose proof (keep_sk _ _ _ _ _ _ _ LI) as SK3.
    pose proof (keep_idl _ _ _ _ _ _ _ LI) as (FRH & UW3 & AGS3 & FRL). unfold frameH in FRH.
    pose proof LI as (PREX & AXX & KO & KI & KP & CR & LBOK). cbn [app] in PREX. cbn [ar_RT ar_FR push amb] in CR.
    pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & CREDX & FRMX). rewrite ESPA in STX. cbn [ar_RT ar_FR push amb length] in CREDX, FRMX.
    assert (HO3 : rw_cells ctasegs m3 DER [C8 (Z_to_bv 64 0)]).
    { eapply rw_cells_agree; [exact AG3| exact HO|]. intros a Ha. cbn in Ha. right; right. exists bO. split; [apply in_or_app; right; exact OIN| clear - Ha OLO OHI; lia]. }
    intros XX Φ DD SAFE LINK. unfold dst, IDL_BODY.
    pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    apply cps_from_evt'. zstep.
    apply evt_done. eapply (implAp_elim _ Σ1 Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    change (i2d_sct_list_cps k kont st) with (abind (i2o_len_pass (sk_items k) 2) (Gk CN CS) st).
    change (Z_to_bv 64 3369852) with (wz I2O_SCT_LIST_A).
    eapply (@i2o_list_out_walkA (push AR f 0) UK BE UR STRCPY B0 CN CS Q) with (lo := lo) (K := K) (ras := bv_unsigned ra :: ras) (j := 0%nat) (X0 := 0x3373cc :: bv_unsigned ra :: ras)
        (STK := STKb) (CST := CSTb) (FRMb := FRMb') (adr := adr) (k := k) (DATA := f + 32) (bD := (qd, f + 32, 8)); rewrite ?ESPA.
    - exact PREX.
    - reflexivity.
    - subst STKb. clear. ecu. lia.
    - subst CSTb. clear - N0. ecu. lia.
    - subst FRMb'. clear. ecu. lia.
    - exact UW3.
    - rewrite unsigned_lit by (clear; lia). reflexivity.
    - apply uk_ctxJ_enter. exact (uk_ctx_call _ _ _ _ E_iol CTX).
    - unfold IOL_REC_DEPTH. clear. lia.
    - apply cons_ne.
    - exact KO.
    - exact KI.
    - eapply sk_repA_relist; [exact SK3|]. intros b Hb. subst LB'. right. exact (sk_repA_blocks_in _ _ _ _ _ SK Hb).
    - subst LB'. left. reflexivity.
    - cbn [blk_addr fst snd]. clear; lia.
    - cbn [blk_addr blk_size fst snd]. clear; lia.
    - clear - G2. Z.div_mod_to_equations. lia.
    - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror (sk_repA_blocks_in _ _ _ _ _ SK Hb)))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. clear - O. lia.
    - exact HDATA3.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      intros st1 Σa ms1 PO. unfold outpost_fail in PO.
      destruct PO as (o0 & o1 & o2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & o3 & o4 & o5 & o6 & Fa & fca & mA & OWa & -> & PREa & AXa & CRa & BKa & SKa & HDa).
      rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x3373cc) by (clear; lia). unfold MallocRep.wz.
      assert (LIA : linv Σa st1 mA OWa bo [] (CSTb - IOL_OUT_COST_A (zlength (sk_items k)))).
      { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := [(f + 32, f + 32 + 8)]%Z) (NEW2 := []);
          [exact LI| cbn [app]; exact PREa| cbn [app]; exact AXa| intros a Ha; right; left; subst XP; cbn [rin_ivs fst snd] in Ha |- *; clear - Ha; lia
          | cbn [ar_RT push amb]; exact CRa| subst CSTb; clear - N0 MC0; ecu; lia| exact BKa| constructor]. }
      assert (HOa : rw_cells ctasegs mA DER [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_agree; [| exact HO3|]; [intros wa' Hr Hc; exact (AXa wa' Hr Hc)|]. intros a Ha. cbn in Ha. split.
        - cbn [app rin_ivs fst snd]. unfold LIBW_A. cbn [rin_ivs fst snd]. pose proof (FRESH bO (in_or_app _ _ _ (or_intror OIN))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
          clear - Ha O BD1 BD5 OLO OHI. lia.
        - right; right. exists bO. split; [subst LB'; right; exact OIN| clear - Ha OLO OHI; lia]. }
      change (Z_to_bv 64 3371980) with (Z_to_bv 64 IDL_RET1).
      eapply idl_none; [exact LIA| subst CSTb; clear - N0 MC0; ecu; lia| exact HOa].
    - (* [comment removed for export] *)
      intros d st1 Σa ms1 PO. unfold outpost_ok in PO.
      destruct PO as (o0 & o1 & o2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & o3 & o4 & o5 & o6 & Fa & fca & mA & AD & tot & -> & Etot & TOTB & PREa & AXa & CRa & BKa & Hd & LBd & SKa & CPLa & HDa & (bs & SRCa & SLa)).
      rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x3373cc) by (clear; lia). unfold MallocRep.wz. unfold MAX_SCT_LIST_SIZE in TOTB.
      assert (LIA : linv Σa st1 mA OW bo [(d, AD, tot)] (CSTb - IOL_OUT_COST_A (zlength (sk_items k)))).
      { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := [(f + 32, f + 32 + 8)]%Z) (NEW2 := [(d, AD, tot)]);
          [exact LI| cbn [app]; exact PREa| cbn [app]; exact AXa| intros a Ha; right; left; subst XP; cbn [rin_ivs fst snd] in Ha |- *; clear - Ha; lia
          | cbn [ar_RT push amb]; exact CRa| subst CSTb; clear - N0 MC0; ecu; lia| exact BKa| constructor; [exact LBd| constructor]]. }
      assert (HOa : rw_cells ctasegs mA DER [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_agree; [| exact HO3|]; [intros wa' Hr Hc; exact (AXa wa' Hr Hc)|]. intros a Ha. cbn in Ha. split.
        - cbn [app rin_ivs fst snd]. unfold LIBW_A. cbn [rin_ivs fst snd]. pose proof (FRESH bO (in_or_app _ _ _ (or_intror OIN))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
          clear - Ha O BD1 BD5 OLO OHI. lia.
        - right; right. exists bO. split; [subst LB'; right; exact OIN| clear - Ha OLO OHI; lia]. }
      rewrite <- Etot.
      change (Z_to_bv 64 3371980) with (Z_to_bv 64 IDL_RET1).
      eapply idl_some; [exact LIA| subst CSTb; clear - N0 MC0; ecu; lia| exact TOTB| exact HDa| exact SRCa| exact SLa| exact HOa].
  Qed.
End ActIdl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem i2d_sct_list_walkA : i2d_sct_list_specA IDL_STACK_A IDL_COST_A IDL_FRAMES_A.
Proof.
  unfold i2d_sct_list_specA. intros until DER. intros PRE TP UW CTX NE KOW KIDS SK ADR OCELL O8 OAP HO Ea0 Ea1 KN KS.
  destruct OCELL as (bO & OIN & OLO & OHI).
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
  pose proof LOSP as LOSPu. pose proof CRED as CREDu. pose proof FRM0 as FRMu. ecu.
  pose proof (zlength_ge0 (sk_items k)) as N0. pose proof (mcost_le 0 ltac:(clear; lia)) as MC0.
  intros XX Φ DD SAFE LINK. subst tp a0 a1.
  change (wz I2D_SCT_LIST_A) with (wz IDL_ENTRY).
  eapply (idl_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold IDL_FRAME, RT_STACK; clear - LOSPu; lia| exact TOP| exact AL16| exact MI| reflexivity
    | clear - FRMu; lia| clear - CREDu N0 MC0; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AG3 FRL FRH HF FRS SPA32 SPAL SPAH GSZ SAVJ.
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qd Hqd].
  pose proof (idl_open_data Σ1 OW LB m3 f qd HEAP3 ltac:(intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))) GEO FRS Hqd) as HEAPp.
  lazymatch type of HF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs m3 f [c0; c1; c2; c3] (c4 :: rest)) HF)) as HD0 end.
  lazymatch type of HD0 with rw_cells _ _ ?a _ => replace a with (f + 32) in HD0 by reflexivity end.
  lazymatch type of HD0 with rw_cells _ _ _ (?c4 :: ?rest) =>
    pose proof (proj1 (proj1 (SctRepA.rw_cells_app ctasegs m3 (f + 32) [c4] rest) HD0)) as HDATA3 end.
  eapply (implAp_elim _ Σ Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| exact EL1].
  unfold MallocRep.wz. change (Z_to_bv 64 IDL_BODY) with (Z_to_bv 64 IDL_BODY).
  eapply (idl_body B0 kont Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K ras adr k DER bO); try eassumption; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma idl_budgets : IDL_STACK_A = 66656 /\ IDL_FRAMES_A = 13 /\ (forall n, IDL_COST_A n = 294978 + 2 * n).
Proof. ecu. split; [reflexivity|]. split; [reflexivity|]. intros n. unfold IDL_COST_A, IOL_OUT_COST_A, IOL_LEN_COST_A, IOL_MALLOC_COST_A. ecu. lia. Qed.
End WithRT.
