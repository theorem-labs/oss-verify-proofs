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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA EncKitA EncActA Fr_i2o_SCT Fr_i2o_SCT_LIST W_sct_completeA W_i2o_sigA W_i2o_sctA W_i2o_sct_failA W_i2o_sct_writeA W_asn1_flagsA W_i2o_list_lenA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac abB := repeat (first [ ab1X | ApATac.ab1 ]).
Local Ltac apre := ual; abB.
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
Definition IOL_OUT_STACK_A : Z := 176 + IOL_LEN_STACK_A.
(* [comment removed for export] *)
Definition IOL_MALLOC_COST_A : Z := 2 * 65535 + 16384.
(* [comment removed for export] *)
Definition IOL_OUT_COST_A (n : Z) : Z := 1 + IOL_LEN_COST_A n + 13 + IOL_MALLOC_COST_A + n.
Definition IOL_OUT_FRAMES_A : Z := 1 + IOL_LEN_FRAMES_A.
(* [comment removed for export] *)
Definition IOL_RAISE : Z := 0x336ebc.
Definition IOL_WHEAD : Z := 0x336ce8.

Lemma mcost_le : forall n, 0 <= n <= 65535 -> 0 <= mcost n <= IOL_MALLOC_COST_A.
Proof. intros n Hn. unfold mcost, IOL_MALLOC_COST_A. destruct (n <=? 64512); lia. Qed.

(* [comment removed for export] *)
Definition Gk {B0 : Type} (CN : @AM bptr B0) (CS : Z -> bptr -> @AM bptr B0) (r : option Z) : @AM bptr B0 :=
  match r with
  | None => CN
  | Some len2 => if MAX_SCT_LIST_SIZE <? len2 then abind (err_raise RS_i2o_list) (fun _ => CN) else abind (amalloc len2) (CS len2)
  end.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec I2O_SCT_LIST_A IOL_NESTED_RET IOL_REC_DEPTH}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ios_w := (E_i2o_SCT_LIST_34b0c8 : uk_call 3369852 3370256 3367120).
Local Notation E_malloc := (E_i2o_SCT_LIST_34b2a0 : uk_call 3369852 3370600 2084388).   (* [comment removed for export] *)
Local Notation E_new := (E_i2o_SCT_LIST_34b2c0 : uk_call 3369852 3370692 2086188).
Local Notation E_dbg := (E_i2o_SCT_LIST_34b2dc : uk_call 3369852 3370720 2086980).
Local Notation E_err := (E_i2o_SCT_LIST_34b2f0 : uk_call 3369852 3370740 2087608).

(* [comment removed for export] *)
Hypothesis STRCPY : strcpy_icontract RT.

Local Ltac ecu := unfold IOL_OUT_STACK_A, IOL_OUT_COST_A, IOL_OUT_FRAMES_A, IOL_MALLOC_COST_A, IOL_LEN_STACK_A, IOL_LEN_COST_A, IOL_LEN_FRAMES_A,
                         I2O_SCT_FAIL_STACK_A, I2O_SCT_FAIL_COST_A, I2O_SCT_FAIL_FRAMES_A, I2O_SCT_LEN_STACK_A, I2O_SCT_W_STACK_A, I2O_SIG_STACK_A, IOS_FRAME,
                         ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK,
                         ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, CRYPTO_FREE_STACK,
                         CRYPTO_MALLOC_STACK, RT_STACK in *.

(* [comment removed for export] *)
Definition outpost_fail (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (k : skr bptr) (DATA : Z) (st1 : ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' st1 m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(DATA, DATA + 8)]%Z ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K st1 OW' m m'
    /\ sk_repA m' LB adr k
    /\ rw_cells ctasegs m' DATA [C8 (wz 0)].

(* [comment removed for export] *)
Definition outpost_ok (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (k : skr bptr) (DATA : Z) (d : bptr) (st1 : ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' AD (tot : Z),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 tot) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ tot = 2 + i2o_sum (sk_items k) /\ 2 <= tot <= MAX_SCT_LIST_SIZE
    /\ ap_preA Σ' st1 m' OW ((d, AD, tot) :: LB) E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(DATA, DATA + 8)]%Z ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K st1 OW m m'
    /\ ~ In d (map blk_id (OW ++ LB)) /\ lbokA (d, AD, tot)
    /\ sk_repA m' LB adr k /\ Forall (fun x => sct_complete x = true) (sk_items k)
    /\ rw_cells ctasegs m' DATA [C8 (wz AD)]
    /\ (exists bs, bytes_at ctasegs m' AD bs /\ length bs = Z.to_nat tot).

(* [comment removed for export] *)
Lemma iol_open_p : forall Σ1 OW LB m f q,
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m -> (forall b, In b LB -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m (shad f) iol_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) m.
Proof.
  intros Σ1 OW LB m f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 0) Σ1 OW LB m f 0%nat q (f + 32) 8 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 0) with 64; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m (shad f) iol_shadow_pro 4%nat (f + 32) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b Hb) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 0) with 64 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

Section ActOut.
  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z).
  Variables (lo : Z) (K : list block) (ras : list Z) (STK CST FRMb : Z) (adr : bptr -> Z) (k : skr bptr) (DATA : Z) (bD : block).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo STK CST FRMb.
  Hypothesis STKB : IOL_OUT_STACK_A <= STK.
  Hypothesis CSTB : IOL_OUT_COST_A (zlength (sk_items k)) <= CST.
  Hypothesis FRMB : IOL_OUT_FRAMES_A <= FRMb.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  (* [comment removed for export] *)
  Variables (j : nat) (X0 : list Z).
  Hypothesis ERAS : bv_unsigned ra :: ras = repeat IOL_NESTED_RET j ++ X0.
  Hypothesis CTXJ : uk_ctxJ j X0.
  Hypothesis JB : (S j <= IOL_REC_DEPTH)%nat.
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis SK : sk_repA m LB adr k.
  Hypothesis DIN : In bD LB.
  Hypothesis DLO : blk_addr bD <= DATA.
  Hypothesis DHI : DATA + 8 <= blk_addr bD + blk_size bD.
  Hypothesis D8 : DATA mod 8 = 0.
  Hypothesis DAP : forall b, In b (sk_blocks adr k) -> DATA + 8 <= blk_addr b \/ blk_addr b + blk_size b <= DATA.
  Hypothesis HD : rw_cells ctasegs m DATA [C8 (wz 0)].
  (* [comment removed for export] *)
  Variables (Σ1 : rts RT) (m3 : mem) (f spa : Z) (g : nat) (junk gj j0 j8 j16 j24 j32 j40 : list byte) (qp : bptr).
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3.
  Hypothesis HEAPp : @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((qp, f + 32, 8) :: LB) m3.
  Hypothesis QPF : ~ In qp (map blk_id (OW ++ LB)).
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 0 b.
  Hypothesis GEO : fr_geo f 0.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis EL1 : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AG3 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis FRL3 : rw_cells ctasegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk].   (* [comment removed for export] *)
  Hypothesis FRH3 : rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis HP3 : rw_cells ctasegs m3 (f + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 176 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 160.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 72.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Variables (B0 : Type) (CN : @AM bptr B0) (CS : Z -> bptr -> @AM bptr B0) (Q : B0 * ap_st bptr -> rts RT -> machine_state -> Prop).
  Hypothesis KN : forall st1 Σ' ms',
    outpost_fail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (IOL_OUT_COST_A (zlength (sk_items k))) adr k DATA st1 Σ' ms' ->
    implAp (CN st1) Σ' Q ms'.
  Hypothesis KS : forall d st1 Σ' ms',
    outpost_ok ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (IOL_OUT_COST_A (zlength (sk_items k))) adr k DATA d st1 Σ' ms' ->
    implAp (CS (2 + i2o_sum (sk_items k)) d st1) Σ' Q ms'.

  Let STKb : Z := STK - 176.
  Let CSTb : Z := CST - 1.
  Let FRMb' : Z := FRMb - 1.
  Let LB' : list block := (qp, f + 32, 8) :: LB.
  Let XP : list (Z * Z) := [(f + 32, f + 40); (DATA, DATA + 8)]%Z.
  (* [comment removed for export] *)
  Let linv : rts RT -> ap_st bptr -> mem -> list block -> Z * Z -> list block -> Z -> Prop :=
    @oinv (push AR f 0) (Z_to_bv 64 (spa + 32)) spa m3 Σ1 LB' E lo K XP STKb CSTb FRMb'.
  Let frameH (mX : mem) : Prop := rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ost (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mX : mem) (pc : Z) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
            x18 (Z_to_bv 64 DATA) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (adr (sk_blk k))) x22 x23 x24 (Z_to_bv 64 (shad f)) x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mX (seg_rom ctasegs).

  Lemma base_facts :
    0 <= bv_unsigned sp < 2 ^ 64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo /\ 0 <= lo
    /\ lo <= bv_unsigned sp - STK /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
    /\ 0 < f /\ f mod 64 = 0 /\ f + 64 <= ACEIL /\ SEGTOP_A <= f /\ (f + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f /\ CST <= rt_credit RT Σ /\ Z.of_nat (length FRM) + FRMb <= Z.of_nat FRAMES_MAX
    /\ 0 < blk_addr bD /\ blk_addr bD + blk_size bD <= ACEIL /\ 0 < DATA < 2 ^ 64 /\ bv_unsigned (Z_to_bv 64 (spa + 32)) = spa + 32.
  Proof.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
    pose proof STKB as STKu. ecu.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LOSP SPAL SPAH SPR LO0 STKu; plia).
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; plia).
    pose proof (AH_range_gen _ _ _ _ bD HEAP (in_or_app _ _ _ (or_intror DIN))) as (B1 & _ & _ & B4 & _).
    split; [exact SPR|]. split; [exact CE1|]. split; [exact CE2|]. split; [exact CE3|]. split; [exact CEIL|]. split; [exact LO0|]. split; [exact LOSP|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact ESPA|]. split; [exact Ef|]. split; [clear - CRED; lia|]. split; [clear - FRM0; lia|]. split; [exact B1|]. split; [exact B4|].
    split; [clear - B1 B4 DLO DHI CE3; plia|]. apply unsigned_lit; clear - CE1 CEIL LOSP SPAL SPAH SPR LO0 STKu; plia.
  Qed.

  Lemma bD_seg : blk_addr bD + blk_size bD <= 65536 \/ 12365824 <= blk_addr bD.
  Proof. pose proof PRE as (HEAP & _). pose proof (AH_range_gen _ _ _ _ bD HEAP (in_or_app _ _ _ (or_intror DIN))) as (_ & _ & _ & _ & B5). exact B5. Qed.

  Lemma OKALL : Forall (sct_ok adr) (sk_items k).
  Proof.
    pose proof PRE as (HEAP & _). pose proof SK as (_ & _ & _ & HF & _).
    apply Forall_forall. intros x Hx. eapply (sct_ok_of_repA _ _ _ _ _ _ HEAP). exact (proj1 (Forall_forall _ _) HF x Hx).
  Qed.

  Lemma KH : @kit_hyps (push AR f 0) (Z_to_bv 64 (spa + 32)) spa LB' lo XP STKb.
  Proof.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. ecu.
    unfold kit_hyps. rewrite ESPA32. split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL|]. split; [exact LO0|]. split; [subst STKb; clear - LOSP SPAL; lia|].
    split; [subst STKb; clear - STKu; plia|]. split; [clear; lia|]. split; [clear - TOP SPAH; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    subst XP LB'. constructor; [| constructor; [| constructor]]; cbn [fst snd].
    - exists (qp, f + 32, 8). split; [left; reflexivity| cbn; clear; lia].
    - exists bD. split; [right; exact DIN| clear - DLO DHI; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma linv0 : linv Σ1 st m3 OW bo [] CSTb.
  Proof.
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu. pose proof (zlength_ge0 (sk_items k)) as Z0. pose proof (mcost_le 0 ltac:(clear; lia)) as MC.
    apply (oinv_entry _ _ _ _ _ _ _ _ _ _ _ _ KH).
    - subst STKb CSTb FRMb'. replace (STK - 176) with (STK - 160 - 16) by (clear; lia).
      pose proof (pro_closeA Σ st m OW LB E bo sp lo STK CST FRMb f 0%nat Σ1 m3 spa 160 PRE HEAP3 ST3 MI3 AG3 CR1 SPA32 ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia)
                    ltac:(clear; lia) ltac:(clear - STKu; lia) ltac:(clear - CSTu Z0 MC; unfold IOL_MALLOC_COST_A in *; lia) ltac:(clear - FRMu; lia)) as P3.
      destruct P3 as (_ & REST). split; [subst LB'; exact HEAPp| exact REST].
    - exact KOW.
    - exact KIDS.
  Qed.

  (* [comment removed for export] *)
  Lemma keep_out : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX ->
    frameH mX /\ uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras) /\ agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX
    /\ rw_cells ctasegs mX (spa + 32) [CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk].
  Proof.
    intros until CX. intros (_ & AX & _).
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. ecu. nrm. rewrite ESPA32 in AX.
    assert (AXS : forall a, spa + 32 <= a < USTACK_TOP -> ~ (f + 32 <= a < f + 40) -> ~ (DATA <= a < DATA + 8) -> mX (wa a) = m3 (wa a)).
    { intros a Ha N1 N2. unfold USTACK_TOP in Ha. apply AX; [clear - Ha SPR CEIL LOSP STKu SPAL LO0; lia|]. split; [| left; unfold USTACK_TOP; exact Ha].
      subst XP. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha N1 N2 CEIL CE1 LOSP STKu SPAL. lia. }
    assert (FHI : f + 64 <= spa) by (clear - G3 CEIL LOSP STKu SPAL; lia).
    assert (DHI' : DATA + 8 <= spa) by (clear - BD2 DHI CEIL LOSP STKu SPAL; lia).
    assert (AGS : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX).
    { intros a Ha Hr. unfold USTACK_TOP in Hr. rewrite (AXS a ltac:(unfold USTACK_TOP; clear - Hr SPAH; lia) ltac:(clear - Hr FHI SPAH; lia) ltac:(clear - Hr DHI' SPAH; lia)).
      apply AG3; [exact Ha| left; unfold USTACK_TOP; exact Hr]. }
    assert (FRH : frameH mX).
    { unfold frameH. eapply rw_cells_agree; [| exact FRH3|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. apply AXS; [unfold USTACK_TOP; clear - Ha TOP SPAH; lia| clear - Ha FHI SPAH; lia| clear - Ha DHI' SPAH; lia]. }
    split; [exact FRH|]. split; [| split; [exact AGS|]].
    - eapply (uw_call m mX spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [exact UW| exact AGS| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| unfold USTACK_TOP; clear - TOP; lia| apply bv_unsigned_in_range|].
      rewrite !Z_to_bv_bv_unsigned. cbn [app]. exact FRH.
    - pose proof (rw_cells_skip m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk] 32 FRL3 eq_refl) as H.
      eapply rw_cells_agree; [| exact H|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbv beta. cbn [cells_size csize Nat.add] in Ha. apply AXS; [unfold USTACK_TOP; clear - Ha TOP SPAH GSZ; lia| clear - Ha FHI; lia| clear - Ha DHI'; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma keep_sk : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX -> sk_repA mX LB adr k.
  Proof.
    intros until CX. intros (PREX & AX & _). pose proof base_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _ & _ & ESPA & _ & _ & _ & _ & _ & _ & ESPA32). rewrite ESPA32 in AX.
    pose proof PRE as (HEAP & _).
    assert (SK3 : sk_repA m3 LB adr k).
    { eapply sk_repA_agree; [exact AG3| | exact SK]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha]. }
    eapply sk_repA_agree; [exact AX| | exact SK3]. intros b a Hb Ha. pose proof (sk_repA_blocks_in _ _ _ _ _ SK Hb) as HbL.
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror HbL))) as (B1 & _ & _ & B4 & B5). pose proof (FRESH b (in_or_app _ _ _ (or_intror HbL))) as O.
    unfold off_fr in O. change (fs_size 0) with 64 in O. pose proof (DAP b Hb) as DA.
    split.
    - subst XP. unfold LIBW_A. cbn [app rin_ivs fst snd]. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Ha, B1, B5, O, DA. clear - Ha B1 B5 O DA. lia.
    - right; right. exists b. split; [subst LB'; right; exact HbL| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma linv_munch : forall ΣX stX mX OWX boX NEW CX mY W,
    linv ΣX stX mX OWX boX NEW CX -> munch W mX mY -> wmono ctasegs mX mY -> mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    Forall (fun iv => (lo <= fst iv /\ snd iv <= spa + 32) \/ iv = (f + 32, f + 40) \/ iv = (DATA, DATA + 8) \/ (exists b, In b NEW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    linv ΣX stX mY OWX boX NEW CX.
  Proof.
    intros until W. intros LI MU WM MI ST HW. pose proof base_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESPA & _ & _ & _ & _ & _ & _ & ESPA32).
    eapply (oinv_munch _ _ _ _ _ _ _ _ _ _ _ _ KH); [exact LI| exact MU| exact WM| exact MI| exact ST|].
    eapply Forall_impl; [| exact HW]. intros [u v] [[H1 H2]|[H1|[H1|(b & Hb & H1 & H2)]]]; cbn [fst snd] in *.
    - left. cbn [fst snd]. rewrite ESPA32. split; [exact H1| exact H2].
    - right; left. exists (f + 32, f + 40). injection H1 as -> ->. split; [subst XP; left; reflexivity| cbn; clear; lia].
    - right; left. exists (DATA, DATA + 8). injection H1 as -> ->. split; [subst XP; right; left; reflexivity| cbn; clear; lia].
    - right; right. exists b. split; [exact Hb| cbn; split; [exact H1| exact H2]].
  Qed.

  (* [comment removed for export] *)
  Lemma close_out : forall ΣX stX mX OWX NEW CX Σ' m',
    linv ΣX stX mX OWX bo NEW CX -> CST - IOL_OUT_COST_A (zlength (sk_items k)) <= CX ->
    AHEAP Σ' OWX (NEW ++ LB) m' -> rt_credit RT Σ' = rt_credit RT ΣX -> stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
    agree_on (aclient_addr (OWX ++ (NEW ++ LB)) spa) mX m' ->
    ap_preA Σ' stX m' OWX (NEW ++ LB) E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(DATA, DATA + 8)]%Z ++ LIBW_A) m m'
    /\ rt_credit RT Σ - IOL_OUT_COST_A (zlength (sk_items k)) <= rt_credit RT Σ'
    /\ blocks_kept K stX OWX m m'.
  Proof.
    intros until m'. intros LI HCX HEAP' CR' ST' MI' AG'.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. ecu.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & CRED & _).
    destruct LI as (PREX & AX & KO & KI & KP & CR & LBOK).
    pose proof PREX as (HEAPX & ASX & IDSX & DCX & STX & _ & _ & _ & _ & MIX & CREDX & _). rewrite ESPA32 in AX. cbn [ar_RT ar_FR push amb] in CREDX, CR.
    split; [| split; [| split]].
    - unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASX | exact AG']|]. split; [exact IDSX|].
      split; [eapply data_cells_rt; [exact ASX | exact DCX | exact AG']|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSP STKu; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [clear - CREDX CR'; lia|]. pose proof FRMB as FRMu. clear - FRM0 FRMu. ecu. lia.
    - eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [exact AG3 | clear; lia]|].
      eapply ax_pres_trans.
      + unfold ax_pres. eapply agree_on_mono; [exact AX|]. intros a [HXa Ha]. split.
        * subst XP. intros HIN. apply HXa. cbn [app]. cbn [app rin_ivs fst snd] in HIN |- *.
          destruct HIN as [HIN|HIN]; [| exact HIN]. exfalso.
          destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha HIN G3 CEIL LOSP STKu; lia| |].
          -- destruct Ha as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; clear - Hlh HIN G4; unfold SEGTOP_A in G4; lia.
          -- pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
             destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O HIN. lia.
        * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [subst LB'; right; exact Hb| exact Hr]].
      + eapply (ax_pres_of_aclient (OWX ++ NEW) LB); [rewrite <- app_assoc; exact AG' | clear - SPAH; lia].
    - subst CSTb. clear - CR CR1 CR' HCX. lia.
    - eapply (blocks_kept_post K stX OWX (NEW ++ LB)); [| exact AG']. eapply (blocks_kept_pre K stX OW OWX LB); [exact KOW | exact AG3 |].
      split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP].
  Qed.

  (* [comment removed for export] *)
  Lemma close_pb : forall ΣX OWX NEW mX, @BnHeapA.AHEAP (push AR f 0) ΣX OWX (NEW ++ LB') mX -> @BnHeapA.AHEAP (push AR f 0) ΣX OWX (NEW ++ LB) mX.
  Proof.
    intros ΣX OWX NEW mX H. subst LB'.
    eapply (@frame_obj_close (push AR f 0)) with (f := f) (k := 0%nat) (b := (qp, f + 32, 8)); [left; reflexivity| | unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
    eapply AHEAP_permLB; [exact H|]. symmetry. apply Permutation_middle.
  Qed.

  (* [comment removed for export] *)
  Lemma out_raise : forall ΣX stX mX OWX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x26 x28 x29 x30 x31 : word) FX fcX,
    linv ΣX stX mX OWX bo [] CX -> CST - IOL_OUT_COST_A (zlength (sk_items k)) + 13 <= CX -> rw_cells ctasegs mX DATA [C8 (wz 0)] ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] ->
    implAp (abind (err_raise RS_i2o_list) (fun _ => CN) stX) ΣX Q
      (ost x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 (Z_to_bv 64 f) (Z_to_bv 64 f) x26 (Z_to_bv 64 (-1)) x28 x29 x30 x31 FX fcX mX IOL_RAISE).
  Proof.
    intros until fcX. intros LI HCX HDX FRLO.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu. pose proof (zlength_ge0 (sk_items k)) as N0.
    pose proof (keep_out _ _ _ _ _ _ _ LI) as (FRH & UWX & AGS & FRK). unfold frameH in FRH.
    pose proof LI as (PREX & AXX & KO & KI & KP & CR & LBOK). cbn [app] in PREX. cbn [ar_RT ar_FR push amb] in CR.
    pose proof PREX as (HEAPX & ASX & _ & _ & STX & _ & _ & _ & _ & MIX & CREDX & FRMX). rewrite ESPA in STX. cbn [ar_RT ar_FR push amb length] in CREDX, FRMX.
    (* [comment removed for export] *)
    destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_I2O_SCT_LIST_A 13 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    (* [comment removed for export] *)
    assert (KD : forall mA mB, ax_pres LB' spa LIBW_A mA mB -> rw_cells ctasegs mA DATA [C8 (wz 0)] -> rw_cells ctasegs mB DATA [C8 (wz 0)]).
    { intros mA mB AXab H. eapply rw_cells_agree; [| exact H|]; [intros wa' Hr Hc; exact (AXab wa' Hr Hc)|].
      intros a Ha. cbn in Ha. pose proof bD_seg as BD5. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha BD1 BD5 DLO DHI; lia| right; right; exists bD; split; [subst LB'; right; exact DIN| clear - Ha DLO DHI; lia]]. }
    assert (KL : forall mA mB, ax_pres LB' spa LIBW_A mA mB -> rw_cells ctasegs mA spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] -> rw_cells ctasegs mB spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]).
    { intros mA mB AXab H. eapply rw_cells_agree; [| exact H|]; [intros wa' Hr Hc; exact (AXab wa' Hr Hc)|].
      intros a Ha. cbn in Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEIL CE1 LOSP STKu SPAL; plia| left; clear - Ha TOP SPAH; plia]. }
    unfold err_raise. rewrite abind_assoc.
    intros XX Φ DD SAFE LINK. unfold ost, IOL_RAISE.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep.
    apply evt_done. eapply (implAp_elim _ ΣX ΣX _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    eapply implAp_abind.
    { pose proof (@ERR_new_walkA (push AR f 0) UK BE bo) as W1. unfold ap_stmtA in W1.
      eapply W1; [eapply ap_preA_weaken; [exact PREX| subst STKb; clear - STKu; ecu; lia| subst CSTb; clear - HCX CREDX CSTu N0; ecu; lia| subst FRMb'; clear - FRMu FRMX; ecu; lia]
                | reflexivity| rewrite ESPA; exact UWX| rewrite unsigned_lit by (clear; lia); rewrite ERAS; refine (uk_ctxJ_call j X0 _ _ E_new _ CTXJ); unfold IOL_NESTED_RET; clear; lia| apply cons_ne| reflexivity| exact KO| exact KI]. }
    intros r1 Σa ms1 PO1. cbv beta in PO1.
    destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & Fa & fca & mA & OWa & boa & -> & PREa & AXa & CRa & BKa & EBOa). subst boa.
    rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x336ec4) by (clear; lia).
    assert (LIA : linv Σa (snd r1) mA OWa bo [] (CX - ERR_NEW_COST)).
    { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := []) (NEW2 := []);
        [exact LI| cbn [app]; exact PREa| cbn [app]; exact AXa| intros a []| cbn [ar_RT push amb]; exact CRa| subst CSTb; unfold ERR_NEW_COST; clear - HCX CSTu N0; lia| exact BKa| constructor]. }
    pose proof (keep_out _ _ _ _ _ _ _ LIA) as (FRHa & UWa & AGSa & FRKa). unfold frameH in FRHa. pose proof (KD _ _ AXa HDX) as HDa. pose proof (KL _ _ AXa FRLO) as FRLa.
    pose proof LIA as (PREA & AXA & KOa & KIa & _). cbn [app] in PREA.
    pose proof PREA as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & CREDa & FRMa). rewrite ESPA in STa. cbn [ar_RT ar_FR push amb length] in CREDa, FRMa.
    rewrite abind_assoc. eapply implAp_abind.
    { (* [comment removed for export] *)
      apply implAp_from_evt. pose proof (munch_refl (@nil (Z * Z)) mA) as MU1. pose proof (wmono_refl ctasegs mA) as WM1. unfold MallocRep.wz. do 6 zstep. apply evt_done.
      pose proof (@ERR_set_debug_walkA (push AR f 0) UK BE STRCPY RS_i2o_list A_CT_OCT_C_A A_I2O_SCT_LIST_A bo fs fk ns nk LF LN) as W2. unfold ap_stmtA in W2.
      eapply W2; [eapply ap_preA_weaken; [exact PREA| subst STKb; clear - STKu; ecu; lia| subst CSTb; clear - HCX CREDa CSTu N0; ecu; lia| subst FRMb'; clear - FRMu FRMa; ecu; lia]
                | reflexivity| rewrite ESPA; exact UWa| rewrite unsigned_lit by (clear; lia); rewrite ERAS; refine (uk_ctxJ_call j X0 _ _ E_dbg _ CTXJ); unfold IOL_NESTED_RET; clear; lia| apply cons_ne
                | unfold A_CT_OCT_C_A, A_I2O_SCT_LIST_A, MallocRep.wz; cbn [rs_line RS_i2o_list]; repeat split; reflexivity| exact KOa| exact KIa]. }
    intros r2 Σb ms2 PO2. cbv beta in PO2.
    destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & Fb & fcb & mB & OWb & bob & -> & PREb & AXb & CRb & BKb & EBOb). subst bob.
    rewrite ESPA in AXb. cbn [ar_RT push amb] in CRb. rewrite (ret_pc_even 0x336ee0) by (clear; lia).
    assert (LIB : linv Σb (snd r2) mB OWb bo [] (CX - ERR_NEW_COST - ERR_SET_DEBUG_COST)).
    { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := []) (NEW2 := []);
        [exact LIA| cbn [app]; exact PREb| cbn [app]; exact AXb| intros a []| cbn [ar_RT push amb]; exact CRb| subst CSTb; unfold ERR_NEW_COST, ERR_SET_DEBUG_COST; clear - HCX CSTu N0; lia| exact BKb| constructor]. }
    pose proof (keep_out _ _ _ _ _ _ _ LIB) as (FRHb & UWb & AGSb & FRKb). unfold frameH in FRHb. pose proof (KD _ _ AXb HDa) as HDb. pose proof (KL _ _ AXb FRLa) as FRLb.
    pose proof LIB as (PREB & AXB & KOb & KIb & _). cbn [app] in PREB.
    pose proof PREB as (_ & _ & _ & _ & STb & _ & _ & _ & _ & MIb & CREDb & FRMb2). rewrite ESPA in STb. cbn [ar_RT ar_FR push amb length] in CREDb, FRMb2.
    (* [comment removed for export] *)
    eapply implAp_abind.
    { apply implAp_from_evt. pose proof (munch_refl (@nil (Z * Z)) mB) as MU2. pose proof (wmono_refl ctasegs mB) as WM2. unfold MallocRep.wz. do 4 zstep. apply evt_done.
      pose proof (@ERR_set_error_closedA (push AR f 0) UK BE RS_i2o_list 50 105 bo) as W3. unfold ERR_set_error_specA, ap_stmtA in W3.
      eapply W3; [eapply ap_preA_weaken; [exact PREB| subst STKb; clear - STKu; ecu; lia| subst CSTb; clear - HCX CREDb CSTu N0; ecu; lia| subst FRMb'; clear - FRMu FRMb2; ecu; lia]
                | reflexivity| rewrite ESPA; exact UWb| rewrite unsigned_lit by (clear; lia); rewrite ERAS; refine (uk_ctxJ_call j X0 _ _ E_err _ CTXJ); unfold IOL_NESTED_RET; clear; lia| apply cons_ne
                | unfold ERR_LIB_SYS, MallocRep.wz; cbn [rs_code RS_i2o_list]; unfold ERR_LIB_CT; repeat split; first [reflexivity | (clear; lia)]| exact KOb| exact KIb]. }
    intros r3 Σc ms3 PO3. cbv beta in PO3.
    destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & PREc & AXc & CRc & BKc & EBOc). subst boc.
    rewrite ESPA in AXc. cbn [ar_RT push amb] in CRc. rewrite (ret_pc_even 0x336ef4) by (clear; lia).
    assert (LIC : linv Σc (snd r3) mC OWc bo [] (CX - 13)).
    { replace (CX - 13) with (CX - ERR_NEW_COST - ERR_SET_DEBUG_COST - ERR_SET_ERROR_COST) by (unfold ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST; clear; lia).
      eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := []) (NEW2 := []);
        [exact LIB| cbn [app]; exact PREc| cbn [app]; exact AXc| intros a []| cbn [ar_RT push amb]; exact CRc| subst CSTb; unfold ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST; clear - HCX CSTu N0; lia| exact BKc| constructor]. }
    pose proof (keep_out _ _ _ _ _ _ _ LIC) as (FRHc & UWc & AGSc & FRKc). unfold frameH in FRHc. pose proof (KD _ _ AXc HDb) as HDc. pose proof (KL _ _ AXc FRLb) as FRLc.
    pose proof LIC as (PREC & _). cbn [app] in PREC. pose proof PREC as (HEAPc & _ & _ & _ & STc & _ & _ & _ & _ & MIc & _). rewrite ESPA in STc.
    (* [comment removed for export] *)
    assert (FRF : rw_cells ctasegs mC spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk]).
    { apply (proj2 (SctRepA.rw_cells_app ctasegs mC spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk])). split; [exact FRLc|]. cbn [cells_size csize Nat.add]. exact FRKc. }
    intros X2 Φ2 D2 SAFE2 LINK2. change (Z_to_bv 64 3370740) with (wz IOL_EXIT).
    eapply (@iol_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact (close_pb _ _ [] _ HEAPc)| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STc| exact CEIL| clear - LOSP STKu SPAL; lia
      | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIc| exact FRF| exact FRHc| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply (implAp_elim _ Σc Σ' _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| exact LIVE'].
    apply KN. rewrite (v_addiw0_int (-1)) by (clear; lia).
    destruct (close_out _ _ _ _ [] (CX - 13) _ _ LIC ltac:(clear - HCX; ecu; lia) HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK').
    unfold outpost_fail. do 16 eexists. exists m', OWc. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|]. split.
    - eapply sk_repA_agree; [exact AG'| | exact (keep_sk _ _ _ _ _ _ _ LIC)]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha].
    - eapply rw_cells_agree; [exact AG'| exact HDc|]. intros a Ha. cbn in Ha. right; right. exists bD. split; [apply in_or_app; right; exact DIN| clear - Ha DLO DHI; lia].
  Qed.

  (* [comment removed for export] *)
  Let CX0 : Z := CSTb - IOL_LEN_COST_A (zlength (sk_items k)) - IOL_MALLOC_COST_A.

  (* [comment removed for export] *)
  Lemma data_cells : forall ΣX stX mX OWX boX d AD tot CX a n,
    linv ΣX stX mX OWX boX [(d, AD, tot)] CX -> AD <= a -> 0 <= n -> a + n <= AD + tot ->
    exists junk, rw_cells ctasegs mX a [CB (Z.to_nat n) junk].
  Proof.
    intros until n. intros (PREX & _) H1 H2 H3. destruct PREX as (HEAPX & _). cbn [app] in HEAPX.
    pose proof (@AH_acc (push AR f 0) _ _ _ _ (d, AD, tot) HEAPX ltac:(apply in_or_app; right; left; reflexivity)) as [W _]. cbn [blk_addr blk_size fst snd] in W.
    apply wr_at_rw_CB; [| exact H2]. destruct W as (W1 & W2 & W3). split; [clear - W1 H1; lia|]. split; [clear - W2 H3; lia|].
    intros i Hi. replace (a + i) with (AD + (a - AD + i)) by (clear; lia). apply W3. clear - Hi H1 H3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma out_tail : forall ΣC mC (d : bptr) (AD tot : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x28 x29 x30 x31 : word) FC fcC (pv : Z),
    Forall (fun x => sct_complete x = true) (sk_items k) -> tot = 2 + i2o_sum (sk_items k) -> tot <= MAX_SCT_LIST_SIZE ->
    linv ΣC st mC OW bo [(d, AD, tot)] (CX0 - zlength (sk_items k)) -> off_fr f 0 (d, AD, tot) -> ~ In d (map blk_id (OW ++ LB)) ->
    rw_cells ctasegs mC (f + 32) [C8 (Z_to_bv 64 pv)] ->
    rw_cells ctasegs mC spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 f)] ->
    rw_cells ctasegs mC DATA [C8 (wz AD)] ->
    implAp (CS tot d st) ΣC Q (ost x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 tot) x28 x29 x30 x31 FC fcC mC IOL_OK).
  Proof.
    intros until pv. intros CPLA Etot TMAX LI OFD DFR HP FRLO HDX. unfold MallocRep.wz in HDX.
    pose proof (i2o_sum_ge0 adr (sk_items k) OKALL) as SUMB0.
    destruct (data_cells _ _ _ _ _ _ _ _ _ AD 2 LI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Etot SUMB0; lia)) as [j02 R02].
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu. pose proof (zlength_ge0 (sk_items k)) as N0.
    pose proof (keep_out _ _ _ _ _ _ _ LI) as (FRH & UWX & AGS & FRK). unfold frameH in FRH.
    pose proof LI as (PREX & AXX & KO & KI & KP & CR & LBOK). cbn [ar_RT ar_FR push amb] in CR.
    pose proof PREX as (HEAPX & ASX & _ & _ & STX & _ & _ & _ & _ & MIX & CREDX & FRMX). rewrite ESPA in STX. cbn [ar_RT ar_FR push amb length] in CREDX, FRMX.
    pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (_ & _ & BND & _ & DJL & DJO).
    pose proof (BND (d, AD, tot) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (D1 & _ & D3 & D4). cbn [blk_addr blk_size fst snd] in D1, D3, D4.
    unfold off_fr in OFD. change (fs_size 0) with 64 in OFD. cbn [blk_addr blk_size fst snd] in OFD.
    pose proof (FRESH bD (in_or_app _ _ _ (or_intror DIN))) as OFB. unfold off_fr in OFB. change (fs_size 0) with 64 in OFB.
    pose proof (DJL (d, AD, tot) bD ltac:(left; reflexivity) ltac:(subst LB'; right; exact DIN)) as DJD. cbn [blk_addr blk_size fst snd] in DJD.
    pose proof SUMB0 as SUMB. clear SUMB0. nrm.
    assert (DIN2 : In (d, AD, tot) (OW ++ [(d, AD, tot)] ++ LB')) by (apply in_or_app; right; left; reflexivity).
    assert (BIN2 : In bD (OW ++ [(d, AD, tot)] ++ LB')) by (apply in_or_app; right; right; subst LB'; right; exact DIN).
    assert (QIN2 : In (qp, f + 32, 8) (OW ++ [(d, AD, tot)] ++ LB')) by (apply in_or_app; right; right; subst LB'; left; reflexivity).
    cbn [app] in HEAPX.
    ablock HEAPX DIN2 ACCD OFFD. ablock HEAPX BIN2 ACCB OFFB. cbn [blk_addr blk_size fst snd] in ACCD, OFFD. unfold SHLO, SHHI in OFFD, OFFB.
    fz OFFD. fz OFFB. fz OFD. fz OFB. fz DJD. fz G5. fz D4.
    intros XX Φ DD SAFE LINK. unfold ost, IOL_OK.
    pose proof (munch_refl [(f + 32, f + 40); (AD, AD + 2)]%Z mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    assert (OFFW : offshW [(f + 32, f + 40); (AD, AD + 2)]%Z) by (thaw G5; thaw OFFD; cbn [offshW]; unfold SHLO, SHHI; clear - G4 G5 OFFD D1 D3 Etot SUMB; lia).
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. sfalse. zstep.
    thaw OFD. thaw OFB. zstep. fz OFD. fz OFB.
    destruct (cb_split2A _ AD 1 1 j02 R02 ltac:(clear; lia) ltac:(clear; lia)) as [R0a R0b]. change (Z.to_nat 1) with 1%nat in R0a, R0b. clear R02.
    (* [comment removed for export] *)
    thaw OFD. thaw DJD. thaw OFB. do 7 zstep. fz OFD. fz DJD. fz OFB.   (* [comment removed for export] *)
    btaken.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mE end.
    match goal with H : munch _ mC mE |- _ => rename H into MUE end. match goal with H : wmono ctasegs mC mE |- _ => rename H into WME end.
    match goal with H : mem_inv ctasegs mE |- _ => rename H into MIE end.
    assert (STE : stk ctasegs mE lo spa) by (first [assumption| eapply stk_transport; [exact STX| exact MUE| exact WME| cbn; clear; lia]]).
    assert (LIE : linv ΣC st mE OW bo [(d, AD, tot)] (CX0 - zlength (sk_items k))).
    { eapply (linv_munch _ _ _ _ _ _ _ _ _ LI MUE WME MIE STE). constructor; [cbn [fst snd]; right; left; reflexivity| constructor; [cbn [fst snd]; right; right; right; exists (d, AD, tot); split; [left; reflexivity| cbn; clear - Etot SUMB; lia]| constructor]]. }
    pose proof (keep_out _ _ _ _ _ _ _ LIE) as (FRHE & _ & _ & FRKE). unfold frameH in FRHE.
    pose proof LIE as (PREE & _). cbn [app] in PREE. pose proof PREE as (HEAPE & _).
    assert (FRF' : rw_cells ctasegs mE spa ([CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 f)] ++ [CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk])).
    { apply (proj2 (SctRepA.rw_cells_app ctasegs mE spa _ _)). split; [exact FRLO| cbn [cells_size csize Nat.add]; exact FRKE]. }
    pose proof (rw_cells_cb_first mE spa _ 4 FRF') as FRF.   (* [comment removed for export] *) cbn [cb_first csize cbytes app] in FRF. clear FRF'.
    apply evt_done. change (Z_to_bv 64 3370740) with (wz IOL_EXIT).
    eapply (@iol_epi_cps AR _) with (lo := lo) (LB := [(d, AD, tot)] ++ LB) (gj := gj) (hrest := []);
      [exact (close_pb _ _ [(d, AD, tot)] _ HEAPE)| | exact STE| exact CEIL| clear - LOSP STKu SPAL; lia
      | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIE| exact FRF| exact FRHE| reflexivity|].
    { intros b [<-|Hb]; [| exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))]. thaw OFD. unfold off_fr. change (fs_size 0) with 64. cbn [blk_addr blk_size fst snd]. exact OFD. }
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply (implAp_elim _ ΣC Σ' _ _ XX Φ DD); [| exact SAFE| exact LINK| exact LIVE'].
    replace (CS tot) with (CS (2 + i2o_sum (sk_items k))) by (rewrite <- Etot; reflexivity). apply KS.
    pose proof (mcost_le 0 ltac:(clear; lia)) as MC0.
    destruct (close_out _ _ _ _ [(d, AD, tot)] (CX0 - zlength (sk_items k)) _ _ LIE ltac:(subst CX0 CSTb; clear; ecu; lia) HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK').
    pose proof LIE as (_ & _ & _ & _ & _ & _ & LBOK1). apply Forall_inv in LBOK1.
    unfold outpost_ok. do 16 eexists. exists m', AD, tot.
    split; [rewrite (v_addiw0_int tot) by (unfold MAX_SCT_LIST_SIZE in TMAX; clear - Etot SUMB TMAX; lia); reflexivity|].
    split; [exact Etot|]. split; [clear - Etot SUMB TMAX; lia|].
    split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|]. split; [exact DFR|]. split; [exact (lbokA_pop _ _ _ LBOK1)|].
    split. { eapply sk_repA_agree; [exact AG'| | exact (keep_sk _ _ _ _ _ _ _ LIE)]. intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; apply in_or_app; right; exact (sk_repA_blocks_in _ _ _ _ _ SK Hb)| exact Ha]. }
    split; [exact CPLA|].
    split. { unfold MallocRep.wz. eapply rw_cells_agree; [exact AG'| exact HDX|]. intros a Ha. cbn in Ha. right; right. exists bD. split; [apply in_or_app; right; apply in_or_app; right; exact DIN| clear - Ha DLO DHI; lia]. }
    pose proof (AH_acc _ _ _ _ (d, AD, tot) HEAP' ltac:(apply in_or_app; right; left; reflexivity)) as [WB _]. cbn [blk_addr blk_size fst snd] in WB.
    destruct (wr_at_rw_CB m' AD tot WB ltac:(clear - Etot SUMB; lia)) as [bs RB].
    exists bs. split; [pose proof (rw_cells_bytes_at _ _ _ _ RB) as BA; cbn [cells_bytes cbytes] in BA; rewrite app_nil_r in BA; exact BA|].
    pose proof RB as [[WF _] _]. cbn in WF. clear - WF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma item_factsO : forall ΣX stX mX OWX boX NEW CX done x t,
    linv ΣX stX mX OWX boX NEW CX -> sk_items k = done ++ x :: t ->
    let SA := adr (sk_blk k) in let num := sk_num k in let i := zlength done in
    exists q na,
      sk_data k = Some (q, na) /\ In (sk_blk k, SA, STACK_SIZE) (OWX ++ NEW ++ LB') /\ SA mod 16 = 0 /\ In (q, adr q, 8 * na) (OWX ++ NEW ++ LB') /\ adr q mod 16 = 0 /\ num <= na
      /\ 0 <= i < num /\ num < 2^23
      /\ ro_cells ctasegs mX SA [C4 (Z_to_bv 64 num)] /\ ro_cells ctasegs mX (SA + 8) [C8 (Z_to_bv 64 (adr q))] /\ ro_cells ctasegs mX (adr q + 8 * i) [C8 (Z_to_bv 64 (adr (sc_blk x)))]
      /\ sct_repA mX LB adr x /\ sct_ok adr x /\ In (sc_blk x, adr (sc_blk x), SCT_SIZE) (OWX ++ NEW ++ LB') /\ In (sc_blk x, adr (sc_blk x), SCT_SIZE) LB /\ adr (sc_blk x) mod 16 = 0
      /\ rw_cells ctasegs mX (adr (sc_blk x)) (sct_cells adr x (-1) 0).
  Proof.
    intros until t. intros LI EQ. cbn zeta. pose proof (keep_sk _ _ _ _ _ _ _ LI) as SKX.
    destruct LI as (PREX & _). destruct PREX as (HEAP & _).
    pose proof (sk_repA_free_view _ _ _ _ SKX) as ((HN & HDp & _) & HIN & HDB & DCS & _ & _).
    pose proof SKX as ((_ & ALS) & _ & HDD & HF & _).
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; lia).
    pose proof (zlength_ge0 done) as D0. pose proof (zlength_ge0 t) as T0.
    destruct (sk_data k) as [[q na]|] eqn:ED; [| exfalso; rewrite HDD in EQ; destruct done; discriminate].
    destruct HDD as (HQ & ALQ & HNA & HNA2 & _). cbn [optr] in HDp, DCS.
    assert (INC2 : forall b, In b LB -> In b (NEW ++ LB')) by (intros b Hb; apply in_or_app; right; subst LB'; right; exact Hb).
    assert (INC : forall b, In b LB -> In b (OWX ++ NEW ++ LB')) by (intros b Hb; apply in_or_app; right; exact (INC2 b Hb)).
    exists q, na. split; [reflexivity|]. split; [exact (INC _ HIN)|]. split; [exact ALS|]. split; [exact (INC _ HQ)|]. split; [exact ALQ|]. split; [exact HNA|].
    split; [clear - LEN D0 T0; lia|]. split; [clear - HNA HNA2; lia|].
    unfold MallocRep.wz, SKO_DATA in HN, HDp. split; [exact HN|]. split; [exact HDp|].
    rewrite EQ in DCS. pose proof (sk_data_cellsA_app _ _ _ _ _ _ DCS) as [DX _]. rewrite Z.add_0_l in DX. unfold MallocRep.wz in DX. split; [exact DX|].
    assert (HX : sct_repA mX LB adr x) by (apply (proj1 (Forall_forall _ _) HF); rewrite EQ; apply in_or_app; right; left; reflexivity).
    split; [exact HX|]. split; [exact (sct_ok_of_repA _ _ _ _ _ _ HEAP (sct_repA_relist _ _ _ _ _ HX (fun b Hb => INC2 b (sct_repA_blocks_in _ _ _ _ HX b Hb))))|].
    pose proof HX as (XIN & XAL & XC & _). split; [exact (INC _ XIN)|]. split; [exact XIN|]. split; [exact XAL| exact XC].
  Qed.

  (* [comment removed for export] *)
  Lemma out_loop : forall rest done acc ΣC mC (d : bptr) (AD tot : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) FC fcC,
    sk_items k = done ++ rest -> rest <> [] -> Forall (fun x => sct_complete x = true) (sk_items k) -> acc = 2 + i2o_sum done -> tot = 2 + i2o_sum (sk_items k) -> tot <= MAX_SCT_LIST_SIZE ->
    linv ΣC st mC OW bo [(d, AD, tot)] (CX0 - zlength done) -> off_fr f 0 (d, AD, tot) -> ~ In d (map blk_id (OW ++ LB)) ->
    rw_cells ctasegs mC (f + 32) [C8 (Z_to_bv 64 (AD + acc))] ->
    rw_cells ctasegs mC spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 f)] ->
    rw_cells ctasegs mC DATA [C8 (wz AD)] ->
    implAp (CS tot d st) ΣC Q (ost x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-1)) (Z_to_bv 64 (zlength done)) x23 (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 acc) x28 x29 x30 x31 FC fcC mC IOL_WHEAD).   (* [comment removed for export] *)
  Proof.
    induction rest as [|x t IH]; intros until fcC; intros EQ NEr CPLA Eacc Etot TMAX LI OFD DFR HP FRLO HDX; [exfalso; exact (NEr eq_refl)|]. unfold MallocRep.wz in HDX.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu. pose proof (zlength_ge0 (sk_items k)) as N0.
    pose proof LI as (PREX & _). cbn [app] in PREX. pose proof PREX as (HEAPC & _ & _ & _ & STC & _ & _ & _ & _ & MIC & _). rewrite ESPA in STC.
    pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LI) as (_ & _ & BND & _ & DJL & DJO).
    pose proof (BND (d, AD, tot) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (D1 & _ & D3 & D4). cbn [blk_addr blk_size fst snd] in D1, D3, D4.
    pose proof (zlength_ge0 done) as D0. pose proof (zlength_ge0 t) as T0.
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; clear; lia).
    unfold off_fr in OFD. change (fs_size 0) with 64 in OFD. cbn [blk_addr blk_size fst snd] in OFD.
    pose proof (FRESH bD (in_or_app _ _ _ (or_intror DIN))) as OFB. unfold off_fr in OFB. change (fs_size 0) with 64 in OFB.
    pose proof (DJL (d, AD, tot) bD ltac:(left; reflexivity) ltac:(subst LB'; right; exact DIN)) as DJD. cbn [blk_addr blk_size fst snd] in DJD.
    pose proof (i2o_sum_ge0 adr (sk_items k) OKALL) as SUMB. nrm.
    assert (CPLx : sct_complete x = true) by (apply (proj1 (Forall_forall _ _) CPLA); rewrite EQ; apply in_or_app; right; left; reflexivity).
    fz OFD. fz OFB. fz DJD. fz G5. fz D4.
    intros XX Φ DD SAFE LINK. unfold ost, IOL_WHEAD.
    pose proof (munch_refl [(f + 32, f + 40)]%Z mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    (* [comment removed for export] *)
    assert (P2R : 3 <= AD + acc + 2 /\ AD + acc <= AD + tot /\ AD + tot < 2 ^ 63).
    { pose proof OKALL as OK3. rewrite EQ in OK3. apply Forall_app in OK3 as [OKd OKr]. pose proof OKr as OKxt. apply Forall_cons_iff in OKr as [_ OKt].
      pose proof (i2o_sum_ge0 adr done OKd) as Bd. pose proof (i2o_sum_ge0 adr (x :: t) OKxt) as Bxt.
      assert (ES : i2o_sum (sk_items k) = i2o_sum done + i2o_sum (x :: t)) by (rewrite EQ, i2o_sum_app; reflexivity).
      pose proof Etot as ET. rewrite ES in ET. subst acc. thaw D4. clear - D1 D3 D4 Bd Bxt ET CE2 CE3 CEIL. nrm. lia. }
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep.
    thaw OFD. thaw OFB. zstep. fz OFD. fz OFB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : munch _ mC m2 |- _ => rename H into MU2 end. match goal with H : wmono ctasegs mC m2 |- _ => rename H into WM2 end.
    match goal with H : mem_inv ctasegs m2 |- _ => rename H into MI2 end.
    assert (ST2 : stk ctasegs m2 lo spa) by (first [assumption| eapply stk_transport; [exact STC| exact MU2| exact WM2| cbn; clear; lia]]).
    assert (LI2 : linv ΣC st m2 OW bo [(d, AD, tot)] (CX0 - zlength done)).
    { eapply (linv_munch _ _ _ _ _ _ _ _ _ LI MU2 WM2 MI2 ST2). constructor; [cbn [fst snd]; right; left; reflexivity| constructor]. }
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
    (* [comment removed for export] *)
    destruct (item_factsO _ _ _ _ _ _ _ done x t LI2 EQ) as (q & na & ED & KIN & KAL & QIN & QAL & NA & IR & NR & RNUM & RDAT & RITEM & REPX & OKX & XIN & XINL & XAL & HX).
    pose proof LI2 as (PRE2 & _). cbn [app] in PRE2. pose proof PRE2 as (HEAP2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRED2 & FRM2). cbn [ar_RT ar_FR push amb length] in CRED2, FRM2.
    pose proof LI2 as (_ & _ & _ & _ & _ & CR2 & _). cbn [ar_RT ar_FR push amb] in CR2.
    pose proof (AH_range_gen _ _ _ _ _ HEAP2 XIN) as (XB0 & _ & _ & XBC & _). cbn [blk_addr blk_size fst snd] in XB0, XBC.
    pose proof (FRESH _ (in_or_app _ _ _ (or_intror XINL))) as OFX. unfold off_fr in OFX. change (fs_size 0) with 64 in OFX. cbn [blk_addr blk_size fst snd] in OFX.
    pose proof (DJL (d, AD, tot) _ ltac:(left; reflexivity) ltac:(subst LB'; right; exact XINL)) as DJX. cbn [blk_addr blk_size fst snd] in DJX. nrm.
    (* [comment removed for export] *)
    pose proof OKX as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
    assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q' n']|] eqn:ES; [pose proof (SIGP q' n' eq_refl); clear - H; lia| clear; lia]).
    assert (LXR : 0 <= i2o_sct_len x <= 196702) by (unfold i2o_sct_len; destruct (sc_version x =? 0); clear - ELR BLR SL; lia).
    clear VR HR GR SIGP BLOBP LOGP ELR BLR EXTP EXTL BLBL SL.
    assert (ACCB : 0 <= acc /\ acc + 2 + i2o_sct_len x + i2o_sum t = tot).
    { pose proof OKALL as OK3. rewrite EQ in OK3. apply Forall_app in OK3 as [OKd OKr]. apply Forall_cons_iff in OKr as [_ OKt].
      pose proof (i2o_sum_ge0 adr done OKd) as Bd. pose proof (i2o_sum_ge0 adr t OKt) as Bt.
      assert (ES : i2o_sum (sk_items k) = i2o_sum done + (2 + i2o_sct_len x + i2o_sum t)) by (rewrite EQ, i2o_sum_app; reflexivity).
      pose proof Etot as ET. rewrite ES in ET. subst acc. clear - Bd Bt ET. lia. }
    pose proof (i2o_sum_ge0 adr t ltac:(pose proof OKALL as OK3; rewrite EQ in OK3; apply Forall_app in OK3 as [_ OKr]; apply Forall_cons_iff in OKr as [_ OKt]; exact OKt)) as BT.
    fz OFX. fz DJX.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (@OPENSSL_sk_value_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (q := q) (SA := adr (sk_blk k)) (num := sk_num k) (D := adr q) (na := na) (i := zlength done) (V := adr (sc_blk x));
        rewrite ?ESPA; [exact HEAP2| exact ST2| exact MI2| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
        | exact KIN| exact KAL| exact QIN| exact QAL| exact NA| exact RNUM| exact RDAT| exact IR| clear - NR; lia| exact RITEM| reflexivity| reflexivity]. }
    cbv beta. intros ms2 PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mD & -> & MUD & WMD & MID & STD & _). rewrite ?ESPA in MUD. rewrite ?ESPA in STD.
    rewrite (ret_pc_even 0x336d08) by (clear; lia).
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in HX; [| rewrite SctRep.sct_cells_size; cbn; clear - XBC CEIL LOSP STKu SPAL; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in HP; [| cbn; thaw G5; clear - G3 CEIL LOSP STKu SPAL; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in FRLO; [| cbn; clear; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUD WMD) in HDX; [| cbn; clear - BD2 DLO DHI CEIL LOSP STKu SPAL; lia].
    pose proof (linv_munch _ _ _ _ _ _ _ _ _ LI2 MUD WMD MID STD ltac:(constructor; [cbn [fst snd]; left; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LID.
    pose proof LID as (PRED & _). cbn [app] in PRED. pose proof PRED as (HEAPD & _).
    assert (REPD : sct_repA mD LB adr x).
    { pose proof (keep_sk _ _ _ _ _ _ _ LID) as SKD. pose proof SKD as (_ & _ & _ & HF & _). apply (proj1 (Forall_forall _ _) HF). rewrite EQ. apply in_or_app. right. left. reflexivity. }
    (* [comment removed for export] *)
    destruct (data_cells _ _ _ _ _ _ _ _ _ (AD + acc + 2) (i2o_sct_len x) LID ltac:(clear - ACCB; lia) ltac:(clear - LXR; lia) ltac:(clear - ACCB BT; lia)) as [jo RX].
    apply evt_done. clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mD) as MU. pose proof (wmono_refl ctasegs mD) as WM.
    apply cps_from_evt'. unfold MallocRep.wz.
    (* [comment removed for export] *)
    zstep. zstep.
    apply evt_done. change (Z_to_bv 64 3367120) with (wz I2O_SCT_A).
    thaw OFD. thaw OFX. thaw DJX.
    eapply (@i2o_sct_write_cpsA (push AR f 0) _) with (lo := lo) (STK := STKb) (OW := OW) (LB := [(d, AD, tot)] ++ LB') (adr := adr) (sc := x) (PP := f + 32) (P := AD + acc + 2)
        (bPP := (qp, f + 32, 8)) (bP := (d, AD, tot)); rewrite ?ESPA.
    - exact HEAPD.
    - exact STD.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    - subst STKb. clear - LOSP SPAL. lia.
    - subst STKb. ecu. clear - STKu. lia.
    - clear - TOP SPAH. plia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MID.
    - reflexivity.
    - cbn [ar_FR push amb length]. clear - FRM2 FRMu. lia.
    - cbn [ar_RT push amb]. subst CX0 CSTb. clear - CR2 CRED0 CR1 CSTu D0 T0 LEN. ecu. unfold sk_num in *. lia.
    - eapply sct_repA_relist; [exact REPD|]. intros b Hb. apply in_or_app. right. subst LB'. right. exact (sct_repA_blocks_in _ _ _ _ REPD b Hb).
    - exact CPLx.
    - apply in_or_app. right. apply in_or_app. right. subst LB'. left. reflexivity.
    - cbn. clear. lia.
    - cbn. clear. lia.
    - clear - G2. Z.div_mod_to_equations. lia.
    - exact HP.
    - apply in_or_app. right. apply in_or_app. left. left. reflexivity.
    - cbn. clear - ACCB. lia.
    - cbn. clear - ACCB BT. lia.
    - exact RX.
    - intros b Hb. pose proof (DJL (d, AD, tot) b ltac:(left; reflexivity) ltac:(subst LB'; right; exact (sct_repA_blocks_in _ _ _ _ REPD b Hb))) as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ ACCB BT LXR. lia.
    - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror (sct_repA_blocks_in _ _ _ _ REPD b Hb)))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. clear - O. lia.
    - clear - OFD ACCB BT LXR. lia.
    - reflexivity.
    - reflexivity.
    - fz OFD. fz OFX. fz DJX.
      intros ΣE mE y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 FE fcE HEAPE CRE ELE STE MIE AGE HPE.
      rewrite (ret_pc_even 0x336d10) by (clear; lia). cbn [ar_RT ar_PMc push amb] in CRE, ELE |- *. rewrite ?ESPA in STE. rewrite ?ESPA in AGE. unfold MallocRep.wz in HPE.
      assert (LIE : linv ΣE st mE OW bo [(d, AD, tot)] (CX0 - zlength done - 1)).
      { eapply (oinv_heapN _ _ _ _ _ _ _ _ _ _ _ _ KH) with (L1 := OW ++ [(d, AD, tot)] ++ LB') (NEW' := [(d, AD, tot)]) (cst := 1);
          [exact LID| | intros b Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; right; exact Hb]| exact HEAPE| pose proof LID as (_ & _ & _ & _ & _ & _ & LBOK); exact LBOK
          | exact MIE| exact STE| cbn [ar_RT push amb]; clear - CRE; lia| subst CX0 CSTb; clear - CSTu D0 T0 LEN; ecu; unfold sk_num in *; lia].
        eapply agree_on_mono; [exact AGE|]. intros a (Ha & HXa & HNa). split; [exact Ha|]. cbn [outside fst snd]. split; [| split; [| exact I]].
        + subst XP. cbn [rin_ivs fst snd] in HXa. clear - HXa. lia.
        + intros Hr. apply HNa. exists (d, AD, tot). split; [left; reflexivity| cbn; clear - Hr ACCB BT LXR; lia]. }
      pose proof (keep_out _ _ _ _ _ _ _ LIE) as (FRHE & UWE & AGSE & FRKE). unfold frameH in FRHE.
      pose proof LIE as (PREE & _). cbn [app] in PREE. pose proof PREE as (HEAPE' & _ & _ & _ & STE' & _ & _ & _ & _ & MIE' & _). rewrite ESPA in STE'.
      assert (KA : forall A' cs, rw_cells ctasegs mD A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> aclient_addr (OW ++ [(d, AD, tot)] ++ LB') spa a /\ ~ (f + 32 <= a < f + 40) /\ ~ (AD + acc + 2 <= a < AD + acc + 2 + i2o_sct_len x)) -> rw_cells ctasegs mE A' cs).
      { intros A' cs H HA. eapply rw_cells_agree; [exact AGE| exact H|]. intros a Ha. destruct (HA a Ha) as (H1 & H2 & H3). split; [exact H1|]. cbn [outside fst snd]. clear - H2 H3. repeat split; try exact I; lia. }
      apply KA in FRLO; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; thaw G5; split; [left; clear - Ha TOP SPAH GSZ; plia| clear - Ha G3 D3 CEIL LOSP STKu SPAL ACCB BT LXR; split; lia]].
      thaw DJD. thaw OFB.
      apply KA in HDX; [| intros a Ha; cbn in Ha; split; [right; right; exists bD; split; [apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact DIN| clear - Ha DLO DHI; lia]| clear - Ha OFB DJD DLO DHI ACCB BT LXR; split; lia]].
      fz DJD. fz OFB. clear KA.
      destruct (data_cells _ _ _ _ _ _ _ _ _ (AD + acc) 2 LIE ltac:(clear - ACCB; lia) ltac:(clear; lia) ltac:(clear - ACCB BT LXR; lia)) as [j2 R2].
      destruct (cb_split2A _ (AD + acc) 1 1 j2 R2 ltac:(clear; lia) ltac:(clear; lia)) as [R2a R2b]. change (Z.to_nat 1) with 1%nat in R2a, R2b. clear R2.
      cbn [app] in HEAPE.
      assert (DIN2 : In (d, AD, tot) (OW ++ [(d, AD, tot)] ++ LB')) by (apply in_or_app; right; left; reflexivity).
      ablock HEAPE DIN2 ACCD OFFD. cbn [blk_addr blk_size fst snd] in ACCD, OFFD. unfold SHLO, SHHI in OFFD.
      clear MU WM. pose proof (munch_refl [(AD + acc, AD + acc + 2)]%Z mE) as MU. pose proof (wmono_refl ctasegs mE) as WM.
      assert (OFFW : offshW [(AD + acc, AD + acc + 2)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - OFFD D1 D3 ACCB BT LXR; lia).
      fz OFFD.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 LXR; lia| clear K0].
      thaw OFD. thaw DJD. thaw DJX. thaw OFB.
      remember (AD + acc) as P2 eqn:EP2.
      step_until 2083400%Z.
      subst P2.
      fz OFD. fz DJD. fz DJX. fz OFB.
      rewrite (swrap32_small (zlength done + 1)) by (unfold sk_num in LEN, NR; clear - D0 T0 LEN NR; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      match goal with H : munch _ mE mG |- _ => rename H into MUG end. match goal with H : wmono ctasegs mE mG |- _ => rename H into WMG end.
      match goal with H : mem_inv ctasegs mG |- _ => rename H into MIG end.
      assert (STG : stk ctasegs mG lo spa) by (first [assumption| eapply stk_transport; [exact STE'| exact MUG| exact WMG| cbn; clear; lia]]).
      assert (LIG : linv ΣE st mG OW bo [(d, AD, tot)] (CX0 - zlength done - 1)).
      { eapply (linv_munch _ _ _ _ _ _ _ _ _ LIE MUG WMG MIG STG). constructor; [cbn [fst snd]; right; right; right; exists (d, AD, tot); split; [left; reflexivity| cbn; clear - ACCB BT LXR; lia]| constructor]. }
      pose proof LIG as (PREG & _). cbn [app] in PREG. pose proof PREG as (HEAPG & _).
      pose proof (keep_sk _ _ _ _ _ _ _ LIG) as SKG. destruct (sk_repA_free_view _ _ _ _ SKG) as ((RNUMG & _ & _) & _). unfold MallocRep.wz in RNUMG.
      eapply evt_cut.
      { eapply (@OPENSSL_sk_num_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (SA := adr (sk_blk k)) (num := sk_num k);
          rewrite ?ESPA; [exact HEAPG| exact STG| exact MIG| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
          | exact KIN| exact KAL| exact RNUMG| unfold sk_num in *; clear - NR D0 T0 LEN; lia| reflexivity]. }
      cbv beta. intros ms3 PO.
      destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & mF & -> & MUF & WMF & MIF & STF & _). rewrite ?ESPA in MUF. rewrite ?ESPA in STF.
      rewrite (ret_pc_even 0x336d7c) by (clear; lia).
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in HPE; [| cbn; thaw G5; clear - G3 CEIL LOSP STKu SPAL; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in FRLO; [| cbn; clear; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUF WMF) in HDX; [| cbn; clear - BD2 DLO DHI CEIL LOSP STKu SPAL; lia].
      pose proof (linv_munch _ _ _ _ _ _ _ _ _ LIG MUF WMF MIF STF ltac:(constructor; [cbn [fst snd]; left; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LIF.
      try clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctasegs mF) as WM.
      (* [comment removed for export] *)
      destruct t as [|x2 t2].
      + (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?signed_small, ?unsigned_lit by (unfold sk_num in *; clear - NR D0 T0 LEN; lia); unfold sk_num, zlength in *; cbn [length] in *; clear - LEN; lia| clear K1].
        zstep. cbn [i2o_sum] in ACCB. replace (acc + i2o_sct_len x + 2) with tot by (clear - ACCB; lia).
        zstep. rewrite (Z.shiftr_div_pow2 _ 16), Z.div_small by (unfold MAX_SCT_LIST_SIZE in TMAX; clear - TMAX SUMB Etot; lia). zstep. btaken. zstep.
        apply evt_done. eapply (implAp_elim _ ΣC ΣE _ _ XX Φ DD); [| exact SAFE| exact LINK| exact ELE].
        cbn [i2o_sum] in ACCB. replace (acc + i2o_sct_len x + 2) with tot by (clear - ACCB; lia).
        eapply out_tail; [exact CPLA| exact Etot| exact TMAX| | thaw OFD; unfold off_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; exact OFD| exact DFR| exact HPE| exact FRLO| exact HDX].
        replace (zlength (sk_items k)) with (zlength done + 1) by (rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; clear; lia). rewrite Z.sub_add_distr. exact LIF.
      + (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1; [clear K1| exfalso; revert K1; rewrite ?signed_small, ?unsigned_lit by (unfold sk_num in *; clear - NR D0 T0 LEN; lia); unfold sk_num, zlength in *; cbn [length] in *; clear - LEN; lia].
        apply evt_done. eapply (implAp_elim _ ΣC ΣE _ _ XX Φ DD); [| exact SAFE| exact LINK| exact ELE].
        replace (zlength done + 1) with (zlength (done ++ [x])) by (rewrite zlength_app_l; unfold zlength; cbn [length]; clear; lia).
        replace (acc + i2o_sct_len x + 2) with (2 + i2o_sum (done ++ [x])) by (subst acc; rewrite i2o_sum_app; cbn [i2o_sum]; clear; lia).
        change (Z_to_bv 64 3370216) with (Z_to_bv 64 IOL_WHEAD).
        eapply (IH (done ++ [x])); [rewrite EQ, <- app_assoc; reflexivity| discriminate| exact CPLA| reflexivity| exact Etot| exact TMAX| | thaw OFD; unfold off_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; exact OFD| exact DFR| | exact FRLO| exact HDX].
        * rewrite zlength_app_l. unfold zlength at 2. cbn [length]. rewrite Z.sub_add_distr. exact LIF.
        * replace (AD + (2 + i2o_sum (done ++ [x]))) with (AD + acc + 2 + i2o_sct_len x) by (subst acc; rewrite i2o_sum_app; cbn [i2o_sum]; clear; lia). exact HPE.
  Qed.

  (* [comment removed for export] *)
  Lemma out_start : forall (x1 x5 x6 x7 x13 x14 x15 x16 x17 x18 x22 x27 x28 x29 x30 x31 : word) F1 fc1,
    implAp (abind (i2o_len_pass (sk_items k) 2) (Gk CN CS) st) Σ1 Q
      (ost x1 x5 x6 x7 (Z_to_bv 64 (-15)) (Z_to_bv 64 78430) (Z_to_bv 64 3369852) x13 x14 x15 x16 x17 x18 x22 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) x27 x28 x29 x30 x31 F1 fc1 m3 IOL_BODY).   (* [comment removed for export] *)
  Proof.
    intros.
    pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0 & BD1 & BD2 & BD3 & ESPA32).
    pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu. pose proof (zlength_ge0 (sk_items k)) as N0.
    pose proof linv0 as LI. pose proof (keep_sk _ _ _ _ _ _ _ LI) as SK3.
    pose proof (keep_out _ _ _ _ _ _ _ LI) as (FRH & UW3 & AGS3 & FRK). unfold frameH in FRH.
    pose proof LI as (PREX & AXX & KO & KI & KP & CR & LBOK). cbn [app] in PREX. cbn [ar_RT ar_FR push amb] in CR.
    pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & CREDX & FRMX). rewrite ESPA in STX. cbn [ar_RT ar_FR push amb length] in CREDX, FRMX.
    assert (HD3 : rw_cells ctasegs m3 DATA [C8 (Z_to_bv 64 0)]).
    { eapply rw_cells_agree; [exact AG3| exact HD|]. intros a Ha. cbn in Ha. right; right. exists bD. split; [apply in_or_app; right; exact DIN| clear - Ha DLO DHI; lia]. }
    pose proof (rw_cells_app_l _ _ [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] _ FRL3) as FRLO.
    pose proof (FRESH bD (in_or_app _ _ _ (or_intror DIN))) as OFB. unfold off_fr in OFB. change (fs_size 0) with 64 in OFB.
    assert (BIN : In bD (OW ++ LB')) by (apply in_or_app; right; subst LB'; right; exact DIN).
    ablock HEAPX BIN ACCB OFFB. unfold SHLO, SHHI in OFFB.
    pose proof (mcost_le 0 ltac:(clear; lia)) as MC0. nrm. fz OFB. fz OFFB. fz G5.
    intros XX Φ DD SAFE LINK. unfold ost, IOL_BODY.
    pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep. btaken. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply evt_done. eapply (implAp_elim _ Σ1 Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| reflexivity].
    change (Z_to_bv 64 3369852) with (wz I2O_SCT_LIST_A).
    eapply (@i2o_list_len_walkA (push AR f 0) UK BE UR STRCPY B0 (Gk CN CS) Q) with (lo := lo) (K := K) (ras := bv_unsigned ra :: ras) (j := S j) (X0 := X0)
        (STK := STKb) (CST := CSTb) (FRMb := FRMb') (adr := adr) (k := k); rewrite ?ESPA.
    - exact PREX.
    - reflexivity.
    - subst STKb. clear - STKu. ecu. lia.
    - subst CSTb. clear - CSTu N0 MC0. ecu. lia.
    - subst FRMb'. clear - FRMu. ecu. lia.
    - exact UW3.
    - rewrite unsigned_lit by (clear; lia). rewrite ERAS. reflexivity.
    - exact (uk_ctxJ_rec j X0 CTXJ JB).
    - apply cons_ne.
    - exact KO.
    - exact KI.
    - eapply sk_repA_relist; [exact SK3|]. intros b Hb. subst LB'. right. exact (sk_repA_blocks_in _ _ _ _ _ SK Hb).
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      intros Σa ms1 PO. unfold lenpost_ok in PO.
      destruct PO as (o0 & o1 & o2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & o3 & o4 & o5 & o6 & Fa & fca & mA & -> & PREa & AXa & CRa & BKa & SKa & CPLA).
      rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x336e4c) by (clear; lia). unfold MallocRep.wz.
      assert (LIA : linv Σa st mA OW bo [] (CSTb - IOL_LEN_COST_A (zlength (sk_items k)))).
      { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := []) (NEW2 := []);
          [exact LI| cbn [app]; exact PREa| cbn [app]; exact AXa| intros a []| cbn [ar_RT push amb]; exact CRa| subst CSTb; clear - CSTu N0 MC0; ecu; lia| exact BKa| constructor]. }
      pose proof (keep_out _ _ _ _ _ _ _ LIA) as (FRHa & UWa & AGSa & FRKa). unfold frameH in FRHa.
      assert (KXa : forall A' cs, rw_cells ctasegs m3 A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> ax_client LB' spa LIBW_A a) -> rw_cells ctasegs mA A' cs).
      { intros A' cs H HA. eapply rw_cells_agree; [| exact H| exact HA]. intros wa' Hr Hc. exact (AXa wa' Hr Hc). }
      pose proof bD_seg as BD5.
      apply KXa in FRLO; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEIL CE1 LOSP STKu SPAL; lia| left; clear - Ha TOP SPAH; plia]].
      apply KXa in HD3; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha BD1 BD5 DLO DHI; lia| right; right; exists bD; split; [subst LB'; right; exact DIN| clear - Ha DLO DHI; lia]]].
      thaw G5. apply KXa in HP3; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha G4; plia| right; right; exists (qp, f + 32, 8); split; [subst LB'; left; reflexivity| cbn; clear - Ha; lia]]]. fz G5.
      clear KXa.
      pose proof (i2o_sum_ge0 adr (sk_items k) OKALL) as SUMB.
      unfold Gk. destruct (Z.ltb MAX_SCT_LIST_SIZE (2 + i2o_sum (sk_items k))) eqn:EB.
      + (* [comment removed for export] *)
        unfold MAX_SCT_LIST_SIZE in EB. rewrite EB.
        intros X2 Φ2 D2 SAFE2 LINK2. clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
        apply cps_from_evt'. zstep. zstep. btaken.
        apply evt_done. eapply (implAp_elim _ Σa Σa _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| reflexivity].
        change (Z_to_bv 64 3370684) with (Z_to_bv 64 IOL_RAISE).
        eapply out_raise; [exact LIA| subst CSTb; clear - CSTu N0 MC0; ecu; lia| exact HD3| exact FRLO].
      + (* [comment removed for export] *)
        apply Z.ltb_ge in EB. unfold MAX_SCT_LIST_SIZE in EB |- *.
        replace (65535 <? 2 + i2o_sum (sk_items k)) with false by (symmetry; apply Z.ltb_ge; exact EB).
        set (tot := 2 + i2o_sum (sk_items k)) in *.
        pose proof LIA as (PREA & _ & KOa & KIa & _ & CRA & _). cbn [app] in PREA. cbn [ar_RT ar_FR push amb] in CRA.
        pose proof PREA as (HEAPA & ASA & _ & _ & STA & _ & _ & _ & _ & MIA & CREDA & FRMA). rewrite ESPA in STA. cbn [ar_RT ar_FR push amb length] in CREDA, FRMA. pose proof ASA as (_ & (CSA & _) & _).
        intros X2 Φ2 D2 SAFE2 LINK2. clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
        apply cps_from_evt'. zstep. zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 EB SUMB; subst tot; lia| clear K0].
        zstep. zstep. zstep. zstep.
        apply evt_done. eapply (implAp_elim _ Σa Σa _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| reflexivity].
        eapply (implAp_abind (amalloc tot) (CS tot) st Σa (fun r Σ' ms' => snd r = st /\ ~ In (fst r) (map blk_id (OW ++ LB')) /\
                  @calloc_postA (push AR f 0) (Z_to_bv 64 0x336e68) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 0) (Z_to_bv 64 DATA) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (adr (sk_blk k))) _ (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) Σa OW LB' tot lo mA
                     (fun A m' => exists junk, rw_cells ctasegs m' A [CB (Z.to_nat tot) junk]) (fst r) Σ' ms')).
        { unfold amalloc. change (Z_to_bv 64 2084388) with (wz CRYPTO_MALLOC).
          eapply (@CRYPTO_malloc_walkAp (push AR f 0) UK BE _) with (lo := lo) (OW := OW) (LB := LB') (n := tot) (ras := bv_unsigned ra :: ras); rewrite ?ESPA; try reflexivity.
          * exact HEAPA.
          * exact STA.
          * unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
          * subst STKb. ecu. clear - LOSP STKu SPAL. lia.
          * clear - TOP SPAH. plia.
          * clear - SPA32. Z.div_mod_to_equations. lia.
          * exact MIA.
          * exact CSA.
          * subst tot. clear - EB SUMB. lia.
          * pose proof (mcost_le tot ltac:(subst tot; clear - EB SUMB; lia)) as MC. cbn [ar_RT push amb]. subst CSTb. clear - MC CRA CRED0 CR1 CSTu N0. ecu. lia.
          * exact UWa.
          * rewrite unsigned_lit by (clear; lia). rewrite ERAS. refine (uk_ctxJ_call j X0 _ _ E_malloc _ CTXJ). unfold IOL_NESTED_RET. clear. lia.
          * intros p Σb msb Hp POb. apply implAp_ret. split; [reflexivity|]. split; [exact Hp| exact POb]. }
        intros [pd st'] Σb msb (Est & Hp & POb). cbn [fst snd] in Est, Hp, POb. subst st'.
        destruct POb as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fb & fcb & mB & AD & -> & MIB & STB & AGB & CRB & BRB & HEAPB & ACCB0 & (junkd & RB)).
        unfold MallocRep.wz in *. rewrite ?ESPA in STB. rewrite ?ESPA in AGB. cbn [ar_RT push amb] in CRB. rewrite (ret_pc_even 0x336e68) by (clear; lia).
        pose proof (@AH_ow_off_fr (push AR f 0) _ _ _ _ f 0%nat _ HEAPB (or_introl eq_refl) (or_introl eq_refl)) as OFD.
        pose proof (mcost_le tot ltac:(subst tot; clear - EB SUMB; lia)) as MC.
        assert (LIB : linv Σb st mB OW bo [(pd, AD, tot)] CX0).
        { replace CX0 with (CSTb - IOL_LEN_COST_A (zlength (sk_items k)) - IOL_MALLOC_COST_A) by reflexivity.
          eapply (oinv_alloc _ _ _ _ _ _ _ _ _ _ _ _ KH); [exact LIA| cbn [app]; exact AGB| cbn [app]; exact HEAPB| exact MIB| exact STB| cbn [ar_RT push amb]; clear - CRB MC; lia| subst CSTb; clear - CSTu N0 MC0; ecu; lia]. }
        cbn [fst snd].
        pose proof LIB as (PREB & _ & _ & _ & _ & CRBk & LBOKb). cbn [app] in PREB. cbn [ar_RT ar_FR push amb] in CRBk.
        pose proof PREB as (HEAPB' & _ & _ & _ & STB' & _ & _ & _ & _ & MIB' & _). rewrite ESPA in STB'.
        pose proof (keep_out _ _ _ _ _ _ _ LIB) as (FRHb & UWb & AGSb & FRKb). unfold frameH in FRHb.
        pose proof (oinv_facts _ _ _ _ _ _ _ _ _ _ _ _ KH _ _ _ _ _ _ _ LIB) as (_ & _ & BND & _ & DJL & DJO).
        pose proof (BND (pd, AD, tot) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (D1 & _ & D3 & D4). cbn [blk_addr blk_size fst snd] in D1, D3, D4.
        pose proof (DJL (pd, AD, tot) bD ltac:(left; reflexivity) ltac:(subst LB'; right; exact DIN)) as DJD. cbn [blk_addr blk_size fst snd] in DJD.
        unfold off_fr in OFD. change (fs_size 0) with 64 in OFD. cbn [blk_addr blk_size fst snd] in OFD. nrm.
        assert (KB : forall A' cs, rw_cells ctasegs mA A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> aclient_addr (OW ++ LB') spa a) -> rw_cells ctasegs mB A' cs).
        { intros A' cs H HA. eapply rw_cells_agree; [exact AGB| exact H| exact HA]. }
        apply KB in FRLO; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; clear - Ha TOP SPAH; plia].
        apply KB in HD3; [| intros a Ha; cbn in Ha; right; right; exists bD; split; [exact BIN| clear - Ha DLO DHI; lia]].
        apply KB in HP3; [| intros a Ha; cbn in Ha; right; right; exists (qp, f + 32, 8); split; [apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia]].
        clear KB RB.
        assert (BIN2 : In bD (OW ++ [(pd, AD, tot)] ++ LB')) by (apply in_or_app; right; right; subst LB'; right; exact DIN).
        thaw OFFB. clear ACCB OFFB. ablock HEAPB' BIN2 ACCB OFFB. unfold SHLO, SHHI in OFFB.
        intros X3 Φ3 D3' SAFE3 LINK3.
        clear MU WM. pose proof (munch_refl [(DATA, DATA + 8); (spa + 16, spa + 32); (f + 32, f + 40)]%Z mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
        assert (OFFW : offshW [(DATA, DATA + 8); (spa + 16, spa + 32); (f + 32, f + 40)]%Z).
        { thaw G5. cbn [offshW]. unfold SHLO, SHHI. clear - G4 G5 OFFB DLO DHI CEIL CE1 CE2 LOSP STKu SPAL BD1. lia. }
        fz OFFB.
        apply cps_from_evt'.
        (* [comment removed for export] *)
        ab_shload 8. ab_ichk 11%Z 0%Z 0.
        thaw OFB. thaw DJD. thaw OFD. zstep. fz OFB. fz DJD. fz OFD.
        zstep. if_cases K1; zify_cond K1; first [exfalso; revert K1; rewrite ?unsigned_lit by (clear - D1 D3 CE3; lia); intros K1; clear - K1 D1; lia | try clear K1].
        (* [comment removed for export] *)
        ab_shload 8. ab_ichk 10%Z 0%Z 0.
        zstep. zstep.
        thaw OFB. thaw DJD. thaw OFD. thaw G5. zstep. zstep. zstep. fz OFB. fz DJD. fz OFD. fz G5.
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        match goal with H : munch _ mB m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs mB m4 |- _ => rename H into WM4 end.
        match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
        assert (ST4 : stk ctasegs m4 lo spa) by (first [assumption| eapply stk_transport; [exact STB'| exact MU4| exact WM4| cbn; clear; lia]]).
        assert (LI4 : linv Σb st m4 OW bo [(pd, AD, tot)] CX0).
        { eapply (linv_munch _ _ _ _ _ _ _ _ _ LIB MU4 WM4 MI4 ST4).
          constructor; [cbn [fst snd]; right; right; left; reflexivity| constructor; [cbn [fst snd]; left; clear - CEIL LOSP STKu SPAL; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor]]]. }
        pose proof LI4 as (PRE4 & _). cbn [app] in PRE4. pose proof PRE4 as (HEAP4 & _ & _ & _ & ST4' & _ & _ & _ & _ & MI4' & _). rewrite ESPA in ST4'.
        pose proof (keep_sk _ _ _ _ _ _ _ LI4) as SK4. destruct (sk_repA_free_view _ _ _ _ SK4) as ((RNUM4 & _ & _) & KINL & HDD4 & _). unfold MallocRep.wz in RNUM4.
        pose proof SK4 as ((_ & KAL) & _ & HDD & _).
        assert (KIN4 : In (sk_blk k, adr (sk_blk k), STACK_SIZE) (OW ++ [(pd, AD, tot)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact KINL).
        assert (NR : sk_num k < 2 ^ 23) by (unfold sk_num; destruct (sk_data k) as [[q na]|]; [destruct HDD as (_ & _ & HNA & HNA2 & _); unfold sk_num in HNA; clear - HNA HNA2; lia| rewrite HDD; unfold zlength; cbn; lia]).
        eapply evt_cut.
        { eapply (@OPENSSL_sk_num_specA (push AR f 0)) with (lo := lo) (kb := sk_blk k) (SA := adr (sk_blk k)) (num := sk_num k);
            rewrite ?ESPA; [exact HEAP4| exact ST4'| exact MI4'| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| subst STKb; clear - LOSP STKu SPAL; lia
            | exact KIN4| exact KAL| exact RNUM4| unfold sk_num in *; clear - NR N0; lia| reflexivity]. }
        cbv beta. intros ms3 PO.
        destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m5 & -> & MU5 & WM5 & MI5 & ST5 & _). rewrite ?ESPA in MU5. rewrite ?ESPA in ST5.
        rewrite (ret_pc_even 0x336cd8) by (clear; lia).
        apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU5 WM5) in FRLO; [| cbn; clear; lia].
        apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU5 WM5) in HP3; [| cbn; thaw G5; clear - G3 CEIL LOSP STKu SPAL; lia].
        apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU5 WM5) in HD3; [| cbn; clear - BD2 DLO DHI CEIL LOSP STKu SPAL; lia].
        pose proof (linv_munch _ _ _ _ _ _ _ _ _ LI4 MU5 WM5 MI5 ST5 ltac:(constructor; [cbn [fst snd]; left; subst STKb; clear - LOSP STKu SPAL; lia| constructor])) as LI5.
        try clear MU; try clear WM. pose proof (munch_refl (@nil (Z * Z)) m5) as MU. pose proof (wmono_refl ctasegs m5) as WM.
        assert (DFR : ~ In pd (map blk_id (OW ++ LB))).
        { intros Hin. apply Hp. rewrite map_app in Hin |- *. apply in_app_iff in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; subst LB'; right; exact Hin]. }
        (* [comment removed for export] *)
        assert (EI' : exists l, sk_items k = l) by (eexists; reflexivity). destruct EI' as [[|x t] EI].
        * (* [comment removed for export] *)
          zstep. if_cases K0; zify_cond K0; [clear K0| exfalso; match goal with K2 : 0 < Z.land (sk_num k) _ |- _ => unfold sk_num, zlength in K2; rewrite EI in K2; cbn [length] in K2; change (Z.land (Z.of_nat 0) 18446744073709551615) with 0 in K2; clear - K2; lia end].
          zstep. zstep. zstep.
          assert (T2 : tot = 2) by (subst tot; rewrite EI; reflexivity). try rewrite T2. rewrite T2 in SAFE3. rewrite T2 in LI5. thaw OFD. rewrite T2 in OFD. fz OFD.
          apply evt_done. eapply (implAp_elim _ Σb Σb _ _ X3 Φ3 D3'); [| exact SAFE3| exact LINK3| reflexivity].
          change (Z_to_bv 64 3290852) with (Z_to_bv 64 IOL_OK).
          eapply out_tail; [exact CPLA| rewrite EI; reflexivity| unfold MAX_SCT_LIST_SIZE; clear; lia| rewrite EI; unfold zlength; cbn [length Z.of_nat]; rewrite Z.sub_0_r; exact LI5
            | thaw OFD; unfold off_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; exact OFD| exact DFR| exact HP3| exact FRLO| exact HD3].
        * (* [comment removed for export] *)
          zstep. if_cases K0; zify_cond K0;
            [exfalso; unfold sk_num in K0, NR; rewrite EI in K0, NR; rewrite land64_small in K0 by (clear - NR; unfold zlength in *; cbn [length] in *; lia);
             apply Bool.andb_false_iff in K0; destruct K0 as [K0|K0]; apply Z.ltb_ge in K0; clear - K0 NR; unfold zlength in *; cbn [length] in *; lia
            | try clear K2 K3].
          zstep. zstep. zstep.
          apply evt_done. eapply (implAp_elim _ Σb Σb _ _ X3 Φ3 D3'); [| exact SAFE3| exact LINK3| reflexivity].
          change (Z_to_bv 64 3370216) with (Z_to_bv 64 IOL_WHEAD).
          eapply (out_loop (sk_items k) [] 2); [reflexivity| rewrite EI; discriminate| exact CPLA| reflexivity| reflexivity| exact EB| unfold zlength; cbn [length Z.of_nat]; rewrite Z.sub_0_r; exact LI5
            | thaw OFD; unfold off_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; exact OFD| exact DFR| exact HP3| exact FRLO| exact HD3].
    - (* [comment removed for export] *)
      intros st1 Σa ms1 PO. unfold lenpost_fail in PO.
      destruct PO as (o0 & o1 & o2 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & o3 & o4 & o5 & o6 & Fa & fca & mA & OWa & -> & PREa & AXa & CRa & BKa & SKa).
      rewrite ESPA in AXa. cbn [ar_RT push amb] in CRa. rewrite (ret_pc_even 0x336e4c) by (clear; lia). unfold MallocRep.wz.
      rewrite abind_assoc. change (abind (err_raise RS_i2o_list) (fun a : unit => abind ((fun _ : unit => aret (@None Z)) a) (Gk CN CS)) st1) with (abind (err_raise RS_i2o_list) (fun _ => CN) st1).
      assert (LIA : linv Σa st1 mA OWa bo [] (CSTb - IOL_LEN_COST_A (zlength (sk_items k)))).
      { eapply (oinv_after _ _ _ _ _ _ _ _ _ _ _ _ KH) with (XX := []) (NEW2 := []);
          [exact LI| cbn [app]; exact PREa| cbn [app]; exact AXa| intros a []| cbn [ar_RT push amb]; exact CRa| subst CSTb; clear - CSTu N0 MC0; ecu; lia| exact BKa| constructor]. }
      assert (KXa : forall A' cs, rw_cells ctasegs m3 A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> ax_client LB' spa LIBW_A a) -> rw_cells ctasegs mA A' cs).
      { intros A' cs H HA. eapply rw_cells_agree; [| exact H| exact HA]. intros wa' Hr Hc. exact (AXa wa' Hr Hc). }
      pose proof bD_seg as BD5.
      apply KXa in FRLO; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEIL CE1 LOSP STKu SPAL; lia| left; clear - Ha TOP SPAH; plia]].
      apply KXa in HD3; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha BD1 BD5 DLO DHI; lia| right; right; exists bD; split; [subst LB'; right; exact DIN| clear - Ha DLO DHI; lia]]].
      clear KXa.
      intros X2 Φ2 D2 SAFE2 LINK2. clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      apply cps_from_evt'. zstep. zstep. btaken.
      apply evt_done. eapply (implAp_elim _ Σa Σa _ _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| reflexivity].
      change (Z_to_bv 64 3370684) with (Z_to_bv 64 IOL_RAISE).
      eapply out_raise; [exact LIA| subst CSTb; clear - CSTu N0 MC0; ecu; lia| exact HD3| exact FRLO].
  Qed.
End ActOut.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem i2o_list_out_walkA : forall (B0 : Type) (CN : @AM bptr B0) (CS : Z -> bptr -> @AM bptr B0) (Q : B0 * ap_st bptr -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
    (lo : Z) (K : list block) (ras : list Z) (j : nat) (X0 : list Z) (STK CST FRMb : Z) (adr : bptr -> Z) (k : skr bptr) (DATA : Z) (bD : block),
  ap_preA Σ st m OW LB E bo sp lo STK CST FRMb -> tp = wz TP_A ->
  IOL_OUT_STACK_A <= STK -> IOL_OUT_COST_A (zlength (sk_items k)) <= CST -> IOL_OUT_FRAMES_A <= FRMb ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> bv_unsigned ra :: ras = repeat IOL_NESTED_RET j ++ X0 -> uk_ctxJ j X0 -> (S j <= IOL_REC_DEPTH)%nat -> ras <> nil ->
  (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
  sk_repA m LB adr k ->
  In bD LB -> blk_addr bD <= DATA -> DATA + 8 <= blk_addr bD + blk_size bD -> DATA mod 8 = 0 ->
  (forall b, In b (sk_blocks adr k) -> DATA + 8 <= blk_addr b \/ blk_addr b + blk_size b <= DATA) ->
  rw_cells ctasegs m DATA [C8 (wz 0)] ->
  a0 = wz (adr (sk_blk k)) -> a1 = wz DATA ->
  (forall st1 Σ' ms',
     outpost_fail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (IOL_OUT_COST_A (zlength (sk_items k))) adr k DATA st1 Σ' ms' ->
     implAp (CN st1) Σ' Q ms') ->
  (forall d st1 Σ' ms',
     outpost_ok ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (IOL_OUT_COST_A (zlength (sk_items k))) adr k DATA d st1 Σ' ms' ->
     implAp (CS (2 + i2o_sum (sk_items k)) d st1) Σ' Q ms') ->
  implAp (abind (i2o_len_pass (sk_items k) 2) (Gk CN CS) st) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz I2O_SCT_LIST_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until bD. intros PRE TP STKB CSTB FRMB UW ERAS CTXJ JB NE KOW KIDS SK DIN DLO DHI D8 DAP HD -> -> KN KS.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
  pose proof STKB as STKu. pose proof CSTB as CSTu. pose proof FRMB as FRMu. ecu.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). pose proof (zlength_ge0 (sk_items k)) as N0. pose proof (mcost_le 0 ltac:(clear; lia)) as MC0.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  intros XX Φ DD SAFE LINK.
  change (wz I2O_SCT_LIST_A) with (wz IOL_ENTRY).
  eapply (iol_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold IOL_FRAME, RT_STACK; clear - LOSP STKu; lia| exact TOP| exact AL16| exact MI| exact TP
    | clear - FRM0 FRMu; lia| clear - CRED CSTu N0 MC0; unfold IOL_MALLOC_COST_A in *; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AG3 FRL FRH HF FRS SPA32 SPAL SPAH GSZ SAVJ.
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qp Hqp].
  pose proof (iol_open_p Σ1 OW LB m3 f qp HEAP3 ltac:(intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))) GEO FRS Hqp) as HEAPp.
  eapply (implAp_elim _ Σ Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| exact EL1].
  unfold MallocRep.wz. change (Z_to_bv 64 IOL_BODY) with (Z_to_bv 64 IOL_BODY).
  lazymatch type of HF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs m3 f [c0; c1; c2; c3] (c4 :: rest)) HF)) as HD0 end.
  lazymatch type of HD0 with rw_cells _ _ ?a _ => replace a with (f + 32) in HD0 by reflexivity end.
  lazymatch type of HD0 with rw_cells _ _ _ (?c4 :: ?rest) =>
    pose proof (proj1 (proj1 (SctRepA.rw_cells_app ctasegs m3 (f + 32) [c4] rest) HD0)) as HP3 end.
  eapply out_start; [exact PRE| exact STKB| exact CSTB| exact FRMB| exact UW| exact ERAS| exact CTXJ| exact JB| exact KOW| exact KIDS| exact SK| exact DIN| exact DLO| exact DHI| exact D8| exact DAP| exact HD
    | exact HEAP3| exact HEAPp| exact FRESH| exact GEO| exact CR1| exact ST3| exact MI3| exact AG3| exact FRL| exact FRH| exact HP3| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact KN| exact KS].
Qed.
End WithRT.
