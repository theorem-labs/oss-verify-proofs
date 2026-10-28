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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_obj_free ApErrKitA2 W_prefix_create W_get_objectA W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_err_newA W_err_set_debugA W_err_vsetA W_get_object_closedA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep W_sct_set1_signature W_sct_list_free W_o2i_sig W_sct_new W_o2i_sct W_o2i_sct_list W_sk_leaves W_sk_push O2iKit SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA RtGenStmtA W_crypto_reallocA W_sct_newA W_sct_set1_signatureA W_sct_freeA W_sct_list_freeA W_sk_newA W_sk_pushA O2iKitA W_o2i_sigA O2iSctStmtB O2iSctListStmtB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctWire.                (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require O2iKitAR.                     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarKitA.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ab1B := first [ ab1X | ApATac.ab1 ].
Local Ltac abB := repeat ab1B.
Local Ltac apre := ual; abB.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
(* [comment removed for export] *)
Local Ltac frz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
Ltac ApATac.ashb ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let S1 := fresh "SHB1_" in let S2 := fresh "SHB2_" in
      first
        [ match goal with HEAP : BnHeapA.AHEAP _ _ _ mc |- _ => destruct (AH_shb _ _ _ _ HEAP) as [S1 S2] end
        | match goal with SH : shb_cells _ _ _ mc |- _ => destruct SH as [S1 S2] end
        | match goal with
          | HEAP : BnHeapA.AHEAP _ _ _ ?m0, MU : munch ?W ?m0 mc |- _ =>
              destruct (shb_cells_munch _ _ _ _ _ (AH_shb _ _ _ _ HEAP) MU
                          ltac:(intros xq__ Hxq__; unfold A_GOT_SHB, A_SHB_CELL in Hxq__; cbn [outside]; unfold BnHeapA.ACEIL, SHLO, SHHI in *; uchk_open; lia)) as [S1 S2]
          | SH : shb_cells _ _ _ ?m0, MU : munch ?W ?m0 mc |- _ =>
              destruct (shb_cells_munch _ _ _ _ _ SH MU ltac:(intros xq__ Hxq__; cbn [outside]; unfold BnHeapA.ACEIL, SHLO, SHHI in *; uchk_open; lia)) as [S1 S2]
          end
        | fail 100 "ashb: no AHEAP / shb_cells hypothesis reaches the current memory (directly or through a munch footprint)" ]
  end.

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
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Notation zxb_lit := CtRepP.W_get_object_walk.zxb_lit.
Notation znth_range8 := CtRepP.W_get_object_walk.znth_range.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OSL_RAISE1 : Z := 0x33697c.     (* [comment removed for export] *)
Definition OSL_NULL : Z := 0x336998.       (* [comment removed for export] *)
Definition OSL_RET : Z := 0x33699c.        (* [comment removed for export] *)
Definition OSL_RAISE2 : Z := 0x336a3c.     (* [comment removed for export] *)
Definition OSL_ERR : Z := 0x336a58.        (* [comment removed for export] *)
Definition OSL_FREE : Z := 0x336a80.       (* [comment removed for export] *)
Definition OSL_HEAD : Z := 0x3368b0.       (* [comment removed for export] *)
Definition OSL_ITER : Z := 0x3368b8.       (* [comment removed for export] *)
Definition OSL_DONE : Z := 0x3369f8.       (* [comment removed for export] *)

Local Notation E_new262 := (E_o2i_SCT_LIST_34aac4 : uk_call 0x336764 0x3367b8 0x1fd52c).
Local Notation E_sknew := (E_o2i_SCT_LIST_34aba8 : uk_call 0x336764 0x33685c 0x1fb288).
Local Notation E_setcmp := (E_o2i_SCT_LIST_34abb8 : uk_call 0x336764 0x33686c 0x1fb8c0).
Local Notation E_setcopy := (E_o2i_SCT_LIST_34abc8 : uk_call 0x336764 0x33687c 0x1fb910).
Local Notation E_setfree := (E_o2i_SCT_LIST_34abd8 : uk_call 0x336764 0x33688c 0x1fb870).
Local Notation E_osct := (E_o2i_SCT_LIST_34ac84 : uk_call 0x336764 0x33691c 0x335704).
Local Notation E_push := (E_o2i_SCT_LIST_34aca0 : uk_call 0x336764 0x336938 0x1fc6f8).
Local Notation E_new268 := (E_o2i_SCT_LIST_34acd0 : uk_call 0x336764 0x336968 0x1fd52c).
Local Notation E_dbg1 := (E_o2i_SCT_LIST_34acec : uk_call 0x336764 0x336984 0x1fd844).
Local Notation E_err1 := (E_o2i_SCT_LIST_34ad00 : uk_call 0x336764 0x336998 0x1fdab8).
Local Notation E_new289 := (E_o2i_SCT_LIST_34ad4c : uk_call 0x336764 0x3369e0 0x1fd52c).
Local Notation E_new296 := (E_o2i_SCT_LIST_34ada0 : uk_call 0x336764 0x336a28 0x1fd52c).
Local Notation E_dbg2 := (E_o2i_SCT_LIST_34adbc : uk_call 0x336764 0x336a44 0x1fd844).
Local Notation E_err2 := (E_o2i_SCT_LIST_34add0 : uk_call 0x336764 0x336a58 0x1fdab8).
Local Notation E_lfree := (E_o2i_SCT_LIST_34ae0c : uk_call 0x336764 0x336a88 0x3376b8).

(* [comment removed for export] *)
Lemma osl_mcost_0_small : forall n, 0 <= n <= 64512 -> mcost n = 0.
Proof. intros n Hn. unfold mcost. replace (n <=? 64512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRs := (@ar_FR AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

(* [comment removed for export] *)
Hypothesis STRCPY : strcpy_icontract RT.
Hypothesis REA : realloc_contract_gen RT.
(* [comment removed for export] *)
Hypothesis HO2I : o2i_sct_specA2 O2I_SCT_STACK_A O2I_SCT_COST_A O2I_SCT_FRAMES_A.

Local Ltac ecu := unfold O2I_SCT_LIST_STACK_A, O2I_SCT_LIST_COST_A, O2I_SCT_LIST_FRAMES_A, O2I_SCT_STACK_A, O2I_SCT_COST_A, O2I_SCT_FRAMES_A,
                         O2I_SIG_STACK_A, O2I_SIG_COST_A, O2I_SIG_FRAMES_A, GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A,
                         SK_NEW_NULL_STACK_A, SK_PUSH_STACK_A, SK_POP_FREE_STACK_A, SCT_FREE_STACK_A, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, CRYPTO_FREE_STACK,
                         ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK,
                         ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, RT_STACK in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block) (ras : list Z).
  Variables (adr : bptr -> Z) (c : list Z) (D len PIN : Z).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo O2I_SCT_LIST_STACK_A O2I_SCT_LIST_COST_A O2I_SCT_LIST_FRAMES_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx O2I_SCT_LIST_A (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis ELEN : len = zlength c.
  Hypothesis D0 : 0 <= D.      (* [comment removed for export] *)
  Hypothesis D63 : D + zlength c < 2 ^ 63.
  Hypothesis DF : Forall (fun b => 0 <= b < 256) c.
  Hypothesis HB0 : bytes_at ctasegs m D (to_bytes c).
  Hypothesis PBX : c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis CPIN : cellA_in LB PIN 8.
  Hypothesis ALP : PIN mod 8 = 0.
  Hypothesis PIND : PIN + 8 <= D \/ D + zlength c <= PIN.
  Hypothesis HPIN : rw_cells ctasegs m PIN [C8 (wz D)].

  Definition XPs : list (Z * Z) := [(PIN, PIN + 8)].
  (* [comment removed for export] *)
  Local Notation oinvS := (oinv sp m Σ LB E lo K c D XPs (-96) O2I_SCT_STACK_A O2I_SCT_LIST_COST_A O2I_SCT_LIST_FRAMES_A).
  (* [comment removed for export] *)
  Definition lframeA : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation SPOST := (o2i_list_postA2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K O2I_SCT_LIST_COST_A adr len PIN) (only parsing).

  Lemma ctx_factsA :
    0 <= D /\ D + zlength c < 2 ^ 63
    /\ ACEIL <= lo /\ 12365824 <= lo /\ lo <= bv_unsigned sp - O2I_SCT_LIST_STACK_A
    /\ bv_unsigned sp + 16 <= USTACK_TOP /\ 0 <= bv_unsigned sp < 2 ^ 64 /\ bv_unsigned sp mod 16 = 0
    /\ Z.of_nat (length (to_bytes c)) = zlength c /\ List.NoDup (map blk_id (OW ++ LB))
    /\ (exists bq, In bq LB /\ blk_addr bq <= PIN /\ PIN + 8 <= blk_addr bq + blk_size bq /\ 0 < blk_addr bq /\ blk_addr bq + blk_size bq <= ACEIL
                  /\ (blk_addr bq + blk_size bq <= 65536 \/ 12365824 <= blk_addr bq))
    /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ SEGTOP_A <= ACEIL
    /\ O2I_SCT_LIST_COST_A <= rt_credit RT Σ /\ Z.of_nat (length FRs) + O2I_SCT_LIST_FRAMES_A <= Z.of_nat FRAMES_MAX
    /\ bv_unsigned (Z_to_bv 64 PIN) = PIN /\ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96.
  Proof.
    destruct PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). pose proof C1 as C1'. unfold SEGTOP_A in C1.
    destruct CPIN as (bq & HBQ & Q1 & Q2). pose proof (AH_blk _ _ _ _ bq HEAP ltac:(apply in_app_iff; right; exact HBQ)) as (Q3 & _ & Q4 & Q5).
    assert (EPIN : bv_unsigned (Z_to_bv 64 PIN) = PIN) by (apply unsigned_lit; clear - Q1 Q2 Q3 Q4 C3; unfold BnHeapA.ACEIL, STACK_WIN, USTACK_TOP in *; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR CEIL C1 LOSP; ecu; lia).
    repeat (split; [first [assumption| (clear - CEIL C1; lia)| (unfold to_bytes, zlength; rewrite length_map; reflexivity)| exact (AH_nodup _ _ _ _ HEAP)]|]).
    split; [exists bq; repeat (split; [assumption|]); exact Q5|].
    split; [exact C2|]. split; [exact C3|]. split; [exact C1'|]. split; [clear - CRED; lia|]. split; [clear - FRM; lia|]. split; [exact EPIN| exact ESP].
  Qed.

  Local Ltac ctx := pose proof ctx_factsA as (D0' & D63' & CEIL & GLO & LO & TOP & SPR & AL16 & DLEN & NDL & CELL & SHI & SWIN & CE1 & CRED0 & FRM0 & EPIN & ESP);
                   pose proof LO as LOSPu; unfold O2I_SCT_LIST_STACK_A, O2I_SCT_STACK_A, O2I_SIG_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in LOSPu.

  (* [comment removed for export] *)
  Lemma KHs : kit_hyps sp LB lo c D XPs (-96) O2I_SCT_STACK_A.
  Proof.
    ctx. unfold kit_hyps, XPs. split; [exact DF|]. split; [exact CEIL|]. split; [clear - CEIL GLO; lia|]. split; [clear - LOSPu; ecu; lia|].
    split; [clear; ecu; lia|]. split; [clear; lia|]. split; [exact TOP|]. split; [exact AL16|]. split; [reflexivity|].
    split. { constructor; [| constructor]. cbn [fst snd]. destruct CPIN as (bq & HBQ & Q1 & Q2). exists bq. split; [exact HBQ| split; [exact Q1| exact Q2]]. }
    split. { constructor; [| constructor]. cbn [fst snd]. right. clear - PIND. lia. }
    split; [exact PBX| clear - D0; lia].
  Qed.
  (* [comment removed for export] *)
  Local Ltac kit L := eapply (L AR sp m Σ LB E lo K c D XPs (-96) O2I_SCT_STACK_A O2I_SCT_LIST_COST_A O2I_SCT_LIST_FRAMES_A KHs).
  Local Ltac kitp L H := pose proof (L AR sp m Σ LB E lo K c D XPs (-96) O2I_SCT_STACK_A O2I_SCT_LIST_COST_A O2I_SCT_LIST_FRAMES_A KHs) as H.

  (* [comment removed for export] *)
  Lemma oinv0 : oinvS Σ st m OW bo [] O2I_SCT_LIST_COST_A.
  Proof.
    kit @oinv_entry; [| exact KOW| exact KIDS| exact HB0].
    eapply ap_preA_weaken; [exact PRE| unfold O2I_SCT_LIST_STACK_A; clear; lia| clear; ecu; lia| clear; ecu; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma cells_keptA : forall mA mB (NEW : list block) vpin,
    ax_pres (NEW ++ LB) (bv_unsigned sp + -96) LIBW_A mA mB ->
    (rw_cells ctasegs mA (bv_unsigned sp + -96) lframeA -> rw_cells ctasegs mB (bv_unsigned sp + -96) lframeA)
    /\ (rw_cells ctasegs mA PIN [C8 vpin] -> rw_cells ctasegs mB PIN [C8 vpin]).
  Proof.
    intros mA mB NEW vpin AX. ctx. destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5).
    split.
    - intros H. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. cbn [cells_size csize Nat.add lframeA] in Ha.
      split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEIL GLO LOSPu; lia| left; clear - Ha TOP; unfold USTACK_TOP in *; lia].
    - intros H. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. cbn in Ha.
      split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha Q1 Q2 Q5; lia|]. right; right. exists bq. split; [apply in_app_iff; right; exact HBQ| clear - Ha Q1 Q2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma uw_at_call : forall ΣX stX mX OWX boX NEW CX,
    oinvS ΣX stX mX OWX boX NEW CX -> rw_cells ctasegs mX (bv_unsigned sp + -96) lframeA ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + -96) (bv_unsigned sp) (bv_unsigned ra :: ras).
  Proof.
    intros until CX. intros OI FRx. ctx. pose proof OI as (_ & AXc & _). destruct CELL as (bq & _ & Q1 & Q2 & Q3 & Q4 & _).
    unfold lframeA in FRx.
    uw_call_axX_tac m 96 UW AXc FRx;
      [ clear; lia
      | intros a Ha; apply rin_ivs_app in Ha as [Ha|Ha];
        [ unfold XPs in Ha; cbn [rin_ivs fst snd app] in Ha; clear - Ha Q1 Q2 Q4 CEIL LOSPu; lia
        | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb GLO LOSPu; lia ]
      | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac err_call Wc Ec OIc FRc :=
    eapply (@oinv_ap_callA AR UK sp m Σ LB E lo K c D XPs (-96) O2I_SCT_STACK_A O2I_SCT_LIST_COST_A O2I_SCT_LIST_FRAMES_A KHs);
    [ exact Wc | exact OIc | ecu; clear; lia | | ecu; clear; lia
    | eapply uw_at_call; [exact OIc| exact FRc]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ Ec CTX)
    | apply cons_ne
    | ].

  (* [comment removed for export] *)
  Definition site_okA (base : Z) (nj : nat) (tl : Z) (rs : rsite) : Prop :=
    (base = 0x3367b0 /\ nj = 6%nat /\ tl = OSL_RAISE1 /\ rs = RS_list_len) \/ (base = 0x336960 /\ nj = 5%nat /\ tl = OSL_RAISE1 /\ rs = RS_list_mismatch)
    \/ (base = 0x3369d8 /\ nj = 6%nat /\ tl = OSL_RAISE2 /\ rs = RS_list_lt2) \/ (base = 0x336a20 /\ nj = 5%nat /\ tl = OSL_RAISE2 /\ rs = RS_list_sctlen).

  (* [comment removed for export] *)
  Definition raise_postA (pc : Z) (x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (vpin : word) (mX : mem) (CX : Z) (NEW : list block) (boX : Z * Z)
      (r : unit * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FY : bvmap 5 word) (fcY : bv 32) mY OWY,
      ms' = MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               FY (Z_to_bv 64 pc) fcY None mY (seg_rom ctasegs)
      /\ oinvS ΣY (snd r) mY OWY boX NEW (CX - GETOBJ_ERR_COST_A)
      /\ rw_cells ctasegs mY (bv_unsigned sp + -96) lframeA /\ rw_cells ctasegs mY PIN [C8 vpin]
      /\ ax_pres (NEW ++ LB) (bv_unsigned sp + -96) LIBW_A mX mY.

  (* [comment removed for export] *)
  Local Ltac raise_body Enew rs nlit Edbg Eerr :=
    lazymatch goal with
    | OI : oinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?ΣX ?stX ?mX ?OWX ?boX ?NEW ?CX, FRx : rw_cells ctasegs ?mX (bv_unsigned sp + -96) lframeA,
      HPx : rw_cells ctasegs ?mX PIN [C8 ?vpin], CXle : GETOBJ_ERR_COST_A <= ?CX,
      LF : lit_okA A_CT_OCT_C_A ?fs ?fk _, LN : lit_okA A_O2I_SCT_LIST_A ?ns ?nk _ |- _ =>
      (* [comment removed for export] *)
      eapply implAp_abind;
      [ apply implAp_from_evt; step; apply evt_done; err_call constr:(@ERR_new_walkA AR UK BE boX) Enew OI FRx; [ecu; clear - CXle; lia| reflexivity] |];
      let r1 := fresh "r" in let Σ1 := fresh "Σ" in let ms1 := fresh "ms" in let PO1 := fresh "PO" in
      intros r1 Σ1 ms1 PO1; cbv beta in PO1;
      let mA := fresh "mA" in let OWa := fresh "OWa" in let OIa := fresh "OIa" in let AXa := fresh "AXa" in let bo1 := fresh "bo" in let EBO1 := fresh "EBO" in
      let Ta1 := fresh "FRa" in let Ta3 := fresh "HPa" in
      destruct PO1 as (?q0 & ?q1 & ?q2 & ?q10 & ?q11 & ?q12 & ?q13 & ?q14 & ?q15 & ?q16 & ?q17 & ?q3 & ?q4 & ?q5 & ?q6 & ?F1 & ?fc1 & mA & OWa & bo1
                        & -> & OIa & AXa & EBO1); subst bo1;
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end;
      destruct (cells_keptA mX mA NEW vpin AXa) as [Ta1 Ta3]; specialize (Ta1 FRx); specialize (Ta3 HPx);
      clear FRx HPx;
      let OC := fresh "OC" in let STa := fresh "STa" in let MIa := fresh "MIa" in
      kitp @oinv_call OC; pose proof (OC _ _ _ _ _ _ _ OIa) as (_ & STa & _ & _ & _ & _ & MIa & _); clear OC;
      repeat match goal with H : munch _ _ _ |- _ => clear H | H : wmono ctasegs _ _ |- _ => clear H end;
      let MU := fresh "MU" in let WM := fresh "WM" in pose proof (munch_refl (@nil (Z * Z)) mA) as MU; pose proof (wmono_refl ctasegs mA) as WM;
      (* [comment removed for export] *)
      eapply implAp_abind;
      [ apply implAp_from_evt; do nlit step; apply evt_done; unfold OSL_RAISE1, OSL_RAISE2;
        err_call constr:(@ERR_set_debug_walkA AR UK BE STRCPY rs _ _ boX fs fk ns nk LF LN) Edbg OIa Ta1;
        [ pose proof OIa as (PREa & _); pose proof PREa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa & _); ecu; clear - CRa CXle; lia
        | unfold A_CT_OCT_C_A, A_O2I_SCT_LIST_A, MallocRep.wz; cbn [rs_line RS_list_len RS_list_mismatch RS_list_lt2 RS_list_sctlen]; repeat split; reflexivity ] |];
      let r2 := fresh "r" in let Σ2 := fresh "Σ" in let ms2 := fresh "ms" in let PO2 := fresh "PO" in
      intros r2 Σ2 ms2 PO2; cbv beta in PO2;
      let mB := fresh "mB" in let OWb := fresh "OWb" in let OIb := fresh "OIb" in let AXb := fresh "AXb" in let bo2 := fresh "bo" in let EBO2 := fresh "EBO" in
      let Tb1 := fresh "FRb" in let Tb3 := fresh "HPb" in
      destruct PO2 as (?p0 & ?p1 & ?p2 & ?p10 & ?p11 & ?p12 & ?p13 & ?p14 & ?p15 & ?p16 & ?p17 & ?p3 & ?p4 & ?p5 & ?p6 & ?F2 & ?fc2 & mB & OWb & bo2
                        & -> & OIb & AXb & EBO2); subst bo2;
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end;
      destruct (cells_keptA mA mB NEW vpin AXb) as [Tb1 Tb3]; specialize (Tb1 Ta1); specialize (Tb3 Ta3);
      clear Ta1 Ta3;
      let OC2 := fresh "OC" in let STb := fresh "STb" in let MIb := fresh "MIb" in
      kitp @oinv_call OC2; pose proof (OC2 _ _ _ _ _ _ _ OIb) as (_ & STb & _ & _ & _ & _ & MIb & _); clear OC2;
      repeat match goal with H : munch _ _ _ |- _ => clear H | H : wmono ctasegs _ _ |- _ => clear H end;
      let MU2 := fresh "MU" in let WM2 := fresh "WM" in pose proof (munch_refl (@nil (Z * Z)) mB) as MU2; pose proof (wmono_refl ctasegs mB) as WM2;
      (* [comment removed for export] *)
      eapply implAp_mono;
      [ apply implAp_from_evt; do 4 step; apply evt_done;
        err_call constr:(@ERR_set_error_closedA AR UK BE rs 50 105 boX) Eerr OIb Tb1;
        [ pose proof OIb as (PREb & _); pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _);
          pose proof OIa as (PREa' & _); pose proof PREa' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa' & _); ecu; clear - CRa' CRb CXle; lia
        | unfold ERR_LIB_SYS, MallocRep.wz; cbn [rs_code RS_list_len RS_list_mismatch RS_list_lt2 RS_list_sctlen]; unfold ERR_LIB_CT; repeat split; first [reflexivity | (clear; lia)] ] |];
      let r3 := fresh "r" in let Σ3 := fresh "Σ" in let ms3 := fresh "ms" in let PO3 := fresh "PO" in
      intros r3 Σ3 ms3 PO3; cbv beta in PO3;
      let mC := fresh "mC" in let OWc := fresh "OWc" in let OIc := fresh "OIc" in let AXc := fresh "AXc" in let boC := fresh "boC" in let EBO3 := fresh "EBO" in
      let Tc1 := fresh "FRc" in let Tc3 := fresh "HPc" in
      destruct PO3 as (?o0 & ?o1 & ?o2 & ?o10 & ?o11 & ?o12 & ?o13 & ?o14 & ?o15 & ?o16 & ?o17 & ?o3 & ?o4 & ?o5 & ?o6 & ?F3 & ?fc3 & mC & OWc & boC
                        & -> & OIc & AXc & EBO3);
      destruct (cells_keptA mB mC NEW vpin AXc) as [Tc1 Tc3];
      unfold raise_postA; do 17 eexists; exists mC, OWc;
      split; [match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end; reflexivity|];
      split; [ kit @oinv_credit; [exact OIc| pose proof OIc as (PREc & _); pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _); ecu; clear - CRc CXle; lia]
             | split; [exact (Tc1 Tb1)| split; [exact (Tc3 Tb3)| exact (ax_pres_trans _ _ _ _ _ _ AXa (ax_pres_trans _ _ _ _ _ _ AXb AXc))]]]
    end.

  Lemma raise_siteA : forall base nj tl rs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (FX : bvmap 5 word) (fcX : bv 32) ΣX stX mX OWX boX NEW CX vpin,
    site_okA base nj tl rs ->
    oinvS ΣX stX mX OWX boX NEW CX -> GETOBJ_ERR_COST_A <= CX ->
    rw_cells ctasegs mX (bv_unsigned sp + -96) lframeA -> rw_cells ctasegs mX PIN [C8 vpin] ->
    implAp (err_raise rs stX) ΣX (raise_postA (tl + 28) x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 vpin mX CX NEW boX)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until vpin. intros SITE OI CXle FRx HPx. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold err_raise, MallocRep.wz, OSL_RAISE1, OSL_RAISE2.
    destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_O2I_SCT_LIST_A 13 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    destruct SITE as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]]]; cbn [Z.add];
      [ raise_body constr:(E_new262) RS_list_len ltac:(7) constr:(E_dbg1) constr:(E_err1)
      | raise_body constr:(E_new268) RS_list_mismatch ltac:(6) constr:(E_dbg1) constr:(E_err1)
      | raise_body constr:(E_new289) RS_list_lt2 ltac:(7) constr:(E_dbg2) constr:(E_err2)
      | raise_body constr:(E_new296) RS_list_sctlen ltac:(6) constr:(E_dbg2) constr:(E_err2) ].
  Qed.

  (* [comment removed for export] *)
  Lemma ret_nullA : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX CX vpin,
    oinvS ΣX stX mX OWX boX [] CX -> 0 <= CX ->
    rw_cells ctasegs mX (bv_unsigned sp + -96) lframeA -> rw_cells ctasegs mX PIN [C8 vpin] ->
    evt ctasegs (SPOST (None, stX) ΣX)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 OSL_NULL) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until vpin. intros OI HCX FR HP. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (HEAPX & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold lframeA in FR. unfold OSL_NULL, MallocRep.wz.
    step. step. do 12 step. release_frame FR STX (bv_unsigned sp). step. step.
    apply evt_done.
    match goal with H : stk ctasegs mX lo (bv_unsigned sp) |- _ => rename H into STF end.
    kitp @pre_resp PR. destruct (PR _ _ _ _ _ _ _ OI STF) as (PREF & AXF & CRF & BKF & FRF & LBF). clear PR.
    unfold o2i_list_postA2, MallocRep.wz. cbn [fst snd app].
    do 14 eexists. exists FX, fcX, mX, OWX, boX, adr, (@nil block), vpin. cbn [app].
    split; [reflexivity|]. split; [exact PREF|]. split; [unfold XPs in AXF; exact AXF|]. split; [clear - CRF HCX; lia|]. split; [exact BKF|].
    split; [intros b Hb; reflexivity|]. split; [intros b []|]. split; [constructor|]. split; [exact HP| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ret_someA : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW CX (adrk : bptr -> Z) (k : skr bptr) vpin,
    oinvS ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    Permutation NEW (sk_blocks adrk k) -> sk_repA mX (OWX ++ NEW ++ LB) adrk k -> (forall b, In b LB -> adrk (blk_id b) = adr (blk_id b)) ->
    2 + sk_wire k <= len -> len <= MAX_SCT_LIST_SIZE -> 3 * zlength (sk_items k) + 2 <= len ->
    rw_cells ctasegs mX (bv_unsigned sp + -96) lframeA -> rw_cells ctasegs mX PIN [C8 vpin] ->
    evt ctasegs (SPOST (Some k, stX) ΣX)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 OSL_RET) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until vpin. intros OI HCX PM SK ADRK W1 W2 W3 FR HP. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI) as (_ & _ & _ & FRSH & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (HEAPX & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold lframeA in FR. unfold OSL_RET, MallocRep.wz.
    step. do 12 step. release_frame FR STX (bv_unsigned sp). step. step.
    apply evt_done.
    match goal with H : stk ctasegs mX lo (bv_unsigned sp) |- _ => rename H into STF end.
    kitp @pre_resp PR. destruct (PR _ _ _ _ _ _ _ OI STF) as (PREF & AXF & CRF & BKF & FRF & LBF). clear PR.
    unfold o2i_list_postA2, MallocRep.wz. cbn [fst snd app].
    do 14 eexists. exists FX, fcX, mX, OWX, boX, adrk, NEW, vpin.
    split; [reflexivity|]. split; [exact PREF|]. split; [unfold XPs in AXF; exact AXF|]. split; [clear - CRF HCX; lia|]. split; [exact BKF|].
    split; [exact ADRK|]. split; [exact FRF|]. split; [exact LBF|]. split; [exact HP|]. split; [exact PM|]. split; [exact SK|]. split; [exact W1|]. split; [exact W2| exact W3].
  Qed.

  (* [comment removed for export] *)
  Lemma free_exitA : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW CX (adrk : bptr -> Z) (k : skr bptr) vpin,
    oinvS ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    Permutation NEW (sk_blocks adrk k) -> sk_repA mX (OWX ++ NEW ++ LB) adrk k -> zlength (sk_items k) < 2 ^ 31 ->
    rw_cells ctasegs mX (bv_unsigned sp + -96) lframeA -> rw_cells ctasegs mX PIN [C8 vpin] ->
    implAp (abind (sk_free_all k) (fun _ => aret None) stX) ΣX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 OSL_ERR) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until vpin. intros OI HCX PM SK N31 FR HP. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRSH & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _). clear OC.
    pose proof OI as (_ & _ & _ & _ & _ & _ & _ & LBOK).
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold OSL_ERR, MallocRep.wz. apply implAp_from_evt.
    step. if_cases K9; zc K9; [| exfalso; apply K9; reflexivity]. clear K9.
    step. step. apply evt_done.
    (* [comment removed for export] *)
    pose proof (AH_adopt_list ΣX NEW OWX LB mX HEAPX LBOK) as HEAPa.
    assert (SKa : sk_repA mX (NEW ++ OWX) adrk k).
    { eapply sk_repA_relist; [exact SK|]. intros b Hb. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb]. }
    pose proof (AH_nodup _ _ _ _ HEAPa) as NDa. rewrite map_app in NDa. pose proof (nodup_app_l _ _ NDa) as NDl.
    change (Z_to_bv 64 3372728) with (wz SCT_LIST_FREE_A).
    eapply implAp_abind.
    { eapply (@SCT_LIST_free_walkA AR UK BE) with (lo := lo) (adr := adrk) (ras := bv_unsigned ra :: ras);
        [ exact HEAPa | rewrite ESP; exact STX | exact CEIL | rewrite ESP; clear - LOSPu; ecu; lia
        | rewrite ESP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MIX | reflexivity | exact CSX
        | rewrite ESP; eapply uw_at_call; [exact OI| exact FR]
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_lfree CTX)
        | apply cons_ne | exact SKa | exact N31 | reflexivity ]. }
    intros [u st'] Σ' ms' PO. cbn [fst snd].
    destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & Er & MI2 & ST2 & AG2 & CR2 & HEAP2).
    injection Er as Est. subst st'. rewrite (ret_pc_even 0x336a88) by (clear; lia). rewrite ?ESP in AG2, ST2.
    (* [comment removed for export] *)
    pose proof (CtSctP.W_o2i_sct_list.remove_sk_perm adrk k [] NEW OWX PM NDl) as PMR. cbn [app] in PMR. unfold remove_sk in AG2, HEAP2.
    assert (OI2 : oinvS Σ' stX m2 OWX boX [] (CX - 0)).
    { kit @oinv_heap; [exact OI| | | cbn [app]; eapply (@AHEAP_permOW AR); [exact HEAP2| exact PMR]| apply Forall_nil| exact MI2| exact ST2| clear - CR2; lia| clear - HCX; lia].
      - eapply agree_on_mono; [exact AG2|]. intros a [Ha _]. exact Ha.
      - intros b Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; eapply Permutation_in; [symmetry; exact PMR| exact Hb]| right; exact Hb]. }
    rewrite Z.sub_0_r in OI2.
    (* [comment removed for export] *)
    destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5).
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add lframeA] in Ha; clear - Ha TOP; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]].
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
    cbn [fst snd]. apply implAp_ret_evt || apply implAp_from_evt.
    step. change (Z_to_bv 64 3369368) with (Z_to_bv 64 OSL_NULL).
    eapply ret_nullA; [exact OI2| exact HCX| exact FR| exact HP].
  Qed.

  (* [comment removed for export] *)
  Local Ltac ab_join_j t u J ABok :=
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let pt := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
      let pu := eval vm_compute in (bv_key (Z_to_bv 5 u)) in
      eapply (evt_cut segs (fun ms => exists vt vu : word, ms = MS (tset pu vu (tset pt vt R)) F (Z_to_bv 64 J) fc rv m ro));
      [ lazymatch type of ABok with
        | absh_ok ?b ?X ?s =>
            let k := fresh "k" in let K1 := fresh "K1" in let K2 := fresh "K2" in let Es := fresh "Es" in let Ez := fresh "Ez" in
            destruct (absh_cases b X s ABok) as [-> | (k & K1 & K2 & Es & Ez)];
            [ rewrite ?zxb_z8, ?sxb_z8; Step.step; try first [if_false | if_true]; ab_at_join
            | rewrite ?Es, ?Ez; clear Es Ez;
              ab_branch; Step.step; ab_addi_opt; rewrite ?ab_land7w, ?ab_land7u; ab_branch;
              Step.step;     (* [comment removed for export] *)
              ab_at_join ]
        end
      | let ms1 := fresh "ms" in let vt := fresh "abt" in let vu := fresh "abu" in
        intros ms1 (vt & vu & ->); map_cbv_set; clear ABok ]
    end.

  (* [comment removed for export] *)
  Definition linvA (k : skr bptr) (pq ll : Z) (ΣX : rts RT) (stX : ap_st bptr) (mX : mem) (OWX : list block) (boX : Z * Z)
      (NEW : list block) (adrk : bptr -> Z) (CX : Z) : Prop :=
    oinvS ΣX stX mX OWX boX NEW CX /\ Permutation NEW (sk_blocks adrk k) /\ sk_repA mX (OWX ++ NEW ++ LB) adrk k
    /\ (forall b, In b LB -> adrk (blk_id b) = adr (blk_id b))
    /\ rw_cells ctasegs mX (bv_unsigned sp + -96) lframeA /\ rw_cells ctasegs mX PIN [C8 (wz (D + pq))]
    /\ 2 <= pq /\ 0 <= ll /\ pq + ll <= zlength c /\ 3 * sk_num k + 2 <= pq /\ 2 + sk_wire k <= pq
    /\ na_sched (sk_data k) /\ match sk_data k with Some (_, na) => sk_num k <= na | None => True end
    /\ 13 + 9 * ll + 2 * mcost ll + push_reserve (sk_num k) <= CX.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sk_blocks_clientA : forall ΣX stX mX OWX boX NEW CX adrk k b a,
    oinvS ΣX stX mX OWX boX NEW CX -> Permutation NEW (sk_blocks adrk k) -> In b (sk_blocks adrk k) -> blk_addr b <= a < blk_addr b + blk_size b ->
    ax_client (NEW ++ LB) (bv_unsigned sp + -96) ([(PIN, PIN + 8)] ++ LIBW_A) a /\ ax_client (NEW ++ LB) (bv_unsigned sp + -96) LIBW_A a /\ a < bv_unsigned sp + -96.
  Proof.
    intros until a. intros OI PM Hb Ha. ctx. destruct CELL as (bq & HBQ & Q1 & Q2 & _).
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI) as (_ & _ & BND & _ & DJL & _). clear OF.
    assert (HN : In b NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]).
    pose proof (BND b ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HN)) as (B1 & B2 & B3 & B4).
    pose proof (DJL b bq HN HBQ) as DJ.
    assert (AC : aclient_addr (NEW ++ LB) (bv_unsigned sp + -96) a) by (right; right; exists b; split; [apply in_or_app; left; exact HN| exact Ha]).
    assert (NL : ~ rin_ivs LIBW_A a) by (intros HL; pose proof (libw_rangeA a HL); clear - H Ha B1 B3 B4; lia).
    split; [| split; [split; [exact NL| exact AC]| clear - Ha B3 CEIL LOSPu; lia]]. split; [| exact AC].
    intros HL. apply rin_ivs_app in HL as [HL|HL]; [cbn [rin_ivs fst snd] in HL; clear - HL Ha DJ Q1 Q2; lia| exact (NL HL)].
  Qed.

  (* [comment removed for export] *)
  Lemma iter_bodyA : forall (LOOPF : skr bptr -> Z -> Z -> AM (option (skr bptr))) (ll : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      (k : skr bptr) (pq : Z) ΣX stX mX OWX boX NEW adrk CX,
    (forall (k' : skr bptr) (pq' ll' : Z) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word) (FY : bvmap 5 word) (fcY : bv 32)
            ΣY stY mY OWY boY NEW' adrk' CY,
        linvA k' pq' ll' ΣY stY mY OWY boY NEW' adrk' CY -> ll' <= ll - 3 ->
        implAp (LOOPF k' pq' ll' stY) ΣY SPOST
          (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) y5 y6 y7 sp (Z_to_bv 64 0) y10 y11 y12 y13 y14 y15 y16 y17 (wz (adrk' (sk_blk k'))) (Z_to_bv 64 PIN) y20 y21
                   (Z_to_bv 64 SHB) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) (Z_to_bv 64 ll') (Z_to_bv 64 1) s11 y28 y29 y30 y31)
              FY (Z_to_bv 64 OSL_HEAD) fcY None mY (seg_rom ctasegs))) ->
    linvA k pq ll ΣX stX mX OWX boX NEW adrk CX -> 2 <= ll -> zlength c <= MAX_SCT_LIST_SIZE ->
    implAp ((let sct_len := u16be c pq in
             let p := pq + 2 in
             let ll2 := ll - 2 in
             if (sct_len =? 0) || (ll2 <? sct_len) then err_raise RS_list_sctlen ;;; sk_free_all k ;;; aret None
             else
               let ll3 := ll2 - sct_len in
               r <- o2i_sct c p sct_len ;;
               match r with
               | None => sk_free_all k ;;; aret None
               | Some sc => k' <- sk_push k sc ;; LOOPF k' (p + sct_len) ll3
               end) stX) ΣX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) (Z_to_bv 64 PIN) x20 x21
               (Z_to_bv 64 SHB) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) (Z_to_bv 64 ll) (Z_to_bv 64 1) s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 OSL_ITER) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until CX. intros IH LI L2 LENB. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    destruct LI as (OI & PM & SK & ADRK & FR & HP & PQ2 & LL0 & PQL & NUMB & WIRE & SCH & NLE & CRB).
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _ & CRX & _). clear OC.
    pose proof OI as (_ & _ & KO & KI & _ & HB & CRT & LBOK).
    destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0 in PQL; unfold zlength in PQL; cbn in PQL; clear - PQL PQ2 L2; lia|].
    pose proof (BND (pb, PA, psz) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (PB3 & _ & PB4 & PB5). cbn [blk_addr blk_size fst snd] in PB3, PB4, PB5.
    destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5).
    set (KA := adrk (sk_blk k)) in *.
    assert (HKIN : In (sk_blk k, KA, STACK_SIZE) (sk_blocks adrk k)) by (unfold CtSctP.SctStmt.sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity).
    assert (HKN : In (sk_blk k, KA, STACK_SIZE) NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact HKIN]).
    pose proof (BND (sk_blk k, KA, STACK_SIZE) ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HKN)) as (BK0 & _ & BKC & BKI). cbn [blk_addr blk_size fst snd] in BK0, BKC, BKI. unfold STACK_SIZE in BKC, BKI.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    pose proof (znth_range8 c pq DF) as R0. pose proof (znth_range8 c (pq + 1) DF) as R1.
    set (sl := u16be c pq). pose proof (u16be_range c pq) as SLR. fold sl in SLR.
    assert (HBQ' : In bq (OWX ++ NEW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HBQ).
    assert (HBD' : In (pb, PA, psz) (OWX ++ NEW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HPB).
    ablock HEAPX HBQ' ACCQ OFFQ. ablock HEAPX HBD' ACCD OFFD.
    pose proof (munch_refl [(PIN, PIN + 8)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (OFF : offshW [(PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ OFFD.
    frz Q5. frz PB5. frz BKI. frz PIND.
    unfold lframeA in FR. unfold MallocRep.wz in HP. unfold OSL_ITER, MallocRep.wz.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. step. step. ab_shload 1.
    pose proof (payload_readA _ D c pq (wa (D + pq)) HB DF ltac:(clear - PQ2 PQL L2; lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth c pq)) by (clear - R0; lia).
    lazymatch goal with H : absh_ok ?b _ _ |- _ => ab_join 13%Z 14%Z 0x3368ec%Z H end.     (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (pq + 1) (wa (D + pq + 1)) HB DF ltac:(clear - PQ2 PQL L2; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c (pq + 1))) by (clear - R1; lia).
    step. step. step.
    setreg 20%Z (Z_to_bv 64 sl)
      ltac:(subst sl; unfold u16be; rewrite !BY by (clear - PQ2 PQL L2; lia); f_equal;
            rewrite (unsigned_lit (znth c pq)), (unsigned_lit (znth c (pq + 1))) by (clear - R0 R1; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c pq * 256)) by (clear - R0; lia); symmetry; apply CtSctP.W_o2i_sig.lor_shl8; clear - R0 R1; lia).
    step. setreg 25%Z (Z_to_bv 64 (ll - 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - LL0 L2 PQL LENB PQ2; unfold MAX_SCT_LIST_SIZE in LENB; lia); bv_solve).
    step. step. setreg 10%Z (Z_to_bv 64 (D + pq + 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0' D63' PQ2 PQL L2; lia); bv_solve) || idtac.
    name_mem m1.
    match goal with H : munch _ mX m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs mX m1 |- _ => rename H into WM1 end.
    match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
    assert (OI1 : oinvS ΣX stX m1 OWX boX NEW CX).
    { kit @oinv_munch; [exact OI| exact MU1| exact WM1| exact MI1| exact STX|]. constructor; [| constructor]. right; left. exists (PIN, PIN + 8). split; [unfold XPs; left; reflexivity| cbn [fst snd]; clear; lia]. }
    assert (SK1 : sk_repA m1 (OWX ++ NEW ++ LB) adrk k).
    { eapply sk_repA_agree; [apply (agree_on_of_munch_nw _ _ _ MU1)| | exact SK]. intros b a Hb Ha. cbn [outside fst snd]. split; [| exact I].
      assert (HN : In b NEW) by (eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]). pose proof (DJL b bq HN HBQ) as DJ. clear - Ha DJ Q1 Q2. lia. }
    cbv zeta. fold sl.
    step. if_cases KS; zc KS.
    - (* [comment removed for export] *)
      replace ((sl =? 0) || (ll - 2 <? sl)) with true.
      2:{ symmetry. destruct (Z.eq_dec sl 0) as [->|NZ]; [reflexivity|]. rewrite O2iKitAR.land_ones64_small in KS by (clear - NZ SLR; lia). apply orb_true_intro. right. apply Z.ltb_lt. clear - KS NZ SLR; lia. }
      apply evt_done. eapply implAp_abind.
      { eapply (raise_siteA 0x336a20 5%nat OSL_RAISE2 RS_list_sctlen); [right; right; right; repeat split; reflexivity| exact OI1| clear - CRB LL0 SLR; pose proof (mcost_nonneg ll); pose proof (push_reserve_nonneg (sk_num k)); ecu; lia| exact FR| exact HP]. }
      intros r ΣF msF RP. unfold raise_postA in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & -> & OIF & FRF & HPF & AXF).
      cbv beta. unfold OSL_RAISE2. change (Z_to_bv 64 (3369532 + 28)) with (Z_to_bv 64 OSL_ERR).
      eapply (free_exitA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcF ΣF (snd r) mF OWF boX NEW (CX - GETOBJ_ERR_COST_A) adrk k);
        [exact OIF| clear - CRB LL0 SLR; pose proof (mcost_nonneg ll); pose proof (push_reserve_nonneg (sk_num k)); ecu; lia| exact PM| | clear - NUMB PQL LENB LL0; unfold sk_num in NUMB; unfold MAX_SCT_LIST_SIZE in LENB; lia| exact FRF| exact HPF].
      eapply sk_repA_relist; [| intros b Hb; apply in_or_app; right; apply in_or_app; left; eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]].
      eapply (sk_repA_agree _ m1 mF); [exact AXF| | exact SK1]. intros b a Hb Ha. exact (proj1 (proj2 (sk_blocks_clientA ΣX stX m1 OWX boX NEW CX adrk k b a OI1 PM Hb Ha))).
    - (* [comment removed for export] *)
      assert (SL1 : 1 <= sl <= ll - 2).
      { destruct (Z.eq_dec sl 0) as [E0|NZ]; [exfalso; rewrite E0 in KS; revert KS; change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615; unfold MAX_SCT_LIST_SIZE in LENB; clear - LENB PQL LL0 PQ2; lia|].
        rewrite O2iKitAR.land_ones64_small in KS by (clear - NZ SLR; lia). clear - KS NZ SLR; lia. }
      clear KS. replace ((sl =? 0) || (ll - 2 <? sl)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq| apply Z.ltb_ge]; clear - SL1; lia).
      step. step. step. step. apply evt_done.
      pose proof OI1 as (PRE1 & AX1 & KO1 & KI1 & KP1 & HB1 & CR1 & LBOK1).
      pose proof HO2I as W. unfold o2i_sct_specA2 in W.
      eapply implAp_abind.
      { eapply W with (LB := NEW ++ LB) (K := K) (adr := adrk) (c := c) (D := D) (p := pq + 2) (len := sl) (PIN := PIN) (lo := lo) (E := E) (bo := boX) (OW := OWX) (ras := bv_unsigned ra :: ras); clear W.
        - eapply ap_preA_weaken; [exact PRE1| clear; lia| | clear; ecu; lia].
          cbn [ar_RT push amb] in CRX |- *. clear - CRB CRX SL1 LL0 SLR; ecu. pose proof (mcost_mono sl ll ltac:(lia)). pose proof (mcost_nonneg sl). pose proof (push_reserve_nonneg (sk_num k)). lia.
        - reflexivity.
        - rewrite ESP. eapply uw_at_call; [exact OI1| exact FR].
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_osct CTX).
        - apply cons_ne.
        - exact KO1.
        - exact KI1.
        - split; [exact HB1|]. split; [exact DF|]. split; [clear - PB1 PB3; lia|]. split; [exact D63'|]. split; [clear - LENB PQL PQ2 LL0; unfold MAX_SCT_LIST_SIZE in LENB; lia|].
          right. exists (pb, PA, psz). split; [apply in_or_app; right; exact HPB| cbn; clear - PB1 PB2; lia].
        - clear - PQ2; lia.
        - unfold MAX_SCT_SIZE. clear - SL1 LL0 PQL LENB PQ2; unfold MAX_SCT_LIST_SIZE in LENB; lia.
        - clear - SL1 PQL; lia.
        - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| rewrite (ADRK b Hb); apply ADR; exact Hb].
          destruct b as [[q Aq] n]. cbn. symmetry. eapply (CtSctP.W_o2i_sct_list.sk_blocks_adr adrk k). eapply Permutation_in; [exact PM| exact Hb].
        - exists bq. split; [apply in_or_app; right; exact HBQ| split; [exact Q1| exact Q2]].
        - exact ALP.
        - unfold frozen in PIND. exact PIND.
        - replace (D + (pq + 2)) with (D + pq + 2) by (clear; lia). exact HP.
        - reflexivity.
        - reflexivity.
        - reflexivity. }
      clear W.
      intros r ΣO msO POST. unfold o2i_sct_postA2 in POST. rewrite ?ESP in POST.
      destruct POST as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & FS & fcS & mO & OWO & boO & adrO & NEWO
                        & -> & PREO & AXO & CRO & BKO & ADRO & FRO & LBOKO & RES).
      destruct r as [ox stO]. cbn [fst snd] in *.
      rewrite (ret_pc_even 0x33691c) by (clear; lia).
      cbn [ar_RT push amb] in CRO.
      assert (OIO : oinvS ΣO stO mO OWO boO (NEWO ++ NEW) (CX - O2I_SCT_COST_A sl)).
      { kit @oinv_after; [exact OI1| exact PREO| exact AXO| | exact CRO| | exact BKO| exact LBOKO].
        - intros a Ha. cbn [rin_ivs fst snd app] in Ha. destruct Ha as [Ha|[]]. right; left. unfold XPs. cbn [rin_ivs fst snd]. left. exact Ha.
        - cbn [ar_RT push amb] in CRX |- *. clear - CRB CRX SL1 LL0 SLR; ecu. pose proof (mcost_mono sl ll ltac:(lia)). pose proof (mcost_nonneg sl). pose proof (push_reserve_nonneg (sk_num k)). lia. }
      (* [comment removed for export] *)
      assert (CLf : forall a, bv_unsigned sp + -96 <= a < bv_unsigned sp -> ax_client (NEW ++ LB) (bv_unsigned sp + -96) ([(PIN, PIN + 8)] ++ LIBW_A) a).
      { intros a Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha Q1 Q2 Q4 CEIL GLO LOSPu; lia| left; clear - Ha TOP; unfold USTACK_TOP in *; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AXO) in FR; [| intros a Ha; apply CLf; cbn [cells_size csize Nat.add] in Ha; clear - Ha; lia].
      assert (SKO : sk_repA mO (OWO ++ (NEWO ++ NEW) ++ LB) adrk k).
      { eapply sk_repA_relist; [| intros b Hb; apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]].
        eapply (sk_repA_agree _ m1 mO); [exact AXO| | exact SK1]. intros b a Hb Ha. exact (proj1 (sk_blocks_clientA ΣX stX m1 OWX boX NEW CX adrk k b a OI1 PM Hb Ha)). }
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OIO) as (HEAPO & NDO & BNDO & FRSHO & DJLO & DJOO). clear OF.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OIO) as (_ & STO & _ & _ & _ & _ & MIO & CSO & ASO & CRO' & _). clear OC.
      pose proof ASO as (_ & (_ & RSO & _) & _).
      clear MU1 WM1. pose proof (munch_refl (@nil (Z * Z)) mO) as MU. pose proof (wmono_refl ctasegs mO) as WM.
      cbv beta. apply implAp_from_evt.
      destruct ox as [x|].
      2:{ (* [comment removed for export] *)
          destruct RES as (ENO & HPO). subst NEWO. cbn [app] in OIO, SKO.
          step. if_cases K0; zc K0; [| exfalso; apply K0; reflexivity]. clear K0.
          apply evt_done. change (Z_to_bv 64 3369560) with (Z_to_bv 64 OSL_ERR).
          eapply (free_exitA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FS fcS ΣO stO mO OWO boO NEW (CX - O2I_SCT_COST_A sl) adrk k);
            [exact OIO| cbn [ar_RT push amb] in CRX |- *; clear - CRB CRX SL1 LL0 SLR; ecu; pose proof (mcost_mono sl ll ltac:(lia)); pose proof (mcost_nonneg sl); pose proof (push_reserve_nonneg (sk_num k)); lia
            | exact PM| exact SKO| clear - NUMB PQL LENB LL0; unfold sk_num in NUMB; unfold MAX_SCT_LIST_SIZE in LENB; lia| exact FR| unfold MallocRep.wz in HPO; exact HPO]. }
      (* [comment removed for export] *)
      destruct RES as (ENO & SRX & HPO & VERX & WLX). unfold MallocRep.wz in HPO.
      assert (HXB : In (sc_blk x, adrO (sc_blk x), SCT_SIZE) NEWO) by (rewrite ENO; unfold CtSctP.W_sct_list_free.sct_blocks; rewrite !in_app_iff; do 4 right; left; reflexivity).
      pose proof (BNDO (sc_blk x, adrO (sc_blk x), SCT_SIZE) ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_app_iff; left; exact HXB)) as (AX0 & _ & AXC & AXI). cbn [blk_addr blk_size fst snd] in AX0, AXC, AXI. unfold SCT_SIZE in AXC, AXI.
      set (AX := adrO (sc_blk x)) in *.
      step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?O2iKitAR.land_ones64_small, ?unsigned_lit by (clear - AX0 AXC CN; lia); clear - AX0; lia|]. clear K0.
      step. step. setreg 25%Z (Z_to_bv 64 (ll - 2 - sl)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - SL1 LL0 PQL LENB PQ2 SLR; unfold MAX_SCT_LIST_SIZE in LENB; lia); bv_solve).
      step. step. step. apply evt_done.
      (* [comment removed for export] *)
      set (SKB := dblk adrk (sk_data k) ++ [(sk_blk k, KA, STACK_SIZE)]).
      set (REST := NEWO ++ scts_blocks adrk (sk_items k)).
      assert (PMS : Permutation (NEWO ++ NEW) (SKB ++ REST)).
      { subst SKB REST. unfold CtSctP.SctStmt.sk_blocks. fold KA. eapply Permutation_trans; [apply Permutation_app_head; exact PM|].
        symmetry. eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_refl. }
      assert (OIS : oinvS ΣO stO mO OWO boO (SKB ++ REST) (CX - O2I_SCT_COST_A sl)) by (kit @oinv_perm; [exact PMS| exact OIO]).
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OIS) as (HEAPS & NDS & _ & FRSHS & DJLS & DJOS). clear OF.
      pose proof OIS as (_ & _ & _ & _ & _ & _ & _ & LBOKS). pose proof LBOKS as LBOKS'. rewrite Forall_app in LBOKS'. destruct LBOKS' as [LBOKB LBOKR].
      rewrite <- app_assoc in HEAPS.
      pose proof (AH_adopt_list ΣO SKB OWO (REST ++ LB) mO HEAPS LBOKB) as HEAPa.
      (* [comment removed for export] *)
      pose proof SKO as ((HKL & KAL) & (sorted & SRT & HCK) & HDK & HFK & NDK). fold KA in HKL, HCK, KAL. rewrite sk_cells_rawA in HCK.
      assert (HDW : exists jb,
                match sk_data k with
                | Some (q, na) => In (q, optr adrk (sk_data k), 8 * na) (SKB ++ OWO) /\ q <> sk_blk k /\ sk_num k <= na /\ SK_MIN_NODES <= na < 2^23
                                  /\ rw_cells ctasegs mO (optr adrk (sk_data k)) (map C8 (map (ptrw adrk) (sk_items k)) ++ [CB (length jb) jb]) /\ Z.of_nat (length jb) = 8 * (na - sk_num k)
                | None => sk_items k = [] /\ optr adrk (sk_data k) = 0 /\ jb = []
                end).
      { destruct (sk_data k) as [[q na]|] eqn:EDK.
        - destruct HDK as (HI & _ & Hn & Hna & jb & JB & HBK). exists jb. split; [subst SKB; apply in_or_app; left; cbn; left; reflexivity|]. split.
          { intros E0. rewrite !map_app in NDK. cbn [CtSctP.W_sk_leaves.dblk map blk_id fst snd app] in NDK.
            destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ NDK) as (N23 & _ & _). apply NoDup_cons_iff in N23. destruct N23 as [NN _]. apply NN. left. symmetry. exact E0. }
          split; [exact NLE|]. split; [exact Hna|]. split; [unfold CtSctP.W_sk_leaves.data_block in HBK; exact HBK| exact JB].
        - exists []. split; [exact HDK|]. split; reflexivity. }
      destruct HDW as (jb & HDW).
      assert (PRC : sk_push_mcost k <= push_reserve (sk_num k) - push_reserve (sk_num k + 1)).
      { unfold sk_push_mcost. destruct (sk_data k) as [[q na]|] eqn:EDK; [| pose proof (push_reserve_mono (sk_num k) (sk_num k + 1) ltac:(clear; lia)); clear - H; lia].
        cbn [na_sched] in SCH. pose proof (sched_ge4 na SCH) as NA4.
        destruct (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) eqn:RM; [pose proof (push_reserve_mono (sk_num k) (sk_num k + 1) ltac:(clear; lia)); clear - H; lia|].
        apply Z.leb_gt in RM. assert (EN : sk_num k = na) by (unfold SK_MIN_NODES in RM; clear - RM NLE NA4; lia). rewrite EN.
        apply sched_grow_cost; [exact SCH| clear - EN NUMB PQL LENB LL0; unfold MAX_SCT_LIST_SIZE in LENB; lia]. }
      change (Z_to_bv 64 2082552) with (wz OPENSSL_SK_PUSH_A).
      eapply implAp_abind.
      { eapply (@OPENSSL_sk_push_walkA AR UK BE REA) with (OW := SKB ++ OWO) (LB := REST ++ LB) (lo := lo) (SA := KA) (X := AX) (D := optr adrk (sk_data k)) (sorted := sorted)
                                                         (ws := map (ptrw adrk) (sk_items k)) (jb := jb) (ras := bv_unsigned ra :: ras);
          [ exact HEAPa| rewrite ESP; exact STO| exact CEIL| rewrite ESP; clear - LOSPu; ecu; lia| rewrite ESP; clear - TOP; lia| rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia
          | exact MIO| reflexivity| rewrite unsigned_lit by (clear; lia); reflexivity| exact CSO| exact RSO
          | subst SKB; apply in_or_app; left; apply in_or_app; right; left; reflexivity
          | exact HCK| exact SRT| clear - NUMB PQL LENB LL0; unfold MAX_SCT_LIST_SIZE in LENB; lia| exact HDW
          | unfold zlength, sk_num; rewrite !length_map; reflexivity| clear - AX0 AXC CN; lia| reflexivity| reflexivity
          | eapply Z.le_trans; [exact PRC|]; cbn [ar_RT push amb] in CRO' |- *; pose proof (push_reserve_nonneg (sk_num k + 1)); pose proof (mcost_nonneg (ll - 2 - sl));
            clear - CRB CRO' H H0 SL1 LL0 SLR; ecu; pose proof (mcost_mono sl ll ltac:(lia)); lia
          | rewrite ESP; eapply uw_at_call; [exact OIS| exact FR]
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_push CTX) ]. }
      intros r1 ΣP msP POP. unfold push_postA in POP. rewrite ?ESP in POP.
      destruct POP as (z0 & z1 & z2 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & FP & fcP & mP & q' & D' & na' & jb'
                       & -> & ER1 & MIP & STP & AGP & CRP & BRP & HEAPP & HCP & HDP & JBP & NA1 & NA2 & ENA).
      subst r1. cbn [fst snd].
      rewrite (ret_pc_even 0x336938) by (clear; lia). unfold MallocRep.wz.
      cbn [ar_RT push amb] in CRP.
      (* [comment removed for export] *)
      assert (RIN1 : forall b, In b NEWO -> In b REST) by (intros b Hb; subst REST; apply in_or_app; left; exact Hb).
      assert (RIN2 : forall b, In b (scts_blocks adrk (sk_items k)) -> In b REST) by (intros b Hb; subst REST; apply in_or_app; right; exact Hb).
      assert (NQO : forall q0, In q0 (map blk_id (NEWO ++ NEW)) -> ~ In q0 (map blk_id OWO)).
      { intros q0 Hq0 Hin. apply in_map_iff in Hq0. destruct Hq0 as (b & <- & Hb). apply (FRSHO b Hb). rewrite map_app. apply in_or_app. left. exact Hin. }
      assert (SKNO : ~ In (sk_blk k) (map blk_id OWO)).
      { apply NQO. rewrite map_app. apply in_or_app. right. exact (in_map blk_id _ _ HKN). }
      assert (ELR : lremove (sk_data k) (SKB ++ OWO) = (sk_blk k, KA, STACK_SIZE) :: OWO).
      { subst SKB. destruct (sk_data k) as [[q na]|] eqn:EDK; cbn [CtSctP.W_sk_leaves.dblk CtRepP.ApErrKit.lremove app]; [| reflexivity].
        destruct HDW as (HqI & NQS & _).
        rewrite lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl. rewrite lb_remove_cons. cbn [blk_id fst snd].
        rewrite (bptr_eqb_neq (sk_blk k) q) by (intros E0; apply NQS; symmetry; exact E0). f_equal. apply lb_remove_notin.
        apply NQO. rewrite map_app. apply in_or_app. right. apply (in_map blk_id _ (q, adrk q, 8 * na)).
        eapply Permutation_in; [apply Permutation_sym; exact PM|]. unfold CtSctP.SctStmt.sk_blocks. rewrite EDK, !in_app_iff. right. left. left. reflexivity. }
      rewrite ELR in HEAPP, AGP. rewrite lb_remove_cons in AGP. cbn [blk_id fst snd] in AGP. rewrite bptr_eqb_refl, (lb_remove_notin _ _ SKNO) in AGP.
      change ((q', D', 8 * na') :: (sk_blk k, KA, STACK_SIZE) :: OWO) with ([(q', D', 8 * na'); (sk_blk k, KA, STACK_SIZE)] ++ OWO) in HEAPP.
      destruct (AH_release_list ΣP _ OWO (REST ++ LB) mP HEAPP) as [HEAPr LBOK2].
      set (NEW1 := [(q', D', 8 * na'); (sk_blk k, KA, STACK_SIZE)] ++ REST).
      assert (N1a : forall b, In b REST -> In b NEW1) by (intros b Hb; subst NEW1; apply in_or_app; right; exact Hb).
      assert (PC0 : 0 <= sk_push_mcost k) by (unfold sk_push_mcost; destruct (sk_data k) as [[q0 na0]|]; [destruct (Z.max (sk_num k + 1) SK_MIN_NODES <=? na0); [clear; lia| apply mcost_nonneg]| clear; lia]).
      assert (OIP : oinvS ΣP stO mP OWO boO NEW1 (CX - O2I_SCT_COST_A sl - sk_push_mcost k)).
      { kit @oinv_heap; [exact OIS| eapply agree_on_mono; [exact AGP| intros a [Ha _]; exact Ha]| | subst NEW1; rewrite <- app_assoc; exact HEAPr| subst NEW1; apply Forall_app; split; [exact LBOK2| exact LBOKR]| exact MIP| exact STP| exact CRP|].
        - intros b Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; right; exact Hb].
        - split; [exact PC0|]. cbn [ar_RT push amb] in CRX |- *. pose proof (push_reserve_nonneg (sk_num k + 1)).
          clear - CRB CRX PRC H SL1 LL0 SLR; ecu. pose proof (mcost_mono sl ll ltac:(lia)). pose proof (mcost_nonneg ll). lia. }
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OIP) as (HEAPP' & NDP & BNDP & FRSHP & DJLP & DJOP). clear OF.
      (* [comment removed for export] *)
      set (k1 := mkSK (sk_blk k) (Some (q', na')) (sk_items k ++ [x])).
      set (adrk' := fun b : bptr => if bptr_eqb b q' then D' else adrO b).
      assert (E1 : adrk' q' = D') by (subst adrk'; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      pose proof (AH_nodup _ _ _ _ HEAPP) as NQ. cbn [map blk_id fst snd app] in NQ. apply NoDup_cons_iff in NQ. destruct NQ as [NQ' _].
      (* [comment removed for export] *)
      assert (AGX : forall q0, q0 = sk_blk k \/ In q0 (map blk_id (OWO ++ REST ++ LB)) -> adrk' q0 = adrO q0).
      { intros q0 Hq0. subst adrk'. cbn beta. rewrite (bptr_eqb_neq q0 q'); [reflexivity|]. intros ->. apply NQ'.
        destruct Hq0 as [->|Hq0]; [left; reflexivity| right]. rewrite !map_app, !in_app_iff in Hq0 |- *. exact Hq0. }
      (* [comment removed for export] *)
      assert (AOK : forall q0, In q0 (map blk_id (sk_blocks adrk k)) -> adrO q0 = adrk q0).
      { intros q0 Hq0. apply in_map_iff in Hq0. destruct Hq0 as (b & <- & Hb). apply ADRO. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]. }
      assert (EKA' : adrk' (sk_blk k) = KA).
      { rewrite AGX by (left; reflexivity). subst KA. apply AOK. exact (in_map blk_id _ _ HKIN). }
      assert (AIT : forall s q0, In s (sk_items k) -> In q0 (CtSctP.O2iKit.sct_ids s) -> adrk' q0 = adrk q0).
      { intros s q0 Hs Hq0. rewrite <- (CtSctP.W_o2i_sct_list.sct_blocks_ids adrk) in Hq0. apply in_map_iff in Hq0. destruct Hq0 as (b & <- & Hb).
        pose proof (CtSctP.W_o2i_sct_list.scts_blocks_in adrk _ _ _ Hs Hb) as HbS.
        rewrite AGX by (right; rewrite !map_app, !in_app_iff; right; left; first [exact (in_map blk_id _ _ (RIN2 _ HbS))| right; exact (in_map blk_id _ _ HbS)]).
        apply AOK. unfold CtSctP.SctStmt.sk_blocks. rewrite !map_app, !in_app_iff. left. exact (in_map blk_id _ _ HbS). }
      assert (AXT : forall q0, In q0 (CtSctP.O2iKit.sct_ids x) -> adrk' q0 = adrO q0).
      { intros q0 Hq0. rewrite <- (CtSctP.W_o2i_sct_list.sct_blocks_ids adrO), <- ENO in Hq0. apply in_map_iff in Hq0. destruct Hq0 as (b & <- & Hb).
        apply AGX. right. rewrite !map_app, !in_app_iff. right. left. first [exact (in_map blk_id _ _ (RIN1 _ Hb))| left; exact (in_map blk_id _ _ Hb)]. }
      assert (EB1 : sk_blocks adrk' k1 = (scts_blocks adrk (sk_items k) ++ NEWO) ++ [(q', D', 8 * na'); (sk_blk k, KA, STACK_SIZE)]).
      { unfold CtSctP.SctStmt.sk_blocks. subst k1. cbn [sk_items sk_data sk_blk CtSctP.W_sk_leaves.dblk]. rewrite E1, EKA'.
        rewrite CtSctP.W_o2i_sct_list.scts_blocks_app. cbn [CtSctP.W_sct_list_free.scts_blocks]. rewrite app_nil_r.
        rewrite (CtSctP.W_o2i_sct_list.scts_blocks_ext adrk adrk' (sk_items k)) by (intros s q0 Hs Hq0; exact (AIT s q0 Hs Hq0)).
        rewrite (CtSctP.W_o2i_sct_list.sct_blocks_ext adrO adrk' x) by (intros q0 Hq0; exact (AXT q0 Hq0)). rewrite <- ENO, <- !app_assoc. reflexivity. }
      assert (PM1 : Permutation NEW1 (sk_blocks adrk' k1)).
      { rewrite EB1. subst NEW1 REST. eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply Permutation_app_comm. }
      (* [comment removed for export] *)
      assert (CLP : forall b a, In b REST -> blk_addr b <= a < blk_addr b + blk_size b -> aclient_addr (OWO ++ REST ++ LB) (bv_unsigned sp + -96) a).
      { intros b a Hb Ha. right; right. exists b. split; [apply in_or_app; right; apply in_or_app; left; exact Hb| exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha TOP; unfold USTACK_TOP in *; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP) in HPO; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]].
      assert (HFK' : Forall (sct_repA mP (OWO ++ NEW1 ++ LB) adrk') (sk_items k ++ [x])).
      { apply Forall_app. split.
        - apply Forall_forall. intros s Hs. pose proof (proj1 (Forall_forall _ _) HFK s Hs) as SRs.
          apply (sct_repA_ext adrk adrk'); [intros q0 Hq0; exact (AIT s q0 Hs Hq0)|].
          eapply sct_repA_relist; [| intros b Hb; apply in_or_app; right; apply in_or_app; left; apply N1a; apply RIN2; eapply CtSctP.W_o2i_sct_list.scts_blocks_in; [exact Hs| exact Hb]].
          eapply sct_repA_agree; [exact AGP| | exact SRs]. intros b a Hb Ha. eapply CLP; [apply RIN2; eapply CtSctP.W_o2i_sct_list.scts_blocks_in; [exact Hs| exact Hb]| exact Ha].
        - constructor; [| constructor]. apply (sct_repA_ext adrO adrk'); [intros q0 Hq0; exact (AXT q0 Hq0)|].
          eapply sct_repA_relist; [| intros b Hb; apply in_or_app; right; apply in_or_app; left; apply N1a; apply RIN1; rewrite ENO; exact Hb].
          eapply sct_repA_agree; [exact AGP| | exact SRX]. intros b a Hb Ha. eapply CLP; [apply RIN1; rewrite ENO; exact Hb| exact Ha]. }
      assert (EN1 : sk_num k1 = sk_num k + 1) by (subst k1; unfold sk_num, zlength; cbn [sk_items]; rewrite length_app; cbn [length]; lia).
      assert (SK2 : sk_repA mP (OWO ++ NEW1 ++ LB) adrk' k1).
      { split; [| split; [| split; [| split; [exact HFK'|]]]].
        - change (sk_blk k1) with (sk_blk k). rewrite EKA'. split; [apply in_or_app; right; apply in_or_app; left; subst NEW1; right; left; reflexivity| exact KAL].
        - exists (sorted_after sorted (sk_num k)). split; [unfold CtSctP.W_sk_push.sorted_after; destruct (negb (sorted =? 0) && (0 <? sk_num k)); clear - SRT; lia|].
          change (sk_blk k1) with (sk_blk k). rewrite EKA', sk_cells_rawA, EN1. change (sk_data k1) with (Some (q', na')). cbn [optr olen]. rewrite E1. exact HCP.
        - change (sk_data k1) with (Some (q', na')). cbv beta iota. rewrite E1, EN1. destruct BRP as (_ & D16 & _).
          split; [apply in_or_app; right; apply in_or_app; left; subst NEW1; left; reflexivity|]. split; [exact D16|]. split; [clear - NA1; lia|]. split; [exact NA2|].
          exists jb'. split; [clear - JBP; lia|]. unfold CtSctP.W_sk_leaves.data_block. change (sk_items k1) with (sk_items k ++ [x]).
          rewrite map_app. cbn [map]. rewrite (map_ext_in (ptrw adrk') (ptrw adrk) (sk_items k)).
          2:{ intros s Hs. unfold CtSctP.W_sk_leaves.ptrw. rewrite (AIT s (sc_blk s) Hs); [reflexivity|]. unfold CtSctP.O2iKit.sct_ids. rewrite !in_app_iff. do 4 right. left. reflexivity. }
          unfold CtSctP.W_sk_leaves.ptrw at 2. rewrite (AXT (sc_blk x)) by (unfold CtSctP.O2iKit.sct_ids; rewrite !in_app_iff; do 4 right; left; reflexivity).
          subst AX. rewrite map_app in HDP. cbn [map] in HDP. rewrite map_app. cbn [map]. unfold MallocRep.wz in HDP |- *. exact HDP.
        - eapply BnHeapA.nodup_ids_perm; [exact PM1|]. rewrite (map_app blk_id OWO), (map_app blk_id NEW1 LB) in NDP.
          destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ NDP) as (N23 & _ & _). destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ N23) as (_ & _ & N2). exact N2. }
      (* [comment removed for export] *)
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mP) as MU. pose proof (wmono_refl ctasegs mP) as WM.
      apply implAp_from_evt. step. if_cases KN; zc KN; [| exfalso; revert KN; rewrite ?O2iKitAR.land_ones64_small, ?unsigned_lit by (clear - NUMB PQL LENB LL0 PQ2; unfold sk_num in *; unfold MAX_SCT_LIST_SIZE in LENB; pose proof (zlength_ge0' (sk_items k)); lia); clear - NUMB PQ2; unfold sk_num in *; pose proof (zlength_ge0' (sk_items k)); lia].
      clear KN. apply evt_done. change (Z_to_bv 64 3369136) with (Z_to_bv 64 OSL_HEAD).
      replace (Z_to_bv 64 KA) with (wz (adrk' (sk_blk k1))) by (change (sk_blk k1) with (sk_blk k); rewrite EKA'; reflexivity).
      change (mkSK (sk_blk k) (Some (q', na')) (sk_items k ++ [x])) with k1.
      eapply (IH k1 (pq + 2 + sl) (ll - 2 - sl)); [| clear - SL1; lia].
      split; [exact OIP|]. split; [exact PM1|]. split; [exact SK2|].
      split. { intros b Hb. rewrite AGX by (right; rewrite !map_app, !in_app_iff; right; right; exact (in_map blk_id _ _ Hb)). rewrite (ADRO b) by (apply in_or_app; right; exact Hb). apply ADRK. exact Hb. }
      split; [exact FR|]. split; [unfold MallocRep.wz; replace (D + (pq + 2 + sl)) with (D + (pq + 2) + sl) by (clear; lia); exact HPO|].
      rewrite EN1. change (sk_data k1) with (Some (q', na')). cbv beta iota. cbn [na_sched].
      assert (WK1 : sk_wire k1 = sk_wire k + 2 + i2o_sct_len x) by (subst k1; rewrite <- (sk_wire_snoc (sk_blk k) (Some (q', na'))); unfold sk_wire; reflexivity).
      assert (SCH1 : In na' sched).
      { rewrite ENA. unfold sk_na_after. destruct (sk_data k) as [[q0 na0]|] eqn:EDK; [| left; reflexivity]. cbn [na_sched] in SCH.
        destruct (Z.max (sk_num k + 1) SK_MIN_NODES <=? na0) eqn:RM; [exact SCH|]. apply sched_next; [exact SCH|].
        apply Z.leb_gt in RM. pose proof (sched_ge4 na0 SCH). unfold SK_MIN_NODES in RM. clear - RM H NLE NUMB PQL LENB LL0. unfold MAX_SCT_LIST_SIZE in LENB. lia. }
      repeat split; try exact SCH1.
      + clear - PQ2 SL1; lia.
      + clear - SL1; lia.
      + clear - PQL SL1; lia.
      + clear - NUMB SL1; lia.
      + rewrite WK1. clear - WIRE WLX; lia.
      + clear - NA1; lia.
      + pose proof (mcost_superadd (ll - 2 - sl) sl ltac:(clear - SL1; lia) ltac:(clear - SL1; lia) ltac:(clear - SL1 LL0 PQL LENB PQ2; unfold MAX_SCT_LIST_SIZE in LENB; lia)) as MS1.
        replace (ll - 2 - sl + sl) with (ll - 2) in MS1 by (clear; lia). pose proof (mcost_mono (ll - 2) ll ltac:(clear - SL1; lia)) as MS2.
        clear - CRB PRC MS1 MS2 SL1 LL0; ecu. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_okA : forall fuel (ll : Z) (k : skr bptr) (pq : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW adrk CX,
    linvA k pq ll ΣX stX mX OWX boX NEW adrk CX -> ll < Z.of_nat fuel -> zlength c <= MAX_SCT_LIST_SIZE ->
    implAp (o2i_loop fuel c k pq ll stX) ΣX SPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 (wz (adrk (sk_blk k))) (Z_to_bv 64 PIN) x20 x21
               (Z_to_bv 64 SHB) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) (Z_to_bv 64 ll) (Z_to_bv 64 1) s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 OSL_HEAD) fcX None mX (seg_rom ctasegs)).
  Proof.
    induction fuel as [|f IHf]; intros until CX; intros LI LLF LENB.
    { exfalso. destruct LI as (_ & _ & _ & _ & _ & _ & _ & LL0 & _). cbn in LLF. clear - LL0 LLF. lia. }
    ctx. pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    pose proof LI as (OI & PM & SK & ADRK & FR & HP & PQ2 & LL0 & PQL & NUMB & WIRE & SCH & NLE & CRB).
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (push_reserve_nonneg (sk_num k)) as PR0. pose proof (mcost_nonneg ll) as ML0.
    cbn [o2i_loop]. unfold OSL_HEAD, MallocRep.wz. unfold MallocRep.wz in HP.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    apply implAp_from_evt. step. if_cases K0; zc K0.
    - (* [comment removed for export] *)
      replace (ll <=? 0) with true by (symmetry; apply Z.leb_le; revert K0; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; clear - LENB LL0 PQL PQ2; lia); clear; lia).
      assert (L0 : ll = 0) by (revert K0; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; clear - LENB LL0 PQL PQ2; lia); clear - LL0; lia). clear K0.
      step. if_cases K9; zc K9; [| exfalso; apply K9; reflexivity]. clear K9.
      apply evt_done. apply implAp_aret_evt. change (Z_to_bv 64 3369372) with (Z_to_bv 64 OSL_RET).
      eapply ret_someA; [exact OI| clear - CRB PR0 ML0 LL0; lia| exact PM| exact SK| exact ADRK| rewrite ELEN; clear - WIRE PQL L0; lia| rewrite ELEN; exact LENB| rewrite ELEN; clear - NUMB PQL L0; unfold sk_num in NUMB; lia| exact FR| exact HP].
    - assert (L1 : 1 <= ll) by (revert K0; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; clear - LENB LL0 PQL PQ2; lia); clear - LL0; lia). clear K0.
      replace (ll <=? 0) with false by (symmetry; apply Z.leb_gt; clear - L1; lia).
      step. if_cases K1; zc K1.
      + (* [comment removed for export] *)
        assert (E1 : ll = 1) by (revert K1; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; clear - LENB LL0 PQL PQ2; lia); clear; lia). clear K1.
        replace (ll <? 2) with true by (symmetry; apply Z.ltb_lt; clear - E1; lia).
        apply evt_done. eapply implAp_abind.
        { eapply (raise_siteA 0x3369d8 6%nat OSL_RAISE2 RS_list_lt2); [right; right; left; repeat split; reflexivity| exact OI| clear - CRB PR0 ML0 LL0; ecu; lia| exact FR| exact HP]. }
        intros r ΣF msF RP. unfold raise_postA in RP.
        destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & -> & OIF & FRF & HPF & AXF).
        cbv beta. unfold OSL_RAISE2. change (Z_to_bv 64 (3369532 + 28)) with (Z_to_bv 64 OSL_ERR).
        assert (OI' : oinvS ΣX stX mX OWX boX NEW CX) by exact OI.
        eapply (free_exitA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF fcF ΣF (snd r) mF OWF boX NEW (CX - GETOBJ_ERR_COST_A) adrk k);
          [exact OIF| clear - CRB PR0 ML0 LL0; ecu; lia| exact PM| | clear - NUMB PQL LENB LL0; unfold sk_num in NUMB; unfold MAX_SCT_LIST_SIZE in LENB; lia| exact FRF| exact HPF].
        eapply sk_repA_relist; [| intros b Hb; apply in_or_app; right; apply in_or_app; left; eapply Permutation_in; [apply Permutation_sym; exact PM| exact Hb]].
        eapply (sk_repA_agree _ mX mF); [exact AXF| | exact SK]. intros b a Hb Ha. exact (proj1 (proj2 (sk_blocks_clientA ΣX stX mX OWX boX NEW CX adrk k b a OI' PM Hb Ha))).
      + (* [comment removed for export] *)
        assert (L2 : 2 <= ll) by (revert K1; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LENB; clear - LENB LL0 PQL PQ2; lia); clear - L1; lia). clear K1.
        replace (ll <? 2) with false by (symmetry; apply Z.ltb_ge; clear - L2; lia).
        apply evt_done. change (Z_to_bv 64 3369144) with (Z_to_bv 64 OSL_ITER).
        eapply (iter_bodyA (o2i_loop f c) ll); [| exact LI| exact L2| exact LENB].
        intros until CY. intros LI' LL'. eapply IHf; [exact LI'| cbn in LLF; clear - LLF LL'; lia| exact LENB].
  Qed.

  (* [comment removed for export] *)
  Theorem list_mainA : forall (tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tp = wz TP_A ->
    implAp (o2i_sct_list c len st) Σ SPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz PIN) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz O2I_SCT_LIST_A) fc None m (seg_rom ctasegs)).
  Proof.
    intros until t6. intros TP. ctx. subst tp.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & _).
    pose proof oinv0 as OI0.
    unfold MallocRep.wz in HPIN. pose proof HPIN as HP. clear HPIN.
    destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    unfold O2I_SCT_LIST_A, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. do 14 step.
    step. step. step. step. name_mem m1.
    assert (OI1 : oinvS Σ st m1 OW bo [] O2I_SCT_LIST_COST_A).
    { kit @oinv_munch; [exact OI0| exact MU| exact WM| exact MI| exact ST| constructor; [left; cbn [fst snd]; clear - LOSPu; lia| constructor]]. }
    unfold o2i_sct_list.
    step. if_cases KL; zc KL.
    2:{ (* [comment removed for export] *)
        replace ((len <? 2) || (MAX_SCT_LIST_SIZE <? len)) with true.
        2:{ symmetry. unfold MAX_SCT_LIST_SIZE. destruct (Z.lt_ge_cases len 2) as [Hl|Hl]; [apply orb_true_intro; left; apply Z.ltb_lt; exact Hl|].
            destruct (Z.lt_ge_cases 65535 len) as [Hh|Hh]; [apply orb_true_intro; right; apply Z.ltb_lt; exact Hh|].
            exfalso. revert KL. rewrite O2iKitAR.land_ones64_neg by (clear - Hl Hh; lia). clear - Hl Hh; lia. }
        apply evt_done. eapply implAp_abind.
        { eapply (raise_siteA 0x3367b0 6%nat OSL_RAISE1 RS_list_len); [left; repeat split; reflexivity| exact OI1| clear; ecu; lia| exact FR| exact HP]. }
        intros r ΣF msF RP. unfold raise_postA in RP.
        destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & -> & OIF & FRF & HPF & AXF).
        cbn [fst snd]. apply implAp_aret_evt. unfold OSL_RAISE1. change (Z_to_bv 64 (3369340 + 28)) with (Z_to_bv 64 OSL_NULL).
        eapply ret_nullA; [exact OIF| clear; ecu; lia| exact FRF| exact HPF]. }
    (* [comment removed for export] *)
    assert (LEN : 2 <= len <= MAX_SCT_LIST_SIZE).
    { unfold MAX_SCT_LIST_SIZE. pose proof (zlength_ge0' c) as Z0. rewrite <- ELEN in Z0.
      destruct (Z.lt_ge_cases len 65536) as [Hs|Hs].
      - rewrite O2iKitAR.land_ones64_neg in KL by (clear - Hs Z0; lia). clear - KL Hs Z0. lia.
      - exfalso. rewrite O2iKitAR.land_ones64_small in KL by (clear - Hs D63' ELEN D0'; subst len; lia). clear - KL Hs D63' ELEN D0'. subst len. lia. }
    replace ((len <? 2) || (MAX_SCT_LIST_SIZE <? len)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; clear - LEN; lia). clear KL.
    destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0 in ELEN; unfold zlength in ELEN; cbn in ELEN; clear - ELEN LEN; lia|].
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI1) as (HEAP1 & ND1 & BND & _). clear OF. cbn [app] in HEAP1.
    pose proof (BND (pb, PA, psz) ltac:(apply in_app_iff; right; exact HPB)) as (PB3 & _ & PB4 & PB5). cbn [blk_addr blk_size fst snd] in PB3, PB4, PB5.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    pose proof (znth_range8 c 0 DF) as R0. pose proof (znth_range8 c 1 DF) as R1.
    pose proof OI1 as (_ & _ & _ & _ & _ & HB1 & _).
    set (ll := u16be c 0). pose proof (u16be_range c 0) as LLR. fold ll in LLR.
    assert (HBQ' : In bq (OW ++ LB)) by (apply in_app_iff; right; exact HBQ). assert (HBD' : In (pb, PA, psz) (OW ++ LB)) by (apply in_app_iff; right; exact HPB).
    ablock HEAP1 HBQ' ACCQ OFFQ. ablock HEAP1 HBD' ACCD OFFD.
    clear MU WM. pose proof (munch_refl [(PIN, PIN + 8)]%Z m1) as MU. pose proof (wmono_refl ctasegs m1) as WM.
    assert (OFF : offshW [(PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ OFFD.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI1) as (_ & ST1 & _ & _ & _ & _ & MI1 & _). clear OC.
    frz Q5. frz PB5. frz PIND.
    (* [comment removed for export] *)
    step. step. step. step. step. ab_shload 1.
    pose proof (payload_readA _ D c 0 (wa D) HB1 DF ltac:(clear - LEN ELEN; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD. rewrite (zxb_lit (znth c 0)) by (clear - R0; lia).
lazymatch goal with H : absh_ok ?b _ _ |- _ => ab_join 14%Z 15%Z 0x33681c%Z H end.     (* [comment removed for export] *)
    pose proof (payload_readA _ D c 1 (wa (D + 1)) HB1 DF ltac:(clear - LEN ELEN; lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth c 1)) by (clear - R1; lia).
    (* [comment removed for export] *)
    step. step. setreg 10%Z (Z_to_bv 64 (D + 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0' D63'; lia); bv_solve) || idtac.
    step. setreg 25%Z (Z_to_bv 64 ll)
      ltac:(subst ll; unfold u16be; rewrite !BY by (clear - LEN ELEN; lia); replace (0 + 1) with 1 by (clear; lia); f_equal;
            rewrite (unsigned_lit (znth c 0)), (unsigned_lit (znth c 1)) by (clear - R0 R1; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c 0 * 256)) by (clear - R0; lia); symmetry; apply CtSctP.W_o2i_sig.lor_shl8; clear - R0 R1; lia).
    step. setreg 12%Z (Z_to_bv 64 (len - 2)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LEN; clear - LEN; lia); bv_solve).
    step. name_mem m2.
    match goal with H : munch _ m1 m2 |- _ => rename H into MU2 end. match goal with H : wmono ctasegs m1 m2 |- _ => rename H into WM2 end.
    match goal with H : mem_inv ctasegs m2 |- _ => rename H into MI2 end.
    assert (OI2 : oinvS Σ st m2 OW bo [] O2I_SCT_LIST_COST_A).
    { kit @oinv_munch; [exact OI1| exact MU2| exact WM2| exact MI2| exact ST1|]. constructor; [| constructor]. right; left. exists (PIN, PIN + 8). split; [unfold XPs; left; reflexivity| cbn [fst snd]; clear; lia]. }
    step. if_cases KM; zc KM.
    { (* [comment removed for export] *)
      replace (negb (ll =? len - 2)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; intros E0; apply KM; rewrite E0; reflexivity).
      apply evt_done. eapply implAp_abind.
      { eapply (raise_siteA 0x336960 5%nat OSL_RAISE1 RS_list_mismatch); [right; left; repeat split; reflexivity| exact OI2| clear; ecu; lia| exact FR| exact HP]. }
      intros r ΣF msF RP. unfold raise_postA in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & -> & OIF & FRF & HPF & AXF).
      cbn [fst snd]. apply implAp_aret_evt. unfold OSL_RAISE1. change (Z_to_bv 64 (3369340 + 28)) with (Z_to_bv 64 OSL_NULL).
      eapply ret_nullA; [exact OIF| clear; ecu; lia| exact FRF| exact HPF]. }
    assert (ELL : ll = len - 2) by (revert KM; rewrite ?unsigned_lit by (unfold MAX_SCT_LIST_SIZE in LEN; clear - LEN LLR; lia); clear; lia). clear KM.
    replace (negb (ll =? len - 2)) with false by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; exact ELL).
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    step. if_cases K9; zc K9; [| exfalso; apply K9; reflexivity]. clear K9.
    step. apply evt_done.
    cbn [abind apbind amalloc aret fst snd]. change SZ_STACK with STACK_SIZE.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI2) as (HEAP2 & ST2 & _ & _ & _ & _ & MI2' & CS2 & _ & CR2 & _). clear OC.
    change (Z_to_bv 64 2077320) with (wz OPENSSL_SK_NEW_NULL_A).
    eapply (@OPENSSL_sk_new_null_walkA AR UK BE) with (lo := lo) (OW := OW) (LB := [] ++ LB) (ras := bv_unsigned ra :: ras);
      [exact HEAP2| rewrite ESP; exact ST2| exact CEIL| rewrite ESP; clear - LOSPu; ecu; lia| rewrite ESP; clear - TOP; lia| rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia
      | exact MI2'| reflexivity| exact CS2| rewrite ESP; eapply uw_at_call; [exact OI2| exact FR]| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_sknew CTX)|].
    intros kb ΣN msN FRESHN PON. unfold calloc_postA in PON. rewrite ?ESP in PON.
    destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & FN & fcN & mN & SA & -> & MIN & STN & AGN & CRN & BRN & HEAPN & ACCN & HCN).
    rewrite (ret_pc_even 0x33685c) by (clear; lia). unfold MallocRep.wz.
    rewrite (osl_mcost_0_small STACK_SIZE) in CRN by (unfold STACK_SIZE; clear; lia).
    assert (OI3 : oinvS ΣN st mN OW bo [(kb, SA, STACK_SIZE)] (O2I_SCT_LIST_COST_A - 0)).
    { kit @oinv_alloc; [exact OI2| exact AGN| exact HEAPN| exact MIN| exact STN| exact CRN| clear; ecu; lia]. }
    rewrite Z.sub_0_r in OI3.
    pose proof BRN as (K0 & K16 & _ & KC & KI). unfold STACK_SIZE in KC, KI.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI3) as (HEAP3 & ND3 & _ & FRSH3 & DJL3 & _). clear OF. cbn [app] in HEAP3.
    apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha TOP; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGN) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]].
    pose proof (DJL3 (kb, SA, STACK_SIZE) bq ltac:(left; reflexivity) HBQ) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold STACK_SIZE in DJQ. frz DJQ.
    assert (HKIN : In (kb, SA, STACK_SIZE) (OW ++ (kb, SA, STACK_SIZE) :: LB)) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    clear MU2 WM2. pose proof (munch_refl (@nil (Z * Z)) mN) as MU. pose proof (wmono_refl ctasegs mN) as WM.
    apply implAp_from_evt. step. step. step.
    eapply evt_cut.
    { eapply (@OPENSSL_sk_set_thunk_specA AR OPENSSL_SK_SET_CMP_THUNKS_A 0 0 0 SK_SCT_CMP_THUNK_A SK_SCT_CMP_THUNK_A 0 0) with (lo := lo) (pst := kb);
        [ left; repeat split; reflexivity | exact HEAP3 | exact HKIN | rewrite ESP; exact STN | exact MIN | exact CEIL | rewrite ESP; clear - LOSPu; ecu; lia | exact HCN
        | unfold SK_SCT_CMP_THUNK_A; clear; lia | exact K16 | reflexivity | reflexivity ]. }
    intros msA (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mA & -> & MUa & WMa & MIa & STa & HCa).
    rewrite (ret_pc_even 0x33686c) by (clear; lia). rewrite ?ESP in STa, MUa.
    assert (OIa : oinvS ΣN st mA OW bo [(kb, SA, STACK_SIZE)] O2I_SCT_LIST_COST_A).
    { kit @oinv_munch; [exact OI3| exact MUa| exact WMa| exact MIa| exact STa|].
      constructor; [left; cbn [fst snd]; clear - LOSPu; lia|]. constructor; [| constructor]. right; right. exists (kb, SA, STACK_SIZE). split; [left; reflexivity| cbn; unfold STACK_SIZE; clear; lia]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in FR; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; unfold STACK_SIZE; clear - Ha KC CEIL LOSPu; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unfold STACK_SIZE; unfold frozen in DJQ; clear - Ha DJQ Q1 Q2 Q4 CEIL LOSPu; lia].
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OIa) as (HEAPa & _). clear OF. cbn [app] in HEAPa.
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    step. step. step.
    eapply evt_cut.
    { eapply (@OPENSSL_sk_set_thunk_specA AR OPENSSL_SK_SET_COPY_THUNKS_A SK_SCT_CMP_THUNK_A 0 0 SK_SCT_COPY_THUNK_A SK_SCT_CMP_THUNK_A 0 SK_SCT_COPY_THUNK_A) with (lo := lo) (pst := kb);
        [ right; right; repeat split; reflexivity | exact HEAPa | exact HKIN | rewrite ESP; exact STa | exact MIa | exact CEIL | rewrite ESP; clear - LOSPu; ecu; lia | exact HCa
        | unfold SK_SCT_COPY_THUNK_A; clear; lia | exact K16 | reflexivity | reflexivity ]. }
    intros msB (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & mB & -> & MUb & WMb & MIb & STb & HCb).
    rewrite (ret_pc_even 0x33687c) by (clear; lia). rewrite ?ESP in STb, MUb.
    assert (OIb : oinvS ΣN st mB OW bo [(kb, SA, STACK_SIZE)] O2I_SCT_LIST_COST_A).
    { kit @oinv_munch; [exact OIa| exact MUb| exact WMb| exact MIb| exact STb|].
      constructor; [left; cbn [fst snd]; clear - LOSPu; lia|]. constructor; [| constructor]. right; right. exists (kb, SA, STACK_SIZE). split; [left; reflexivity| cbn; unfold STACK_SIZE; clear; lia]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in FR; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; unfold STACK_SIZE; clear - Ha KC CEIL LOSPu; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in HP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unfold STACK_SIZE; unfold frozen in DJQ; clear - Ha DJQ Q1 Q2 Q4 CEIL LOSPu; lia].
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OIb) as (HEAPb & _). clear OF. cbn [app] in HEAPb.
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
    step. step. step.
    eapply evt_cut.
    { eapply (@OPENSSL_sk_set_thunk_specA AR OPENSSL_SK_SET_THUNKS_A SK_SCT_CMP_THUNK_A 0 SK_SCT_COPY_THUNK_A SK_SCT_FREEFUNC_THUNK_A SK_SCT_CMP_THUNK_A SK_SCT_FREEFUNC_THUNK_A SK_SCT_COPY_THUNK_A) with (lo := lo) (pst := kb);
        [ right; left; repeat split; reflexivity | exact HEAPb | exact HKIN | rewrite ESP; exact STb | exact MIb | exact CEIL | rewrite ESP; clear - LOSPu; ecu; lia | exact HCb
        | unfold SK_SCT_FREEFUNC_THUNK_A; clear; lia | exact K16 | reflexivity | reflexivity ]. }
    intros msC (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & mC & -> & MUc & WMc & MIc & STc & HCc).
    rewrite (ret_pc_even 0x33688c) by (clear; lia). rewrite ?ESP in STc, MUc.
    assert (OIc : oinvS ΣN st mC OW bo [(kb, SA, STACK_SIZE)] O2I_SCT_LIST_COST_A).
    { kit @oinv_munch; [exact OIb| exact MUc| exact WMc| exact MIc| exact STc|].
      constructor; [left; cbn [fst snd]; clear - LOSPu; lia|]. constructor; [| constructor]. right; right. exists (kb, SA, STACK_SIZE). split; [left; reflexivity| cbn; unfold STACK_SIZE; clear; lia]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in FR; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; unfold STACK_SIZE; clear - Ha KC CEIL LOSPu; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unfold STACK_SIZE; unfold frozen in DJQ; clear - Ha DJQ Q1 Q2 Q4 CEIL LOSPu; lia].
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    (* [comment removed for export] *)
    step. step. if_cases K1; zc K1; [| exfalso; revert K1; rewrite ?O2iKitAR.land_ones64_small, ?unsigned_lit by (clear - K0 KC CN; lia); clear - K0; lia]. clear K1.
    step. apply evt_done.
    set (k0 := mkSK kb (@None (bptr * Z)) (@nil (sctr bptr))).
    set (adrk := fun b : bptr => if bptr_eqb b kb then SA else adr b).
    assert (EKA : adrk kb = SA) by (subst adrk; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (EB0 : sk_blocks adrk k0 = [(kb, SA, STACK_SIZE)]) by (unfold CtSctP.SctStmt.sk_blocks; subst k0; cbn [sk_items sk_data sk_blk CtSctP.W_sct_list_free.scts_blocks CtSctP.W_sk_leaves.dblk app]; rewrite EKA; reflexivity).
    unfold MallocRep.wz. change (Z_to_bv 64 3369136) with (Z_to_bv 64 OSL_HEAD).
    replace (Z_to_bv 64 SA) with (Z_to_bv 64 (adrk (sk_blk k0))) by (change (sk_blk k0) with kb; rewrite EKA; reflexivity).
    change (mkSK kb None []) with k0.
    rewrite EPIN. eapply (loop_okA (Z.to_nat len) ll k0 2); [| rewrite Z2Nat.id by (clear - LEN; lia); clear - ELL LEN; lia| rewrite ELEN in LEN; exact (proj2 LEN)].
    split; [exact OIc|]. split; [rewrite EB0; apply Permutation_refl|]. split.
    { split; [split; [change (sk_blk k0) with kb; rewrite EKA; apply in_or_app; right; left; reflexivity| change (sk_blk k0) with kb; rewrite EKA; exact K16]|].
      split. { exists 1. split; [clear; lia|]. change (sk_blk k0) with kb. rewrite EKA, sk_cells_rawA. subst k0. cbn [sk_num sk_data sk_items optr olen zlength length Z.of_nat].
               unfold CtSctP.W_sk_new.sk_cells0 in HCc. unfold sk_rawA. exact HCc. }
      split; [subst k0; cbn [sk_data sk_items]; reflexivity|].
      split; [subst k0; cbn [sk_items]; constructor|].
      subst k0. cbn [sk_items sk_data sk_blk CtSctP.W_sct_list_free.scts_blocks CtSctP.W_sk_leaves.dblk app map blk_id fst snd]. constructor; [intros []| constructor]. }
    split. { intros b Hb. subst adrk. cbn beta. rewrite (bptr_eqb_neq (blk_id b) kb); [reflexivity|]. intros E0.
             apply (FRSH3 (kb, SA, STACK_SIZE) ltac:(left; reflexivity)). cbn [blk_id fst snd app]. rewrite map_app. apply in_app_iff. right. rewrite <- E0. apply in_map. exact Hb. }
    split; [exact FR|]. split; [unfold MallocRep.wz; exact HP|].
    subst k0. unfold sk_num, sk_wire, scts_wire. cbn [sk_items sk_data na_sched map fold_right length zlength Z.of_nat]. rewrite push_reserve_0.
    pose proof (mcost_nonneg ll). assert (ML : mcost ll <= 2 * ll + 16384) by (unfold mcost; destruct (ll <=? 64512); clear - ELL LEN; lia).
    unfold MAX_SCT_LIST_SIZE in LEN. clearbody ll. subst ll. clear - ELEN LEN H ML. ecu. change (zlength (@nil (sctr bptr))) with 0. repeat split; try exact I; lia.
  Qed.
End Act.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem o2i_sct_list_walkA : o2i_sct_list_specA2 O2I_SCT_LIST_STACK_A (fun _ => O2I_SCT_LIST_COST_A) O2I_SCT_LIST_FRAMES_A.
Proof.
  unfold o2i_sct_list_specA2. intros until PIN. intros PRE TP UW CTX NE KOW KIDS ELEN D0 D63 DF HB0 PBX ADR CPIN ALP PIND HPIN -> -> ->.
  eapply list_mainA; eassumption.
Qed.


End WithRT.
