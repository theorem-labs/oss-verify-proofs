(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_asn1_stringA W_item_d2i_stmtA W_check_tlenA Fr_asn1_check_tlen CtFuzzStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep W_sct_list_free W_sk_leaves W_o2i_sct_list SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA W_time_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA RtGenStmtA W_crypto_reallocA W_sct_freeA W_sct_list_freeA W_sk_newA O2iKitA O2iKitAR W_o2i_sigA O2iSctStmtB O2iSctListStmtB Fr_d2i_SCT_LIST SctStmtA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctWire.                (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import Fr_FuzzerTestOneInput HarKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DSL_AFTER_D2I : Z := 0x337170.   (* [comment removed for export] *)
Definition DSL_AFTER_LIST : Z := 0x3371a4.  (* [comment removed for export] *)
Definition DSL_FREE : Z := 0x3371c0.        (* [comment removed for export] *)
Definition DSL_NULL : Z := 0x3371cc.        (* [comment removed for export] *)

Local Notation E_d2i := (E_d2i_SCT_LIST_34b594 : uk_call 0x337020 0x337170 0x246e0c).
Local Notation E_get0 := (E_d2i_SCT_LIST_34b5a4 : uk_call 0x337020 0x337180 0x224e40).
Local Notation E_getlen := (E_d2i_SCT_LIST_34b5b8 : uk_call 0x337020 0x337194 0x224df0).
Local Notation E_list := (E_d2i_SCT_LIST_34b5c8 : uk_call 0x337020 0x3371a4 0x336764).
Local Notation E_ofree := (E_d2i_SCT_LIST_34b618 : uk_call 0x337020 0x3371c8 0x246e80).

(* [comment removed for export] *)
Definition D2I_SCT_LIST_STACK_A : Z := 144 + Z.max D2I_OCTET_STACK_A O2I_SCT_LIST_STACK_A.
Definition D2I_SCT_LIST_COST_A (n : Z) : Z := 1 + D2I_OCTET_COST_A n + O2I_SCT_LIST_COST_A.
Definition D2I_SCT_LIST_FRAMES_A : Z := 1 + Z.max D2I_OCTET_FRAMES_A O2I_SCT_LIST_FRAMES_A.

(* [comment removed for export] *)
Lemma D2I_SCT_LIST_COST_A_bound : forall n, 0 <= n < 2 ^ 26 -> 0 <= D2I_SCT_LIST_COST_A n <= 2 ^ 30 + 2 ^ 27.
Proof. intros n Hn. unfold D2I_SCT_LIST_COST_A, O2I_SCT_LIST_COST_A. pose proof (D2I_OCTET_COST_A_bound n Hn). lia. Qed.
Lemma D2I_SCT_LIST_BUD_A : 0 <= D2I_SCT_LIST_STACK_A <= CT_FUZZ_STACK_A - 128 /\ 0 <= D2I_SCT_LIST_FRAMES_A <= CT_FUZZ_FRAMES_A - 1
  /\ (forall n, 0 <= n < 2 ^ 26 -> 0 <= D2I_SCT_LIST_COST_A n <= 2 ^ 30 + 2 ^ 27).
Proof.
  split; [| split; [| exact D2I_SCT_LIST_COST_A_bound]].
  - unfold D2I_SCT_LIST_STACK_A, D2I_OCTET_STACK_A, O2I_SCT_LIST_STACK_A, O2I_SCT_STACK_A, O2I_SIG_STACK_A, CHECK_TLEN_STACK_A, GETOBJ_STACK_A, ACTL_FRAME,
           ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK, CT_FUZZ_STACK_A, D_libiface.FUZZ_STACK. clear. lia.
  - unfold D2I_SCT_LIST_FRAMES_A, D2I_OCTET_FRAMES_A, O2I_SCT_LIST_FRAMES_A, O2I_SCT_FRAMES_A, O2I_SIG_FRAMES_A, CHECK_TLEN_FRAMES_A, GETOBJ_FRAMES_A,
           ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, CT_FUZZ_FRAMES_A, FRAMES_MAX. clear. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis HD2I : forall f, @d2i_octet_specA (push AR f 1) UK D2I_OCTET_STACK_A D2I_OCTET_COST_A D2I_OCTET_FRAMES_A.
(* [comment removed for export] *)
Hypothesis HLIST : forall f, @o2i_sct_list_specA2 (push AR f 1) UK O2I_SCT_LIST_STACK_A (fun _ => O2I_SCT_LIST_COST_A) O2I_SCT_LIST_FRAMES_A.

Local Ltac ecu := unfold D2I_SCT_LIST_STACK_A, D2I_SCT_LIST_COST_A, D2I_SCT_LIST_FRAMES_A, D2I_OCTET_STACK_A, D2I_OCTET_FRAMES_A,
                         O2I_SCT_LIST_STACK_A, O2I_SCT_LIST_COST_A, O2I_SCT_LIST_FRAMES_A, O2I_SCT_STACK_A, O2I_SCT_FRAMES_A,
                         O2I_SIG_STACK_A, O2I_SIG_FRAMES_A, CHECK_TLEN_STACK_A, CHECK_TLEN_FRAMES_A, GETOBJ_FRAMES_A, GETOBJ_STACK_A, ACTL_FRAME, ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK,
                         ERR_SET_ERROR_STACK, ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_STACK, ERR_VSET_ERROR_FRAMES,
                         ERR_NEW_STACK, ERR_NEW_FRAMES, ERR_SET_DEBUG_STACK, ERR_SET_DEBUG_FRAMES, RT_STACK in *.   (* [comment removed for export] *)

Lemma oct0_cellsA : forall (m : mem) A jf24 jf40 jf64 jf72,
  rw_cells ctasegs m A [C8 (Z_to_bv 64 DSL_MAGIC); C8 (Z_to_bv 64 DSL_DESCR); C8 (Z_to_bv 64 DSL_ENTRY); CB 8 jf24; C8 (Z_to_bv 64 0); CB 24 jf40; CB 8 jf64; CB 48 jf72] ->
  rw_cells ctasegs m (A + 32) [C8 (Z_to_bv 64 0)] /\ rw_cells ctasegs m (A + 64) [CB 8 jf64].
Proof.
  intros m A jf24 jf40 jf64 jf72 H.
  pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs m A [C8 (Z_to_bv 64 DSL_MAGIC); C8 (Z_to_bv 64 DSL_DESCR); C8 (Z_to_bv 64 DSL_ENTRY); CB 8 jf24] _) H)) as H1.
  cbn [cells_size csize Nat.add] in H1. replace (A + Z.of_nat 32) with (A + 32) in H1 by (clear; lia).
  split; [exact (proj1 (proj1 (SctRepA.rw_cells_app ctasegs m (A + 32) [C8 (Z_to_bv 64 0)] _) H1))|].
  pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs m (A + 32) [C8 (Z_to_bv 64 0); CB 24 jf40] _) H1)) as H2.
  cbn [cells_size csize Nat.add] in H2. replace (A + 32 + Z.of_nat 32) with (A + 64) in H2 by (clear; lia).
  exact (proj1 (proj1 (SctRepA.rw_cells_app ctasegs m (A + 64) [CB 8 jf64] _) H2)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
  Variables (X : Type) (KK : option (skr bptr) -> @AM bptr X) (Q : X * ap_st bptr -> rts RT -> machine_state -> Prop).
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block) (ras : list Z).
  Variables (adr : bptr -> Z) (d : list Z) (D PIN : Z).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo D2I_SCT_LIST_STACK_A (D2I_SCT_LIST_COST_A (zlength d)) D2I_SCT_LIST_FRAMES_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx D2I_SCT_LIST_A (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D d.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis CPIN : cellA_in LB PIN 8.
  Hypothesis ALP : PIN mod 8 = 0.
  Hypothesis PIND : d = [] \/ PIN + 8 <= D \/ D + zlength d <= PIN.
  Hypothesis HPIN : rw_cells ctasegs m PIN [C8 (wz D)].
  Hypothesis HK : forall ok st' Σ' ms',
    d2i_list_postA2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (D2I_SCT_LIST_COST_A (zlength d)) adr D (zlength d) PIN ok st' Σ' ms' ->
    implAp (KK ok st') Σ' Q ms'.
  (* [comment removed for export] *)
  Variables (Σ1 : rts RT) (m3 : mem) (f spa : Z) (g : nat) (junk gj j0 j8 j16 j24 jf64 jst : list (bv 8)) (qo qp : bptr).
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3.
  Hypothesis HEAPp3 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW (fto_pbs f qo qp ++ LB) m3.
  Hypothesis QOF : ~ In qo (map blk_id (OW ++ LB)).
  Hypothesis QPF : ~ In qp (map blk_id (OW ++ LB)).
  Hypothesis QOP : qo <> qp.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 1 b.
  Hypothesis GEO : @fr_geo (push AR f 1) f 1.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis EL1 : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AG3 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis FRL3 : rw_cells ctasegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB g junk].   (* [comment removed for export] *)
  Hypothesis FRH3 : rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis HO3 : rw_cells ctasegs m3 (f + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis HJ3 : rw_cells ctasegs m3 (f + 64) [CB 8 jf64].
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 144 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 128.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 48.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

  Let STKb : Z := Z.max D2I_OCTET_STACK_A O2I_SCT_LIST_STACK_A.
  Let CSTb : Z := D2I_SCT_LIST_COST_A (zlength d) - 1.
  Let FRMb : Z := D2I_SCT_LIST_FRAMES_A - 1.
  Let LB' : list block := fto_pbs f qo qp ++ LB.
  Let XP : list (Z * Z) := [(f + 32, f + 40); (f + 64, f + 72); (PIN, PIN + 8)]%Z.
  Let spk : word := Z_to_bv 64 (spa + 32).
  (* [comment removed for export] *)
  Let adr1 : bptr -> Z := fun b => if bptr_eqb b qo then f + 32 else if bptr_eqb b qp then f + 64 else adr b.
  (* [comment removed for export] *)
  Let linv : rts RT -> ap_st bptr -> mem -> list block -> Z * Z -> list block -> Z -> Prop :=
    @oinv (push AR f 1) spk m3 Σ1 LB' E lo K d D XP spa STKb CSTb FRMb.
  (* [comment removed for export] *)
  Definition dst (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mX : mem) (pc : Z) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) (Z_to_bv 64 PIN) (Z_to_bv 64 (zlength d)) x21 x22 x23 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) s11 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mX (seg_rom ctasegs).

  Lemma base_facts :
    0 <= bv_unsigned sp < 2 ^ 64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo /\ 0 <= lo
    /\ lo <= bv_unsigned sp - D2I_SCT_LIST_STACK_A /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
    /\ 0 < f /\ f mod 64 = 0 /\ f + 128 <= ACEIL /\ SEGTOP_A <= f /\ (f + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f /\ D2I_SCT_LIST_COST_A (zlength d) <= rt_credit RT Σ /\ Z.of_nat (length FRs) + D2I_SCT_LIST_FRAMES_A <= Z.of_nat FRAMES_MAX
    /\ Forall (fun b => 0 <= b < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 26 /\ Z.of_nat (length (to_bytes d)) = zlength d
    /\ (d = [] \/ exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd /\ 0 < blk_addr bd /\ (blk_addr bd + blk_size bd <= 65536 \/ 12365824 <= blk_addr bd) /\ off_fr f 1 bd
                  /\ blk_addr bd + blk_size bd <= ACEIL)
    /\ (exists bq, In bq LB /\ blk_addr bq <= PIN /\ PIN + 8 <= blk_addr bq + blk_size bq /\ 0 < blk_addr bq /\ blk_addr bq + blk_size bq <= ACEIL
                  /\ (blk_addr bq + blk_size bq <= 65536 \/ 12365824 <= blk_addr bq) /\ off_fr f 1 bq)
    /\ bv_unsigned (Z_to_bv 64 PIN) = PIN /\ bv_unsigned (Z_to_bv 64 (spa + 32)) = spa + 32 /\ List.NoDup (map blk_id (OW ++ LB)).
  Proof.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G4, G5. cbn [ar_SP0 push amb] in G3.
    pose proof LOSP as LOSPu. ecu.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LOSPu SPAL SPAH SPR LO0; plia).
    assert (ESPK : bv_unsigned (Z_to_bv 64 (spa + 32)) = spa + 32) by (apply unsigned_lit; clear - CE1 CEIL LOSPu SPAL SPAH SPR LO0; plia).
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; plia).
    destruct PAY as (HB & DF & D0 & D63 & D26 & HBLK).
    destruct CPIN as (bq & HBQ & Q1 & Q2). pose proof (AH_range_gen _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror HBQ))) as (Q3 & _ & _ & Q4 & Q5).
    assert (EPIN : bv_unsigned (Z_to_bv 64 PIN) = PIN) by (apply unsigned_lit; clear - Q1 Q2 Q3 Q4 CE3; plia).
    split; [exact SPR|]. split; [exact CE1|]. split; [exact CE2|]. split; [exact CE3|]. split; [exact CEIL|]. split; [exact LO0|]. split; [exact LOSP|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact ESPA|]. split; [exact Ef|]. split; [clear - CRED; lia|]. split; [clear - FRM0; lia|].
    split; [exact DF|]. split; [exact D0|]. split; [exact D63|]. split; [exact D26|]. split; [clear; unfold to_bytes, zlength; rewrite length_map; reflexivity|].
    split. { destruct HBLK as [E0|(bd & HBD & BD1 & BD2)]; [left; exact E0| right]. pose proof (AH_range_gen _ _ _ _ bd HEAP (in_or_app _ _ _ (or_intror HBD))) as (B1 & _ & _ & B4 & B5).
             exists bd. repeat (split; [assumption|]). split; [exact (FRESH bd (in_or_app _ _ _ (or_intror HBD)))| exact B4]. }
    split; [exists bq; repeat (split; [assumption|]); exact (FRESH bq (in_or_app _ _ _ (or_intror HBQ)))|].
    split; [exact EPIN|]. split; [exact ESPK| exact (AH_nodup _ _ _ _ HEAP)].
  Qed.

  Local Ltac bf := pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0
                                            & DF & D0 & D63 & D26 & DLEN & BDX & BQX & EPIN & ESPK & NDL);
                   pose proof LOSP as LOSPu; unfold D2I_SCT_LIST_STACK_A, D2I_OCTET_STACK_A, O2I_SCT_LIST_STACK_A, O2I_SCT_STACK_A, O2I_SIG_STACK_A, CHECK_TLEN_STACK_A, GETOBJ_STACK_A, ACTL_FRAME,
                                                   ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in LOSPu.

  (* [comment removed for export] *)
  Local Ltac pce H := change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in H.

  Lemma adr1_facts : adr1 qo = f + 32 /\ adr1 qp = f + 64 /\ (forall b, In b LB -> adr1 (blk_id b) = adr (blk_id b)) /\ (forall b, In b LB' -> adr1 (blk_id b) = blk_addr b).
  Proof.
    assert (E1 : adr1 qo = f + 32) by (subst adr1; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (E2 : adr1 qp = f + 64) by (subst adr1; cbn beta; rewrite (bptr_eqb_neq qp qo) by (intros E0; apply QOP; symmetry; exact E0); rewrite bptr_eqb_refl; reflexivity).
    assert (E3 : forall b, In b LB -> adr1 (blk_id b) = adr (blk_id b)).
    { intros b Hb. subst adr1. cbn beta.
      rewrite (bptr_eqb_neq (blk_id b) qo) by (intros E0; apply QOF; rewrite <- E0, map_app; apply in_or_app; right; apply in_map; exact Hb).
      rewrite (bptr_eqb_neq (blk_id b) qp) by (intros E0; apply QPF; rewrite <- E0, map_app; apply in_or_app; right; apply in_map; exact Hb). reflexivity. }
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    intros b Hb. subst LB'. unfold fto_pbs in Hb. cbn [app] in Hb. destruct Hb as [<-|[<-|Hb]]; [exact E1| exact E2| rewrite (E3 b Hb); apply ADR; exact Hb].
  Qed.

  Lemma KH : @kit_hyps (push AR f 1) spk LB' lo d D XP spa STKb.
  Proof.
    bf. destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    unfold kit_hyps. subst spk. rewrite ESPK. split; [exact DF|]. split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL|]. split; [exact LO0|].
    split; [subst STKb; clear - LOSPu SPAL; ecu; lia|]. split; [subst STKb; clear; ecu; lia|]. split; [clear; lia|]. split; [clear - TOP SPAH; lia|].
    split; [clear - SPA32; Z.div_mod_to_equations; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    split. { subst XP LB'. unfold fto_pbs. constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd app].
             - exists (qo, f + 32, 8). split; [left; reflexivity| cbn; clear; lia].
             - exists (qp, f + 64, 8). split; [right; left; reflexivity| cbn; clear; lia].
             - exists bq. split; [right; right; exact HBQ| clear - Q1 Q2; lia]. }
    split. { subst XP. constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
             - destruct BDX as [E0|(bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC)]; [left; exact E0| right]. unfold off_fr in OD. change (fs_size 1) with 128 in OD. clear - OD BD1 BD2. lia.
             - destruct BDX as [E0|(bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC)]; [left; exact E0| right]. unfold off_fr in OD. change (fs_size 1) with 128 in OD. clear - OD BD1 BD2. lia.
             - exact PIND. }
    split; [| clear - D0; lia]. destruct BDX as [E0|(bd & HBD & BD1 & BD2 & _)]; [left; exact E0| right].
    exists (blk_id bd), (blk_addr bd), (blk_size bd). split; [subst LB'; apply in_or_app; right; destruct bd as [[? ?] ?]; exact HBD| split; [exact BD1| exact BD2]].
  Qed.

  Local Ltac kit L := eapply (L (push AR f 1) spk m3 Σ1 LB' E lo K d D XP spa STKb CSTb FRMb KH).
  Local Ltac kitp L H := pose proof (L (push AR f 1) spk m3 Σ1 LB' E lo K d D XP spa STKb CSTb FRMb KH) as H.

  (* [comment removed for export] *)
  Lemma linv0 : linv Σ1 st m3 OW bo [] CSTb.
  Proof.
    bf. destruct PAY as (HB & _).
    pose proof (pro_closeA Σ st m OW LB E bo sp lo D2I_SCT_LIST_STACK_A (D2I_SCT_LIST_COST_A (zlength d)) D2I_SCT_LIST_FRAMES_A f 1%nat Σ1 m3 spa 128 PRE HEAP3 ST3 MI3 AG3 CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(clear; ecu; lia) ltac:(clear; ecu; pose proof (D2I_OCTET_COST_A_bound 0 ltac:(lia)); unfold D2I_OCTET_COST_A in *; pose proof (zlength_ge0' d); lia) ltac:(clear; ecu; lia)) as P3.
    destruct P3 as (_ & AS3 & IDS3 & DC3 & _ & CEIL3 & LOSP3 & TOP3 & AL3 & _ & CRED3 & FRM3). rewrite ESPA in LOSP3, TOP3, AL3.
    kit @oinv_entry; [| exact KOW| exact KIDS|].
    - unfold ap_preA. rewrite ESPA. cbn [ar_FR ar_RT ar_SP0 push amb length]. cbn [ar_FR ar_RT ar_SP0 push amb length] in CRED3, FRM3.
      split; [exact HEAPp3|]. split; [exact AS3|]. split; [exact IDS3|]. split; [exact DC3|]. split; [exact ST3|].
      split; [exact CEIL3|]. split; [subst STKb; clear - LOSP3; ecu; lia|]. split; [exact TOP3|]. split; [exact AL3|]. split; [exact MI3|].
      split; [subst CSTb; exact CRED3| subst FRMb; exact FRM3].
    - eapply bytes_at_agree; [exact AG3| exact HB|]. intros a Ha. rewrite DLEN in Ha.
      destruct BDX as [E0|(bd & HBD & BD1 & BD2 & _)]; [exfalso; rewrite E0 in Ha; unfold zlength in Ha; cbn in Ha; clear - Ha; lia|].
      right; right. exists bd. split; [apply in_or_app; right; exact HBD| clear - Ha BD1 BD2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma keepA : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX ->
    rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells ctasegs mX (spa + 32) [CB g junk]
    /\ uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras)
    /\ agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX.
  Proof.
    intros until CX. intros (_ & AX & _). bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). subst spk. rewrite ESPK in AX.
    assert (FHI : f + 128 <= spa) by (clear - G3 CEIL LOSPu SPAL; plia).
    assert (QHI : PIN + 8 <= spa) by (clear - Q2 Q4 CEIL LOSPu SPAL; plia).
    assert (AXS : forall a, spa + 32 <= a < USTACK_TOP -> mX (wa a) = m3 (wa a)).
    { intros a Ha. unfold USTACK_TOP in Ha. apply AX; [clear - Ha SPR CEIL LOSPu SPAL LO0; lia|]. split; [| left; unfold USTACK_TOP; exact Ha].
      subst XP. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha FHI QHI CEIL CE1 LOSPu SPAL. plia. }
    assert (AGS : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX).
    { intros a Ha Hr. unfold USTACK_TOP in Hr. rewrite (AXS a ltac:(unfold USTACK_TOP; clear - Hr SPAH; lia)). apply AG3; [exact Ha| left; unfold USTACK_TOP; exact Hr]. }
    assert (FRH : rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_agree; [| exact FRH3|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. apply AXS. clear - Ha TOP SPAH. unfold USTACK_TOP in *. lia. }
    split; [exact FRH|]. split; [| split; [| exact AGS]].
    - pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB g junk]) FRL3)) as FJ. cbn [cells_size csize Nat.add] in FJ.
      replace (spa + Z.of_nat 32) with (spa + 32) in FJ by (clear; lia).
      eapply rw_cells_agree; [| exact FJ|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbv beta. cbn [cells_size csize Nat.add] in Ha. apply AXS. clear - Ha TOP SPAH GSZ. unfold USTACK_TOP in *. lia.
    - eapply (uw_call m mX spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [exact UW| exact AGS| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| clear - TOP; unfold USTACK_TOP in *; lia| apply bv_unsigned_in_range|].
      rewrite !Z_to_bv_bv_unsigned. cbn [app]. exact FRH.
  Qed.

  (* [comment removed for export] *)
  Lemma close_pbs : forall ΣX OWX NEW mX, @BnHeapA.AHEAP (push AR f 1) ΣX OWX (NEW ++ LB') mX -> @BnHeapA.AHEAP (push AR f 1) ΣX OWX (NEW ++ LB) mX.
  Proof.
    intros ΣX OWX NEW mX H. subst LB'. unfold fto_pbs in H. cbn [app] in H.
    assert (H2 : @BnHeapA.AHEAP (push AR f 1) ΣX OWX (NEW ++ (qp, f + 64, 8) :: LB) mX).
    { eapply (@frame_obj_close (push AR f 1)) with (f := f) (k := 1%nat) (b := (qo, f + 32, 8)); [left; reflexivity| | unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
      eapply AH_lb_perm; [exact H|]. symmetry. apply Permutation_middle. }
    eapply (@frame_obj_close (push AR f 1)) with (f := f) (k := 1%nat) (b := (qp, f + 64, 8)); [left; reflexivity| | unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
    eapply AH_lb_perm; [exact H2|]. symmetry. apply Permutation_middle.
  Qed.

  (* [comment removed for export] *)
  Lemma closeA : forall ΣX stX mX OWX boX NEW CX Σ' m',
    linv ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    AHEAP Σ' OWX (NEW ++ LB) m' -> rt_credit RT Σ' = rt_credit RT ΣX -> stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
    agree_on (aclient_addr (OWX ++ (NEW ++ LB)) spa) mX m' ->
    ap_preA Σ' stX m' OWX (NEW ++ LB) E boX sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)]%Z ++ LIBW_A) m m'
    /\ rt_credit RT Σ - D2I_SCT_LIST_COST_A (zlength d) <= rt_credit RT Σ'
    /\ blocks_kept K stX OWX m m'
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB)))
    /\ Forall lbokA NEW.
  Proof.
    intros until m'. intros LI HCX HEAP' CR' ST' MI' AG'. bf.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & CRED & _).
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (_ & _ & _ & FRSH & _). clear OF.
    destruct LI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    pose proof PREX as (HEAPX & ASX & IDSX & DCX & STX & _ & _ & _ & _ & MIX & CREDX & _). subst spk. rewrite ESPK in AX. cbn [ar_RT ar_FR push amb] in CREDX, CR.
    split; [| split; [| split; [| split; [| split]]]].
    - unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASX | exact AG']|]. split; [exact IDSX|].
      split; [eapply data_cells_rt; [exact ASX | exact DCX | exact AG']|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSPu; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [clear - CREDX CR'; lia|]. clear - FRM0. ecu. lia.
    - eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [exact AG3 | clear; lia]|].
      eapply ax_pres_trans.
      + unfold ax_pres. eapply agree_on_mono; [exact AX|]. intros a [HXa Ha]. split.
        * subst XP. intros HIN. apply HXa. cbn [app rin_ivs fst snd] in HIN |- *.
          destruct HIN as [HIN|[HIN|HIN]]; [| | exact HIN]; exfalso;
            (destruct Ha as [Ha|[Ha|(b & Hb & Hr)]];
             [ clear - Ha HIN G3 CEIL LOSPu SPAL; plia
             | pose proof (client_static_below a Ha); clear - H HIN G4; unfold SEGTOP_A in G4; lia
             | pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O; unfold off_fr in O; change (fs_size 1) with 128 in O;
               destruct b as [[bq' bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O; clear - Hr O HIN; lia ]).
        * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [subst LB'; apply in_or_app; right; exact Hb| exact Hr]].
      + eapply (ax_pres_of_aclient (OWX ++ NEW) LB); [rewrite <- app_assoc; exact AG' | clear - SPAH; lia].
    - subst CSTb. clear - CR CR1 CR' HCX. lia.
    - eapply (blocks_kept_post K stX OWX (NEW ++ LB)); [| exact AG'].
      eapply (blocks_kept_pre K stX OW OWX LB); [exact KOW | exact AG3|].
      split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP].
    - intros b Hb Hin. apply (FRSH b Hb). rewrite map_app in Hin |- *. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left; exact Hin| right; subst LB'; rewrite map_app; apply in_or_app; right; exact Hin].
    - eapply Forall_impl; [| exact LBOK]. intros b Hb. exact (lbokA_pop _ _ _ Hb).
  Qed.
  Local Notation SPOST := (fun r => d2i_list_postA2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (D2I_SCT_LIST_COST_A (zlength d)) adr D (zlength d) PIN (fst r) (snd r)) (only parsing).

  (* [comment removed for export] *)
  Lemma dsl_exitA : forall ΣX stX mX OWX boX NEW CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 : word) FX fcX
      (ok : option (skr bptr)) (adrX : bptr -> Z),
    linv ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 f)] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    match ok with
    | None => NEW = [] /\ x21 = Z_to_bv 64 0 /\ exists pv, rw_cells ctasegs mX PIN [C8 pv]
    | Some k => x21 = Z_to_bv 64 (adrX (sk_blk k)) /\ Permutation NEW (sk_blocks adrX k) /\ sk_repA mX (OWX ++ NEW ++ LB') adrX k
                /\ rw_cells ctasegs mX PIN [C8 (wz (D + zlength d))] /\ 3 * zlength (sk_items k) + 2 <= MAX_SCT_LIST_SIZE /\ 2 + sk_wire k <= MAX_SCT_LIST_SIZE
    end ->
    implAp (KK ok stX) ΣX Q (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 FX fcX mX DSL_EXIT).
  Proof.
    intros until adrX. intros LI HCX FRLo ADRX RES. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    pose proof (keepA _ _ _ _ _ _ _ LI) as (FRH & FJ & UWX & AGS).
    pose proof LI as (PREX & _ & _ & _ & _ & _ & _ & LBOK). cbn [app] in PREX. pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & _). rewrite ESPA in STX.
    pose proof (rw_cells_app_join mX spa _ _ FRLo ltac:(cbn [cells_size csize Nat.add]; replace (spa + Z.of_nat 32) with (spa + 32) by (clear; lia); exact FJ)) as FRL. cbn [app] in FRL.
    intros XX Φ DD SAFE LINK. unfold dst. change (Z_to_bv 64 DSL_EXIT) with (wz DSL_EXIT).
    eapply (@dsl_epi_cps AR _) with (lo := lo) (LB := NEW ++ LB) (gj := gj) (hrest := []);
      [exact (close_pbs _ _ _ _ HEAPX)| | exact STX| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| clear - LOSPu SPAL; lia| exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIX| exact FRL| exact FRH| reflexivity|].
    { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [| exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))].
      pose proof (proj1 (Forall_forall _ _) LBOK b Hb) as [_ NPB].
      destruct (@AH_fr_blk (push AR f 1) ΣX OWX (NEW ++ LB') mX f 1%nat b HEAPX (or_introl eq_refl) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as [IN|OFF];
        [exfalso; apply NPB; exists f, 1%nat; split; [left; reflexivity| exact IN]| exact OFF]. }
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply (implAp_elim _ ΣX Σ' _ _ XX Φ DD); [| exact SAFE| exact LINK| exact LIVE'].
    apply HK.
    destruct (closeA _ _ _ _ _ NEW CX _ _ LI HCX HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK' & NFR & LBOK').
    assert (KPIN : forall v, rw_cells ctasegs mX PIN [C8 v] -> rw_cells ctasegs m' PIN [C8 v]).
    { intros v H. eapply rw_cells_agree; [exact AG'| exact H|]. intros a Ha. cbn in Ha. right; right. exists bq. split; [apply in_or_app; right; apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]. }
    unfold d2i_list_postA2. cbn [fst snd].
    destruct ok as [k|].
    - destruct RES as (-> & PM & SK & HP & N3 & W2).
      do 14 eexists. exists FX, fcX, m', OWX, boX, adrX, NEW. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
      split; [exact ADRX|]. split; [exact NFR|]. split; [exact LBOK'|]. split; [exact PM|].
      split; [| split; [exact (KPIN _ HP)| split; [exact N3| exact W2]]].
      eapply sk_repA_agree; [exact AG'| |].
      + intros b a Hb Ha. right; right. exists b. split; [| exact Ha]. apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
      + eapply sk_repA_relist; [exact SK|]. intros b Hb. apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
    - destruct RES as (EN & -> & (pv & HP)).
      do 14 eexists. exists FX, fcX, m', OWX, boX, adrX, NEW. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
      split; [exact ADRX|]. split; [exact NFR|]. split; [exact LBOK'|]. split; [exact EN|]. exists pv. exact (KPIN _ HP).
  Qed.

  (* [comment removed for export] *)
  Lemma free_tailA : forall (ok : option (skr bptr)) ΣT stT mT OWT boT CT (adrO adrT : bptr -> Z) (NEWO NEWT : list block) (os : octet bptr)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 xr x23 x28 x29 x30 x31 : word) FT fcT (pvT : word),
    let A := adrO (os_blk os) in let DP := optr adrO (os_data os) in
    linv ΣT stT mT OWT boT (NEWT ++ NEWO) CT -> 0 <= CT ->
    NEWO = oct_blocks adrO os -> match os_data os with Some (dp, _) => dp <> os_blk os | None => True end ->
    (forall b, In b LB -> adrT (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mT spa [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 f)] ->
    rw_cells ctasegs mT (f + 32) [C8 (Z_to_bv 64 A)] -> rw_cells ctasegs mT PIN [C8 pvT] ->
    rw_cells ctasegs mT A (asn1_string_cells (os_len os) V_ASN1_OCTET_STRING DP 0) ->
    xr = Z_to_bv 64 match ok with Some k => adrT (sk_blk k) | None => 0 end ->
    match ok with
    | None => NEWT = []
    | Some k => Permutation NEWT (sk_blocks adrT k) /\ sk_repA mT (OWT ++ NEWT ++ NEWO ++ LB') adrT k /\ pvT = wz (D + zlength d)
                /\ 3 * zlength (sk_items k) + 2 <= MAX_SCT_LIST_SIZE /\ 2 + sk_wire k <= MAX_SCT_LIST_SIZE
    end ->
    implAp (abind (octet_free os) (fun _ => KK ok) stT) ΣT Q
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 xr (Z_to_bv 64 (f + 32)) x23 x28 x29 x30 x31 FT fcT mT DSL_FREE).
  Proof.
    intros until pvT. cbv zeta. intros LI HCT ENO NBD ADRT FRLo HOC HP OCS XR RES. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    set (A := adrO (os_blk os)) in *. set (DP := optr adrO (os_data os)) in *.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPT & NDT & BND & FRSH & DJL & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STT & _ & LOX & _ & _ & MIT & CST & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWT & _).
    pose proof LI as (_ & _ & _ & _ & _ & _ & _ & LBOK). pose proof LBOK as LBOK'. rewrite Forall_app in LBOK'. destruct LBOK' as [LBOKT LBOKO].
    assert (OIN : In (os_blk os, A, ASN1_STRING_SIZE) NEWO) by (rewrite ENO; left; reflexivity).
    pose proof (BND (os_blk os, A, ASN1_STRING_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; exact OIN)) as (BA0 & _ & BAC & BAI). cbn [blk_addr blk_size fst snd] in BA0, BAC, BAI. unfold ASN1_STRING_SIZE in BAC, BAI. pce BAC.
    (* [comment removed for export] *)
    assert (HEAPq : @BnHeapA.AHEAP (push AR f 1) ΣT OWT (NEWO ++ (NEWT ++ LB')) mT).
    { eapply (@AH_lb_perm (push AR f 1)); [exact HEAPT|]. rewrite (app_assoc NEWO NEWT LB'). apply Permutation_app_tail. apply Permutation_app_comm. }
    pose proof (@AH_adopt_list (push AR f 1) ΣT NEWO OWT (NEWT ++ LB') mT HEAPq LBOKO) as HEAPa.
    pose proof (@AH_nodup_l (push AR f 1) _ _ _ _ HEAPa) as NDl.
    pose proof (munch_refl (@nil (Z * Z)) mT) as MU. pose proof (wmono_refl ctasegs mT) as WM.
    unfold dst, DSL_FREE. unfold MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. apply evt_done.
    change (Z_to_bv 64 2387584) with (wz ASN1_OCTET_STRING_FREE_A).
    (* [comment removed for export] *)
    assert (KT : forall Σ' ms',
      @vfree_postA (push AR f 1) (Z_to_bv 64 0x3371c8) (Z_to_bv 64 spa) gp sp (Z_to_bv 64 spa) (Z_to_bv 64 f) (Z_to_bv 64 PIN) (Z_to_bv 64 (zlength d)) xr (Z_to_bv 64 (f + 32)) x23
                  (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) s11 ΣT OWT (NEWT ++ LB') lo mT (fun _ => True) Σ' ms' ->
      implAp (KK ok stT) Σ' Q ms').
    { intros Σ' ms' PO. unfold vfree_postA in PO.
      destruct PO as (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4 & _).
      rewrite ?ESPA in ST4. rewrite ?ESPA in AG4. cbn [ar_RT push amb] in CR4. rewrite (ret_pc_even 0x3371c8) by (clear; lia). unfold apres in AG4.
      assert (LI4 : linv Σ' stT m4 OWT boT NEWT (CT - 0)).
      { eapply (@oinv_heap (push AR f 1) spk m3 Σ1 LB' E lo K d D XP spa STKb CSTb FRMb KH _ _ _ _ _ _ _ Σ' m4 (OWT ++ (NEWT ++ LB')) NEWT 0);
          [exact LI| eapply agree_on_mono; [exact AG4| intros a [Ha _]; exact Ha]| intros b [Hb|Hb]; apply in_or_app; [left; exact Hb| right; apply in_or_app; right; exact Hb]
          | exact HEAP4| exact LBOKT| exact MI4| exact ST4| cbn [ar_RT push amb]; clear - CR4; lia| clear - HCT; lia]. }
      rewrite Z.sub_0_r in LI4.
      apply (rw_cells_agree _ _ _ _ _ AG4) in FRLo; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; clear - Ha TOP SPAH; unfold USTACK_TOP in *; lia].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; subst LB'; apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]].
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
      apply implAp_from_evt. step. apply evt_done.
      change (Z_to_bv 64 3371472) with (Z_to_bv 64 DSL_EXIT).
      eapply (dsl_exitA Σ' stT m4 OWT boT NEWT CT) with (ok := ok) (adrX := adrT); [exact LI4| exact HCT| exact FRLo| exact ADRT|].
      destruct ok as [k|].
      - destruct RES as (PM & SK & EPV & N3 & W2). subst pvT. split; [exact XR|]. split; [exact PM|]. split; [| split; [exact HP| split; [exact N3| exact W2]]].
        eapply sk_repA_agree; [exact AG4| |].
        + intros b a Hb Ha. right; right. exists b. split; [| exact Ha]. apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
        + eapply sk_repA_relist; [exact SK|]. intros b Hb. apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
      - split; [exact RES|]. split; [exact XR|]. exists pvT. exact HP. }
    (* [comment removed for export] *)
    rewrite ENO in HEAPa, NDl. unfold oct_blocks in HEAPa, NDl. unfold octet_free.
    destruct (os_data os) as [[dp n]|] eqn:EOD; cbn [abind apbind afree_opt afree aret option_map fst snd app] in HEAPa, NDl |- *.
    - pose proof NDl as NDl'. cbn [map app blk_id fst snd] in NDl'. apply NoDup_cons_iff in NDl' as [NI1 ND2]. pose proof ND2 as ND2'. apply NoDup_cons_iff in ND2' as [NI2 ND3].
      assert (ND1 : List.NoDup (map blk_id ((os_blk os, A, ASN1_STRING_SIZE) :: OWT))) by (cbn [map blk_id fst snd]; constructor; [intros Hin; apply NI1; right; exact Hin| exact ND3]).
      assert (ER : lb_remove (os_blk os) (lb_remove dp ((os_blk os, A, ASN1_STRING_SIZE) :: (dp, adrO dp, n) :: OWT)) = OWT).
      { rewrite (lb_remove_cons dp (os_blk os, A, ASN1_STRING_SIZE)). cbn [blk_id fst snd]. rewrite (bptr_eqb_neq (os_blk os) dp) by (intros E0; apply NBD; symmetry; exact E0).
        rewrite (lb_remove_head (dp, adrO dp, n) OWT ND2). exact (lb_remove_head (os_blk os, A, ASN1_STRING_SIZE) OWT ND1). }
      eapply (@ASN1_pfree_walkA (push AR f 1) UK BE _) with (lo := lo) (OW := (os_blk os, A, ASN1_STRING_SIZE) :: (dp, adrO dp, n) :: OWT) (LB := NEWT ++ LB')
          (pblk := os_blk os) (pdata := dp) (len := os_len os) (ty := V_ASN1_OCTET_STRING) (D := adrO dp) (alloc := n) (ras := bv_unsigned ra :: ras); rewrite ?ESPA.
      + reflexivity.
      + exact HEAPa.
      + exact STT.
      + unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      + subst STKb. clear - LOX. ecu. lia.
      + clear - TOP SPAH. plia.
      + clear - SPA32. Z.div_mod_to_equations. lia.
      + exact MIT.
      + reflexivity.
      + exact CST.
      + left. reflexivity.
      + right. left. reflexivity.
      + intros E0. apply NBD. symmetry. exact E0.
      + subst DP. cbn [optr] in OCS. exact OCS.
      + reflexivity.
      + exact UWT.
      + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_ofree CTX).
      + intros Σ' ms' PO. apply KT. rewrite ER in PO. exact PO.
    - assert (ER : lb_remove (os_blk os) ((os_blk os, A, ASN1_STRING_SIZE) :: OWT) = OWT) by (exact (lb_remove_head (os_blk os, A, ASN1_STRING_SIZE) OWT NDl)).
      eapply (@ASN1_pfree_nodata_walkA (push AR f 1) UK BE _) with (lo := lo) (OW := (os_blk os, A, ASN1_STRING_SIZE) :: OWT) (LB := NEWT ++ LB')
          (pblk := os_blk os) (len := os_len os) (ty := V_ASN1_OCTET_STRING) (ras := bv_unsigned ra :: ras); rewrite ?ESPA.
      + reflexivity.
      + exact HEAPa.
      + exact STT.
      + unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      + subst STKb. clear - LOX. ecu. lia.
      + clear - TOP SPAH. plia.
      + clear - SPA32. Z.div_mod_to_equations. lia.
      + exact MIT.
      + reflexivity.
      + exact CST.
      + left. reflexivity.
      + subst DP. cbn [optr] in OCS. exact OCS.
      + reflexivity.
      + exact UWT.
      + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_ofree CTX).
      + intros Σ' ms' PO. apply KT. rewrite ER in PO. exact PO.
  Qed.

  (* [comment removed for export] *)
  Lemma dsl_bodyA : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX,   (* [comment removed for export] *)
    implAp (d2i_list_tree d KK st) Σ1 Q
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z_to_bv 64 SHB) s7 x28 x29 x30 x31 FX fcX m3 DSL_BODY).
  Proof.
    intros. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    pose proof adr1_facts as (E1o & E1p & ADR1 & ADR1').
    pose proof linv0 as LI.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAP3' & ND3 & BND & FRSH & DJL & _). clear OF. cbn [app] in HEAP3'.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & _ & _ & _ & _ & _ & _ & CS3 & _ & CR3 & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UW3 & _).
    pose proof LI as (_ & _ & KO & KI & _ & HB3 & CRT & _). cbn [ar_RT push amb] in CR3, CRT.
    (* [comment removed for export] *)
    pose proof HPIN as HP. unfold MallocRep.wz in HP.
    apply (rw_cells_agree _ _ _ _ _ AG3) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]].
    pose proof FRL3 as FRLo. apply (proj1 (SctRepA.rw_cells_app ctasegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB g junk])) in FRLo. destruct FRLo as [FRLo _].
    assert (HBQ' : In bq (OW ++ [] ++ LB')) by (apply in_or_app; right; cbn [app]; subst LB'; apply in_or_app; right; exact HBQ).
    assert (HQO : In (qo, f + 32, 8) (OW ++ [] ++ LB')) by (apply in_or_app; right; cbn [app]; subst LB'; left; reflexivity).
    assert (HQP : In (qp, f + 64, 8) (OW ++ [] ++ LB')) by (apply in_or_app; right; cbn [app]; subst LB'; right; left; reflexivity).
    ablock HEAP3' HBQ' ACCQ OFFQ. ablock HEAP3' HQP ACCP OFFP.
    pose proof (munch_refl [(spa + 24, spa + 32); (f + 64, f + 72); (PIN, PIN + 8)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM. pose proof MI3 as MI. pose proof ST3 as STX.
    pose proof HJ3 as HJ. pose proof HO3 as HO.
    (* [comment removed for export] *)
    frz FRL3. frz FRH3. frz ST3. frz MI3. frz HJ3. frz HO3.
    assert (OFF : offshW [(spa + 24, spa + 32); (f + 64, f + 72); (PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ OFFP CEIL LOSPu SPAL CE2 Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ OFFP.
    assert (QP : PIN + 8 <= f + 32 \/ f + 128 <= PIN) by (unfold off_fr in OQ; change (fs_size 1) with 128 in OQ; clear - OQ Q1 Q2; lia).
    frz Q5. frz OQ.
    unfold dst, DSL_BODY, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    ab_shload 8. step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. rewrite ?zxb_z8, ?sxb_z8. if_false. step.             (* [comment removed for export] *)
    step. step.                    (* [comment removed for export] *)
    step. setreg 22%Z (Z_to_bv 64 (f + 32)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - G1 G3 CE3 CN; lia); bv_solve) || idtac.   (* [comment removed for export] *)
    step. step. step. step. name_mem m5. apply evt_done.   (* [comment removed for export] *)
    match goal with H : munch _ m3 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m3 m5 |- _ => rename H into WM5 end.
    match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
    assert (LI5 : linv Σ1 st m5 OW bo [] CSTb).
    { kit @oinv_munch; [exact LI| exact MU5| exact WM5| exact MI5| exact STX|].
      constructor; [left; cbn [fst snd]; rewrite ESPK; clear - LOSPu SPAL; lia|]. constructor; [right; left; exists (f + 64, f + 72)%Z; split; [subst XP; right; left; reflexivity| cbn; clear; lia]|].
      constructor; [right; left; exists (PIN, PIN + 8)%Z; split; [subst XP; right; right; left; reflexivity| cbn; clear; lia]| constructor]. }
    pose proof LI5 as (PRE5 & _ & KO5 & KI5 & _ & HB5 & _).
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI5) as (_ & ST5 & _ & _ & _ & _ & _ & _ & _ & CR5 & _). clear OC. cbn [ar_RT push amb] in CR5.
    (* [comment removed for export] *)
    unfold d2i_list_tree. change (Z_to_bv 64 2387468) with (wz D2I_ASN1_OCTET_STRING_A).
    eapply implAp_abind.
    { pose proof (HD2I f) as W. unfold d2i_octet_specA in W.
      eapply W with (LB := LB') (K := K) (adr := adr1) (D := D) (OPP := f + 64) (OCT := f + 32) (lo := lo) (E := E) (bo := bo) (OW := OW) (ras := bv_unsigned ra :: ras); clear W.
      - eapply ap_preA_weaken; [exact PRE5| subst STKb; clear; lia| clear - CR5 CRT CRED0 CR1 D26; subst CSTb; ecu; pose proof (D2I_OCTET_COST_A_bound (zlength d) ltac:(clear - D26; pose proof (zlength_ge0' d); lia)); lia| subst FRMb; clear; ecu; lia].
      - reflexivity.
      - rewrite ESPA. exact (proj1 (proj2 (proj2 (keepA _ _ _ _ _ _ _ LI5)))).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_d2i CTX).
      - apply cons_ne.
      - exact KO5.
      - exact KI5.
      - split; [exact HB5|]. split; [exact DF|]. split; [exact D0|]. split; [exact D63|]. split; [exact D26|].
        destruct BDX as [E0|(bd & HBD & BD1 & BD2 & _)]; [left; exact E0| right]. exists bd. split; [subst LB'; apply in_or_app; right; exact HBD| split; [exact BD1| exact BD2]].
      - exact ADR1'.
      - exists (qp, f + 64, 8). split; [subst LB'; unfold fto_pbs; right; left; reflexivity| cbn; clear; lia].
      - clear - G2. Z.div_mod_to_equations. lia.
      - destruct BDX as [E0|(bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC)]; [left; exact E0| right]. unfold off_fr in OD. change (fs_size 1) with 128 in OD. clear - OD BD1 BD2. lia.
      - exact HJ.
      - exists (qo, f + 32, 8). split; [subst LB'; unfold fto_pbs; left; reflexivity| cbn; clear; lia].
      - clear - G2. Z.div_mod_to_equations. lia.
      - destruct BDX as [E0|(bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC)]; [left; exact E0| right]. unfold off_fr in OD. change (fs_size 1) with 128 in OD. clear - OD BD1 BD2. lia.
      - exact HO.
      - right. clear; lia.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    intros r ΣO msO PO. unfold d2i_octet_postA in PO. rewrite ?ESPA in PO.
    destruct PO as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & FS & fcS & mO & OWO & boO & adrO & NEWO & ov & cv
                    & -> & PREO & AXO & CRO & BKO & ADRO & FRSHO & LBOKO & HOP & HOC & RES).
    destruct r as [oo stO]. cbn [fst snd] in *.
    rewrite (ret_pc_even 0x337170) by (clear; lia). cbn [ar_RT push amb] in CRO.
    assert (LIO : linv ΣO stO mO OWO boO (NEWO ++ []) (CSTb - D2I_OCTET_COST_A (zlength d))).
    { kit @oinv_after; [exact LI5| exact PREO| exact AXO| | exact CRO| | exact BKO| exact LBOKO].
      - intros a Ha. cbn [rin_ivs fst snd app] in Ha. right; left. subst XP. cbn [rin_ivs fst snd]. clear - Ha. lia.
      - clear - CR5 CRT CRED0 CR1 D26; subst CSTb; ecu. pose proof (D2I_OCTET_COST_A_bound (zlength d) ltac:(clear - D26; pose proof (zlength_ge0' d); lia)). lia. }
    rewrite app_nil_r in LIO.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AXO) in FRLo; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha G3 CEIL CE1 LOSPu SPAL; nrm; lia| left; clear - Ha TOP SPAH; unfold USTACK_TOP in *; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXO) in HP; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; unfold frozen in Q5; clear - Ha QP Q1 Q2 Q3 Q5; lia| right; right; exists bq; split; [subst LB'; apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]]].
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIO) as (HEAPO & NDO & BNDO & FRSHO' & DJLO & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIO) as (_ & STO & _ & _ & _ & _ & MIO & CSO & ASO & CRO' & _). clear OC. cbn [ar_RT push amb] in CRO'.
    pose proof (keepA _ _ _ _ _ _ _ LIO) as (_ & _ & UWO & _).
    clear MU5 WM5. pose proof (munch_refl (@nil (Z * Z)) mO) as MU. pose proof (wmono_refl ctasegs mO) as WM.
    pose proof FRLo as FRLo'.   (* [comment removed for export] *)
    apply implAp_from_evt.
    destruct oo as [os|].
    2:{ (* [comment removed for export] *)
        rename RES into ENO. subst NEWO.
        step. if_cases K0; zc K0; [| exfalso; apply K0; reflexivity]. clear K0.
        step. apply evt_done. change (Z_to_bv 64 3371472) with (Z_to_bv 64 DSL_EXIT).
        eapply (dsl_exitA ΣO stO mO OWO boO [] (CSTb - D2I_OCTET_COST_A (zlength d))) with (ok := None) (adrX := adr);
          [exact LIO| clear - D26; subst CSTb; ecu; pose proof (D2I_OCTET_COST_A_bound (zlength d) ltac:(clear - D26; pose proof (zlength_ge0' d); lia)); lia| exact FRLo'| intros b Hb; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. eexists. exact HP. }
    (* [comment removed for export] *)
    destruct RES as (ENO & ORP & ->). unfold MallocRep.wz in HOC.
    pose proof ORP as (OIN & OAL & OCS & OLEN & ODF & OL31 & ODAT).
    set (A := adrO (os_blk os)) in *.
    assert (OINA : In (os_blk os, A, ASN1_STRING_SIZE) NEWO) by (rewrite ENO; left; reflexivity).
    pose proof (BNDO (os_blk os, A, ASN1_STRING_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; exact OINA)) as (BA0 & _ & BAC & BAI). cbn [blk_addr blk_size fst snd] in BA0, BAC, BAI. unfold ASN1_STRING_SIZE in BAC, BAI. pce BAC.
    set (DP := optr adrO (os_data os)) in *.
    assert (DPR : 0 <= DP /\ DP + zlength (os_bytes os) < 2 ^ 63 /\ 0 <= DP < 2 ^ 64 /\ (os_data os = None -> DP = 0)).
    { subst DP. destruct (os_data os) as [[dp n]|] eqn:EOD; cbn [optr].
      - destruct ODAT as (NBD & DIN & DLE & DBY). pose proof (BNDO (dp, adrO dp, n) ltac:(apply in_or_app; right; apply in_or_app; left; rewrite ENO; right; cbn; rewrite EOD; left; reflexivity)) as (B1 & B2 & B3 & B4).
        cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4. pce B3. split; [clear - B1; lia|]. split; [clear - B1 B2 B3 DLE OLEN CN; lia|]. split; [clear - B1 B2 B3 CN; lia| discriminate].
      - rewrite ODAT. unfold zlength. cbn. clear. repeat split; try lia. }
    destruct DPR as (DP0 & DP63 & DP64 & DPN).
    assert (OL0 : 0 <= os_len os) by (rewrite OLEN; apply zlength_ge0').
    step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?O2iKitAR.land_ones64_small, ?unsigned_lit by (clear - BA0 BAC CN; lia); clear - BA0; lia|]. clear K0.
    (* [comment removed for export] *)
    step. step.
    eapply evt_cut.
    { eapply (@ASN1_STRING_get0_data_specA (push AR f 1)) with (lo := lo) (OW := OWO) (LB := NEWO ++ LB') (xb := os_blk os);
        [exact HEAPO| rewrite ESPA; exact STO| exact MIO| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; clear - LOSPu SPAL; lia
        | apply in_or_app; right; apply in_or_app; left; exact OINA| clear - OAL; unfold al16 in OAL; Z.div_mod_to_equations; lia| exact OCS| exact DP64| reflexivity]. }
    intros msG (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & mG & -> & MUg & WMg & MIg & STg & _).
    rewrite (ret_pc_even 0x337180) by (clear; lia). rewrite ?ESPA in STg, MUg.
    assert (LIG : linv ΣO stO mG OWO boO NEWO (CSTb - D2I_OCTET_COST_A (zlength d))).
    { kit @oinv_munch; [exact LIO| exact MUg| exact WMg| exact MIg| exact STg|]. constructor; [left; cbn [fst snd]; rewrite ESPK; clear - LOSPu SPAL; lia| constructor]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUg)) in FRLo'; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUg)) in HP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha Q2 Q4 CEIL LOSPu SPAL; nrm; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUg)) in HOC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LOSPu SPAL; nrm; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUg)) in HOP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LOSPu SPAL; nrm; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUg)) in OCS; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BAC CEIL LOSPu SPAL; nrm; lia].
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIG) as (HEAPG & _). clear OF.
    clear MU WM WMg. pose proof (munch_refl [(f + 64, f + 72)]%Z mG) as MU. pose proof (wmono_refl ctasegs mG) as WM.
    (* [comment removed for export] *)
    pose proof (DJLO _ _ OINA ltac:(subst LB'; apply in_or_app; left; right; left; reflexivity)) as OFA. cbn [blk_addr blk_size fst snd] in OFA. unfold ASN1_STRING_SIZE in OFA.
    frz MUg. unfold asn1_string_cells in OCS.
    (* [comment removed for export] *)
    step. step. step. step.
    match goal with H : munch _ mG ?mx |- _ => rename H into MUh end. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mH end.
    match goal with H : mem_inv ctasegs mH |- _ => rename H into MIh end. match goal with H : stk ctasegs mH lo spa |- _ => rename H into STh end.
    match goal with H : wmono ctasegs mG mH |- _ => rename H into WMh end.
    assert (LIH : linv ΣO stO mH OWO boO NEWO (CSTb - D2I_OCTET_COST_A (zlength d))).
    { kit @oinv_munch; [exact LIG| exact MUh| exact WMh| exact MIh| exact STh|].
      constructor; [right; left; exists (f + 64, f + 72)%Z; split; [subst XP; right; left; reflexivity| cbn; clear; lia]| constructor]. }
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIH) as (HEAPH & _). clear OF.
    eapply evt_cut.
    { eapply (@ASN1_STRING_get_length_specA (push AR f 1)) with (lo := lo) (OW := OWO) (LB := NEWO ++ LB') (xb := os_blk os);
        [exact HEAPH| rewrite ESPA; exact STh| exact MIh| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; clear - LOSPu SPAL; lia
        | apply in_or_app; right; apply in_or_app; left; exact OINA| clear - OAL; unfold al16 in OAL; Z.div_mod_to_equations; lia| exact OCS| clear - OL0 OL31; lia| reflexivity]. }
    intros msI (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & mI & -> & MUi & WMi & MIi & STi & _).
    rewrite (ret_pc_even 0x337194) by (clear; lia). rewrite ?ESPA in STi, MUi.
    assert (LII : linv ΣO stO mI OWO boO NEWO (CSTb - D2I_OCTET_COST_A (zlength d))).
    { kit @oinv_munch; [exact LIH| exact MUi| exact WMi| exact MIi| exact STi|]. constructor; [left; cbn [fst snd]; rewrite ESPK; clear - LOSPu SPAL; lia| constructor]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUi)) in FRLo'; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUi)) in HP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha Q2 Q4 CEIL LOSPu SPAL; nrm; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUi)) in HOC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LOSPu SPAL; nrm; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUi)) in HOP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LOSPu SPAL; nrm; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUi)) in OCS; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BAC CEIL LOSPu SPAL; nrm; lia].
    (* [comment removed for export] *)
    thaw MUg.
    assert (MUOI : munch [(spa - 16, spa); (f + 64, f + 72)]%Z mO mI).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUg]; intros x Hx; cbn [outside fst snd] in Hx |- *; clear - Hx; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUh]; intros x Hx; cbn [outside fst snd] in Hx |- *; clear - Hx; lia|].
      eapply munch_weaken; [| exact MUi]; intros x Hx; cbn [outside fst snd] in Hx |- *; clear - Hx; lia. }
    clear MUg MUh WMh MUi WMi. pose proof (munch_refl (@nil (Z * Z)) mI) as MU. pose proof (wmono_refl ctasegs mI) as WM.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LII) as (HEAPI & NDI & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LII) as (_ & _ & _ & _ & _ & _ & _ & CSI & _ & CRI & _). clear OC. cbn [ar_RT push amb] in CRI.
    pose proof LII as (PREI & _ & KOI & KII & _ & _ & CRTI & _). cbn [ar_RT push amb] in CRTI.
    (* [comment removed for export] *)
    step. step. step. step. apply evt_done.
    (* [comment removed for export] *)
    change (Z_to_bv 64 3368804) with (wz O2I_SCT_LIST_A).
    assert (AGD : agree_on (fun a => exists b, In b NEWO /\ blk_addr b <= a < blk_addr b + blk_size b) mO mI).
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUOI)|]. intros a (b & Hb & Hr).
      pose proof (BNDO b ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (B1 & B2 & B3 & B4). pce B3.
      pose proof (DJLO _ _ Hb ltac:(subst LB'; apply in_or_app; left; right; left; reflexivity)) as DJb. cbn [blk_addr blk_size fst snd] in DJb.
      cbn [outside fst snd]. clear - Hr B3 DJb CEIL LOSPu SPAL. lia. }
    assert (LTB : Z.of_nat (length (to_bytes (os_bytes os))) = os_len os) by (rewrite OLEN; clear; unfold to_bytes, zlength; rewrite length_map; reflexivity).
    eapply implAp_abind.
    { pose proof (HLIST f) as W. unfold o2i_sct_list_specA2 in W.
      eapply W with (LB := NEWO ++ LB') (K := K) (adr := adrO) (c := os_bytes os) (D := DP) (PIN := f + 64) (lo := lo) (E := E) (bo := boO) (OW := OWO) (ras := bv_unsigned ra :: ras); clear W.
      - eapply ap_preA_weaken; [exact PREI| subst STKb; clear; lia| clear - CRI; subst CSTb; ecu; lia| subst FRMb; clear; ecu; lia].
      - reflexivity.
      - rewrite ESPA. exact (proj1 (proj2 (proj2 (keepA _ _ _ _ _ _ _ LII)))).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_list CTX).
      - apply cons_ne.
      - exact KOI.
      - exact KII.
      - exact OLEN.
      - exact DP0.
      - exact DP63.
      - exact ODF.
      - destruct (os_data os) as [[dp n]|] eqn:EOD.
        + destruct ODAT as (NBD & DIN & DLE & DBY). subst DP. cbn [optr].
          eapply bytes_at_agree; [exact AGD| exact DBY|]. intros a Ha. rewrite LTB in Ha. exists (dp, adrO dp, n).
          split; [rewrite ENO; unfold oct_blocks; rewrite EOD; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; clear - Ha DLE; lia].
        + rewrite ODAT, (DPN eq_refl). unfold bytes_at, to_bytes, zlength. cbn. repeat split; first [clear; lia| intros i Hi; exfalso; clear - Hi; lia].
      - destruct (os_data os) as [[dp n]|] eqn:EOD; [right| left; exact ODAT]. destruct ODAT as (NBD & DIN & DLE & DBY).
        exists dp, (adrO dp), n. split; [apply in_or_app; left; rewrite ENO; unfold oct_blocks; rewrite EOD; right; left; reflexivity|]. subst DP. cbn [optr]. clear - DLE OLEN. lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| rewrite (ADRO b Hb); exact (ADR1' b Hb)].
        rewrite ENO in Hb. unfold oct_blocks in Hb. destruct Hb as [<-|Hb]; [reflexivity|]. destruct (os_data os) as [[dp n]|]; [| destruct Hb]. destruct Hb as [<-|[]]. reflexivity.
      - exists (qp, f + 64, 8). split; [apply in_or_app; right; subst LB'; unfold fto_pbs; right; left; reflexivity| cbn; clear; lia].
      - clear - G2. Z.div_mod_to_equations. lia.
      - destruct (os_data os) as [[dp n]|] eqn:EOD.
        + destruct ODAT as (NBD & DIN & DLE & DBY).
          pose proof (DJLO (dp, adrO dp, n) (qp, f + 64, 8) ltac:(rewrite ENO; unfold oct_blocks; rewrite EOD; right; left; reflexivity) ltac:(subst LB'; apply in_or_app; left; right; left; reflexivity)) as DJd.
          cbn [blk_addr blk_size fst snd] in DJd. subst DP. cbn [optr]. clear - DJd DLE OLEN. lia.
        + rewrite ODAT, (DPN eq_refl). unfold zlength. cbn. clear - G1. lia.
      - exact HOP.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    intros r ΣL msL POL. unfold o2i_list_postA2 in POL. rewrite ?ESPA in POL.
    destruct POL as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & FL & fcL & mL & OWL & boL & adrL & NEWL & pv
                     & -> & PREL & AXL & CRL & BKL & ADRL & FRSHL & LBOKL & HPL & RESL).
    destruct r as [ok stL]. cbn [fst snd] in PREL, BKL, RESL |- *.
    rewrite (ret_pc_even 0x3371a4) by (clear; lia). cbn [ar_RT push amb] in CRL.
    assert (LIL : linv ΣL stL mL OWL boL (NEWL ++ NEWO) (CSTb - D2I_OCTET_COST_A (zlength d) - O2I_SCT_LIST_COST_A)).
    { kit @oinv_after; [exact LII| exact PREL| exact AXL| | exact CRL| | exact BKL| exact LBOKL].
      - intros a Ha. cbn [rin_ivs fst snd app] in Ha. right; left. subst XP. cbn [rin_ivs fst snd]. clear - Ha. lia.
      - clear - CRI; subst CSTb; ecu; lia. }
    set (CL := CSTb - D2I_OCTET_COST_A (zlength d) - O2I_SCT_LIST_COST_A) in LIL.
    assert (HCL : 0 <= CL) by (subst CL CSTb; unfold D2I_SCT_LIST_COST_A; clear; lia).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AXL) in FRLo'; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha G3 CEIL CE1 LOSPu SPAL; nrm; lia| left; clear - Ha TOP SPAH; unfold USTACK_TOP in *; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXL) in HP; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; unfold frozen in Q5; clear - Ha QP Q1 Q2 Q3 Q5; lia| right; right; exists bq; split; [apply in_or_app; right; subst LB'; apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AXL) in HOC; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha G4; unfold SEGTOP_A in G4; lia| right; right; exists (qo, f + 32, 8); split; [apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AXL) in OCS; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha OFA BAI; lia| right; right; exists (os_blk os, A, ASN1_STRING_SIZE); split; [apply in_or_app; left; exact OINA| cbn; unfold ASN1_STRING_SIZE; clear - Ha; lia]]].
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIL) as (HEAPL & _ & BNDL & _ & DJLL & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIL) as (_ & STL & _ & _ & _ & _ & MIL & _). clear OC.
    clear MU WM. pose proof (munch_refl [(PIN, PIN + 8)]%Z mL) as MU. pose proof (wmono_refl ctasegs mL) as WM.
    assert (NBD : match os_data os with Some (dp, _) => dp <> os_blk os | None => True end) by (destruct (os_data os) as [[dp n]|]; [exact (proj1 ODAT)| exact I]).
    assert (ADRL' : forall b, In b LB -> adrL (blk_id b) = adr (blk_id b)).
    { intros b Hb. rewrite (ADRL b) by (apply in_or_app; right; subst LB'; apply in_or_app; right; exact Hb). rewrite (ADRO b) by (subst LB'; apply in_or_app; right; exact Hb). exact (ADR1 b Hb). }
    (* [comment removed for export] *)
    pose proof (DJLL (os_blk os, A, ASN1_STRING_SIZE) bq ltac:(apply in_or_app; right; exact OINA) ltac:(subst LB'; apply in_or_app; right; exact HBQ)) as DJq.
    cbn [blk_addr blk_size fst snd] in DJq. unfold ASN1_STRING_SIZE in DJq.
    apply implAp_from_evt.
    destruct ok as [k|].
    - (* [comment removed for export] *)
      destruct RESL as (PML & SKL & WL1 & WL2 & WL3).
      pose proof (BNDL (sk_blk k, adrL (sk_blk k), STACK_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; eapply Permutation_in; [symmetry; exact PML|]; unfold sk_blocks; rewrite !in_app_iff; right; right; left; reflexivity)) as (BK0 & _ & BKC & BKI).
      cbn [blk_addr blk_size fst snd] in BK0, BKC, BKI. pce BKC. unfold STACK_SIZE in BKC, BKI.
      step. step. if_cases KZ; zc KZ; [exfalso; revert KZ; rewrite ?O2iKitAR.land_ones64_small, ?unsigned_lit by (clear - BK0 BKC CN; lia); clear - BK0; lia|]. clear KZ.
      assert (HBQL : In bq (OWL ++ (NEWL ++ NEWO) ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; apply in_or_app; right; exact HBQ).
      ablock HEAPL HBQL ACCQ2 OFFQ2.
      assert (OFF2 : offshW [(PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ2 CEIL LOSPu SPAL CE2 Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ2.
      ab_shload 8.
      step. step. setreg 10%Z (Z_to_bv 64 (D + zlength d)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 CN; pose proof (zlength_ge0' d); lia); bv_solve).
      step. name_mem mS. apply evt_done.
      match goal with H : munch _ mL mS |- _ => rename H into MUs end. match goal with H : wmono ctasegs mL mS |- _ => rename H into WMs end.
      match goal with H : mem_inv ctasegs mS |- _ => rename H into MIs end. match goal with H : stk ctasegs mS lo spa |- _ => rename H into STs end.
      assert (LIS : linv ΣL stL mS OWL boL (NEWL ++ NEWO) CL).
      { kit @oinv_munch; [exact LIL| exact MUs| exact WMs| exact MIs| exact STs|].
        constructor; [right; left; exists (PIN, PIN + 8)%Z; split; [subst XP; right; right; left; reflexivity| cbn; clear; lia]| constructor]. }
      assert (SKS : sk_repA mS (OWL ++ NEWL ++ NEWO ++ LB') adrL k).
      { eapply sk_repA_agree; [apply (agree_on_of_munch_nw _ _ _ MUs)| | exact SKL]. intros b a Hb Ha. cbn [outside fst snd].
        pose proof (DJLL b bq ltac:(apply in_or_app; left; eapply Permutation_in; [symmetry; exact PML| exact Hb]) ltac:(subst LB'; apply in_or_app; right; exact HBQ)) as DJ.
        clear - DJ Ha Q1 Q2. lia. }
      eapply (free_tailA (Some k) ΣL stL mS OWL boL CL adrO adrL NEWO NEWL os);
        [exact LIS| exact HCL| exact ENO| exact NBD| exact ADRL'| exact FRLo'| exact HOC| exact HP| exact OCS| reflexivity|].
      split; [exact PML|]. split; [exact SKS|]. split; [reflexivity|]. split; [clear - WL3 WL2; lia| clear - WL1 WL2; lia].
    - (* [comment removed for export] *)
      step. step. if_cases KZ; zc KZ; [| exfalso; apply KZ; reflexivity]. clear KZ. apply evt_done.
      eapply (free_tailA None ΣL stL mL OWL boL CL adrO adrL NEWO NEWL os);
        [exact LIL| exact HCL| exact ENO| exact NBD| exact ADRL'| exact FRLo'| exact HOC| exact HP| exact OCS| reflexivity| exact RESL].
  Qed.
End Act.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem d2i_sct_list_walkA : d2i_sct_list_specA2 D2I_SCT_LIST_STACK_A D2I_SCT_LIST_COST_A D2I_SCT_LIST_FRAMES_A.
Proof.
  unfold d2i_sct_list_specA2. intros until PIN. intros PRE TP UW CTX NE KOW KIDS PAY ADR CPIN ALP PIND HPIN Ea0 Ea1 Ea2 HK.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
  pose proof PAY as (_ & _ & _ & _ & D26 & _).
  pose proof LOSP as LOSPu. pose proof CRED as CREDu. pose proof FRM0 as FRMu. ecu.
  intros XX Φ DD SAFE LINK. subst tp a0 a1 a2.
  (* [comment removed for export] *)
  pose proof (AH_ceil _ _ _ _ HEAP) as (_ & _ & CE3).
  destruct CPIN as (bq & HBQ & Q1 & Q2). pose proof (AH_range_gen _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror HBQ))) as (Q3 & _ & _ & Q4 & _).
  assert (EPIN : bv_unsigned (Z_to_bv 64 PIN) = PIN) by (apply unsigned_lit; clear - Q1 Q2 Q3 Q4 CE3; unfold BnHeapA.ACEIL, SHHI, STACK_WIN, USTACK_TOP in *; lia).
  change (wz D2I_SCT_LIST_A) with (wz DSL_ENTRY).
  eapply (dsl_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold DSL_FRAME, RT_STACK; clear - LOSPu; lia| exact TOP| exact AL16
    | unfold MallocRep.wz; rewrite EPIN; clear - Q1 Q3; lia| unfold MallocRep.wz; rewrite EPIN; exact ALP
    | exact MI| reflexivity
    | clear - FRMu; lia
    | clear - CREDu D26; pose proof (D2I_OCTET_COST_A_bound (zlength d) ltac:(split; [apply zlength_ge0'| exact D26])); lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 jf24 jf40 jf64 jf72 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AG3 FRL FRH HF FRS SPA32 SPAL SPAH GSZ SAVJ.
  change (dsl_shadow_pro jst) with (fto_shadow_pro jst) in FRS.
  destruct (fto_open_pbs Σ1 OW LB m3 f jst HEAP3 FRESH GEO FRS) as (qo & qp & HEAPp3 & QOF & QPF & QOP).
  destruct (oct0_cellsA m3 f jf24 jf40 jf64 jf72 HF) as [HO3 HJ3].
  eapply (implAp_elim _ Σ Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| exact EL1].
  unfold MallocRep.wz. rewrite EPIN.   (* [comment removed for export] *)
  eapply dsl_bodyA; try eassumption. exists bq. split; [exact HBQ| split; [exact Q1| exact Q2]].
Qed.

End WithRT.
