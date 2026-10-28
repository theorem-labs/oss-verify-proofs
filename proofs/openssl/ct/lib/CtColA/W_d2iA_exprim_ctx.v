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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA EdgesA UnwindX UnwindRecA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_item_d2i_exA W_item_d2i_tailA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_bufmemA W_collectA W_d2iA_stmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.
Notation payload_readA := CtRepA.W_get_object_walkA.payload_readA.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Section Body.
  (* [comment removed for export] *)
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCTL : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_gen_specA AR' UK.

  (* [comment removed for export] *)
  Variables (STK : Z) (CST : Z -> Z) (FRMb : Z).
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (adr : bptr -> Z) (D : Z) (d : list Z) (OPP PV TLC : Z) (j31 : list byte).
  Variables (f spa : Z) (g : nat) (junk gj : list byte) (Σ1 : rts RT) (m3 : mem).
  Let len := zlength d.
  Let gr := get_object d 0 len.

  (* [comment removed for export] *)
  Hypothesis PRE0 : ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRMb.
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis CELLS : d2i_cells_okA m LB D d OPP PV TLC j31.
  Hypothesis LEN1 : 0 < len.

  (* [comment removed for export] *)
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m3.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 2 b.
  Hypothesis GEO : @fr_geo (push AR f 2) f 2.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 272 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 256.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 168.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Hypothesis STKB : ADEP_FRAME + CHECK_TLEN_STACK_A + 6 * 176 <= STK.
  Hypothesis FRMBb : 1 + CHECK_TLEN_FRAMES_A <= FRMb.
(* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma exo_ctx :
    Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 26
    /\ 12365824 <= ACEIL /\ 17594333495296 <= ACEIL /\ ACEIL + 8388608 <= 140737488355328
    /\ ACEIL <= lo /\ 0 <= lo /\ lo + 272 + CHECK_TLEN_STACK_A <= bv_unsigned sp /\ 66320 <= CHECK_TLEN_STACK_A
    /\ bv_unsigned sp + 16 <= USTACK_TOP /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes d)) = zlength d /\ bv_unsigned (Z_to_bv 64 spa) = spa
    /\ 0 < f /\ f mod 64 = 0 /\ f + 256 <= ACEIL /\ 12365824 <= f /\ bv_unsigned (Z_to_bv 64 f) = f /\ (f + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ (f + 248 <= shad f \/ shad f + 32 <= f) /\ 2147450880 <= shad f /\ shad f + 32 <= 17594333495296
    /\ (exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd /\ 0 < blk_addr bd /\ blk_addr bd + blk_size bd <= ACEIL
                   /\ (blk_addr bd + blk_size bd <= 0x10000 \/ SEGTOP_A <= blk_addr bd) /\ off_fr f 2 bd)
    /\ (exists bq, In bq LB /\ blk_addr bq <= OPP /\ OPP + 8 <= blk_addr bq + blk_size bq /\ 0 < blk_addr bq /\ blk_addr bq + blk_size bq <= ACEIL
                   /\ (blk_addr bq + blk_size bq <= 0x10000 \/ SEGTOP_A <= blk_addr bq) /\ off_fr f 2 bq)
    /\ (exists bv, In bv LB /\ blk_addr bv <= PV /\ PV + 8 <= blk_addr bv + blk_size bv /\ 0 < blk_addr bv /\ blk_addr bv + blk_size bv <= ACEIL
                   /\ (blk_addr bv + blk_size bv <= 0x10000 \/ SEGTOP_A <= blk_addr bv) /\ off_fr f 2 bv)
    /\ (exists bt, In bt LB /\ blk_addr bt <= TLC /\ TLC + 32 <= blk_addr bt + blk_size bt /\ 0 < blk_addr bt /\ blk_addr bt + blk_size bt <= ACEIL
                   /\ (blk_addr bt + blk_size bt <= 0x10000 \/ SEGTOP_A <= blk_addr bt) /\ off_fr f 2 bt).
  Proof.
    clear KOW KIDS AGF HCTL.
    destruct PRE0 as (HEAP & _ & _ & _ & ST & CEIL & LOSP & TOP & _ & _ & _ & _).
    destruct CELLS as (PAY & COPP & CPV & CTLC & _).
    destruct PAY as (_ & DF & D0 & D63 & D26 & HB).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in C1, C2, C3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof STKB as LOSP'. unfold ADEP_FRAME in LOSP'.
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    assert (ESS : 66320 <= CHECK_TLEN_STACK_A) by (unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK; clear; lia).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold SEGTOP_A in G4. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3.
    assert (CELL : forall A n, cellA_in LB A n -> exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b /\ 0 < blk_addr b
                   /\ blk_addr b + blk_size b <= BnHeapA.ACEIL /\ (blk_addr b + blk_size b <= 0x10000 \/ SEGTOP_A <= blk_addr b) /\ off_fr f 2 b).
    { intros A n (b & Hb & H1 & H2). assert (Hb' : In b (OW ++ LB)) by (apply in_or_app; right; exact Hb).
      pose proof (AH_range_gen _ _ _ _ _ HEAP Hb') as (R0 & _ & _ & R3 & R4). exists b. repeat (split; [assumption|]). exact (FRESH b Hb'). }
    split; [exact DF|]. split; [exact D0|]. split; [exact D63|]. split; [exact D26|].
    split; [clear - C1; lia|]. split; [clear - C2; lia|]. split; [clear - C3; lia|].
    split; [exact CEIL|]. split; [exact LO0|]. split; [clear - LOSP LOSP'; lia|]. split; [exact ESS|]. split; [exact TOP|]. split; [exact SPR|].
    split; [unfold to_bytes, zlength; rewrite length_map; reflexivity|].
    split; [apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 CEIL LO0 LOSP LOSP' SPAL SPAH SPR ESS; lia|].
    split; [exact G1|]. split; [exact G2|]. split; [unfold BnHeapA.ACEIL; exact G3|]. split; [exact G4|].
    split; [apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia|]. split; [exact G5|].
    assert (SHR : 2147450880 <= shad f /\ shad f + 32 <= 17594333495296).
    { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
      assert (f / 8 + 32 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 32); [apply Z.div_lt_upper_bound; clear - G3 C3; unfold BnHeapA.ACEIL in *; lia | clear - H0; lia]). clear - H H0. lia. }
    split; [clear - G5 SHR; unfold shad, SHB in *; destruct G5 as [G5|G5]; [left | right]; Z.div_mod_to_equations; lia|].
    split; [clear - SHR; lia|]. split; [clear - SHR; lia|].
    split. { destruct HB as [E0|(b & Hb & H1 & H2)]; [exfalso; clear - LEN1 E0; unfold len in LEN1; rewrite E0 in LEN1; unfold zlength in LEN1; cbn in LEN1; lia|]. exact (CELL D (zlength d) ltac:(exists b; auto)). }
    split; [exact (CELL OPP 8 COPP)|]. split; [exact (CELL PV 8 CPV)| exact (CELL TLC 32 CTLC)].
  Qed.

  (* [comment removed for export] *)
  Definition exo_lowA := ex_lowA OPP PV f g junk.
  Definition exo_frameA := ex_frameA.

  (* [comment removed for export] *)
  Definition exo_pbs (qfc qb : bptr) : list block := [(qfc, f + 64, 1); (qb, f + 80, 32)].
  Definition exo_XP : list (Z * Z) := [(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32); (f + 64, f + 65); (f + 80, f + 112)].
  Definition exo_inv (qfc qb : bptr) (mr : mem) : rts RT -> ap_st bptr -> mem -> list block -> Z * Z -> list block -> Z -> Prop :=
    @oinv (push AR f 2) sp mr Σ1 (exo_pbs qfc qb ++ LB) E lo K d D exo_XP (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1).

End Body.
End WithRT.
