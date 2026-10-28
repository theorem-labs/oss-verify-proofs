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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_err_newA W_err_set_debugA W_err_vsetA W_get_object_closedA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep W_sct_set1_signature W_sct_list_free W_o2i_sig W_sct_new W_o2i_sct O2iKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA W_sct_newA W_sct_set1_signatureA W_sct_freeA W_sct_list_freeA O2iKitAR W_o2i_sigA Fr_o2i_SCT O2iSctStmtB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Notation sct_cells := CtSctP.SctRep.sct_cells.
Notation set_sig_cells := CtSctP.W_sct_set1_signature.set_sig_cells.
Notation sct_blocks := CtSctP.W_sct_list_free.sct_blocks.
Notation oblk := CtSctP.W_sct_list_free.oblk.
Notation remove_sct := CtSctP.W_sct_list_free.remove_sct.
Notation sct_new_cells := CtSctP.W_sct_new.sct_new_cells.
Notation zxb_lit := CtRepP.W_get_object_walk.zxb_lit.
Notation znth_range8 := CtRepP.W_get_object_walk.znth_range.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition OSC_RAISE : Z := 0x335820.       (* [comment removed for export] *)
Definition OSC_ERR0 : Z := 0x335934.       (* [comment removed for export] *)
Definition OSC_ERR : Z := 0x335938.
Definition OSC_FIN : Z := 0x3358fc.       (* [comment removed for export] *)
Definition OSC_V1 : Z := 0x3359f0.
Definition OSC_NV1 : Z := 0x3358a8.

Local Notation E_new99 := (E_o2i_SCT_34978c : uk_call 0x335704 0x335828 0x1fd52c).
Local Notation E_new114 := (E_o2i_SCT_34978c : uk_call 0x335704 0x335828 0x1fd52c).
Local Notation E_new128 := (E_o2i_SCT_34978c : uk_call 0x335704 0x335828 0x1fd52c).
Local Notation E_dbg := (E_o2i_SCT_3497a8 : uk_call 0x335704 0x335844 0x1fd844).
Local Notation E_err := (E_o2i_SCT_3497bc : uk_call 0x335704 0x335858 0x1fdab8).
Local Notation E_sctnew := (E_o2i_SCT_3497c4 : uk_call 0x335704 0x335860 0x3374cc).
Local Notation E_dup135 := (E_o2i_SCT_349844 : uk_call 0x335704 0x3358c4 0x203fd8).
Local Notation E_free91c := (E_o2i_SCT_3498d8 : uk_call 0x335704 0x335940 0x337578).
Local Notation E_dup104 := (E_o2i_SCT_3499d8 : uk_call 0x335704 0x335a1c 0x203fd8).
Local Notation E_dup118 := (E_o2i_SCT_349c9c : uk_call 0x335704 0x335bfc 0x203fd8).
Local Notation E_sig := (E_o2i_SCT_349d08 : uk_call 0x335704 0x335c58 0x335420).

Lemma mcost_0_small : forall n, 0 <= n <= 64512 -> mcost n = 0.
Proof. intros n Hn. unfold mcost. replace (n <=? 64512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma sct_new_cells_repA : forall (m : mem) A adr0 pn,
  rw_cells ctasegs m A (sct_new_cells (Z_to_bv 64 (-1))) -> rw_cells ctasegs m A (sct_cells adr0 (sct_new pn) (-1) 0).
Proof.
  intros m A adr0 pn H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold CtSctP.SctRep.sct_cells, CtSctP.W_sct_new.sct_new_cells, MallocRep.wz; cbn -[Z_to_bv le4 le8]; bytes_lit_eq| reflexivity].
Qed.

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

Local Ltac ecu := unfold O2I_SCT_STACK_A, O2I_SCT_COST_A, O2I_SCT_FRAMES_A, O2I_SIG_STACK_A, O2I_SIG_COST_A, O2I_SIG_FRAMES_A, GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A,
                         SCT_NEW_STACK_A, CRYPTO_MEMDUP_STACK_A, SCT_FREE_STACK_A, SCT_SET1_SIGNATURE_STACK_A, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, CRYPTO_FREE_STACK,
                         ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK,
                         ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, RT_STACK in *.

(* [comment removed for export] *)
Lemma osc_open_p : forall Σ1 OW LB m f q,
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m -> (forall b, In b LB -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m (shad f) osc_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) m.
Proof.
  intros Σ1 OW LB m f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 0) Σ1 OW LB m f 0%nat q (f + 32) 8 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 0) with 64; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m (shad f) osc_shadow_pro 4%nat (f + 32) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b Hb) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 0) with 64 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block) (ras : list Z).
  Variables (adr : bptr -> Z) (c : list Z) (D p len PIN : Z).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo O2I_SCT_STACK_A (O2I_SCT_COST_A len) O2I_SCT_FRAMES_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx O2I_SCT_A (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D c.
  Hypothesis P0 : 0 <= p.
  Hypothesis LEN : 1 <= len <= MAX_SCT_SIZE.
  Hypothesis PL : p + len <= zlength c.
  Hypothesis ADR : forall b, In b LB -> adr (blk_id b) = blk_addr b.
  Hypothesis CPIN : cellA_in LB PIN 8.
  Hypothesis ALP : PIN mod 8 = 0.
  Hypothesis PIND : PIN + 8 <= D \/ D + zlength c <= PIN.
  Hypothesis HPIN : rw_cells ctasegs m PIN [C8 (wz (D + p))].
  (* [comment removed for export] *)
  Variables (Σ1 : rts RT) (m3 m4 : mem) (f spa : Z) (g : nat) (junk gj j0 j8 j16 j24 j32 j40 jp : list (bv 8)) (qp : bptr).
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3.
  Hypothesis QPF : ~ In qp (map blk_id (OW ++ LB)).
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 0 b.
  Hypothesis GEO : @fr_geo (push AR f 0) f 0.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis EL1 : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AG3 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis FRS3 : rw_cells ctasegs m3 (shad f) osc_shadow_pro.
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 176 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 160.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 72.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Hypothesis MU4 : munch [(spa + 48, spa + 56)]%Z m3 m4.
  Hypothesis WM4 : wmono ctasegs m3 m4.
  Hypothesis MI4 : mem_inv ctasegs m4.
  Hypothesis ST4 : stk ctasegs m4 lo spa.
  Hypothesis FRLo4 : rw_cells ctasegs m4 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40].
  Hypothesis FRHi4 : rw_cells ctasegs m4 (spa + 48) [C8 (Z_to_bv 64 f); CB g junk].
  Hypothesis FRH4 : rw_cells ctasegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis HP4 : rw_cells ctasegs m4 (f + 32) [CB 8 jp].

  Let STKb : Z := O2I_SIG_STACK_A.
  Let CSTb : Z := O2I_SCT_COST_A len - 1.
  Let FRMb : Z := O2I_SCT_FRAMES_A - 1.
  Let LB' : list block := (qp, f + 32, 8) :: LB.
  Let XP : list (Z * Z) := [(f + 32, f + 40); (PIN, PIN + 8)]%Z.
  Let spk : word := Z_to_bv 64 (spa + 48).
  (* [comment removed for export] *)
  Let linv : rts RT -> ap_st bptr -> mem -> list block -> Z * Z -> list block -> Z -> Prop :=
    @oinv (push AR f 0) spk m4 Σ1 LB' E lo K c D XP spa STKb CSTb FRMb.
  (* [comment removed for export] *)
  Definition dst (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mX : mem) (pc : Z) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) x19 x20 (Z_to_bv 64 PIN) x22 x23 x24 (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 SHB) x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mX (seg_rom ctasegs).      (* [comment removed for export] *)
  Local Notation SPOST := (o2i_sct_postA2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (O2I_SCT_COST_A len) adr c D p len PIN) (only parsing).

  Lemma base_facts :
    0 <= bv_unsigned sp < 2 ^ 64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo /\ 0 <= lo
    /\ lo <= bv_unsigned sp - O2I_SCT_STACK_A /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
    /\ 0 < f /\ f mod 64 = 0 /\ f + 64 <= ACEIL /\ SEGTOP_A <= f /\ (f + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f /\ O2I_SCT_COST_A len <= rt_credit RT Σ /\ Z.of_nat (length FRs) + O2I_SCT_FRAMES_A <= Z.of_nat FRAMES_MAX
    /\ Forall (fun b => 0 <= b < 256) c /\ 0 < D /\ D + zlength c < 2 ^ 63 /\ zlength c < 2 ^ 26 /\ D + zlength c <= ACEIL /\ Z.of_nat (length (to_bytes c)) = zlength c
    /\ (exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength c <= blk_addr bd + blk_size bd /\ 0 < blk_addr bd /\ (blk_addr bd + blk_size bd <= 65536 \/ 12365824 <= blk_addr bd) /\ off_fr f 0 bd
                  /\ blk_addr bd + blk_size bd <= ACEIL)
    /\ (exists bq, In bq LB /\ blk_addr bq <= PIN /\ PIN + 8 <= blk_addr bq + blk_size bq /\ 0 < blk_addr bq /\ blk_addr bq + blk_size bq <= ACEIL
                  /\ (blk_addr bq + blk_size bq <= 65536 \/ 12365824 <= blk_addr bq) /\ off_fr f 0 bq)
    /\ bv_unsigned (Z_to_bv 64 PIN) = PIN /\ bv_unsigned (Z_to_bv 64 (spa + 48)) = spa + 48 /\ 0 <= mcost len /\ List.NoDup (map blk_id (OW ++ LB)).
  Proof.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5. cbn [ar_SP0 push amb] in G3.
    pose proof LOSP as LOSPu. ecu.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LOSPu SPAL SPAH SPR LO0; plia).
    assert (ESPK : bv_unsigned (Z_to_bv 64 (spa + 48)) = spa + 48) by (apply unsigned_lit; clear - CE1 CEIL LOSPu SPAL SPAH SPR LO0; plia).
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; plia).
    destruct PAY as (HB & DF & D0 & D63 & D26 & HBLK).
    destruct HBLK as [E0|(bd & HBD & BD1 & BD2)]; [exfalso; subst c; unfold zlength in PL; cbn in PL; clear - PL P0 LEN; lia|].
    pose proof (AH_range_gen _ _ _ _ bd HEAP (in_or_app _ _ _ (or_intror HBD))) as (B1 & _ & _ & B4 & B5).
    destruct CPIN as (bq & HBQ & Q1 & Q2). pose proof (AH_range_gen _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror HBQ))) as (Q3 & _ & _ & Q4 & Q5).
    assert (EPIN : bv_unsigned (Z_to_bv 64 PIN) = PIN) by (apply unsigned_lit; clear - Q1 Q2 Q3 Q4 CE3; plia).
    pose proof (mcost_mono len len ltac:(clear - LEN; lia)) as [MC _].
    split; [exact SPR|]. split; [exact CE1|]. split; [exact CE2|]. split; [exact CE3|]. split; [exact CEIL|]. split; [exact LO0|]. split; [exact LOSP|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact ESPA|]. split; [exact Ef|]. split; [clear - CRED; lia|]. split; [clear - FRM0; lia|].
    split; [exact DF|]. split; [exact D0|]. split; [exact D63|]. split; [exact D26|]. split; [clear - B4 BD2; lia|]. split; [clear; unfold to_bytes, zlength; rewrite length_map; reflexivity|].
    split; [exists bd; repeat (split; [assumption|]); split; [exact (FRESH bd (in_or_app _ _ _ (or_intror HBD)))| exact B4]|].
    split; [exists bq; repeat (split; [assumption|]); exact (FRESH bq (in_or_app _ _ _ (or_intror HBQ)))|].
    split; [exact EPIN|]. split; [exact ESPK|]. split; [exact MC| exact (AH_nodup _ _ _ _ HEAP)].
  Qed.

  Local Ltac bf := pose proof base_facts as (SPR & CE1 & CE2 & CE3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0 & FRM0
                                            & DF & D0 & D63 & D26 & DCEIL & DLEN & BDX & BQX & EPIN & ESPK & MC0 & NDL);
                   pose proof LOSP as LOSPu; unfold O2I_SCT_STACK_A, O2I_SIG_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in LOSPu.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac pce H := change (@BnHeapA.ACEIL (push AR f 0)) with (@BnHeapA.ACEIL AR) in H.

  (* [comment removed for export] *)
  Lemma HEAPp : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m3.
  Proof. subst LB'. exact (osc_open_p Σ1 OW LB m3 f qp HEAP3 ltac:(intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))) GEO FRS3 QPF). Qed.

  (* [comment removed for export] *)
  Lemma HPIN4 : rw_cells ctasegs m4 PIN [C8 (wz (D + p))].
  Proof.
    bf. destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). pose proof PRE as (HEAP & _).
    eapply rw_cells_agree; [| exact HPIN|].
    - eapply agree_on_trans; [exact AG3|].
      eapply (aclient_agree_of_munch Σ OW LB OW m m3 m4); [exact HEAP| intros b Hb; exact Hb| exact MU4| clear - CEIL LOSPu SPAL; alia| clear - SPAH; lia].
    - intros a Ha. cbn in Ha. right; right. exists bq. split; [apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia].
  Qed.

  Lemma KH : @kit_hyps (push AR f 0) spk LB' lo c D XP spa STKb.
  Proof.
    bf. destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC). destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    unfold kit_hyps. subst spk. rewrite ESPK. split; [exact DF|]. split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL|]. split; [exact LO0|].
    split; [subst STKb; clear - LOSPu SPAL; ecu; lia|]. split; [subst STKb; clear; ecu; lia|]. split; [clear; lia|]. split; [clear - TOP SPAH; lia|].
    split; [clear - SPA32; Z.div_mod_to_equations; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
    split. { subst XP LB'. constructor; [| constructor; [| constructor]]; cbn [fst snd].
             - exists (qp, f + 32, 8). split; [left; reflexivity| cbn; clear; lia].
             - exists bq. split; [right; exact HBQ| clear - Q1 Q2; lia]. }
    split. { subst XP. constructor; [| constructor; [| constructor]]; cbn [fst snd]; right.
             - unfold off_fr in OD. change (fs_size 0) with 64 in OD. clear - OD BD1 BD2. lia.
             - clear - PIND. lia. }
    split; [| clear - D0; lia]. right. exists (blk_id bd), (blk_addr bd), (blk_size bd).
    split; [subst LB'; right; destruct bd as [[? ?] ?]; exact HBD| split; [exact BD1| exact BD2]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac kit L := eapply (L (push AR f 0) spk m4 Σ1 LB' E lo K c D XP spa STKb CSTb FRMb KH).
  Local Ltac kitp L H := pose proof (L (push AR f 0) spk m4 Σ1 LB' E lo K c D XP spa STKb CSTb FRMb KH) as H.

  (* [comment removed for export] *)
  Lemma linv0 : linv Σ1 st m4 OW bo [] CSTb.
  Proof.
    bf.
    pose proof (pro_closeA Σ st m OW LB E bo sp lo O2I_SCT_STACK_A (O2I_SCT_COST_A len) O2I_SCT_FRAMES_A f 0%nat Σ1 m3 spa 160 PRE HEAP3 ST3 MI3 AG3 CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(clear; ecu; lia) ltac:(clear - MC0; ecu; lia) ltac:(clear; ecu; lia)) as P3.
    destruct P3 as (_ & AS3 & IDS3 & DC3 & _ & CEIL3 & LOSP3 & TOP3 & AL3 & _ & CRED3 & FRM3). rewrite ESPA in LOSP3, TOP3, AL3.
    assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m4).
    { eapply (@AH_frame (push AR f 0)); [exact HEAPp| exact MU4| exact WM4|]. constructor; [left; cbn [fst snd]; clear - CEIL LOSPu SPAL SPAH TOP; plia| constructor]. }
    assert (AGL : agree_on (lib_addr OW) m3 m4).
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)|]. intros a HL. cbn [outside fst snd]. split; [| exact I].
      destruct HL as [HS|(b & Hb & Hr)].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CE1 CEIL LOSPu SPAL. plia.
      - pose proof PRE as (HEAP & _). pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R4 & _).
        destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4. clear - Hr R4 CEIL LOSPu SPAL. plia. }
    kit @oinv_entry; [| exact KOW| exact KIDS|].
    - unfold ap_preA. rewrite ESPA. cbn [ar_FR ar_RT ar_SP0 push amb length]. cbn [ar_FR ar_RT ar_SP0 push amb length] in CRED3, FRM3.
      split; [exact HEAP4|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS3 AGL)|]. split; [exact IDS3|].
      pose proof AS3 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD3)).
      split; [exact (data_cells_agree _ _ _ _ DC3 AGL OD3)|].
      split; [exact ST4|].
      split; [exact CEIL3|]. split; [subst STKb; clear - LOSP3; ecu; lia|]. split; [exact TOP3|]. split; [exact AL3|]. split; [exact MI4|].
      split; [subst CSTb; exact CRED3| subst FRMb; exact FRM3].
    - destruct PAY as (HB & _). pose proof PRE as (HEAP & _). eapply bytes_at_agree; [| exact HB|].
      + eapply agree_on_trans; [exact AG3|].
        eapply (aclient_agree_of_munch Σ OW LB OW m m3 m4); [exact HEAP| intros b Hb; exact Hb| exact MU4| clear - CEIL LOSPu SPAL; alia| clear - SPAH; lia].
      + intros a Ha. rewrite DLEN in Ha. destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
        right; right. exists bd. split; [apply in_or_app; right; exact HBD| clear - Ha BD1 BD2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma keepA : forall ΣX stX mX OWX boX NEW CX, linv ΣX stX mX OWX boX NEW CX ->
    rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells ctasegs mX (spa + 48) [C8 (Z_to_bv 64 f); CB g junk]
    /\ uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras)
    /\ agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX.
  Proof.
    intros until CX. intros (_ & AX & _). bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). subst spk. rewrite ESPK in AX.
    assert (FHI : f + 64 <= spa) by (clear - G3 CEIL LOSPu SPAL; plia).
    assert (QHI : PIN + 8 <= spa) by (clear - Q2 Q4 CEIL LOSPu SPAL; plia).
    assert (AXS : forall a, spa + 48 <= a < USTACK_TOP -> mX (wa a) = m4 (wa a)).
    { intros a Ha. unfold USTACK_TOP in Ha. apply AX; [clear - Ha SPR CEIL LOSPu SPAL LO0; lia|]. split; [| left; unfold USTACK_TOP; exact Ha].
      subst XP. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha FHI QHI CEIL CE1 LOSPu SPAL. plia. }
    assert (A34 : forall a, bv_unsigned sp <= a < USTACK_TOP -> m4 (wa a) = m3 (wa a)).
    { intros a Ha. apply (agree_on_of_munch_nw _ _ _ MU4); [clear - Ha SPR; unfold USTACK_TOP in Ha; lia|]. cbn [outside fst snd]. clear - Ha SPAH. lia. }
    assert (AGS : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mX).
    { intros a Ha Hr. unfold USTACK_TOP in Hr. rewrite (AXS a ltac:(unfold USTACK_TOP; clear - Hr SPAH; lia)), (A34 a ltac:(unfold USTACK_TOP; exact Hr)).
      apply AG3; [exact Ha| left; unfold USTACK_TOP; exact Hr]. }
    assert (FRH : rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_agree; [| exact FRH4|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. apply AXS. clear - Ha TOP SPAH. unfold USTACK_TOP in *. lia. }
    split; [exact FRH|]. split; [| split; [| exact AGS]].
    - eapply rw_cells_agree; [| exact FRHi4|]; [intros wa' Hr Hc; exact Hc|].
      intros a Ha. cbv beta. cbn [cells_size csize Nat.add] in Ha. apply AXS. clear - Ha TOP SPAH GSZ. unfold USTACK_TOP in *. lia.
    - eapply (uw_call m mX spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [exact UW| exact AGS| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| clear - TOP; unfold USTACK_TOP in *; lia| apply bv_unsigned_in_range|].
      rewrite !Z_to_bv_bv_unsigned. cbn [app]. exact FRH.
  Qed.

  (* [comment removed for export] *)
  Lemma close_pb : forall ΣX OWX NEW mX, @BnHeapA.AHEAP (push AR f 0) ΣX OWX (NEW ++ LB') mX -> @BnHeapA.AHEAP (push AR f 0) ΣX OWX (NEW ++ LB) mX.
  Proof.
    intros ΣX OWX NEW mX H. subst LB'.
    eapply (@frame_obj_close (push AR f 0)) with (f := f) (k := 0%nat) (b := (qp, f + 32, 8)); [left; reflexivity| | unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
    eapply AH_lb_perm; [exact H|]. symmetry. apply Permutation_middle.
  Qed.

  (* [comment removed for export] *)
  Lemma closeA : forall ΣX stX mX OWX boX NEW CX Σ' m',
    linv ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    AHEAP Σ' OWX (NEW ++ LB) m' -> rt_credit RT Σ' = rt_credit RT ΣX -> stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
    agree_on (aclient_addr (OWX ++ (NEW ++ LB)) spa) mX m' ->
    ap_preA Σ' stX m' OWX (NEW ++ LB) E boX sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)]%Z ++ LIBW_A) m m'
    /\ rt_credit RT Σ - O2I_SCT_COST_A len <= rt_credit RT Σ'
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
      eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [| clear; apply Z.le_refl]|].
      { eapply (aclient_agree_of_munch Σ OW LB OW m m3 m4); [exact HEAP| intros b Hb; exact Hb| exact MU4| clear - CEIL LOSPu SPAL; alia| clear - SPAH; lia]. }
      eapply ax_pres_trans.
      + unfold ax_pres. eapply agree_on_mono; [exact AX|]. intros a [HXa Ha]. split.
        * subst XP. intros HIN. apply HXa. cbn [app rin_ivs fst snd] in HIN |- *.
          destruct HIN as [HIN|HIN]; [| exact HIN]. exfalso.
          destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha HIN G3 CEIL LOSPu SPAL; plia| |].
          -- pose proof (client_static_below a Ha). clear - H HIN G4; unfold SEGTOP_A in G4; lia.
          -- pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
             destruct b as [[bq' bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O HIN. lia.
        * destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [subst LB'; right; exact Hb| exact Hr]].
      + eapply (ax_pres_of_aclient (OWX ++ NEW) LB); [rewrite <- app_assoc; exact AG' | clear - SPAH; lia].
    - subst CSTb. clear - CR CR1 CR' HCX. lia.
    - eapply (blocks_kept_post K stX OWX (NEW ++ LB)); [| exact AG'].
      eapply (blocks_kept_pre K stX OW OWX LB); [exact KOW | |].
      + eapply agree_on_trans; [exact AG3|]. eapply (aclient_agree_of_munch Σ OW LB OW m m3 m4); [exact HEAP| intros b Hb; exact Hb| exact MU4| clear - CEIL LOSPu SPAL; alia| clear - SPAH; lia].
      + split; [exact KO|]. split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP].
    - intros b Hb Hin. apply (FRSH b Hb). rewrite map_app in Hin |- *. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left; exact Hin| right; subst LB'; right; exact Hin].
    - eapply Forall_impl; [| exact LBOK]. intros b Hb. exact (lbokA_pop _ _ _ Hb).
  Qed.

  (* [comment removed for export] *)
  Lemma osc_exitA : forall ΣX stX mX OWX boX NEW CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x28 x29 x30 x31 : word) FX fcX
      (r : option (sctr bptr)) (adrX : bptr -> Z) (j16' j24' : list (bv 8)),
    linv ΣX stX mX OWX boX NEW CX -> 0 <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    match r with
    | None => NEW = [] /\ x19 = Z_to_bv 64 0 /\ rw_cells ctasegs mX PIN [C8 (wz (D + p))]
    | Some x => NEW = sct_blocks adrX x /\ x19 = Z_to_bv 64 (adrX (sc_blk x)) /\ sct_repA mX (OWX ++ NEW ++ LB) adrX x
                /\ rw_cells ctasegs mX PIN [C8 (wz (D + p + len))] /\ sc_version x = CtWire.byte c p /\ i2o_sct_len x <= len
    end ->
    implAp (ARet (r, stX)) ΣX SPOST (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x28 x29 x30 x31 FX fcX mX OSC_EXIT).
  Proof.
    intros until j24'. intros LI HCX FRLo ADRX RES. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    pose proof (keepA _ _ _ _ _ _ _ LI) as (FRH & FRHi & UWX & AGS).
    pose proof LI as (PREX & _ & _ & _ & _ & _ & _ & LBOK). cbn [app] in PREX. pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & _ & _ & _ & MIX & _). rewrite ESPA in STX.
    (* [comment removed for export] *)
    pose proof (rw_cells_app_join mX spa _ _ FRLo ltac:(cbn [cells_size csize Nat.add]; replace (spa + Z.of_nat 48) with (spa + 48) by (clear; lia); exact FRHi)) as FRL.
    cbn [app] in FRL. apply (rw_cells_cb_first mX spa _ 7) in FRL. cbn [cb_first csize cbytes] in FRL.
    intros XX Φ DD SAFE LINK. unfold dst. change (Z_to_bv 64 OSC_EXIT) with (wz OSC_EXIT).
    eapply (@osc_epi_cps AR _) with (lo := lo) (LB := NEW ++ LB) (gj := gj) (hrest := []);
      [exact (close_pb _ _ _ _ HEAPX)| | exact STX| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| clear - LOSPu SPAL; lia| exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIX| exact FRL| exact FRH| reflexivity|].
    { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [| exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))].
      (* [comment removed for export] *)
      pose proof (proj1 (Forall_forall _ _) LBOK b Hb) as [_ NPB].
      destruct (@AH_fr_blk (push AR f 0) ΣX OWX (NEW ++ LB') mX f 0%nat b HEAPX (or_introl eq_refl) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as [IN|OFF];
        [exfalso; apply NPB; exists f, 0%nat; split; [left; reflexivity| exact IN]| exact OFF]. }
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply (implAp_elim _ ΣX Σ' _ _ XX Φ DD); [| exact SAFE| exact LINK| exact LIVE'].
    apply implAp_ret.
    destruct (closeA _ _ _ _ _ NEW CX _ _ LI HCX HEAP' CR' ST' MI' AG') as (PRE' & AX' & CRE' & BK' & NFR & LBOK').
    assert (KPIN : forall v, rw_cells ctasegs mX PIN [C8 v] -> rw_cells ctasegs m' PIN [C8 v]).
    { intros v H. eapply rw_cells_agree; [exact AG'| exact H|]. intros a Ha. cbn in Ha. right; right. exists bq. split; [apply in_or_app; right; apply in_or_app; right; exact HBQ| clear - Ha Q1 Q2; lia]. }
    unfold o2i_sct_postA2. cbn [fst snd].
    destruct r as [x|].
    - destruct RES as (EN & -> & SR & HP & EV & WL).
      do 14 eexists. exists FX, fcX, m', OWX, boX, adrX, NEW. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
      split; [exact ADRX|]. split; [exact NFR|]. split; [exact LBOK'|]. split; [exact EN|].
      split; [| split; [exact (KPIN _ HP)| split; [exact EV| exact WL]]].
      eapply sct_repA_agreeK; [exact AG'| | exact SR]. intros b a Hb Ha. right; right. exists b. split; [| exact Ha].
      apply in_or_app. right. apply in_or_app. left. rewrite EN. exact Hb.
    - destruct RES as (EN & -> & HP).
      do 14 eexists. exists FX, fcX, m', OWX, boX, adrX, NEW. split; [reflexivity|]. split; [exact PRE'|]. split; [exact AX'|]. split; [exact CRE'|]. split; [exact BK'|].
      split; [exact ADRX|]. split; [exact NFR|]. split; [exact LBOK'|]. split; [exact EN| exact (KPIN _ HP)].
  Qed.

  (* [comment removed for export] *)
  Lemma remove_sct_front : forall adrX xr (OWX L : list block),
    List.NoDup (map blk_id (OWX ++ sct_blocks adrX xr ++ L)) -> remove_sct xr (sct_blocks adrX xr ++ OWX) = OWX.
  Proof.
    intros adrX xr OWX L ND. rewrite (CtSctP.O2iKit.remove_sct_app xr (sct_blocks adrX xr) OWX).
    rewrite (map_app blk_id OWX), (map_app blk_id (sct_blocks adrX xr) L) in ND.
    pose proof (NoDup_app_split _ _ ND) as (N23 & D1 & N1). pose proof (NoDup_app_split _ _ N23) as (N3 & D2 & N2).
    rewrite (CtSctP.O2iKit.remove_sct_self adrX xr N2), (CtSctP.O2iKit.remove_sct_notin adrX xr OWX); [reflexivity|].
    intros q Hq Hin. apply (D1 q Hin). apply in_app_iff. left. exact Hq.
  Qed.

  (* [comment removed for export] *)
  Lemma err_tailA : forall ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 : word) FX fcX
      (xr : sctr bptr) (adrX : bptr -> Z) (AX_ vs : Z) (j16' j24' : list (bv 8)),
    linv ΣX stX mX OWX boX (sct_blocks adrX xr) CX -> 0 <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mX PIN [C8 (wz (D + p))] ->
    adrX (sc_blk xr) = AX_ -> rw_cells ctasegs mX AX_ (sct_cells adrX xr (-1) vs) ->
    implAp (abind (sct_free xr) (fun _ => aret None) stX) ΣX SPOST
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX_) x20 x22 x23 x24 x28 x29 x30 x31 FX fcX mX OSC_ERR).
  Proof.
    intros until j24'. intros LI HCX FRLo ADRX HP EAX HC. subst AX_. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (FRH & FRHi & UWX & AGS).
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _). clear OC.
    pose proof LI as (_ & _ & _ & _ & _ & _ & _ & LBOK).
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    rewrite CtSctP.W_o2i_sct.sct_free_abind. change (ofree (sc_logid xr) _) with (afree_sct xr (ARet (@None (sctr bptr), stX))).
    unfold dst, OSC_ERR. apply implAp_from_evt. step. step. apply evt_done.
    (* [comment removed for export] *)
    pose proof (AH_adopt_list _ _ _ _ _ HEAPX LBOK) as HEAPO.
    assert (NDO : List.NoDup (map blk_id (sct_blocks adrX xr ++ OWX))).
    { pose proof (@AH_nodup (push AR f 0) _ _ _ _ HEAPO) as N. rewrite map_app in N. apply NoDup_app_split in N as (_ & _ & N). exact N. }
    change (Z_to_bv 64 3372408) with (wz SCT_FREE_A).
    eapply (SCT_free_walkA' (AR := push AR f 0)) with (lo := lo) (OW := sct_blocks adrX xr ++ OWX) (LB := LB') (adr := adrX) (x := xr) (ras := bv_unsigned ra :: ras);
      [exact HEAPO| rewrite ESPA; exact STX| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; subst STKb; clear - LOSPu SPAL; ecu; lia
      | rewrite ESPA; clear - TOP SPAH; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MIX| reflexivity| exact CSX
      | apply Forall_forall; intros b Hb; apply in_or_app; left; exact Hb| | exact NDO
      | exact (sct_ptr_cellsA_of_cells _ _ _ _ _ HC)| reflexivity| rewrite ESPA; exact UWX| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free91c CTX)|].
    { pose proof NDO as N. rewrite map_app in N. apply NoDup_app_split in N as (_ & _ & N). exact N. }
    intros ΣF msF PO. unfold ofree_postA in PO. rewrite ?ESPA in PO. rewrite (remove_sct_front adrX xr OWX LB' NDX) in PO.
    destruct PO as (w0 & w1 & w2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & FF & fcF & mF & -> & MIF & STF & AGF & CRF & HEAPF).
    rewrite (ret_pc_even 0x335940) by (clear; lia). unfold MallocRep.wz.
    assert (LIF : linv ΣF stX mF OWX boX [] (CX - 0)).
    { kit @oinv_heap; [exact LI| eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha| intros b Hb; apply in_or_app; exact Hb
        | cbn [app]; exact HEAPF| constructor| exact MIF| exact STF| rewrite CRF; clear; lia| clear - HCX; lia]. }
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctasegs mF) as WM.
    apply implAp_from_evt. step. apply evt_done.
    change (Z_to_bv 64 3365188) with (Z_to_bv 64 OSC_EXIT).
    eapply (osc_exitA ΣF stX mF OWX boX [] (CX - 0)) with (r := None) (adrX := adrX) (j16' := j16') (j24' := j24');
      [exact LIF| clear - HCX; lia| | exact ADRX|].
    - eapply rw_cells_agree; [exact AGF| exact FRLo|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left. clear - Ha SPAH TOP. unfold USTACK_TOP in *. lia.
    - split; [reflexivity|]. split; [reflexivity|].
      eapply rw_cells_agree; [exact AGF| exact HP|]. intros a Ha. cbn in Ha. right; right. exists bq. split; [apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma keptA : forall ΣX stX mA OWX boX NEW CX mB,
    linv ΣX stX mA OWX boX NEW CX -> ax_pres (NEW ++ LB') spa LIBW_A mA mB ->
    (forall cs, rw_cells ctasegs mA spa cs -> Z.of_nat (cells_size cs) = 48 -> rw_cells ctasegs mB spa cs)
    /\ (forall b cxs, In b NEW -> rw_cells ctasegs mA (blk_addr b) cxs -> Z.of_nat (cells_size cxs) <= blk_size b -> rw_cells ctasegs mB (blk_addr b) cxs)
    /\ (forall v, rw_cells ctasegs mA PIN [C8 v] -> rw_cells ctasegs mB PIN [C8 v])
    /\ (forall cp, rw_cells ctasegs mA (f + 32) cp -> Z.of_nat (cells_size cp) = 8 -> rw_cells ctasegs mB (f + 32) cp).
  Proof.
    intros until mB. intros LI AX. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ).
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & _). clear OF.
    split; [| split; [| split]].
    - intros cs H SZ. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. rewrite SZ in Ha. split.
      + intros HL. pose proof (libw_rangeA a HL). clear - H0 Ha CEIL CE1 LOSPu SPAL. plia.
      + left. clear - Ha SPAH TOP. unfold USTACK_TOP in *. lia.
    - intros b cxs Hb H SZ. pose proof (BND b ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)) as (B0 & _ & B3 & B4).
      eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. split.
      + intros HL. pose proof (libw_rangeA a HL). clear - H0 Ha SZ B0 B3 B4. lia.
      + right; right. exists b. split; [apply in_or_app; left; exact Hb| clear - Ha SZ; lia].
    - intros v H. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. cbn in Ha. split.
      + intros HL. pose proof (libw_rangeA a HL). clear - H0 Ha Q1 Q2 Q3 Q5. lia.
      + right; right. exists bq. split; [apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia].
    - intros cp H SZ. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. rewrite SZ in Ha. split.
      + intros HL. pose proof (libw_rangeA a HL). clear - H0 Ha G4. unfold SEGTOP_A in G4. lia.
      + right; right. exists (qp, f + 32, 8). split; [apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia].
  Qed.

  (* [comment removed for export] *)
  Local Ltac err_call Wc Ec OIc UWc :=
    eapply (@oinv_ap_callA (push AR f 0) UK spk m4 Σ1 LB' E lo K c D XP spa STKb CSTb FRMb KH);
    [ exact Wc | exact OIc | subst STKb; ecu; clear; lia | | subst FRMb; ecu; clear; lia
    | exact UWc
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ Ec CTX)
    | apply cons_ne
    | ].     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition raise_postA (x19 x20 x22 x23 x24 : word) (j16' j24' : list (bv 8)) (AX_ : Z) (cxs : list cell) (vpin : word) (CX : Z) (NEW : list block) (boX : Z * Z)
      (r : unit * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (FY : bvmap 5 word) (fcY : bv 32) mY OWY,
      ms' = dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x28 x29 x30 x31 FY fcY mY 0x335858
      /\ linv ΣY (snd r) mY OWY boX NEW (CX - GETOBJ_ERR_COST_A)
      /\ rw_cells ctasegs mY spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40]
      /\ rw_cells ctasegs mY AX_ cxs /\ rw_cells ctasegs mY PIN [C8 vpin].

  (* [comment removed for export] *)
  Lemma raise_err99A : forall ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 : word) FX fcX
      (xr : sctr bptr) (adrX : bptr -> Z) (AX_ vs : Z) (j16' j24' : list (bv 8)),
    linv ΣX stX mX OWX boX (sct_blocks adrX xr) CX -> GETOBJ_ERR_COST_A <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mX PIN [C8 (wz (D + p))] ->
    adrX (sc_blk xr) = AX_ -> rw_cells ctasegs mX AX_ (sct_cells adrX xr (-1) vs) ->
    implAp (abind (err_raise RS_sct_43) (fun _ => abind (sct_free xr) (fun _ => aret None)) stX) ΣX SPOST
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX_) x20 x22 x23 x24 x28 x29 x30 x31 FX fcX mX 0x3359f8).
  Proof.
    intros until j24'. intros LI HCX FRLo ADRX HP EAX HC. subst AX_. bf.
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    assert (HXIN : In (sc_blk xr, adrX (sc_blk xr), SCT_SIZE) (sct_blocks adrX xr)).
    { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. do 4 right. left. reflexivity. }
    destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_O2I_SCT_A 8 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    change 19 with (rs_flen RS_sct_43) in LF. change 8 with (rs_fnlen RS_sct_43) in LN.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold dst, OSC_RAISE.
    eapply (implAp_abind _ _ _ _ (raise_postA (Z_to_bv 64 (adrX (sc_blk xr))) (Z_to_bv 64 99) x22 x23 x24 j16' j24' (adrX (sc_blk xr)) (sct_cells adrX xr (-1) vs) (Z_to_bv 64 (D + p)) CX (sct_blocks adrX xr) boX)).
    { unfold err_raise.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. step. step. step. apply evt_done. err_call constr:(@ERR_new_walkA (push AR f 0) UK BE boX) constr:(E_new99) LI UWX; [ecu; clear - HCX; lia| reflexivity]. }
      intros r1 Σa msa POa. cbv beta in POa.
      destruct POa as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & Fa & fca & mA & OWa & boa & -> & LIa & AXa & EBOa). subst boa.
      rewrite (ret_pc_even 0x335828) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mA LI AXa) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      clear FRLo HC HP AXa. rename T1 into FRLo. rename T2 into HC. rename T3 into HP.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIa) as (_ & STa & _ & _ & _ & _ & MIa & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LIa) as (_ & _ & UWa & _).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. do 6 step. apply evt_done.
        err_call constr:(@ERR_set_debug_walkA (push AR f 0) UK BE STRCPY RS_sct_43 _ _ boX fs fk ns nk LF LN) constr:(E_dbg) LIa UWa.
        - pose proof LIa as (PREa & _). pose proof PREa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa & _). ecu. clear - CRa HCX. lia.
        - unfold A_CT_OCT_C_A, A_O2I_SCT_A, MallocRep.wz. split; [reflexivity|]. split; [| split; reflexivity].
          first [reflexivity| apply bv_eq; rewrite ?unsigned_lit by (clear; cbn; lia); bv_solve]. }
      intros r2 Σb msb POb. cbv beta in POb.
      destruct POb as (p0 & p1 & p2 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & Fb & fcb & mB & OWb & bob & -> & LIb & AXb & EBOb). subst bob.
      rewrite (ret_pc_even 0x335844) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mB LIa AXb) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      clear FRLo HC HP AXb. rename T1 into FRLo. rename T2 into HC. rename T3 into HP.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIb) as (_ & STb & _ & _ & _ & _ & MIb & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LIb) as (_ & _ & UWb & _).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
      (* [comment removed for export] *)
      eapply implAp_mono.
      { apply implAp_from_evt. do 4 step. apply evt_done.
        err_call constr:(@ERR_set_error_closedA (push AR f 0) UK BE RS_sct_43 50 104 boX) constr:(E_err) LIb UWb.
        - pose proof LIb as (PREb & _). pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _).
          pose proof LIa as (PREa' & _). pose proof PREa' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa' & _). ecu. clear - CRa' CRb HCX. lia.
        - unfold ERR_LIB_SYS, ERR_LIB_CT, MallocRep.wz in *. cbn [rs_code]. repeat split; first [reflexivity | (clear; lia)]. }
      intros r3 Σc msc POc. cbv beta in POc.
      destruct POc as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & LIc & AXc & EBOc). subst boc.
      rewrite (ret_pc_even 0x335858) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mC LIb AXc) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      unfold raise_postA, dst. do 16 eexists. exists Fc, fcc, mC, OWc.
      split; [reflexivity|]. split; [| split; [exact T1| split; [exact T2| exact T3]]].
      kit @oinv_credit; [exact LIc|].
      pose proof LIc as (PREc & _). pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _). ecu. clear - CRc HCX. lia. }
    (* [comment removed for export] *)
    intros r3 Σc msc POc. unfold raise_postA in POc.
    destruct POc as (o1 & o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & Fc & fcc & mC & OWc & -> & LIc & FRc & HCc & HPc).
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIc) as (_ & STc & _ & _ & _ & _ & MIc & _). clear OC.
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    cbn [fst snd]. unfold dst. apply implAp_from_evt. step. apply evt_done.
    change (Z_to_bv 64 3365176) with (Z_to_bv 64 OSC_ERR).
    eapply (err_tailA Σc (snd r3) mC OWc boX (CX - GETOBJ_ERR_COST_A)) with (adrX := adrX) (vs := vs);
      [exact LIc| clear - HCX; lia| exact FRc| exact ADRX| exact HPc| reflexivity| exact HCc].
  Qed.

  (* [comment removed for export] *)
  Lemma raise_err114A : forall ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 : word) FX fcX
      (xr : sctr bptr) (adrX : bptr -> Z) (AX_ vs : Z) (j16' j24' : list (bv 8)),
    linv ΣX stX mX OWX boX (sct_blocks adrX xr) CX -> GETOBJ_ERR_COST_A <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mX PIN [C8 (wz (D + p))] ->
    adrX (sc_blk xr) = AX_ -> rw_cells ctasegs mX AX_ (sct_cells adrX xr (-1) vs) ->
    implAp (abind (err_raise RS_sct_ext) (fun _ => abind (sct_free xr) (fun _ => aret None)) stX) ΣX SPOST
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX_) x20 x22 x23 x24 x28 x29 x30 x31 FX fcX mX 0x335bc8).
  Proof.
    intros until j24'. intros LI HCX FRLo ADRX HP EAX HC. subst AX_. bf.
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    assert (HXIN : In (sc_blk xr, adrX (sc_blk xr), SCT_SIZE) (sct_blocks adrX xr)).
    { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. do 4 right. left. reflexivity. }
    destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_O2I_SCT_A 8 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    change 19 with (rs_flen RS_sct_ext) in LF. change 8 with (rs_fnlen RS_sct_ext) in LN.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold dst, OSC_RAISE.
    eapply (implAp_abind _ _ _ _ (raise_postA (Z_to_bv 64 (adrX (sc_blk xr))) (Z_to_bv 64 114) x22 x23 x24 j16' j24' (adrX (sc_blk xr)) (sct_cells adrX xr (-1) vs) (Z_to_bv 64 (D + p)) CX (sct_blocks adrX xr) boX)).
    { unfold err_raise.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. step. step. step. apply evt_done. err_call constr:(@ERR_new_walkA (push AR f 0) UK BE boX) constr:(E_new114) LI UWX; [ecu; clear - HCX; lia| reflexivity]. }
      intros r1 Σa msa POa. cbv beta in POa.
      destruct POa as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & Fa & fca & mA & OWa & boa & -> & LIa & AXa & EBOa). subst boa.
      rewrite (ret_pc_even 0x335828) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mA LI AXa) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      clear FRLo HC HP AXa. rename T1 into FRLo. rename T2 into HC. rename T3 into HP.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIa) as (_ & STa & _ & _ & _ & _ & MIa & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LIa) as (_ & _ & UWa & _).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. do 6 step. apply evt_done.
        err_call constr:(@ERR_set_debug_walkA (push AR f 0) UK BE STRCPY RS_sct_ext _ _ boX fs fk ns nk LF LN) constr:(E_dbg) LIa UWa.
        - pose proof LIa as (PREa & _). pose proof PREa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa & _). ecu. clear - CRa HCX. lia.
        - unfold A_CT_OCT_C_A, A_O2I_SCT_A, MallocRep.wz. split; [reflexivity|]. split; [| split; reflexivity].
          first [reflexivity| apply bv_eq; rewrite ?unsigned_lit by (clear; cbn; lia); bv_solve]. }
      intros r2 Σb msb POb. cbv beta in POb.
      destruct POb as (p0 & p1 & p2 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & Fb & fcb & mB & OWb & bob & -> & LIb & AXb & EBOb). subst bob.
      rewrite (ret_pc_even 0x335844) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mB LIa AXb) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      clear FRLo HC HP AXb. rename T1 into FRLo. rename T2 into HC. rename T3 into HP.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIb) as (_ & STb & _ & _ & _ & _ & MIb & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LIb) as (_ & _ & UWb & _).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
      (* [comment removed for export] *)
      eapply implAp_mono.
      { apply implAp_from_evt. do 4 step. apply evt_done.
        err_call constr:(@ERR_set_error_closedA (push AR f 0) UK BE RS_sct_ext 50 104 boX) constr:(E_err) LIb UWb.
        - pose proof LIb as (PREb & _). pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _).
          pose proof LIa as (PREa' & _). pose proof PREa' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa' & _). ecu. clear - CRa' CRb HCX. lia.
        - unfold ERR_LIB_SYS, ERR_LIB_CT, MallocRep.wz in *. cbn [rs_code]. repeat split; first [reflexivity | (clear; lia)]. }
      intros r3 Σc msc POc. cbv beta in POc.
      destruct POc as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & LIc & AXc & EBOc). subst boc.
      rewrite (ret_pc_even 0x335858) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mC LIb AXc) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      unfold raise_postA, dst. do 16 eexists. exists Fc, fcc, mC, OWc.
      split; [reflexivity|]. split; [| split; [exact T1| split; [exact T2| exact T3]]].
      kit @oinv_credit; [exact LIc|].
      pose proof LIc as (PREc & _). pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _). ecu. clear - CRc HCX. lia. }
    (* [comment removed for export] *)
    intros r3 Σc msc POc. unfold raise_postA in POc.
    destruct POc as (o1 & o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & Fc & fcc & mC & OWc & -> & LIc & FRc & HCc & HPc).
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIc) as (_ & STc & _ & _ & _ & _ & MIc & _). clear OC.
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    cbn [fst snd]. unfold dst. apply implAp_from_evt. step. apply evt_done.
    change (Z_to_bv 64 3365176) with (Z_to_bv 64 OSC_ERR).
    eapply (err_tailA Σc (snd r3) mC OWc boX (CX - GETOBJ_ERR_COST_A)) with (adrX := adrX) (vs := vs);
      [exact LIc| clear - HCX; lia| exact FRc| exact ADRX| exact HPc| reflexivity| exact HCc].
  Qed.

  (* [comment removed for export] *)
  Lemma raise_err128A : forall ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x28 x29 x30 x31 : word) FX fcX
      (xr : sctr bptr) (adrX : bptr -> Z) (AX_ vs : Z) (j16' j24' : list (bv 8)),
    linv ΣX stX mX OWX boX (sct_blocks adrX xr) CX -> GETOBJ_ERR_COST_A <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mX PIN [C8 (wz (D + p))] ->
    adrX (sc_blk xr) = AX_ -> rw_cells ctasegs mX AX_ (sct_cells adrX xr (-1) vs) ->
    implAp (abind (err_raise RS_sct_sig) (fun _ => abind (sct_free xr) (fun _ => aret None)) stX) ΣX SPOST
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX_) x20 x22 x23 x24 x28 x29 x30 x31 FX fcX mX 0x335c6c).
  Proof.
    intros until j24'. intros LI HCX FRLo ADRX HP EAX HC. subst AX_. bf.
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    assert (HXIN : In (sc_blk xr, adrX (sc_blk xr), SCT_SIZE) (sct_blocks adrX xr)).
    { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. do 4 right. left. reflexivity. }
    destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_O2I_SCT_A 8 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    change 19 with (rs_flen RS_sct_sig) in LF. change 8 with (rs_fnlen RS_sct_sig) in LN.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold dst, OSC_RAISE.
    eapply (implAp_abind _ _ _ _ (raise_postA (Z_to_bv 64 (adrX (sc_blk xr))) (Z_to_bv 64 128) x22 x23 x24 j16' j24' (adrX (sc_blk xr)) (sct_cells adrX xr (-1) vs) (Z_to_bv 64 (D + p)) CX (sct_blocks adrX xr) boX)).
    { unfold err_raise.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. step. step. step. apply evt_done. err_call constr:(@ERR_new_walkA (push AR f 0) UK BE boX) constr:(E_new128) LI UWX; [ecu; clear - HCX; lia| reflexivity]. }
      intros r1 Σa msa POa. cbv beta in POa.
      destruct POa as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & Fa & fca & mA & OWa & boa & -> & LIa & AXa & EBOa). subst boa.
      rewrite (ret_pc_even 0x335828) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mA LI AXa) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      clear FRLo HC HP AXa. rename T1 into FRLo. rename T2 into HC. rename T3 into HP.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIa) as (_ & STa & _ & _ & _ & _ & MIa & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LIa) as (_ & _ & UWa & _).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. do 6 step. apply evt_done.      (* [comment removed for export] *)
        err_call constr:(@ERR_set_debug_walkA (push AR f 0) UK BE STRCPY RS_sct_sig _ _ boX fs fk ns nk LF LN) constr:(E_dbg) LIa UWa.
        - pose proof LIa as (PREa & _). pose proof PREa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa & _). ecu. clear - CRa HCX. lia.
        - unfold A_CT_OCT_C_A, A_O2I_SCT_A, MallocRep.wz. split; [reflexivity|]. split; [| split; reflexivity].
          first [reflexivity| apply bv_eq; rewrite ?unsigned_lit by (clear; cbn; lia); bv_solve]. }
      intros r2 Σb msb POb. cbv beta in POb.
      destruct POb as (p0 & p1 & p2 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & Fb & fcb & mB & OWb & bob & -> & LIb & AXb & EBOb). subst bob.
      rewrite (ret_pc_even 0x335844) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mB LIa AXb) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      clear FRLo HC HP AXb. rename T1 into FRLo. rename T2 into HC. rename T3 into HP.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIb) as (_ & STb & _ & _ & _ & _ & MIb & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LIb) as (_ & _ & UWb & _).
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
      (* [comment removed for export] *)
      eapply implAp_mono.
      { apply implAp_from_evt. do 4 step. apply evt_done.
        err_call constr:(@ERR_set_error_closedA (push AR f 0) UK BE RS_sct_sig 50 104 boX) constr:(E_err) LIb UWb.
        - pose proof LIb as (PREb & _). pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _).
          pose proof LIa as (PREa' & _). pose proof PREa' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa' & _). ecu. clear - CRa' CRb HCX. lia.
        - unfold ERR_LIB_SYS, ERR_LIB_CT, MallocRep.wz in *. cbn [rs_code]. repeat split; first [reflexivity | (clear; lia)]. }
      intros r3 Σc msc POc. cbv beta in POc.
      destruct POc as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & Fc & fcc & mC & OWc & boc & -> & LIc & AXc & EBOc). subst boc.
      rewrite (ret_pc_even 0x335858) by (clear; lia).
      destruct (keptA _ _ _ _ _ _ _ mC LIb AXc) as (T1 & T2 & T3 & _).
      specialize (T1 _ FRLo eq_refl). specialize (T2 _ _ HXIN HC ltac:(rewrite CtSctP.SctRep.sct_cells_size; cbn; clear; lia)). specialize (T3 _ HP). cbn [blk_addr fst snd] in T2.
      unfold raise_postA, dst. do 16 eexists. exists Fc, fcc, mC, OWc.
      split; [reflexivity|]. split; [| split; [exact T1| split; [exact T2| exact T3]]].
      kit @oinv_credit; [exact LIc|].
      pose proof LIc as (PREc & _). pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _). ecu. clear - CRc HCX. lia. }
    (* [comment removed for export] *)
    intros r3 Σc msc POc. unfold raise_postA in POc.
    destruct POc as (o1 & o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & Fc & fcc & mC & OWc & -> & LIc & FRc & HCc & HPc).
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIc) as (_ & STc & _ & _ & _ & _ & MIc & _). clear OC.
    clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mC) as MU. pose proof (wmono_refl ctasegs mC) as WM.
    cbn [fst snd]. unfold dst. apply implAp_from_evt. step. apply evt_done.
    change (Z_to_bv 64 3365176) with (Z_to_bv 64 OSC_ERR).
    eapply (err_tailA Σc (snd r3) mC OWc boX (CX - GETOBJ_ERR_COST_A)) with (adrX := adrX) (vs := vs);
      [exact LIc| clear - HCX; lia| exact FRc| exact ADRX| exact HPc| reflexivity| exact HCc].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_okA : forall ΣX stX mX OWX boX CX (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) FX fcX
      (xr : sctr bptr) (adrX : bptr -> Z) (AX_ : Z) (j16' j24' : list (bv 8)) (vpin : word),
    linv ΣX stX mX OWX boX (sct_blocks adrX xr) CX -> 0 <= CX ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    (forall b, In b LB -> adrX (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mX PIN [C8 vpin] -> adrX (sc_blk xr) = AX_ ->
    sct_repA mX (OWX ++ sct_blocks adrX xr ++ LB) adrX xr -> sc_version xr = CtWire.byte c p -> i2o_sct_len xr <= len ->
    implAp (ARet (Some xr, stX)) ΣX SPOST
      (dst x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 AX_) (Z_to_bv 64 0) (Z_to_bv 64 (D + p + len)) x23
           (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) x28 x29 x30 x31 FX fcX mX OSC_FIN).      (* [comment removed for export] *)
  Proof.
    intros until vpin. intros LI HCX FRLo ADRX HP EAX SR EV WL. subst AX_. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). frz Q5.
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    assert (HBQ' : In bq (OWX ++ (sct_blocks adrX xr ++ LB'))) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ).
    pose proof (proj2 (@AH_acc (push AR f 0) _ _ _ _ bq HEAPX HBQ')) as ACCQ. pose proof (@AH_offsh (push AR f 0) _ _ _ _ bq HEAPX HBQ') as OFFQ.
    pose proof (munch_refl [(PIN, PIN + 8)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (OFF : offshW [(PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ.
    assert (QHI : PIN + 8 <= spa) by (clear - Q2 Q4 CEIL LOSPu SPAL; plia).
    unfold dst, OSC_FIN, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. name_mem m6.
    if_cases K0; zc K0; [| exfalso; apply K0; reflexivity]. clear K0.
    apply evt_done.
    match goal with H : munch _ mX m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs mX m6 |- _ => rename H into WM6 end.
    match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end.
    assert (LI6 : linv ΣX stX m6 OWX boX (sct_blocks adrX xr) CX).
    { kit @oinv_munch; [exact LI| exact MU6| exact WM6| exact MI6| exact STX|].   (* [comment removed for export] *)
      constructor; [| constructor]. right; left. exists (PIN, PIN + 8). split; [subst XP; cbn; tauto| cbn [fst snd]; clear; lia]. }
    assert (SR6 : sct_repA m6 (OWX ++ sct_blocks adrX xr ++ LB) adrX xr).
    { eapply sct_repA_agreeK; [apply (agree_on_of_munch_nw _ _ _ MU6)| | exact SR]. intros b a Hb Ha. cbn [outside fst snd]. split; [| exact I].
      pose proof (DJL b bq Hb ltac:(subst LB'; right; exact HBQ)) as DJ. clear - Ha DJ Q1 Q2. lia. }
    change (Z_to_bv 64 3365188) with (Z_to_bv 64 OSC_EXIT).
    eapply (osc_exitA ΣX stX m6 OWX boX (sct_blocks adrX xr) CX) with (r := Some xr) (adrX := adrX) (j16' := j16') (j24' := j24');
      [exact LI6| exact HCX| | exact ADRX|].
    - match goal with H : rw_cells ctasegs m6 spa _ |- _ => exact H end.
    - split; [reflexivity|]. split; [reflexivity|]. split; [exact SR6|]. split; [| split; [exact EV| exact WL]].
      unfold MallocRep.wz. match goal with H : rw_cells ctasegs m6 PIN [C8 _] |- _ => exact H end.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition v1_termA (pn : bptr) : AM (option (sctr bptr)) :=
    let s := set_version (CtWire.byte c p) (sct_new pn) in
      if len <? 43 then err_raise RS_sct_43 ;;; sct_free s ;;; aret None
      else
        let len := len - 43 in
        let p := p + 1 in
        lg <- amalloc CT_V1_HASHLEN ;;
        let s := set_logid (Some lg) s in
        let p := p + CT_V1_HASHLEN in
        let s := set_ts (u64be c p) s in
        let p := p + 8 in
        let len2 := u16be c p in
        let p := p + 2 in
        if len <? len2 then err_raise RS_sct_ext ;;; sct_free s ;;; aret None
        else
          s <- (if 0 <? len2 then e <- amalloc len2 ;; aret (set_ext (Some (e, len2)) len2 s) else aret (set_ext None 0 s)) ;;
          let p := p + len2 in
          let len := len - len2 in
          ' (s, r) <- o2i_sct_signature s c p len ;;
          if r <=? 0 then err_raise RS_sct_sig ;;; sct_free s ;;; aret None
          else aret (Some s).
  Definition nv1_termA (pn : bptr) : AM (option (sctr bptr)) :=
    q <- amalloc len ;; aret (Some (set_blob (Some (q, len)) (set_version (CtWire.byte c p) (sct_new pn)))).

  (* [comment removed for export] *)
  Definition ver_cells (A : Z) : list cell :=
    [C4 (Z_to_bv 64 (znth c p)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

  Lemma nv1_mainA : forall ΣX mX CX (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX (pn : bptr) (A : Z),
    linv ΣX st mX OW bo [(pn, A, SCT_SIZE)] CX -> CSTb <= CX -> znth c p <> 0 ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40] ->
    rw_cells ctasegs mX PIN [C8 (Z_to_bv 64 (D + p))] ->
    rw_cells ctasegs mX A (ver_cells A) ->
    implAp (nv1_termA pn st) ΣX SPOST
      (dst x1 x5 x6 x7 (Z_to_bv 64 (znth c p)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 (D + p))
           (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) x28 x29 x30 x31 FX fcX mX OSC_NV1).      (* [comment removed for export] *)
  Proof.
    intros until A. intros LI HCX VN FRLo HP HC. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF. cbn [app] in HEAPX.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _ & CRX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    pose proof LI as (_ & _ & _ & _ & _ & HBX & CRT & LBOK). cbn [ar_RT push amb] in CRT, CRX.
    pose proof (proj1 (proj1 (Forall_inv LBOK))) as A16. cbn [blk_addr fst snd] in A16.
    pose proof (BND (pn, A, SCT_SIZE) ltac:(apply in_or_app; right; left; reflexivity)) as (A0 & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI. unfold SCT_SIZE in AC, AI. pce AC.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    pose proof (znth_range8 c p DF) as R0.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold nv1_termA, dst, OSC_NV1, MallocRep.wz. cbn [abind apbind amalloc aret fst snd].
    apply implAp_from_evt.
    (* [comment removed for export] *)
    do 6 step. apply evt_done.
    assert (SRC : bytes_at ctasegs mX (D + p) (to_bytes (slice c p len))).
    { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
      replace (D + p) with (D + Z.of_nat (Z.to_nat p)) by (clear - P0; lia). apply bytes_at_skipn; [exact HBX|]. apply Nat2Z.inj_le. rewrite DLEN. clear - P0 PL LEN; lia. }
    assert (SLEN : length (to_bytes (slice c p len)) = Z.to_nat len) by (unfold to_bytes; rewrite length_map; apply slice_length; clear - P0 PL LEN; lia).
    pose proof (mcost_mono len len ltac:(clear - LEN; lia)) as [_ _].
    change (Z_to_bv 64 2113496) with (wz CRYPTO_MEMDUP_A).
    eapply (@CRYPTO_memdup_walkA (push AR f 0) UK BE) with (lo := lo) (OW := OW) (LB := [(pn, A, SCT_SIZE)] ++ LB') (bsrc := bd) (P := D + p) (n := len)
                                                         (src := to_bytes (slice c p len)) (ras := bv_unsigned ra :: ras);
      [exact HEAPX| rewrite ESPA; exact STX| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; clear - LOSPu SPAL; ecu; lia
      | rewrite ESPA; clear - TOP SPAH; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MIX| reflexivity| exact CSX
      | apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBD| clear - BD1 P0; lia| clear - BD2 PL; lia| exact SRC| exact SLEN
      | reflexivity| reflexivity| unfold MAX_SCT_SIZE in LEN; clear - LEN; lia
      | subst CSTb; cbn [ar_RT push amb]; clear - CRT CRX HCX MC0; ecu; lia
      | rewrite ESPA; exact UWX| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_dup135 CTX)|].
    intros q ΣQ msQ FRESHQ POQ. unfold calloc_postA in POQ. rewrite ?ESPA in POQ.
    destruct POQ as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & FQ & fcQ & mQ & C
                     & -> & MIQ & STQ & AGQ & CRQ & BRQ & HEAPQ & ACCQ' & (BLKQ & _)).
    rewrite (ret_pc_even 0x3358c4) by (clear; lia). unfold MallocRep.wz.
    pose proof BRQ as (C0 & C16 & _ & CC & CI). pce CC.
    assert (LIQ : linv ΣQ st mQ OW bo [(q, C, len); (pn, A, SCT_SIZE)] (CX - mcost len)).
    { kit @oinv_alloc; [exact LI| exact AGQ| exact HEAPQ| exact MIQ| exact STQ| exact CRQ| clear - HCX MC0; subst CSTb; ecu; lia]. }
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIQ) as (HEAPQ' & NDQ & BNDQ & FRSHQ & DJLQ & _). clear OF. cbn [app] in HEAPQ'.
    assert (NQP : q <> pn).
    { intros E0. pose proof NDQ as N. rewrite map_app in N. apply NoDup_app_split in N as (N & _ & _). cbn [map app blk_id fst snd] in N.
      apply NoDup_cons_iff in N as [N _]. apply N. left. symmetry. exact E0. }
    pose proof (@AH_disjoint_gen (push AR f 0) _ _ _ _ (q, C, len) (pn, A, SCT_SIZE) HEAPQ' ltac:(apply in_or_app; right; left; reflexivity)
                  ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(cbn [blk_id fst snd]; exact NQP)) as DJQA.
    cbn [blk_addr blk_size fst snd] in DJQA. unfold SCT_SIZE in DJQA.
    pose proof (DJLQ (pn, A, SCT_SIZE) bq ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold SCT_SIZE in DJQ.
    pose proof (DJLQ (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(right; left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJO. cbn [blk_addr blk_size fst snd] in DJO. unfold SCT_SIZE in DJO.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGQ) in FRLo; [| intros a Ha; left; cbn in Ha; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGQ) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGQ) in HC; [| intros a Ha; right; right; exists (pn, A, SCT_SIZE); split; [apply in_or_app; right; left; reflexivity| cbn in Ha |- *; unfold SCT_SIZE; clear - Ha; lia]].
    assert (HXIN : In (pn, A, SCT_SIZE) (OW ++ [(q, C, len); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; right; left; reflexivity).
    ablock HEAPQ' HXIN ACCX OFFX. unfold SCT_SIZE in ACCX, OFFX.
    clear MU WM. pose proof (munch_refl [(A + 8, A + 24)]%Z mQ) as MU. pose proof (wmono_refl ctasegs mQ) as WM.
    assert (OFF : offshW [(A + 8, A + 24)]%Z) by (cbn [offshW]; clear - OFFX; unfold SHLO, SHHI in *; lia). clear OFFX.
    frz Q5. frz BD5. frz OQ. frz OD. frz AI. frz CI. frz DJQA.
    unfold ver_cells in HC.
    apply implAp_from_evt. cbn [apbind].
    (* [comment removed for export] *)
    thaw DJQ. frz BLKQ. step.
    step. if_cases K1; zc K1; [exfalso; revert K1; rewrite ?O2iKitAR.land_ones64_small by (clear - C0 CC CN; lia); clear - C0; lia|]. clear K1.
    step.
    step. setreg 22%Z (Z_to_bv 64 (D + p + len)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL LEN; lia); bv_solve).
    name_mem m7. frz DJQ. thaw BLKQ.
    apply evt_done.
    match goal with H : munch _ mQ m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs mQ m7 |- _ => rename H into WM7 end.
    match goal with H : mem_inv ctasegs m7 |- _ => rename H into MI7 end.
    set (adr1 := fun b : bptr => if bptr_eqb b q then C else if bptr_eqb b pn then A else adr b).
    set (xr := set_blob (Some (q, len)) (set_version (CtWire.byte c p) (sct_new pn))).
    assert (Eq1 : adr1 q = C) by (subst adr1; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (Epn : adr1 pn = A) by (subst adr1; cbn beta; rewrite (bptr_eqb_neq pn q) by (intros E0; apply NQP; symmetry; exact E0); rewrite bptr_eqb_refl; reflexivity).
    assert (EB : sct_blocks adr1 xr = [(q, C, len); (pn, A, SCT_SIZE)]).
    { subst xr. unfold CtSctP.W_sct_list_free.sct_blocks. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk set_blob set_version sct_new osz32 option_map CtSctP.W_sct_list_free.oblk app]. rewrite Eq1, Epn. reflexivity. }
    assert (LI7 : linv ΣQ st m7 OW bo (sct_blocks adr1 xr) (CX - mcost len)).
    { rewrite EB. kit @oinv_munch; [exact LIQ| exact MU7| exact WM7| exact MI7| exact STQ|].
      constructor; [| constructor]. right; right. exists (pn, A, SCT_SIZE). split; [right; left; reflexivity| cbn; unfold SCT_SIZE; clear; lia]. }
    assert (ADR1 : forall b, In b LB -> adr1 (blk_id b) = adr (blk_id b)).
    { intros [[b Ab] nb] Hb. subst adr1. cbn.
      rewrite (bptr_eqb_neq b q) by (intros ->; apply (FRSHQ (q, C, len) ltac:(left; reflexivity)); rewrite map_app; apply in_app_iff; right; subst LB'; right; exact (in_map blk_id _ _ Hb)).
      rewrite (bptr_eqb_neq b pn) by (intros ->; apply (FRSHQ (pn, A, SCT_SIZE) ltac:(right; left; reflexivity)); rewrite map_app; apply in_app_iff; right; subst LB'; right; exact (in_map blk_id _ _ Hb)).
      reflexivity. }
    pose proof (CtRepP.W_get_object_walk.znth_range c p DF) as BR.
    assert (SR : sct_repA m7 (OW ++ sct_blocks adr1 xr ++ LB) adr1 xr).
    { rewrite EB. split; [change (sc_blk xr) with pn; rewrite Epn; apply in_app_iff; right; apply in_app_iff; left; right; left; reflexivity|].
      split; [change (sc_blk xr) with pn; rewrite Epn; exact A16|].
      split. { change (sc_blk xr) with pn. rewrite Epn. unfold CtSctP.SctRep.sct_cells. subst xr.
               cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_blob set_version optr osz32 option_map CtSctP.SctRep.logid_len].
               rewrite Eq1, BY, (CtSctP.SctRep.u32_small (znth c p)), (CtSctP.SctRep.u32_small 0) by (clear - BR P0 PL LEN; lia). unfold MallocRep.wz.
               match goal with H : rw_cells ctasegs m7 A _ |- _ => exact H end. }
      split; [exact I|]. split; [exact I|]. split; [exact I|].
      split. { cbn [arr_repA sc_blob xr set_blob]. rewrite Eq1. split; [clear - LEN; lia|]. split; [apply in_app_iff; right; apply in_app_iff; left; left; reflexivity|].
               eexists. eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU7)| exact BLKQ|].
               intros a Ha. cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - LEN; lia). cbn [outside fst snd]. unfold frozen in DJQA. clear - Ha DJQA. lia. }
      split. { cbn. constructor; [| constructor; [intros []| constructor]]. cbn. intros [E0|[]]. exact (NQP (eq_sym E0)). }
      subst xr. cbn [sc_version sc_hash sc_sigalg sc_ts sc_extlen sc_ext sc_sig sc_blob set_blob set_version sct_new olen sct_nid].
      rewrite BY by (clear - P0 PL LEN; lia).
      split; [right; clear - BR; lia|]. split; [intros E0; exfalso; exact (VN E0)|].
      unfold MAX_SCT_SIZE in *. repeat split; clear - LEN; lia. }
    change (Z_to_bv 64 3365116) with (Z_to_bv 64 OSC_FIN).
    rewrite ?EPIN.
    eapply (fin_okA ΣQ st m7 OW bo (CX - mcost len)) with (xr := xr) (adrX := adr1) (j16' := j16) (j24' := j24);
      [exact LI7| clear - HCX MC0 LEN; subst CSTb; ecu; lia| | exact ADR1| | exact Epn| exact SR| subst xr; reflexivity| ].
    - match goal with H : rw_cells ctasegs m7 spa _ |- _ => exact H end.
    - match goal with H : rw_cells ctasegs m7 PIN _ |- _ => exact H end.
    - subst xr. unfold i2o_sct_len. cbn [sc_version sc_bloblen sc_blob set_blob set_version sct_new]. rewrite BY by (clear - P0 PL LEN; lia).
      replace (znth c p =? 0) with false by (symmetry; apply Z.eqb_neq; exact VN). clear; lia.
  Qed.


  (* [comment removed for export] *)
  Definition v1_recA (pn lg : bptr) (ts : Z) (o : option (bptr * Z)) : sctr bptr := mkSCT pn (CtWire.byte c p) None (Some lg) ts o (olen o) 0 0 None.
  (* [comment removed for export] *)
  Definition v1_cellsA (Cl ts X : Z) : list cell :=
    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 Cl); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 ts); C8 (Z_to_bv 64 X); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
  (* [comment removed for export] *)
  Definition v1_sig_termA (x3 : sctr bptr) (el : Z) : AM (option (sctr bptr)) :=
    ' (s, r) <- o2i_sct_signature x3 c (p + 43 + el) (len - 43 - el) ;;
    (if r <=? 0 then err_raise RS_sct_sig ;;; sct_free s ;;; aret None else aret (Some s)).

  (* [comment removed for export] *)
  Lemma v1_tailA : forall ΣX mX CX (x1 x5 x6 x7 x10 x11 x13 x14 x15 x17 x28 x29 x30 x31 : word) FX fcX
      (pn lg : bptr) (A Cl ts : Z) (o : option (bptr * Z)) (adr3 : bptr -> Z) (j16' j24' bl : list (bv 8)),
    let x3 := v1_recA pn lg ts o in
    let el := olen o in
    linv ΣX st mX OW bo (sct_blocks adr3 x3) CX -> O2I_SIG_COST_A (len - 43 - el) + GETOBJ_ERR_COST_A <= CX ->
    adr3 pn = A -> adr3 lg = Cl -> (forall b, In b LB -> adr3 (blk_id b) = adr (blk_id b)) ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16'; CB 8 j24'; CB 8 j32; CB 8 j40] ->
    rw_cells ctasegs mX PIN [C8 (Z_to_bv 64 (D + p))] -> rw_cells ctasegs mX (f + 32) [C8 (Z_to_bv 64 (D + p + 36))] ->      (* [comment removed for export] *)
    rw_cells ctasegs mX A (v1_cellsA Cl ts (optr adr3 o)) ->
    rw_cells ctasegs mX Cl [CB 32 bl] ->
    match o with Some (e, n) => 0 < n /\ exists be, rw_cells ctasegs mX (adr3 e) [CB (Z.to_nat n) be] | None => True end ->
    0 <= el <= len - 43 -> 43 <= len -> znth c p = 0 -> 0 <= ts < 2 ^ 64 ->
    implAp (v1_sig_termA x3 el st) ΣX SPOST
      (dst x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (len - 43)) x13 x14 x15 (Z_to_bv 64 (f + 32)) x17 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 el) (Z_to_bv 64 (D + p + 43))
           (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) x28 x29 x30 x31 FX fcX mX 0x335c20).      (* [comment removed for export] *)
  Proof.
    intros until bl. cbv zeta. intros LI HCX E3pn E3lg ADR3 FRLo HP HJ HC HL HE EL L43 V0 TSR. bf.
    set (x3 := v1_recA pn lg ts o) in *. set (el := olen o) in *.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF. cbn [app] in HEAPX.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _ & CRX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    pose proof LI as (PREX0 & _ & KO & KI & _ & HBX & CRT & LBOK). cbn [ar_RT push amb] in CRT, CRX.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    assert (BY0 : CtWire.byte c p = 0) by (rewrite BY by (clear - P0 PL LEN; lia); exact V0).
    assert (HXIN : In (pn, A, SCT_SIZE) (sct_blocks adr3 x3)).
    { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. do 4 right. left. change (sc_blk x3) with pn. rewrite E3pn. reflexivity. }
    assert (HLIN : In (lg, Cl, 32) (sct_blocks adr3 x3)).
    { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. left. change (sc_logid x3) with (Some lg). cbn. left. rewrite E3lg. reflexivity. }
    assert (NDB : List.NoDup (map blk_id (sct_blocks adr3 x3))).
    { pose proof NDX as N. rewrite map_app in N. apply NoDup_app_split in N as (N & _ & _). rewrite map_app in N. apply NoDup_app_split in N as (_ & _ & N). exact N. }
    pose proof (BND (pn, A, SCT_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; exact HXIN)) as (A0 & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI. unfold SCT_SIZE in AC, AI. pce AC.
    pose proof (BND (lg, Cl, 32) ltac:(apply in_or_app; right; apply in_or_app; left; exact HLIN)) as (L0 & _ & LC & LW). cbn [blk_addr blk_size fst snd] in L0, LC, LW. pce LC.
    assert (A16 : A mod 16 = 0).
    { pose proof (proj1 (proj1 (proj1 (Forall_forall _ _) LBOK _ HXIN))) as X. cbn [blk_addr fst snd] in X. exact X. }
    pose proof (DJL (pn, A, SCT_SIZE) bq HXIN ltac:(subst LB'; right; exact HBQ)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold SCT_SIZE in DJQ.
    pose proof (DJL (pn, A, SCT_SIZE) bd HXIN ltac:(subst LB'; right; exact HBD)) as DJD. cbn [blk_addr blk_size fst snd] in DJD. unfold SCT_SIZE in DJD.
    pose proof (DJL (pn, A, SCT_SIZE) (qp, f + 32, 8) HXIN ltac:(subst LB'; left; reflexivity)) as DJP. cbn [blk_addr blk_size fst snd] in DJP. unfold SCT_SIZE in DJP.
    pose proof (DJL (lg, Cl, 32) (qp, f + 32, 8) HLIN ltac:(subst LB'; left; reflexivity)) as DJLP. cbn [blk_addr blk_size fst snd] in DJLP.
    assert (QP : PIN + 8 <= f + 32 \/ f + 40 <= PIN) by (unfold off_fr in OQ; change (fs_size 0) with 64 in OQ; clear - OQ Q1 Q2; lia).
    assert (DJLA : Cl + 32 <= A \/ A + 104 <= Cl).
    { eapply (@AH_disjoint_gen (push AR f 0) _ _ _ _ (lg, Cl, 32) (pn, A, SCT_SIZE) HEAPX);
        [apply in_or_app; right; apply in_or_app; left; exact HLIN| apply in_or_app; right; apply in_or_app; left; exact HXIN|].
      cbn [blk_id fst snd]. intros ->. unfold CtSctP.W_sct_list_free.sct_blocks in NDB. change (sc_logid x3) with (Some pn) in NDB.
      cbn [osz32 option_map CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in NDB.
      apply NoDup_cons_iff in NDB. destruct NDB as [NN _]. apply NN. rewrite !map_app, !in_app_iff. right. right. right. left. reflexivity. }
    assert (HPOBJ : In (qp, f + 32, 8) (OW ++ sct_blocks adr3 x3 ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; left; reflexivity).
    assert (HXIN' : In (pn, A, SCT_SIZE) (OW ++ sct_blocks adr3 x3 ++ LB')) by (apply in_or_app; right; apply in_or_app; left; exact HXIN).
    ablock HEAPX HXIN' ACCX OFFX. ablock HEAPX HPOBJ ACCP OFFP. unfold SCT_SIZE in ACCX, OFFX.
    pose proof (munch_refl [(A + 56, A + 64); (f + 32, f + 40)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (OFF : offshW [(A + 56, A + 64); (f + 32, f + 40)]%Z) by (cbn [offshW]; clear - OFFX OFFP; unfold SHLO, SHHI in *; lia). clear OFFX OFFP.
    frz Q5. frz BD5. frz OQ. frz OD. frz AI. frz LW. frz DJQ. frz DJD. frz DJLA.
    set (p' := p + 43 + el) in *. set (len' := len - 43 - el) in *.
    unfold v1_cellsA in HC. frz HL.
    unfold dst, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    thaw DJQ. thaw DJP.
    (* [comment removed for export] *)
    step.                                        (* [comment removed for export] *)
    step. setreg 23%Z (Z_to_bv 64 (D + p')) ltac:(symmetry; apply bv_eq; subst p'; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL EL L43; lia); bv_solve).
    step.                                        (* [comment removed for export] *)
    step.                                        (* [comment removed for export] *)
    frz DJQ. frz DJP. frz QP.
    setreg 22%Z (Z_to_bv 64 len') ltac:(symmetry; apply bv_eq; subst len'; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL EL L43; lia); bv_solve).
    step. step. step. step. step. name_mem m8.
    apply evt_done.
    match goal with H : munch _ mX m8 |- _ => rename H into MU8 end. match goal with H : wmono ctasegs mX m8 |- _ => rename H into WM8 end.
    match goal with H : mem_inv ctasegs m8 |- _ => rename H into MI8 end.
    assert (LI8 : linv ΣX st m8 OW bo (sct_blocks adr3 x3) CX).
    { kit @oinv_munch; [exact LI| exact MU8| exact WM8| exact MI8| exact STX|].
      constructor; [right; right; exists (pn, A, SCT_SIZE); split; [exact HXIN| cbn; unfold SCT_SIZE; clear; lia]|].
      constructor; [right; left; exists (f + 32, f + 40)%Z; split; [subst XP; left; reflexivity| cbn; clear; lia]| constructor]. }
    thaw HL. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8)) in HL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; unfold frozen in DJLA; clear - Ha DJLA DJLP; lia].
    assert (HE8 : match o with Some (e, n) => 0 < n /\ exists be, rw_cells ctasegs m8 (adr3 e) [CB (Z.to_nat n) be] | None => True end).
    { destruct o as [[e n]|]; [| exact I]. destruct HE as (Hn & be & HBE).
      assert (HEIN : In (e, adr3 e, n) (sct_blocks adr3 x3)) by (unfold CtSctP.W_sct_list_free.sct_blocks; rewrite !in_app_iff; right; left; left; reflexivity).
      pose proof (BND (e, adr3 e, n) ltac:(apply in_or_app; right; apply in_or_app; left; exact HEIN)) as (BE0 & _ & BEC & _). cbn [blk_addr blk_size fst snd] in BE0, BEC. pce BEC.
      assert (DJE : adr3 e + n <= A \/ A + 104 <= adr3 e).
      { eapply (@AH_disjoint_gen (push AR f 0) _ _ _ _ (e, adr3 e, n) (pn, A, SCT_SIZE) HEAPX);
          [apply in_or_app; right; apply in_or_app; left; exact HEIN| exact HXIN'|].
        cbn [blk_id fst snd]. intros ->. unfold CtSctP.W_sct_list_free.sct_blocks in NDB. change (sc_logid x3) with (Some lg) in NDB. change (sc_ext x3) with (Some (pn, n)) in NDB.
        cbn [osz32 option_map CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in NDB.
        apply NoDup_cons_iff in NDB. destruct NDB as [_ NDB]. apply NoDup_cons_iff in NDB. destruct NDB as [NN _]. apply NN. rewrite !map_app, !in_app_iff. right. right. left. reflexivity. }
      pose proof (DJL (e, adr3 e, n) (qp, f + 32, 8) HEIN ltac:(subst LB'; left; reflexivity)) as DJEP. cbn [blk_addr blk_size fst snd] in DJEP.
      split; [exact Hn|]. exists be. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8)); [exact HBE|].
      intros a Ha. cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - Hn; lia). cbn [outside fst snd]. clear - Ha DJE DJEP. lia. }
    clear HE.
    assert (HC8 : rw_cells ctasegs m8 (adr3 (sc_blk x3)) (sct_cells adr3 x3 (-1) 0)).
    { change (sc_blk x3) with pn. rewrite E3pn. unfold CtSctP.SctRep.sct_cells. subst x3. unfold v1_recA.
      cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen optr osz32 option_map CtSctP.SctRep.logid_len].
      rewrite E3lg, BY0. cbn [CtSctP.SctRep.u32 Z.modulo Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz, CT_V1_HASHLEN. fold el.
      match goal with H : rw_cells ctasegs m8 A _ |- _ => exact H end. }
    (* [comment removed for export] *)
    unfold v1_sig_termA.
    pose proof LI8 as (PREX & _). cbn [app] in PREX.
    pose proof (@o2i_sct_signature_walkA (push AR f 0) UK BE STRCPY) as W. unfold o2i_sct_signature_specA' in W.
    eapply implAp_abind.
    { eapply W with (LB := sct_blocks adr3 x3 ++ LB') (K := K) (adr := adr3) (x := x3) (vs := 0) (PIN := f + 32) (lo := lo) (E := E) (bo := bo) (OW := OW) (ras := bv_unsigned ra :: ras); clear W.
      - eapply ap_preA_weaken; [exact PREX| subst STKb; clear; lia| subst len'; clear - HCX CRX EL; ecu; pose proof (mcost_mono (len - 43 - el) (len - 43 - el) ltac:(lia)); lia| subst FRMb; clear; ecu; lia].
      - reflexivity.
      - rewrite ESPA. exact (proj1 (proj2 (proj2 (keepA _ _ _ _ _ _ _ LI8)))).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_sig CTX).
      - apply cons_ne.
      - exact KO.
      - exact KI.
      - kit @oinv_payload; [exact LI8| exact D0| exact D63| exact D26].
      - clear - P0 PL LEN; lia.
      - subst p'; clear - P0 EL; lia.
      - subst len'; clear - EL; lia.
      - subst p' len'; clear - PL; lia.
      - change (sc_blk x3) with pn. rewrite E3pn. apply in_or_app. left. exact HXIN.
      - change (sc_blk x3) with pn. rewrite E3pn. exact A16.
      - change (sc_blk x3) with pn. rewrite E3pn. unfold frozen in DJD. unfold SCT_SIZE. clear - DJD BD1 BD2. lia.
      - intros pb PA psz Hb H1 H2. change (sc_blk x3) with pn. intros ->.
        destruct (CtSctP.W_o2i_sig.nodup_blk_eq _ _ _ _ _ _ NDX ltac:(apply in_or_app; right; exact Hb) ltac:(apply in_or_app; right; apply in_or_app; left; exact HXIN)) as [-> ->].
        unfold frozen in DJD. unfold SCT_SIZE in H2. clear - DJD BD1 BD2 H1 H2 LEN P0 PL. lia.
      - exact HC8.
      - exact BY0.
      - reflexivity.
      - intros b Hb. apply in_or_app. left. exact Hb.
      - exact NDB.
      - exists (qp, f + 32, 8). split; [apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear; lia].
      - clear - G2. Z.div_mod_to_equations. lia.
      - unfold frozen in OD. unfold off_fr in OD. change (fs_size 0) with 64 in OD. clear - OD BD1 BD2. lia.
      - change (sc_blk x3) with pn. rewrite E3pn. unfold SCT_SIZE. unfold frozen in DJP. clear - DJP. lia.
      - unfold MallocRep.wz. match goal with H : rw_cells ctasegs m8 (f + 32) _ |- _ => exact H end.
      - change (sc_blk x3) with pn. rewrite E3pn. reflexivity.
      - reflexivity.
      - reflexivity. }
    clear W.
    (* [comment removed for export] *)
    intros r ΣS msS POS. unfold o2i_sig_postA in POS. rewrite ?ESPA in POS.
    destruct POS as (v0 & v1 & v2 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v3 & v4 & v5 & v6 & FS & fcS & mS & OWS & boS & adrS & NEWS
                     & -> & PRES & AXS & CRS & BKS & ADRS & LBOKS & HCS & Eblk & Elg & Eext & Eblob & Ever & RST).
    destruct r as [[xr res] st']. cbn [fst snd] in *.
    rewrite (ret_pc_even 0x335c58) by (clear; lia).
    change (sc_blk x3) with pn in AXS, HCS, Eblk. rewrite E3pn in AXS, HCS.
    cbn [ar_RT push amb] in CRS.
    assert (LIS : linv ΣS st' mS OWS boS (NEWS ++ sct_blocks adr3 x3) (CX - O2I_SIG_COST_A len')).
    { kit @oinv_after; [exact LI8| exact PRES| exact AXS| | exact CRS| subst len'; clear - HCX EL; ecu; pose proof (mcost_mono (len - 43 - el) (len - 43 - el) ltac:(lia)); lia| exact BKS| exact LBOKS].
      intros a Ha. cbn [rin_ivs fst snd app] in Ha. destruct Ha as [Ha|[Ha|[]]].
      - right; left. subst XP. cbn [rin_ivs fst snd]. left. clear - Ha; lia.
      - right; right. exists (pn, A, SCT_SIZE). split; [exact HXIN| cbn; unfold SCT_SIZE in *; clear - Ha; lia]. }
    (* [comment removed for export] *)
    assert (CLs : forall a, spa <= a < bv_unsigned sp -> ax_client (sct_blocks adr3 x3 ++ LB') spa ([(f + 32, f + 32 + 8); (A, A + SCT_SIZE)] ++ LIBW_A) a).
    { intros a Ha. split; [unfold LIBW_A, SCT_SIZE; cbn [rin_ivs fst snd app]; clear - Ha AC G3 CEIL CE1 LOSPu SPAL; nrm; lia| left; clear - Ha TOP; unfold USTACK_TOP in *; lia]. }
    assert (CLb : forall b a, In b (sct_blocks adr3 x3) -> (blk_addr b + blk_size b <= A \/ A + 104 <= blk_addr b) -> blk_addr b <= a < blk_addr b + blk_size b ->
                  ax_client (sct_blocks adr3 x3 ++ LB') spa ([(f + 32, f + 32 + 8); (A, A + SCT_SIZE)] ++ LIBW_A) a).
    { intros b a Hb Hd Ha. pose proof (BND b ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (B1 & B2 & B3 & B4).
      pose proof (DJL b (qp, f + 32, 8) Hb ltac:(subst LB'; left; reflexivity)) as BP. cbn [blk_addr blk_size fst snd] in BP.
      split; [unfold LIBW_A, SCT_SIZE; cbn [rin_ivs fst snd app]; clear - Ha Hd B1 B4 BP; lia|]. right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Ha]. }
    apply (rw_cells_agree _ _ _ _ _ AXS) in FRLo; [| intros a Ha; apply CLs; cbn in Ha; clear - Ha SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AXS) in HP; [| intros a Ha; cbn in Ha; split; [unfold LIBW_A, SCT_SIZE; cbn [rin_ivs fst snd app]; unfold frozen in DJQ, Q5, OQ; unfold off_fr in OQ; change (fs_size 0) with 64 in OQ; clear - Ha DJQ Q1 Q2 Q3 Q5 OQ; lia
                                                  | right; right; exists bq; split; [apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AXS) in HL; [| intros a Ha; eapply (CLb (lg, Cl, 32)); [exact HLIN| unfold frozen in DJLA; cbn; clear - DJLA; lia| cbn in Ha |- *; clear - Ha; lia]].
    assert (HE' : match o with Some (e, n) => 0 < n /\ exists be, rw_cells ctasegs mS (adrS e) [CB (Z.to_nat n) be] | None => True end).
    { destruct o as [[e n]|]; [| exact I]. destruct HE8 as (Hn & be & HBE).
      assert (HEIN : In (e, adr3 e, n) (sct_blocks adr3 x3)) by (unfold CtSctP.W_sct_list_free.sct_blocks; rewrite !in_app_iff; right; left; left; reflexivity).
      assert (DJE : adr3 e + n <= A \/ A + 104 <= adr3 e).
      { eapply (@AH_disjoint_gen (push AR f 0) _ _ _ _ (e, adr3 e, n) (pn, A, SCT_SIZE) HEAPX);
          [apply in_or_app; right; apply in_or_app; left; exact HEIN| exact HXIN'|].
        cbn [blk_id fst snd]. intros ->. unfold CtSctP.W_sct_list_free.sct_blocks in NDB. change (sc_logid x3) with (Some lg) in NDB. change (sc_ext x3) with (Some (pn, n)) in NDB.
        cbn [osz32 option_map CtSctP.W_sct_list_free.oblk map blk_id fst snd app] in NDB.
        apply NoDup_cons_iff in NDB. destruct NDB as [_ NDB]. apply NoDup_cons_iff in NDB. destruct NDB as [NN _]. apply NN. rewrite !map_app, !in_app_iff. right. right. left. reflexivity. }
      split; [exact Hn|]. exists be. rewrite (ADRS (e, adr3 e, n)) by (apply in_or_app; left; exact HEIN). cbn [blk_id fst snd].
      apply (rw_cells_agree _ _ _ _ _ AXS); [exact HBE|]. intros a Ha. eapply (CLb (e, adr3 e, n)); [exact HEIN| cbn; exact DJE| cbn in Ha |- *; rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - Hn; lia); clear - Ha; lia]. }
    clear HE8 CLs CLb.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIS) as (_ & STS & _ & _ & _ & _ & MIS & _). clear OC.
    clear MU8 WM8. pose proof (munch_refl (@nil (Z * Z)) mS) as MU. pose proof (wmono_refl ctasegs mS) as WM.
    assert (ElgS : adrS lg = Cl) by (rewrite (ADRS (lg, Cl, 32)) by (apply in_or_app; left; exact HLIN); exact E3lg).
    assert (EpnS : adrS pn = A) by (rewrite (ADRS (pn, A, SCT_SIZE)) by (apply in_or_app; left; exact HXIN); exact E3pn).
    assert (ADRS' : forall b, In b LB -> adrS (blk_id b) = adr (blk_id b)).
    { intros b Hb. rewrite (ADRS b) by (apply in_or_app; right; subst LB'; right; exact Hb). apply ADR3. exact Hb. }
    assert (SGN : 0 <= sc_siglen xr).
    { destruct (res <=? 0); [destruct RST as (_ & _ & SG & _); unfold sc_siglen; rewrite SG; clear; lia|].
      destruct RST as (_ & _ & _ & _ & _ & _ & _ & _ & SG). unfold sc_siglen. destruct (sc_sig xr) as [[q n]|]; clear - SG; lia. }
    assert (EO : oblk adrS o = oblk adr3 o).
    { destruct o as [[e n]|]; [| reflexivity]. cbn. rewrite (ADRS (e, adr3 e, n)) by (apply in_or_app; left; unfold CtSctP.W_sct_list_free.sct_blocks; rewrite !in_app_iff; right; left; left; reflexivity). reflexivity. }
    assert (EB3 : sct_blocks adr3 x3 = [(lg, Cl, 32)] ++ oblk adr3 o ++ [(pn, A, SCT_SIZE)]).
    { unfold CtSctP.W_sct_list_free.sct_blocks. change (sc_logid x3) with (Some lg). change (sc_ext x3) with o. change (sc_blob x3) with (@None (bptr * Z)). change (sc_sig x3) with (@None (bptr * Z)). change (sc_blk x3) with pn.
      cbn [osz32 option_map CtSctP.W_sct_list_free.oblk app]. rewrite E3lg, E3pn. reflexivity. }
    cbv beta. apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases KR; zc KR.
    - (* [comment removed for export] *)
      destruct (res <=? 0) eqn:ER.
      2:{ exfalso. apply Z.leb_gt in ER. destruct RST as (Eres & Hle & _). rewrite O2iKitAR.land_ones64_small in KR by (clear - ER Eres Hle SGN EL L43 LEN; unfold MAX_SCT_SIZE in *; lia).
          apply Bool.andb_false_iff in KR. destruct KR as [KR|KR]; apply Z.ltb_ge in KR; clear - KR ER Eres Hle SGN EL L43 LEN; unfold MAX_SCT_SIZE in *; lia. }
      destruct RST as (Eres & ENS & SIGN & HPl). subst res NEWS. cbn [app] in LIS.
      assert (EBS : sct_blocks adrS xr = sct_blocks adr3 x3).
      { rewrite EB3. unfold CtSctP.W_sct_list_free.sct_blocks. rewrite Elg, Eext, Eblob, SIGN, Eblk. change (sc_logid x3) with (Some lg). change (sc_ext x3) with o. change (sc_blob x3) with (@None (bptr * Z)).
        cbn [osz32 option_map CtSctP.W_sct_list_free.oblk app]. rewrite ElgS, EpnS, EO. reflexivity. }
      rewrite <- EBS in LIS.
      apply evt_done.      (* [comment removed for export] *)
      eapply (raise_err128A ΣS st' mS OWS boS (CX - O2I_SIG_COST_A len')) with (adrX := adrS) (vs := 0);
        [exact LIS| subst len'; clear - HCX; ecu; lia| exact FRLo| exact ADRS'| unfold MallocRep.wz; exact HP| rewrite Eblk; exact EpnS| cbn [Z.leb] in HCS; exact HCS].
    - (* [comment removed for export] *)
      destruct (res <=? 0) eqn:ER.
      { exfalso. apply Z.leb_le in ER. destruct RST as (Eres & _). subst res. revert KR1. change (Z.land (-1) 18446744073709551615) with 18446744073709551615. clear; lia. }
      clear KR0 KR1.
      apply Z.leb_gt in ER. destruct RST as (Eres & Hle & HPl & Ets & Eel & Hh & Ha & Hnid & SG).
      unfold MallocRep.wz in HPl.
      (* [comment removed for export] *)
      step. step. step. setreg 22%Z (Z_to_bv 64 (D + p + len)) ltac:(symmetry; apply bv_eq; subst p' len'; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL EL L43 Eres Hle SGN LEN; unfold MAX_SCT_SIZE in *; lia); bv_solve).
      step.        (* [comment removed for export] *)
      apply evt_done.
      (* [comment removed for export] *)
      assert (EBS : sct_blocks adrS xr = [(lg, Cl, 32)] ++ oblk adrS o ++ NEWS ++ [(pn, A, SCT_SIZE)]).
      { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite Elg, Eext, Eblob, Eblk. change (sc_logid x3) with (Some lg). change (sc_ext x3) with o. change (sc_blob x3) with (@None (bptr * Z)).
        cbn [osz32 option_map CtSctP.W_sct_list_free.oblk app]. rewrite ElgS, EpnS. destruct (sc_sig xr) as [[gq gn]|]; [destruct SG as (-> & _)| rewrite SG]; reflexivity. }
      assert (LIF : linv ΣS st' mS OWS boS (sct_blocks adrS xr) (CX - O2I_SIG_COST_A len')).
      { kit @oinv_perm; [| exact LIS]. rewrite EBS, EB3, EO.
        pose proof (Permutation_app_swap_app NEWS ([(lg, Cl, 32)] ++ oblk adr3 o) [(pn, A, SCT_SIZE)]) as PM. rewrite <- !app_assoc in PM. exact PM. }
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIF) as (_ & NDF & _ & FRESHF & _). clear OF.
      assert (SR : sct_repA mS (OWS ++ sct_blocks adrS xr ++ LB) adrS xr).
      { split. { rewrite Eblk, EpnS. apply in_app_iff. right. apply in_app_iff. left. rewrite EBS. rewrite !in_app_iff. right. right. right. left. reflexivity. }
        split; [rewrite Eblk, EpnS; exact A16|].
        split; [rewrite Eblk, EpnS; replace (if res <=? 0 then 0 else 0) with 0 in HCS by (destruct (res <=? 0); reflexivity); exact HCS|].
        split. { rewrite Elg. change (sc_logid x3) with (Some lg). cbn. rewrite ElgS. split; [clear; lia|]. split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EBS; left; reflexivity|]. eexists. exact HL. }
        split. { rewrite Eext. change (sc_ext x3) with o. destruct o as [[e n]|]; [| exact I]. cbn. destruct HE' as (Hn & be & HBE). split; [exact Hn|].
                 split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EBS; rewrite !in_app_iff; right; left; left; reflexivity|]. exists be. exact HBE. }
        split. { destruct (sc_sig xr) as [[gq gn]|]; [| exact I]. destruct SG as (ENS & Hgn & _ & HG). cbn. split; [exact Hgn|].
                 split; [apply in_app_iff; right; apply in_app_iff; left; rewrite EBS, ENS; rewrite !in_app_iff; right; right; left; left; reflexivity|]. eexists. exact HG. }
        split; [rewrite Eblob; exact I|].
        split. { rewrite (map_app blk_id OWS), (map_app blk_id (sct_blocks adrS xr) LB') in NDF.
                 destruct (NoDup_app_split _ _ NDF) as (N23 & _ & _). destruct (NoDup_app_split _ _ N23) as (_ & _ & N2). exact N2. }
        rewrite Ever, Ets, Eel, Eext, CtSctP.SctRep.sc_siglen_olen || rewrite Ever, Ets, Eel, Eext. change (sc_version x3) with (CtWire.byte c p). change (sc_ts x3) with ts. change (sc_extlen x3) with (olen o). change (sc_ext x3) with o.
        rewrite BY0. split; [right; clear; lia|]. split; [intros _; exact Hnid|]. split; [exact Hh|]. split; [exact Ha|]. split; [exact TSR|]. split; [reflexivity|].
        rewrite <- CtSctP.SctRep.sc_siglen_olen, Eblob. change (sc_blob x3) with (@None (bptr * Z)). cbn [olen]. fold el. unfold MAX_SCT_SIZE in *. clear - EL L43 LEN Eres Hle SGN. repeat split; lia. }
      change (Z_to_bv 64 3365116) with (Z_to_bv 64 OSC_FIN). rewrite ?EPIN.
      eapply (fin_okA ΣS st' mS OWS boS (CX - O2I_SIG_COST_A len')) with (xr := xr) (adrX := adrS) (j16' := j16') (j24' := j24');
        [exact LIF| subst len'; clear - HCX; ecu; lia| exact FRLo| exact ADRS'| unfold MallocRep.wz; exact HP| rewrite Eblk; exact EpnS| exact SR| rewrite Ever; reflexivity|].
      unfold i2o_sct_len. rewrite Ever. change (sc_version x3) with (CtWire.byte c p). rewrite BY0. cbn [Z.eqb]. rewrite Eel. change (sc_extlen x3) with el.
      try subst p'. try subst len'. clear - Eres Hle EL. lia.
  Qed.

  (* [comment removed for export] *)
  Definition v1_ts_termA (pn lg : bptr) : AM (option (sctr bptr)) :=
    let s := set_logid (Some lg) (set_version (CtWire.byte c p) (sct_new pn)) in
    let s := set_ts (u64be c (p + 33)) s in
    let len2 := u16be c (p + 41) in
    if len - 43 <? len2 then err_raise RS_sct_ext ;;; sct_free s ;;; aret None
    else
      s <- (if 0 <? len2 then e <- amalloc len2 ;; aret (set_ext (Some (e, len2)) len2 s) else aret (set_ext None 0 s)) ;;
      v1_sig_termA s len2.
  (* [comment removed for export] *)
  Definition logid_cellsA (Cl : Z) : list cell :=
    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 Cl); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rstepB := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
  Ltac pshload1 ACC :=
    let ad := BnTac.cur_mem_addr in let X := ab_X ad in
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch type of ACC with acc _ ?mb ?a ?n =>
        match goal with MU : munch ?W mb mc |- _ =>
          let RD := fresh "RDsh" in let b := fresh "shb_" in let OK := fresh "ABok" in
          destruct (acc_rdS segs W mb mc a n X 1 ad ACC MU ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(clear; lia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr))
            as (b & RD & OK);
          rstepB; clear RD
        end end end.
  Ltac rshload8 ACC :=
    let ad := BnTac.cur_mem_addr in let X := ab_X ad in
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch type of ACC with acc _ ?mb ?a ?n =>
        match goal with MU : munch ?W mb mc |- _ =>
          let RD := fresh "RDsh" in
          pose proof (acc_rdG segs W mb mc a n X ad ACC MU ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr)) as RD;
          rstepB; clear RD
        end end end.
  Ltac rbranch := rstepB; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true].
  Ltac pchk1 t u J := first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end | rbranch ].

  (* [comment removed for export] *)
  Lemma v1_extA : forall ΣX mX CX (x1 x5 x6 x7 x14 x15 x17 x28 x29 x30 x31 : word) FX fcX (pn lg : bptr) (A Cl ts : Z) (bl : list (bv 8)),
    linv ΣX st mX OW bo [(lg, Cl, 32); (pn, A, SCT_SIZE)] CX -> CSTb <= CX -> znth c p = 0 -> 43 <= len -> lg <> pn ->
    ts = u64be c (p + 33) -> 0 <= ts < 2 ^ 64 ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40] ->
    rw_cells ctasegs mX PIN [C8 (Z_to_bv 64 (D + p))] -> rw_cells ctasegs mX (f + 32) [C8 (Z_to_bv 64 (D + p + 36))] ->
    rw_cells ctasegs mX A (v1_cellsA Cl ts 0) -> rw_cells ctasegs mX Cl [CB 32 bl] ->
    implAp (v1_ts_termA pn lg st) ΣX SPOST
      (dst x1 x5 x6 x7 (Z_to_bv 64 (A + 40)) (Z_to_bv 64 (D + p + 41)) (Z_to_bv 64 ts) (Z_to_bv 64 (Z.shiftr (D + p + 41) 3)) x14 x15 (Z_to_bv 64 (f + 32)) x17
           (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 (D + p)) (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) x28 x29 x30 x31 FX fcX mX 0x335b90).
  Proof.
    intros until bl. intros LI HCX V0 L43 NLP ETS TSR FRLo HP HJ HC HL. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF. cbn [app] in HEAPX.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _ & CRX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    pose proof LI as (_ & _ & _ & _ & _ & HBX & CRT & LBOK). cbn [ar_RT push amb] in CRT, CRX.
    assert (A16 : A mod 16 = 0) by (pose proof (proj1 (proj1 (Forall_inv (Forall_inv_tail LBOK)))) as X; cbn [blk_addr fst snd] in X; exact X).
    pose proof (BND (pn, A, SCT_SIZE) ltac:(apply in_or_app; right; right; left; reflexivity)) as (A0 & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI. unfold SCT_SIZE in AC, AI. pce AC.
    pose proof (BND (lg, Cl, 32) ltac:(apply in_or_app; right; left; reflexivity)) as (L0 & _ & LC & LW). cbn [blk_addr blk_size fst snd] in L0, LC, LW. pce LC.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    assert (BY0 : CtWire.byte c p = 0) by (rewrite BY by (clear - P0 PL LEN; lia); exact V0).
    pose proof (@AH_disjoint_gen (push AR f 0) _ _ _ _ (lg, Cl, 32) (pn, A, SCT_SIZE) HEAPX ltac:(apply in_or_app; right; left; reflexivity)
                  ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(cbn [blk_id fst snd]; exact NLP)) as DJLA.
    cbn [blk_addr blk_size fst snd] in DJLA. unfold SCT_SIZE in DJLA.
    pose proof (DJL (pn, A, SCT_SIZE) bq ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold SCT_SIZE in DJQ.
    pose proof (DJL (pn, A, SCT_SIZE) bd ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact HBD)) as DJD. cbn [blk_addr blk_size fst snd] in DJD. unfold SCT_SIZE in DJD.
    pose proof (DJL (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(right; left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJP. cbn [blk_addr blk_size fst snd] in DJP. unfold SCT_SIZE in DJP.
    pose proof (DJL (lg, Cl, 32) (qp, f + 32, 8) ltac:(left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJLP. cbn [blk_addr blk_size fst snd] in DJLP.
    pose proof (DJL (lg, Cl, 32) bd ltac:(left; reflexivity) ltac:(subst LB'; right; exact HBD)) as DJLD. cbn [blk_addr blk_size fst snd] in DJLD.
    assert (QP : PIN + 8 <= f + 32 \/ f + 40 <= PIN) by (unfold off_fr in OQ; change (fs_size 0) with 64 in OQ; clear - OQ Q1 Q2; lia).
    assert (DPo : D + zlength c <= f + 32 \/ f + 40 <= D) by (unfold off_fr in OD; change (fs_size 0) with 64 in OD; clear - OD BD1 BD2; lia).
    set (len2 := u16be c (p + 41)) in *. pose proof (u16be_range c (p + 41)) as L2R. fold len2 in L2R.
    pose proof (znth_range8 c (p + 41) DF) as R41. pose proof (znth_range8 c (p + 42) DF) as R42.
    (* [comment removed for export] *)
    set (x2 := set_ts ts (set_logid (Some lg) (set_version (CtWire.byte c p) (sct_new pn)))).
    set (adr2 := fun b : bptr => if bptr_eqb b lg then Cl else if bptr_eqb b pn then A else adr b).
    assert (E2lg : adr2 lg = Cl) by (subst adr2; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (E2pn : adr2 pn = A) by (subst adr2; cbn beta; rewrite (bptr_eqb_neq pn lg) by (intros E0; apply NLP; symmetry; exact E0); rewrite bptr_eqb_refl; reflexivity).
    assert (ADR2 : forall b, In b LB -> adr2 (blk_id b) = adr (blk_id b)).
    { intros [[b Ab] nb] Hb. subst adr2. cbn.
      rewrite (bptr_eqb_neq b lg) by (intros ->; apply (FRSH (lg, Cl, 32) ltac:(left; reflexivity)); rewrite map_app; apply in_app_iff; right; subst LB'; right; exact (in_map blk_id _ _ Hb)).
      rewrite (bptr_eqb_neq b pn) by (intros ->; apply (FRSH (pn, A, SCT_SIZE) ltac:(right; left; reflexivity)); rewrite map_app; apply in_app_iff; right; subst LB'; right; exact (in_map blk_id _ _ Hb)).
      reflexivity. }
    assert (EB2 : sct_blocks adr2 x2 = [(lg, Cl, 32); (pn, A, SCT_SIZE)]).
    { subst x2 adr2. unfold CtSctP.W_sct_list_free.sct_blocks. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk set_ts set_logid set_version sct_new osz32 option_map CtSctP.W_sct_list_free.oblk app].
      rewrite bptr_eqb_refl. rewrite (bptr_eqb_neq pn lg) by (intros E0; apply NLP; symmetry; exact E0). rewrite bptr_eqb_refl. reflexivity. }
    assert (HBQ' : In bq (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ).
    assert (HBD' : In bd (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBD).
    assert (HPOBJ : In (qp, f + 32, 8) (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; left; reflexivity).
    ablock HEAPX HPOBJ ACCP OFFP. ablock HEAPX HBD' ACCD OFFD.     (* [comment removed for export] *)
    pose proof (munch_refl [(f + 32, f + 40)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (OFF : offshW [(f + 32, f + 40)]%Z) by (cbn [offshW]; clear - OFFP; unfold SHLO, SHHI in *; lia). clear OFFD OFFP ACCP.
    frz Q5. frz BD5. frz OQ. frz OD. frz AI. frz LW. frz DJLA. frz HL. frz DJQ. frz QP. frz DJD. frz DJP. frz DJLP. frz DJLD. frz DPo. frz G5. frz PIND.
    unfold v1_cellsA in HC. unfold dst, MallocRep.wz. apply implAp_from_evt. ual.
    (* [comment removed for export] *)
    OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. ab_shload 1.
    first [ lazymatch goal with H : absh_ok ?b _ _ |- _ => ab_join 10%Z 12%Z 0x335b9c%Z H end
          | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false ].
    (* [comment removed for export] *)
    OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. ab_shload 1.
    pose proof (payload_readA _ D c (p + 41) (wa (D + p + 41)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. clear RD.
    rewrite (zxb_lit (znth c (p + 41))) by (clear - R41; lia).
    first [ lazymatch goal with H : absh_ok ?b _ _ |- _ => ab_join 12%Z 13%Z 0x335bb4%Z H end
          | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false ].
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 42) (wa (D + p + 42)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth c (p + 42))) by (clear - R42; lia).
    step. setreg 12%Z (Z_to_bv 64 (len - 43)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - LEN L43; unfold MAX_SCT_SIZE in LEN; lia); bv_solve).
    step. step.
    setreg 22%Z (Z_to_bv 64 len2)
      ltac:(subst len2; unfold u16be; rewrite !BY by (clear - P0 PL L43; lia); replace (p + 41 + 1) with (p + 42) by (clear; lia); f_equal;
            rewrite (unsigned_lit (znth c (p + 41))), (unsigned_lit (znth c (p + 42))) by (clear - R41 R42; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c (p + 41) * 256)) by (clear - R41; lia); symmetry; apply CtSctP.W_o2i_sig.lor_shl8; clear - R41 R42; lia).
    (* [comment removed for export] *)
    pose proof LI as LI1.
    assert (HC2 : rw_cells ctasegs mX A (sct_cells adr2 x2 (-1) 0)).
    { subst x2. unfold CtSctP.SctRep.sct_cells.
      cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_version set_logid set_ts optr osz32 option_map CtSctP.SctRep.logid_len].
      rewrite E2lg, BY0. cbn [CtSctP.SctRep.u32 Z.modulo Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz, CT_V1_HASHLEN. exact HC. }
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI1) as (HEAPX1 & _). clear OF. cbn [app] in HEAPX1.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI1) as (_ & ST1 & _ & _ & _ & _ & _ & CSX1 & _ & CRX1 & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI1) as (_ & _ & UWX1 & _).
    pose proof LI1 as (_ & _ & _ & _ & _ & HB1 & _). cbn [ar_RT push amb] in CRX1.
    (* [comment removed for export] *)
    step. if_cases KE; zc KE.
    2:{ (* [comment removed for export] *)
        apply evt_done.
        unfold v1_ts_termA. cbv zeta. rewrite <- ETS. fold len2. fold x2.
        replace (len - 43 <? len2) with true by (symmetry; apply Z.ltb_lt; revert KE; rewrite ?unsigned_lit by (clear - LEN L43 L2R; unfold MAX_SCT_SIZE in LEN; lia); clear; lia).
        eapply (raise_err114A ΣX st mX OW bo CX) with (adrX := adr2) (vs := 0);
          [rewrite EB2; exact LI1| clear - HCX MC0; subst CSTb; ecu; lia| exact FRLo| exact ADR2| unfold MallocRep.wz; exact HP| exact E2pn| exact HC2]. }
    (* [comment removed for export] *)
    assert (LE2 : len2 <= len - 43) by (revert KE; rewrite ?unsigned_lit by (clear - LEN L43 L2R; unfold MAX_SCT_SIZE in LEN; lia); clear; lia). clear KE.
    step. setreg 23%Z (Z_to_bv 64 (D + p + 43)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL L43; lia); bv_solve).
    step. if_cases KZ; zc KZ.
    - (* [comment removed for export] *)
      apply evt_done.
      unfold v1_ts_termA. cbv zeta. rewrite <- ETS. fold len2. fold x2.
      replace (len - 43 <? len2) with false by (symmetry; apply Z.ltb_ge; clear - LE2; lia).
      replace (0 <? len2) with false by (symmetry; apply Z.ltb_ge; clear - KZ; lia).
      cbn [abind apbind aret fst snd].
      assert (EL0 : len2 = 0) by (clear - KZ L2R; lia). rewrite EL0.
      eapply (v1_tailA ΣX mX CX) with (o := None) (adr3 := adr2) (lg := lg) (pn := pn) (A := A) (Cl := Cl) (ts := ts) (bl := bl);
        [rewrite EB2; exact LI1| cbn [olen]; clear - HCX MC0 L43; subst CSTb; ecu; pose proof (mcost_mono (len - 43 - 0) len ltac:(lia)); lia
        | exact E2pn| exact E2lg| exact ADR2| exact FRLo| exact HP| exact HJ| cbn [optr]; unfold v1_cellsA; exact HC| thaw HL; exact HL| exact I| cbn [olen]; clear - L43; lia| exact L43| exact V0| exact TSR].
    - (* [comment removed for export] *)
      assert (L2P : 0 < len2) by (revert KZ; rewrite ?unsigned_lit by (clear - L2R; lia); clear - L2R; lia). clear KZ HC2.
      clear MU WM. pose proof (munch_refl [(spa + 16, spa + 32)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
      do 8 step. name_mem m3'. apply evt_done.
      match goal with H : munch _ mX m3' |- _ => rename H into MU3 end. match goal with H : wmono ctasegs mX m3' |- _ => rename H into WM3 end.
      match goal with H : mem_inv ctasegs m3' |- _ => rename H into MI3X end.
      unfold v1_ts_termA. cbv zeta. rewrite <- ETS. fold len2. fold x2.
      replace (len - 43 <? len2) with false by (symmetry; apply Z.ltb_ge; clear - LE2; lia).
      replace (0 <? len2) with true by (symmetry; apply Z.ltb_lt; exact L2P).
      cbn [abind apbind amalloc aret fst snd].
      assert (LI3 : linv ΣX st m3' OW bo [(lg, Cl, 32); (pn, A, SCT_SIZE)] CX).
      { kit @oinv_munch; [exact LI1| exact MU3| exact WM3| exact MI3X| exact ST1|].
        constructor; [left; cbn [fst snd]; rewrite ESPK; clear - LOSPu SPAL SPAH; lia| constructor]. }
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI3) as (HEAP3X & _). clear OF. cbn [app] in HEAP3X.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI3) as (_ & ST3X & _ & _ & _ & _ & _ & CS3X & _ & CR3X & _). clear OC.
      pose proof (keepA _ _ _ _ _ _ _ LI3) as (_ & _ & UW3X & _).
      pose proof LI3 as (_ & _ & _ & _ & _ & HB3 & _). cbn [ar_RT push amb] in CR3X.
      thaw HL. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in HL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; clear - Ha LC CEIL LOSPu SPAL; nrm; lia].
      assert (SRC : bytes_at ctasegs m3' (D + p + 43) (to_bytes (slice c (p + 43) len2))).
      { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
        replace (D + p + 43) with (D + Z.of_nat (Z.to_nat (p + 43))) by (clear - P0; lia). apply bytes_at_skipn; [exact HB3|]. apply Nat2Z.inj_le. rewrite DLEN. clear - P0 PL L43; lia. }
      assert (SLEN : length (to_bytes (slice c (p + 43) len2)) = Z.to_nat len2) by (unfold to_bytes; rewrite length_map; apply slice_length; clear - P0 PL L43 LE2 L2P; lia).
      change (Z_to_bv 64 2113496) with (wz CRYPTO_MEMDUP_A).
      eapply (@CRYPTO_memdup_walkA (push AR f 0) UK BE) with (lo := lo) (OW := OW) (LB := [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB') (bsrc := bd) (P := D + p + 43) (n := len2)
                                                           (src := to_bytes (slice c (p + 43) len2)) (ras := bv_unsigned ra :: ras);
        [exact HEAP3X| rewrite ESPA; exact ST3X| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; clear - LOSPu SPAL; ecu; lia
        | rewrite ESPA; clear - TOP SPAH; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MI3X| reflexivity| exact CS3X
        | apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBD| clear - BD1 P0; lia| clear - BD2 PL LE2; lia| exact SRC| exact SLEN
        | apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL L43; lia); bv_solve| reflexivity| clear - L2P L2R; lia
        | cbn [ar_RT push amb]; clear - CR3X HCX L2P LE2 L43 LEN MC0; subst CSTb; ecu; pose proof (mcost_mono len2 len ltac:(lia)); lia
        | rewrite ESPA; exact UW3X| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_dup118 CTX)|].
      intros e ΣE msE FRESHE POE. unfold calloc_postA in POE. rewrite ?ESPA in POE.
      destruct POE as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FE & fcE & mE & Ce
                       & -> & MIE & STE & AGE & CRE & BRE & HEAPE & ACCE' & (BLKE & _)).
      rewrite (ret_pc_even 0x335bfc) by (clear; lia). unfold MallocRep.wz.
      cbn [apbind fst snd].
      lazymatch goal with |- implAp ?t ?Σq ?Q ?ms => change (implAp (v1_sig_termA (v1_recA pn lg ts (Some (e, len2))) len2 st) Σq Q ms) end.
      pose proof BRE as (CE0 & CE16 & _ & CEC & CEW). pce CEC.
      assert (LIE : linv ΣE st mE OW bo [(e, Ce, len2); (lg, Cl, 32); (pn, A, SCT_SIZE)] (CX - mcost len2)).
      { kit @oinv_alloc; [exact LI3| exact AGE| exact HEAPE| exact MIE| exact STE| exact CRE| clear - HCX MC0 L2P LE2 L43 LEN; subst CSTb; ecu; pose proof (mcost_mono len2 len ltac:(lia)); lia]. }
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIE) as (HEAPE' & NDE' & BNDE & FRSHE & DJLE & _). clear OF. cbn [app] in HEAPE'.
      assert (NEP : e <> pn).
      { intros E1. pose proof NDE' as N. rewrite map_app in N. apply NoDup_app_split in N as (N & _ & _). cbn [map app blk_id fst snd] in N.
        apply NoDup_cons_iff in N as [N _]. apply N. right. left. symmetry. exact E1. }
      assert (NEL : e <> lg).
      { intros E1. pose proof NDE' as N. rewrite map_app in N. apply NoDup_app_split in N as (N & _ & _). cbn [map app blk_id fst snd] in N.
        apply NoDup_cons_iff in N as [N _]. apply N. left. symmetry. exact E1. }
      set (adr3 := fun b : bptr => if bptr_eqb b e then Ce else adr2 b).
      assert (E3e : adr3 e = Ce) by (subst adr3; cbn beta; rewrite bptr_eqb_refl; reflexivity).
      assert (E3pn : adr3 pn = A) by (subst adr3; cbn beta; rewrite (bptr_eqb_neq pn e) by (intros E0; apply NEP; symmetry; exact E0); exact E2pn).
      assert (E3lg : adr3 lg = Cl) by (subst adr3; cbn beta; rewrite (bptr_eqb_neq lg e) by (intros E0; apply NEL; symmetry; exact E0); exact E2lg).
      assert (ADR3 : forall b, In b LB -> adr3 (blk_id b) = adr (blk_id b)).
      { intros b Hb. subst adr3. cbn beta. rewrite (bptr_eqb_neq (blk_id b) e); [apply ADR2; exact Hb|].
        destruct b as [[b' Ab] nb]. cbn. intros ->. apply (FRSHE (e, Ce, len2) ltac:(left; reflexivity)). rewrite map_app. apply in_app_iff. right. subst LB'. right. exact (in_map blk_id _ _ Hb). }
      assert (EB3 : sct_blocks adr3 (v1_recA pn lg ts (Some (e, len2))) = [(lg, Cl, 32); (e, Ce, len2); (pn, A, SCT_SIZE)]).
      { unfold CtSctP.W_sct_list_free.sct_blocks, v1_recA. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk osz32 option_map CtSctP.W_sct_list_free.oblk app]. rewrite E3lg, E3e, E3pn. reflexivity. }
      pose proof (DJLE (pn, A, SCT_SIZE) bq ltac:(right; right; left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ'. cbn [blk_addr blk_size fst snd] in DJQ'. unfold SCT_SIZE in DJQ'.
      pose proof (DJLE (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(right; right; left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJP'. cbn [blk_addr blk_size fst snd] in DJP'. unfold SCT_SIZE in DJP'.
      pose proof (@AH_disjoint_gen (push AR f 0) _ _ _ _ (e, Ce, len2) (pn, A, SCT_SIZE) HEAPE' ltac:(apply in_or_app; right; left; reflexivity)
                    ltac:(apply in_or_app; right; right; right; left; reflexivity) ltac:(cbn [blk_id fst snd]; exact NEP)) as DJEA.
      cbn [blk_addr blk_size fst snd] in DJEA. unfold SCT_SIZE in DJEA.
      (* [comment removed for export] *)
      apply (rw_cells_agree _ _ _ _ _ AGE) in FRLo; [| intros a Ha; left; cbn in Ha; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HJ; [| intros a Ha; cbn in Ha; right; right; exists (qp, f + 32, 8); split; [apply in_or_app; right; apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HC; [| intros a Ha; right; right; exists (pn, A, SCT_SIZE); split; [apply in_or_app; right; right; left; reflexivity| cbn in Ha |- *; unfold SCT_SIZE; clear - Ha; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HL; [| intros a Ha; right; right; exists (lg, Cl, 32); split; [apply in_or_app; right; left; reflexivity| cbn in Ha |- *; clear - Ha; lia]].
      assert (HXIN' : In (pn, A, SCT_SIZE) (OW ++ [(e, Ce, len2); (lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; right; right; left; reflexivity).
      ablock HEAPE' HXIN' ACCX' OFFX'. unfold SCT_SIZE in ACCX', OFFX'.
      clear MU3 WM3. pose proof (munch_refl [(A + 48, A + 56)]%Z mE) as MU. pose proof (wmono_refl ctasegs mE) as WM.
      assert (OFF' : offshW [(A + 48, A + 56)]%Z) by (cbn [offshW]; clear - OFFX'; unfold SHLO, SHHI in *; lia). clear OFFX'.
      kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LIE) as (_ & STE' & _ & _ & _ & _ & MIE' & _). clear OC.
      frz BLKE. frz DJEA. frz HL.
      apply implAp_from_evt.
      (* [comment removed for export] *)
      thaw DJQ'. thaw DJP'. step. name_mem m5. frz DJQ'. frz DJP'.
      step. step.
      step. if_cases K1; zc K1; [exfalso; revert K1; rewrite ?O2iKitAR.land_ones64_small by (clear - CE0 CEC CN; lia); clear - CE0; lia|]. clear K1.
      apply evt_done.
      assert (LI5 : linv ΣE st m5 OW bo (sct_blocks adr3 (v1_recA pn lg ts (Some (e, len2)))) (CX - mcost len2)).
      { rewrite EB3. kit @oinv_perm; [apply perm_swap|].
        kit @oinv_munch; [exact LIE| exact MU| exact WM| exact MIE'| exact STE'|].
        constructor; [| constructor]. right; right. exists (pn, A, SCT_SIZE). split; [right; right; left; reflexivity| cbn; unfold SCT_SIZE; clear; lia]. }
      thaw BLKE. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in BLKE; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat.add_0_r in Ha; rewrite Z2Nat.id in Ha by (clear - L2P; lia); cbn [outside fst snd]; unfold frozen in DJEA; clear - Ha DJEA; lia].
      thaw HL. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; unfold frozen in DJLA; clear - Ha DJLA; lia].
      pose proof (rw_cells_cb_first _ _ _ 4 FRLo) as FRLo'. cbn [cb_first csize cbytes app] in FRLo'.
      replace (C8 (Z_to_bv 64 Ce)) with (C8 (Z_to_bv 64 (optr adr3 (Some (e, len2))))) in HC by (cbn [optr]; rewrite E3e; reflexivity).
      eapply (v1_tailA ΣE m5 (CX - mcost len2)) with (o := Some (e, len2)) (adr3 := adr3) (lg := lg) (pn := pn) (A := A) (Cl := Cl) (ts := ts) (bl := bl);
        [exact LI5| cbn [olen]; clear - HCX MC0 L43 L2P LE2 LEN; subst CSTb; ecu; pose proof (mcost_mono (len - 43 - len2) len ltac:(lia)); pose proof (mcost_mono len2 len ltac:(lia)); lia
        | exact E3pn| exact E3lg| exact ADR3| exact FRLo'| exact HP| exact HJ| unfold v1_cellsA; exact HC| exact HL| | cbn [olen]; clear - L2P LE2; lia| exact L43| exact V0| exact TSR].
      split; [exact L2P|]. exists (to_bytes (slice c (p + 43) len2)). rewrite E3e. exact BLKE.
  Qed.

  (* [comment removed for export] *)
  Lemma v1_tsA : forall ΣX mX CX (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX (pn lg : bptr) (A Cl : Z) (bl : list (bv 8)),
    linv ΣX st mX OW bo [(lg, Cl, 32); (pn, A, SCT_SIZE)] CX -> CSTb <= CX -> znth c p = 0 -> 43 <= len -> lg <> pn ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40] ->
    rw_cells ctasegs mX PIN [C8 (Z_to_bv 64 (D + p))] -> rw_cells ctasegs mX (f + 32) [CB 8 jp] ->
    rw_cells ctasegs mX A (logid_cellsA Cl) -> rw_cells ctasegs mX Cl [CB 32 bl] ->
    implAp (v1_ts_termA pn lg st) ΣX SPOST
      (dst x1 x5 x6 x7 (Z_to_bv 64 (A + 32)) (Z_to_bv 64 32) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 (D + p))
           (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) x28 x29 x30 x31 FX fcX mX 0x335a54).
  Proof.
    intros until bl. intros LI HCX V0 L43 NLP FRLo HP HJ HC HL. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF. cbn [app] in HEAPX.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _ & CRX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    pose proof LI as (_ & _ & _ & _ & _ & HBX & CRT & LBOK). cbn [ar_RT push amb] in CRT, CRX.
    assert (A16 : A mod 16 = 0) by (pose proof (proj1 (proj1 (Forall_inv (Forall_inv_tail LBOK)))) as X; cbn [blk_addr fst snd] in X; exact X).
    pose proof (BND (pn, A, SCT_SIZE) ltac:(apply in_or_app; right; right; left; reflexivity)) as (A0 & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI. unfold SCT_SIZE in AC, AI. pce AC.
    pose proof (BND (lg, Cl, 32) ltac:(apply in_or_app; right; left; reflexivity)) as (L0 & _ & LC & LW). cbn [blk_addr blk_size fst snd] in L0, LC, LW. pce LC.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    assert (BY0 : CtWire.byte c p = 0) by (rewrite BY by (clear - P0 PL LEN; lia); exact V0).
    pose proof (@AH_disjoint_gen (push AR f 0) _ _ _ _ (lg, Cl, 32) (pn, A, SCT_SIZE) HEAPX ltac:(apply in_or_app; right; left; reflexivity)
                  ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(cbn [blk_id fst snd]; exact NLP)) as DJLA.
    cbn [blk_addr blk_size fst snd] in DJLA. unfold SCT_SIZE in DJLA.
    pose proof (DJL (pn, A, SCT_SIZE) bq ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold SCT_SIZE in DJQ.
    pose proof (DJL (pn, A, SCT_SIZE) bd ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact HBD)) as DJD. cbn [blk_addr blk_size fst snd] in DJD. unfold SCT_SIZE in DJD.
    pose proof (DJL (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(right; left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJP. cbn [blk_addr blk_size fst snd] in DJP. unfold SCT_SIZE in DJP.
    pose proof (DJL (lg, Cl, 32) (qp, f + 32, 8) ltac:(left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJLP. cbn [blk_addr blk_size fst snd] in DJLP.
    assert (QP : PIN + 8 <= f + 32 \/ f + 40 <= PIN) by (unfold off_fr in OQ; change (fs_size 0) with 64 in OQ; clear - OQ Q1 Q2; lia).
    assert (DPo : D + zlength c <= f + 32 \/ f + 40 <= D) by (unfold off_fr in OD; change (fs_size 0) with 64 in OD; clear - OD BD1 BD2; lia).
    assert (HBQ' : In bq (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ).
    assert (HBD' : In bd (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBD).
    assert (HXIN : In (pn, A, SCT_SIZE) (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; right; left; reflexivity).
    assert (HPOBJ : In (qp, f + 32, 8) (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; left; reflexivity).
    ablock HEAPX HBQ' ACCQ OFFQ. ablock HEAPX HBD' ACCD OFFD. ablock HEAPX HXIN ACCX OFFX. ablock HEAPX HPOBJ ACCP OFFP. unfold SCT_SIZE in ACCX, OFFX.
    pose proof (munch_refl [(A + 40, A + 48); (f + 32, f + 40)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (OFF : offshW [(A + 40, A + 48); (f + 32, f + 40)]%Z) by (cbn [offshW]; clear - OFFX OFFP; unfold SHLO, SHHI in *; lia). clear OFFQ OFFD OFFX OFFP.
    clear HBQ' HBD' HXIN HPOBJ ACCQ.
    frz Q5. frz BD5. frz OQ. frz OD. frz AI. frz LW. frz DJLA. frz HL. frz DJLP. frz PIND. frz G5.
    frz DJQ. frz DJD. frz DJP. frz QP. frz DPo.
    (* [comment removed for export] *)
    set (b0 := znth c (p + 33)). set (b1 := znth c (p + 34)). set (b2 := znth c (p + 35)). set (b3 := znth c (p + 36)).
    set (b4 := znth c (p + 37)). set (b5 := znth c (p + 38)). set (b6 := znth c (p + 39)). set (b7 := znth c (p + 40)).
    pose proof (znth_range8 c (p + 33) DF) as R0'. pose proof (znth_range8 c (p + 34) DF) as R1'. pose proof (znth_range8 c (p + 35) DF) as R2'. pose proof (znth_range8 c (p + 36) DF) as R3'.
    pose proof (znth_range8 c (p + 37) DF) as R4'. pose proof (znth_range8 c (p + 38) DF) as R5'. pose proof (znth_range8 c (p + 39) DF) as R6'. pose proof (znth_range8 c (p + 40) DF) as R7'.
    fold b0 in R0'. fold b1 in R1'. fold b2 in R2'. fold b3 in R3'. fold b4 in R4'. fold b5 in R5'. fold b6 in R6'. fold b7 in R7'.
    set (q1 := b0 * 256 + b1). set (q2 := q1 * 256 + b2). set (q3 := q2 * 256 + b3). set (q4 := q3 * 256 + b4). set (q5 := q4 * 256 + b5). set (q6 := q5 * 256 + b6).
    set (ts := u64be c (p + 33)).
    assert (Q1' : 0 <= q1 < 2 ^ 16) by (clear - R0' R1'; lia). assert (Q2' : 0 <= q2 < 2 ^ 24) by (clear - Q1' R2'; lia). assert (Q3' : 0 <= q3 < 2 ^ 32) by (clear - Q2' R3'; lia).
    assert (Q4' : 0 <= q4 < 2 ^ 40) by (clear - Q3' R4'; lia). assert (Q5' : 0 <= q5 < 2 ^ 48) by (clear - Q4' R5'; lia). assert (Q6' : 0 <= q6 < 2 ^ 56) by (clear - Q5' R6'; lia).
    assert (TSQ : ts = q6 * 256 + b7).
    { subst ts q6 q5 q4 q3 q2 q1 b0 b1 b2 b3 b4 b5 b6 b7. unfold u64be. rewrite !BY by (clear - P0 PL L43; lia).
      replace (p + 33 + 1) with (p + 34) by (clear; lia). replace (p + 33 + 2) with (p + 35) by (clear; lia). replace (p + 33 + 3) with (p + 36) by (clear; lia). replace (p + 33 + 4) with (p + 37) by (clear; lia).
      replace (p + 33 + 5) with (p + 38) by (clear; lia). replace (p + 33 + 6) with (p + 39) by (clear; lia). replace (p + 33 + 7) with (p + 40) by (clear; lia). reflexivity. }
    unfold logid_cellsA in HC.
    unfold dst, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 33) (wa (D + p + 33)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 33))) by (clear - R0'; lia).
    fold b0.
    step.
    step.
    step; setreg 13%Z (Z_to_bv 64 (b0 * 2 ^ 56)) ltac:(rewrite (unsigned_lit b0), Z.shiftl_mul_pow2 by (clear - R0'; lia); reflexivity).
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    step.
    pose proof (payload_readA _ D c (p + 34) (wa (D + p + 34)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 34))) by (clear - R1'; lia).
    fold b1.
    step.
    step.
    thaw QP; thaw DPo; thaw DJP; step; frz QP; frz DPo; frz DJP.
    step; setreg 14%Z (Z_to_bv 64 (b1 * 2 ^ 48)) ltac:(rewrite (unsigned_lit b1), Z.shiftl_mul_pow2 by (clear - R1'; lia); reflexivity).
    step; setreg 13%Z (Z_to_bv 64 (q1 * 2 ^ 48)) ltac:(rewrite (unsigned_lit (b1 * 2 ^ 48)), (unsigned_lit (b0 * 2 ^ 56)) by (clear - R0' R1'; lia); change (b0 * 2 ^ 56) with (b0 * 2 ^ (48 + 8)); rewrite CtSctP.W_o2i_sct.lor_hi_lo by (clear - R0' R1'; lia); subst q1; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 35) (wa (D + p + 35)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 35))) by (clear - R2'; lia).
    fold b2.
    step; setreg 12%Z (Z_to_bv 64 (b2 * 2 ^ 40)) ltac:(rewrite (unsigned_lit b2), Z.shiftl_mul_pow2 by (clear - R2'; lia); reflexivity).
    step; setreg 12%Z (Z_to_bv 64 (q2 * 2 ^ 40)) ltac:(rewrite (unsigned_lit (b2 * 2 ^ 40)), (unsigned_lit (q1 * 2 ^ 48)) by (clear - Q1' R2'; lia); change (q1 * 2 ^ 48) with (q1 * 2 ^ (40 + 8)); rewrite CtSctP.W_o2i_sct.lor_hi_lo by (clear - Q1' R2'; lia); subst q2; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 36) (wa (D + p + 36)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 36))) by (clear - R3'; lia).
    fold b3.
    step.
    step; setreg 13%Z (Z_to_bv 64 (b3 * 2 ^ 32)) ltac:(rewrite (unsigned_lit b3), Z.shiftl_mul_pow2 by (clear - R3'; lia); reflexivity).
    step; setreg 12%Z (Z_to_bv 64 (q3 * 2 ^ 32)) ltac:(rewrite (unsigned_lit (b3 * 2 ^ 32)), (unsigned_lit (q2 * 2 ^ 40)) by (clear - Q2' R3'; lia); change (q2 * 2 ^ 40) with (q2 * 2 ^ (32 + 8)); rewrite CtSctP.W_o2i_sct.lor_hi_lo by (clear - Q2' R3'; lia); subst q3; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 37) (wa (D + p + 37)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 37))) by (clear - R4'; lia).
    fold b4.
    step.
    step; setreg 13%Z (Z_to_bv 64 (b4 * 2 ^ 24)) ltac:(rewrite (unsigned_lit b4), Z.shiftl_mul_pow2 by (clear - R4'; lia); reflexivity).
    step; setreg 12%Z (Z_to_bv 64 (q4 * 2 ^ 24)) ltac:(rewrite (unsigned_lit (b4 * 2 ^ 24)), (unsigned_lit (q3 * 2 ^ 32)) by (clear - Q3' R4'; lia); change (q3 * 2 ^ 32) with (q3 * 2 ^ (24 + 8)); rewrite CtSctP.W_o2i_sct.lor_hi_lo by (clear - Q3' R4'; lia); subst q4; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 38) (wa (D + p + 38)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 38))) by (clear - R5'; lia).
    fold b5.
    step.
    step; setreg 13%Z (Z_to_bv 64 (b5 * 2 ^ 16)) ltac:(rewrite (unsigned_lit b5), Z.shiftl_mul_pow2 by (clear - R5'; lia); reflexivity).
    step; setreg 12%Z (Z_to_bv 64 (q5 * 2 ^ 16)) ltac:(rewrite (unsigned_lit (b5 * 2 ^ 16)), (unsigned_lit (q4 * 2 ^ 24)) by (clear - Q4' R5'; lia); change (q4 * 2 ^ 24) with (q4 * 2 ^ (16 + 8)); rewrite CtSctP.W_o2i_sct.lor_hi_lo by (clear - Q4' R5'; lia); subst q5; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 39) (wa (D + p + 39)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 39))) by (clear - R6'; lia).
    fold b6.
    step.
    step; setreg 13%Z (Z_to_bv 64 (b6 * 2 ^ 8)) ltac:(rewrite (unsigned_lit b6), Z.shiftl_mul_pow2 by (clear - R6'; lia); reflexivity).
    step; setreg 12%Z (Z_to_bv 64 (q6 * 2 ^ 8)) ltac:(rewrite (unsigned_lit (b6 * 2 ^ 8)), (unsigned_lit (q5 * 2 ^ 16)) by (clear - Q5' R6'; lia); change (q5 * 2 ^ 16) with (q5 * 2 ^ (8 + 8)); rewrite CtSctP.W_o2i_sct.lor_hi_lo by (clear - Q5' R6'; lia); subst q6; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 40) (wa (D + p + 40)) HBX DF ltac:(clear - P0 PL L43; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    step.
    clear RD.
    rewrite (zxb_lit (znth c (p + 40))) by (clear - R7'; lia).
    fold b7.
    step.
    step; setreg 12%Z (Z_to_bv 64 ts) ltac:(rewrite (unsigned_lit b7), (unsigned_lit (q6 * 2 ^ 8)) by (clear - Q6' R7'; lia); change (2 ^ 8) with 256; rewrite CtSctP.W_o2i_sig.lor_shl8 by (clear - Q6' R7'; lia); rewrite TSQ; reflexivity).
    step.
    thaw DJQ; thaw DJD; thaw DJP; step; frz DJQ; frz DJD; frz DJP.
    setreg 13%Z (Z_to_bv 64 (Z.shiftr (D + p + 41) 3)) ltac:(rewrite unsigned_lit by (clear - D0 D63 P0 PL L43; lia); reflexivity).
    (* [comment removed for export] *)
    name_mem m2.
    match goal with H : munch _ mX m2 |- _ => rename H into MU2 end.
    match goal with H : wmono ctasegs mX m2 |- _ => rename H into WM2 end.
    match goal with H : mem_inv ctasegs m2 |- _ => rename H into MI2 end.
    clear Q1' Q2' Q3' Q4' Q5'.
    assert (TSR : 0 <= ts < 2 ^ 64) by (clear - Q6' R7' TSQ; lia).
    apply evt_done.
    assert (LI2 : linv ΣX st m2 OW bo [(lg, Cl, 32); (pn, A, SCT_SIZE)] CX).
    { kit @oinv_munch; [exact LI| exact MU2| exact WM2| exact MI2| first [exact STX| rewrite ?ESPA in STX; exact STX]|].
      constructor; [right; right; exists (pn, A, SCT_SIZE); split; [right; left; reflexivity| cbn; unfold SCT_SIZE; clear; lia]|].
      constructor; [right; left; exists (f + 32, f + 40)%Z; split; [subst XP; left; reflexivity| cbn; clear; lia]| constructor]. }
    thaw HL. thaw DJLA. thaw DJLP. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU2)) in HL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; clear - Ha DJLA DJLP; lia].
    eapply (v1_extA ΣX m2 CX) with (bl := bl) (ts := ts) (Cl := Cl) (lg := lg) (pn := pn) (A := A);
      [exact LI2| exact HCX| exact V0| exact L43| exact NLP| reflexivity| exact TSR| | | | | exact HL];
      match goal with H : rw_cells ctasegs m2 ?a _ |- rw_cells ctasegs m2 ?a _ => exact H end.
  Qed.


  (* [comment removed for export] *)
  Lemma v1_mainA : forall ΣX mX CX (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX (pn : bptr) (A : Z),
    linv ΣX st mX OW bo [(pn, A, SCT_SIZE)] CX -> CSTb <= CX -> znth c p = 0 ->
    rw_cells ctasegs mX spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40] ->
    rw_cells ctasegs mX PIN [C8 (Z_to_bv 64 (D + p))] ->
    rw_cells ctasegs mX A (ver_cells A) ->
    rw_cells ctasegs mX (f + 32) [CB 8 jp] ->
    implAp (v1_termA pn st) ΣX SPOST
      (dst x1 x5 x6 x7 (Z_to_bv 64 (znth c p)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 (D + p))
           (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) x28 x29 x30 x31 FX fcX mX OSC_V1).
  Proof.
    intros until A. intros LI HCX V0 FRLo HP HC HJ. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAPX & NDX & BND & FRSH & DJL & _). clear OF. cbn [app] in HEAPX.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & STX & _ & _ & _ & _ & MIX & CSX & _ & CRX & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UWX & _).
    pose proof LI as (_ & _ & _ & _ & _ & HBX & CRT & LBOK). cbn [ar_RT push amb] in CRT, CRX.
    pose proof (proj1 (proj1 (Forall_inv LBOK))) as A16. cbn [blk_addr fst snd] in A16.
    pose proof (BND (pn, A, SCT_SIZE) ltac:(apply in_or_app; right; left; reflexivity)) as (A0 & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI. unfold SCT_SIZE in AC, AI. pce AC.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    assert (BY0 : CtWire.byte c p = 0) by (rewrite BY by (clear - P0 PL LEN; lia); exact V0).
    pose proof (munch_refl [(f + 32, f + 40)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    set (x0 := set_version (CtWire.byte c p) (sct_new pn)).
    set (adr0 := fun b : bptr => if bptr_eqb b pn then A else adr b).
    assert (E0pn : adr0 pn = A) by (subst adr0; cbn beta; rewrite bptr_eqb_refl; reflexivity).
    assert (ADR0 : forall b, In b LB -> adr0 (blk_id b) = adr (blk_id b)).
    { intros [[b Ab] nb] Hb. subst adr0. cbn. rewrite (bptr_eqb_neq b pn); [reflexivity|].
      intros ->. apply (FRSH (pn, A, SCT_SIZE) ltac:(left; reflexivity)). rewrite map_app. apply in_app_iff. right. subst LB'. right. exact (in_map blk_id _ _ Hb). }
    assert (EB0 : sct_blocks adr0 x0 = [(pn, A, SCT_SIZE)]).
    { subst x0 adr0. unfold CtSctP.W_sct_list_free.sct_blocks. cbn [sc_logid sc_ext sc_sig sc_blob sc_blk set_version sct_new osz32 option_map CtSctP.W_sct_list_free.oblk app]. rewrite bptr_eqb_refl. reflexivity. }
    assert (HC0 : rw_cells ctasegs mX A (sct_cells adr0 x0 (-1) 0)).
    { subst x0. unfold CtSctP.SctRep.sct_cells, ver_cells in HC |- *.
      cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new set_version optr osz32 option_map CtSctP.SctRep.logid_len].
      rewrite BY0. rewrite V0 in HC. cbn [CtSctP.SctRep.u32 Z.modulo Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz. exact HC. }
    (* [comment removed for export] *)
    assert (QPO : PIN + 8 <= f \/ f + 64 <= PIN) by (unfold off_fr in OQ; change (fs_size 0) with 64 in OQ; clear - OQ Q1 Q2; lia).
    pose proof (DJL (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJP. cbn [blk_addr blk_size fst snd] in DJP. unfold SCT_SIZE in DJP.
    pose proof (DJL (pn, A, SCT_SIZE) bq ltac:(left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold SCT_SIZE in DJQ.
    frz Q5. frz BD5. frz OQ. frz OD. frz AI. frz DJQ.
    unfold v1_termA, dst, OSC_V1, MallocRep.wz. cbv zeta. fold x0. unfold CT_V1_HASHLEN.
    replace (p + 1 + 32 + 8 + 2) with (p + 43) by (clear; lia). replace (p + 1 + 32 + 8) with (p + 41) by (clear; lia). replace (p + 1 + 32) with (p + 33) by (clear; lia).
    unfold ver_cells in HC.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. if_cases K43; zc K43.
    2:{ (* [comment removed for export] *)
        replace (len <? 43) with true by (symmetry; apply Z.ltb_lt; revert K43; rewrite ?unsigned_lit by (clear - LEN; unfold MAX_SCT_SIZE in LEN; lia); clear; lia).
        apply evt_done.
        rewrite <- EB0 in LI.
        change (Z_to_bv 64 99) with (Z_to_bv 64 (rs_line RS_sct_43)).
        eapply (raise_err99A ΣX st mX OW bo CX) with (adrX := adr0) (vs := 0) (xr := x0) (j16' := j16) (j24' := j24);
          [exact LI| clear - HCX MC0; subst CSTb; ecu; lia| exact FRLo| exact ADR0| unfold MallocRep.wz; exact HP| exact E0pn| exact HC0]. }
    (* [comment removed for export] *)
    replace (len <? 43) with false by (symmetry; apply Z.ltb_ge; revert K43; rewrite ?unsigned_lit by (clear - LEN; unfold MAX_SCT_SIZE in LEN; lia); clear; lia).
    assert (L43 : 43 <= len) by (revert K43; rewrite ?unsigned_lit by (clear - LEN; unfold MAX_SCT_SIZE in LEN; lia); clear; lia). clear K43.
    do 6 step. apply evt_done.
    cbn [abind apbind amalloc aret fst snd].
    pose proof LI as LI0.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI0) as (HEAP0 & _). clear OF. cbn [app] in HEAP0.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI0) as (_ & ST0 & _ & _ & _ & _ & _ & CS0 & _ & CR0 & _). clear OC. cbn [ar_RT push amb] in CR0.
    pose proof (keepA _ _ _ _ _ _ _ LI0) as (_ & _ & UW0 & _).
    pose proof LI0 as (_ & _ & _ & _ & _ & HB0 & _).
    assert (SRC : bytes_at ctasegs mX (D + p + 1) (to_bytes (slice c (p + 1) 32))).
    { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
      replace (D + p + 1) with (D + Z.of_nat (Z.to_nat (p + 1))) by (clear - P0; lia). apply bytes_at_skipn; [exact HB0|]. apply Nat2Z.inj_le. rewrite DLEN. clear - P0 PL L43; lia. }
    assert (SLEN : length (to_bytes (slice c (p + 1) 32)) = Z.to_nat 32) by (unfold to_bytes; rewrite length_map; apply slice_length; clear - P0 PL L43; lia).
    change (Z_to_bv 64 2113496) with (wz CRYPTO_MEMDUP_A).
    eapply (@CRYPTO_memdup_walkA (push AR f 0) UK BE) with (lo := lo) (OW := OW) (LB := [(pn, A, SCT_SIZE)] ++ LB') (bsrc := bd) (P := D + p + 1) (n := 32)
                                                         (src := to_bytes (slice c (p + 1) 32)) (ras := bv_unsigned ra :: ras);
      [exact HEAP0| rewrite ESPA; exact ST0| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; clear - LOSPu SPAL; ecu; lia
      | rewrite ESPA; clear - TOP SPAH; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MIX| reflexivity| exact CS0
      | apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBD| clear - BD1 P0; lia| clear - BD2 PL L43; lia| exact SRC| exact SLEN
      | apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL L43; lia); bv_solve| reflexivity| clear; lia
      | rewrite (mcost_0_small 32) by (clear; lia); cbn [ar_RT push amb]; clear - CR0; lia
      | rewrite ESPA; exact UW0| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_dup104 CTX)|].
    intros lg ΣL msL FRESHL POL. unfold calloc_postA in POL. rewrite ?ESPA in POL.
    destruct POL as (u0 & u1 & u2 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & FL & fcL & mL & Cl
                     & -> & MIL & STL & AGL & CRL & BRL & HEAPL & ACCL' & (BLKL & _)).
    rewrite (ret_pc_even 0x335a1c) by (clear; lia). unfold MallocRep.wz.
    cbn [apbind fst snd].
    lazymatch goal with |- implAp ?t ?Σq ?Q ?ms => change (implAp (v1_ts_termA pn lg st) Σq Q ms) end.
    pose proof BRL as (L0 & L16 & _ & LC & LW). pce LC.
    rewrite (mcost_0_small 32) in CRL by (clear; lia).
    assert (LIL : linv ΣL st mL OW bo [(lg, Cl, 32); (pn, A, SCT_SIZE)] (CX - 0)).
    { kit @oinv_alloc; [exact LI0| exact AGL| exact HEAPL| exact MIL| exact STL| exact CRL| clear - HCX MC0; subst CSTb; ecu; lia]. }
    rewrite Z.sub_0_r in LIL.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIL) as (HEAPL' & NDL' & BNDL & FRSHL & DJLL & _). clear OF. cbn [app] in HEAPL'.
    assert (NLP : lg <> pn).
    { intros E1. pose proof NDL' as N. rewrite map_app in N. apply NoDup_app_split in N as (N & _ & _). cbn [map app blk_id fst snd] in N.
      apply NoDup_cons_iff in N as [N _]. apply N. left. symmetry. exact E1. }
    pose proof (@AH_disjoint_gen (push AR f 0) _ _ _ _ (lg, Cl, 32) (pn, A, SCT_SIZE) HEAPL' ltac:(apply in_or_app; right; left; reflexivity)
                  ltac:(apply in_or_app; right; right; left; reflexivity) ltac:(cbn [blk_id fst snd]; exact NLP)) as DJLA.
    cbn [blk_addr blk_size fst snd] in DJLA. unfold SCT_SIZE in DJLA.
    pose proof (DJLL (pn, A, SCT_SIZE) bq ltac:(right; left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ2. cbn [blk_addr blk_size fst snd] in DJQ2. unfold SCT_SIZE in DJQ2.
    pose proof (DJLL (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(right; left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJP2. cbn [blk_addr blk_size fst snd] in DJP2. unfold SCT_SIZE in DJP2.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGL) in FRLo; [| intros a Ha; left; cbn in Ha; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HJ; [| intros a Ha; cbn in Ha; right; right; exists (qp, f + 32, 8); split; [apply in_or_app; right; apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGL) in HC; [| intros a Ha; right; right; exists (pn, A, SCT_SIZE); split; [apply in_or_app; right; left; reflexivity| cbn in Ha |- *; unfold SCT_SIZE; clear - Ha; lia]].
    assert (HXIN : In (pn, A, SCT_SIZE) (OW ++ [(lg, Cl, 32); (pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; right; left; reflexivity).
    ablock HEAPL' HXIN ACCX OFFX. unfold SCT_SIZE in ACCX, OFFX.
    try clear MU WM. pose proof (munch_refl [(A + 24, A + 40)]%Z mL) as MU. pose proof (wmono_refl ctasegs mL) as WM.
    assert (OFF : offshW [(A + 24, A + 40)]%Z) by (cbn [offshW]; clear - OFFX; unfold SHLO, SHHI in *; lia). clear OFFX.
    frz LW. frz DJLA. frz BLKL. thaw DJQ.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step.
    step. if_cases K1; zc K1; [exfalso; revert K1; rewrite ?O2iKitAR.land_ones64_small by (clear - L0 LC CN; lia); clear - L0; lia|]. clear K1.
    step. step. name_mem m6. frz DJQ. frz DJP. frz DJQ2. frz DJP2. thaw BLKL.
    apply evt_done.
    match goal with H : munch _ mL m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs mL m6 |- _ => rename H into WM6 end.
    match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end. rewrite ?ESPA in STL.
    assert (LI6 : linv ΣL st m6 OW bo [(lg, Cl, 32); (pn, A, SCT_SIZE)] CX).
    { kit @oinv_munch; [exact LIL| exact MU6| exact WM6| exact MI6| first [exact STL| match goal with H : stk ctasegs m6 _ _ |- _ => rewrite ?ESPA in H; exact H end]|].
      constructor; [| constructor]. right; right. exists (pn, A, SCT_SIZE). split; [right; left; reflexivity| cbn; unfold SCT_SIZE; clear; lia]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU6)) in BLKL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; unfold frozen in DJLA; clear - Ha DJLA; lia].
    match goal with H : rw_cells ctasegs m6 A _ |- _ => rewrite V0 in H end.
    eapply (v1_tsA ΣL m6 CX) with (bl := to_bytes (slice c (p + 1) 32)); [exact LI6| exact HCX| exact V0| exact L43| exact NLP| | | | | exact BLKL];
      match goal with H : rw_cells ctasegs m6 ?a _ |- rw_cells ctasegs m6 ?a _ => exact H end.
  Qed.

  Lemma sct_bodyA : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) FX fcX,
    implAp (o2i_sct c p len st) Σ1 SPOST
      (dst x1 x5 x6 x7 (Z_to_bv 64 (len + -65536)) (Z_to_bv 64 (-65535)) x12 x13 x14 x15 x16 x17
           s3 (Z_to_bv 64 0) (Z_to_bv 64 len) s7 s8 x28 x29 x30 x31 FX fcX m4 0x335814).      (* [comment removed for export] *)
  Proof.
    intros. bf.
    destruct BQX as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5 & OQ). destruct BDX as (bd & HBD & BD1 & BD2 & BD0 & BD5 & OD & BDC).
    pose proof (conj CE2 (conj CE3 TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    pose proof linv0 as LI.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LI) as (HEAP4 & ND4 & _). clear OF. cbn [app] in HEAP4.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ LI) as (_ & _ & _ & _ & _ & _ & _ & CS4 & _). clear OC.
    pose proof (keepA _ _ _ _ _ _ _ LI) as (_ & _ & UW4 & _).
    pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl ctasegs m4) as WM. pose proof MI4 as MI. pose proof ST4 as STX.
    unfold dst, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases KL; zc KL; rewrite ?land_ones64_neg, ?land_ones64_small, ?unsigned_lit in KL by (unfold MAX_SCT_SIZE in LEN; clear - LEN; lia);
      [| exfalso; unfold MAX_SCT_SIZE in LEN; clear - KL LEN; lia]. clear KL.
    (* [comment removed for export] *)
    step. apply evt_done.
    unfold o2i_sct. replace ((len =? 0) || (MAX_SCT_SIZE <? len)) with false by (symmetry; unfold MAX_SCT_SIZE in *; apply orb_false_intro; [apply Z.eqb_neq| apply Z.ltb_ge]; clear - LEN; lia).
    cbn [abind apbind amalloc aret fst snd]. change SZ_SCT with SCT_SIZE.
    change (Z_to_bv 64 3372236) with (wz SCT_NEW_A).
    eapply (@SCT_new_walkA (push AR f 0) UK BE) with (lo := lo) (OW := OW) (LB := LB') (ras := bv_unsigned ra :: ras);
      [exact HEAP4| rewrite ESPA; exact ST4| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| rewrite ESPA; clear - LOSPu SPAL; ecu; lia
      | rewrite ESPA; clear - TOP SPAH; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MI4| reflexivity| exact CS4
      | rewrite ESPA; exact UW4| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_sctnew CTX)|].
    intros pn ΣN msN FRESHN PON. unfold calloc_postA in PON. rewrite ?ESPA in PON.
    destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & FN & fcN & mN & A
                     & -> & MIN & STN & AGN & CRN & BRN & HEAPN & ACCN & INITN).
    rewrite (ret_pc_even 0x335860) by (clear; lia). unfold MallocRep.wz.
    cbn [apbind fst snd].
    lazymatch goal with |- implAp ((if ?b then _ else _) ?stt) ?ΣY ?Q ?ms => change (implAp ((if b then v1_termA pn else nv1_termA pn) stt) ΣY Q ms) end.
    pose proof BRN as (A0 & A16 & _ & AC & AI). unfold SCT_SIZE in AC, AI. pce AC.
    assert (LIN : linv ΣN st mN OW bo [(pn, A, SCT_SIZE)] (CSTb - mcost SCT_SIZE)).
    { kit @oinv_alloc; [exact LI| exact AGN| exact HEAPN| exact MIN| exact STN| exact CRN| subst CSTb; rewrite (mcost_0_small SCT_SIZE) by (clear; unfold SCT_SIZE; lia); clear - MC0; ecu; lia]. }
    rewrite (mcost_0_small SCT_SIZE) in LIN by (clear; unfold SCT_SIZE; lia). rewrite Z.sub_0_r in LIN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ LIN) as (HEAPN' & NDN & BND & FRSHN & DJL & _). clear OF. cbn [app] in HEAPN'.
    pose proof LIN as (_ & _ & _ & _ & _ & HBN & _).
    (* [comment removed for export] *)
    pose proof HPIN4 as HP. unfold MallocRep.wz in HP.
    apply (rw_cells_agree _ _ _ _ _ AGN) in HP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; subst LB'; right; exact HBQ| clear - Ha Q1 Q2; lia]].
    pose proof FRLo4 as FRLo. apply (rw_cells_agree _ _ _ _ _ AGN) in FRLo; [| intros a Ha; left; cbn in Ha; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia].
    pose proof (sct_new_cells_repA mN A adr pn INITN) as HC. clear INITN. unfold CtSctP.SctRep.sct_cells in HC.
    cbn [sc_version sc_blob sc_bloblen sc_logid sc_ts sc_ext sc_extlen sc_hash sc_sigalg sc_sig sc_siglen sct_new optr osz32 option_map CtSctP.SctRep.logid_len CtSctP.SctRep.u32 Z.modulo Z.pow_pos Pos.iter Z.mul] in HC.
    unfold MallocRep.wz in HC.
    assert (HBQ' : In bq (OW ++ [(pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBQ).
    assert (HBD' : In bd (OW ++ [(pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; apply in_or_app; right; subst LB'; right; exact HBD).
    assert (HXIN : In (pn, A, SCT_SIZE) (OW ++ [(pn, A, SCT_SIZE)] ++ LB')) by (apply in_or_app; right; left; reflexivity).
    ablock HEAPN' HBQ' ACCQ OFFQ. ablock HEAPN' HBD' ACCD OFFD. ablock HEAPN' HXIN ACCX OFFX. unfold SCT_SIZE in ACCX, OFFX.
    pose proof (DJL (pn, A, SCT_SIZE) bq ltac:(left; reflexivity) ltac:(subst LB'; right; exact HBQ)) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ. unfold SCT_SIZE in DJQ.
    pose proof (DJL (pn, A, SCT_SIZE) bd ltac:(left; reflexivity) ltac:(subst LB'; right; exact HBD)) as DJD. cbn [blk_addr blk_size fst snd] in DJD. unfold SCT_SIZE in DJD.
    frz Q5. frz BD5. frz OQ. frz OD. frz DJQ. frz DJD. frz PIND. frz AI.
    pose proof (DJL (pn, A, SCT_SIZE) (qp, f + 32, 8) ltac:(left; reflexivity) ltac:(subst LB'; left; reflexivity)) as DJP. cbn [blk_addr blk_size fst snd] in DJP. unfold SCT_SIZE in DJP.
    pose proof HP4 as HPO. apply (rw_cells_agree _ _ _ _ _ AGN) in HPO; [| intros a Ha; cbn in Ha; right; right; exists (qp, f + 32, 8); split; [apply in_or_app; right; subst LB'; left; reflexivity| cbn; clear - Ha; lia]].
    clear MU WM. pose proof (munch_refl [(f + 32, f + 40); (A, A + 4)]%Z mN) as MU. pose proof (wmono_refl ctasegs mN) as WM.      (* [comment removed for export] *)
    assert (OFF : offshW [(f + 32, f + 40); (A, A + 4)]%Z) by (cbn [offshW]; clear - OFFX G4 G5; unfold SHLO, SHHI, SEGTOP_A in *; lia). clear OFFQ OFFD OFFX.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    pose proof (znth_range8 c p DF) as R0.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?O2iKitAR.land_ones64_small by (clear - A0 AC CN; lia); clear - A0; lia|]. clear K0.
    step. step.
    setreg 24%Z (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) ltac:(rewrite unsigned_lit by (clear - Q1 Q2 Q3 Q4 CN; lia); reflexivity).
    (* [comment removed for export] *)
    assert (DPO : D + zlength c <= f \/ f + 64 <= D) by (unfold frozen, off_fr in OD; change (fs_size 0) with 64 in OD; clear - OD BD1 BD2; lia).
    assert (QPO : PIN + 8 <= f \/ f + 64 <= PIN) by (unfold frozen, off_fr in OQ; change (fs_size 0) with 64 in OQ; clear - OQ Q1 Q2; lia).
    (* [comment removed for export] *)
    step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. ab_shload 4.
    pose proof (payload_readA _ D c p (wa (D + p)) HBN DF ltac:(clear - P0 PL LEN; lia) eq_refl) as RD. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. clear RD.
    first [ lazymatch goal with H : absh_ok ?b _ _ |- _ => ab_join 11%Z 12%Z 0x3358a0%Z H end
          | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false ].
    rewrite (zxb_lit (znth c p)) by (clear - R0; lia).
    (* [comment removed for export] *)
    thaw DJD. thaw DJQ. step. name_mem m5. frz DJD. frz DJQ.
    match goal with H : munch _ mN m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs mN m5 |- _ => rename H into WM5 end.
    match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
    assert (LI5 : linv ΣN st m5 OW bo [(pn, A, SCT_SIZE)] CSTb).
    { kit @oinv_munch; [exact LIN| exact MU5| exact WM5| exact MI5| exact STN|].
      constructor; [right; left; exists (f + 32, f + 40)%Z; split; [subst XP; left; reflexivity| cbn; clear; lia]|].
      constructor; [| constructor]. right; right. exists (pn, A, SCT_SIZE). split; [left; reflexivity| cbn; unfold SCT_SIZE; clear; lia]. }
    match goal with H : rw_cells ctasegs m5 (f + 32) _ |- _ => rename H into HJ5 end.
    step. if_cases KV; zc KV.
    - (* [comment removed for export] *)
      assert (V0 : znth c p = 0) by (revert KV; rewrite ?unsigned_lit by (clear - R0; lia); clear; lia). clear KV.
      replace (CtWire.byte c p =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite BY by (clear - P0 PL LEN; lia); exact V0).
      apply evt_done. change (Z_to_bv 64 3365360) with (Z_to_bv 64 OSC_V1). rewrite ?EPIN.
      eapply (v1_mainA ΣN m5 CSTb); [exact LI5| clear; lia| exact V0| | | | exact HJ5]; assumption.
    - (* [comment removed for export] *)
      assert (VN : znth c p <> 0) by (revert KV; rewrite ?unsigned_lit by (clear - R0; lia); clear; lia). clear KV.
      replace (CtWire.byte c p =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite BY by (clear - P0 PL LEN; lia); exact VN).
      apply evt_done. change (Z_to_bv 64 3365032) with (Z_to_bv 64 OSC_NV1). rewrite ?EPIN.
      eapply (nv1_mainA ΣN m5 CSTb); [exact LI5| clear; lia| exact VN| | | ]; assumption.
  Qed.


End Act.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem o2i_sct_walkA : o2i_sct_specA2 O2I_SCT_STACK_A O2I_SCT_COST_A O2I_SCT_FRAMES_A.
Proof.
  unfold o2i_sct_specA2. intros until PIN. intros PRE TP UW CTX NE KOW KIDS PAY P0 LEN PL ADR CPIN ALP PIND HPIN Ea0 Ea1 Ea2.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM0).
  pose proof LOSP as LOSPu. pose proof CRED as CREDu. pose proof FRM0 as FRMu. ecu.
  pose proof (mcost_mono len len ltac:(clear - LEN; lia)) as [MC0 _].
  intros XX Φ DD SAFE LINK. subst tp a0 a1 a2.
  change (wz O2I_SCT_A) with (wz OSC_ENTRY).
  eapply (osc_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold OSC_FRAME, RT_STACK; clear - LOSPu; lia| exact TOP| exact AL16| exact MI| reflexivity
    | clear - FRMu; lia| clear - CREDu MC0; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 j48 jf24 jf32 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AG3 FRL HFR HF FRS SPA32 SPAL SPAH GSZ SAVJ.
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qp Hqp].
  (* [comment removed for export] *)
  lazymatch type of HF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs m3 f [c0; c1; c2; c3] (c4 :: rest)) HF)) as HP0 end.
  lazymatch type of HP0 with rw_cells _ _ ?a _ => replace a with (f + 32) in HP0 by reflexivity end.
  lazymatch type of HP0 with rw_cells _ _ _ (?c4 :: ?rest) =>
    pose proof (proj1 (proj1 (SctRepA.rw_cells_app ctasegs m3 (f + 32) [c4] rest) HP0)) as HP3 end.
  clear HP0.
  eapply (implAp_elim _ Σ Σ1 _ _ XX Φ DD); [| exact SAFE| exact LINK| exact EL1].
  (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5. cbn [ar_SP0 push amb] in G3.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LOSPu SPAL SPAH SPR LO0; plia).
  pose proof ST3 as ST4. pose proof MI3 as MI4. frz ST3. frz MI3. frz HF. frz FRS. frz HP3. frz AG3.
  unfold MallocRep.wz.
  pose proof (munch_refl [(spa + 48, spa + 56)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  apply implAp_from_evt.
  step. setreg 10%Z (Z_to_bv 64 (len + -65536)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - LEN; unfold MAX_SCT_SIZE in LEN; lia); bv_solve).
  step.
  step. name_mem m4. apply evt_done.      (* [comment removed for export] *)
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  first [match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4' end| idtac].
  thaw HP3. assert (HP4 : rw_cells ctasegs m4 (f + 32) [CB 8 jf32]).
  { eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU4)| exact HP3| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LOSPu SPAL; nrm; lia]. }
  match goal with H : rw_cells ctasegs m4 spa (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) |- _ =>
      pose proof (rw_cells_app_l m4 _ [c0; c1; c2; c3; c4; c5] rest H) as FRLo4;
      pose proof (rw_cells_skip m4 _ [c0; c1; c2; c3; c4; c5] rest 48 H ltac:(reflexivity)) as FRHi4 end.
  thaw ST3. thaw MI3. thaw HF. thaw FRS. thaw AG3.
  eapply (sct_bodyA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K ras adr c D p len PIN); try eassumption; try reflexivity.
Qed.

End WithRT.
