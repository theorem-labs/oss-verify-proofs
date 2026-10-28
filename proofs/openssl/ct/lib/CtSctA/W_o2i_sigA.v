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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_obj_free ApErrKitA2 W_prefix_create W_get_objectA W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_err_newA W_err_set_debugA W_err_vsetA W_get_object_closedA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep W_sct_set1_signature W_sct_list_free W_o2i_sig.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import W_sk_leavesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA W_sct_newA W_sct_set1_signatureA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac frz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Import ListNotations.
Open Scope Z_scope.

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
Notation zxb_lit := CtRepP.W_get_object_walk.zxb_lit.
Notation znth_range8 := CtRepP.W_get_object_walk.znth_range.

(* [comment removed for export] *)
Definition O2I_SIG_STACK_A : Z := 80 + ERR_SET_ERROR_STACK.
Definition O2I_SIG_COST_A (len : Z) : Z := GETOBJ_ERR_COST_A + mcost len.
Definition O2I_SIG_FRAMES_A : Z := GETOBJ_FRAMES_A.

Lemma mcost_mono : forall a b, 0 <= a <= b -> 0 <= mcost a <= mcost b.
Proof.
  intros a b H. unfold mcost.
  destruct (a <=? 64512) eqn:Ea; destruct (b <=? 64512) eqn:Eb;
    rewrite ?Z.leb_le, ?Z.leb_gt in Ea; rewrite ?Z.leb_le, ?Z.leb_gt in Eb; lia.
Qed.

Local Notation E_new42 := (E_o2i_SCT_signature_3493f0 : uk_call 0x335420 0x3354bc 0x1fd52c).
Local Notation E_new58 := (E_o2i_SCT_signature_349510 : uk_call 0x335420 0x3355ac 0x1fd52c).
Local Notation E_new51 := (E_o2i_SCT_signature_349530 : uk_call 0x335420 0x3355cc 0x1fd52c).
Local Notation E_dbg := (E_o2i_SCT_signature_34954c : uk_call 0x335420 0x3355e8 0x1fd844).
Local Notation E_err := (E_o2i_SCT_signature_349560 : uk_call 0x335420 0x3355fc 0x1fdab8).
Local Notation E_set1 := (E_o2i_SCT_signature_3495a0 : uk_call 0x335420 0x33563c 0x3376e4).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

Section Proofs.
  (* [comment removed for export] *)
  Hypothesis STRCPY : strcpy_icontract RT.

  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block) (ras : list Z).
  Variables (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z).
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo O2I_SIG_STACK_A (O2I_SIG_COST_A len) O2I_SIG_FRAMES_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx O2I_SCT_SIGNATURE_A (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D c.
  Hypothesis CNE : 0 < zlength c.
  Hypothesis P0 : 0 <= p.
  Hypothesis LEN0 : 0 <= len.
  Hypothesis PL : p + len <= zlength c.
  Hypothesis HXIN : In (sc_blk x, adr (sc_blk x), SCT_SIZE) LB.
  Hypothesis ALX : adr (sc_blk x) mod 16 = 0.                 (* [comment removed for export] *)
  Hypothesis SEPD : D + zlength c <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= D.
  Hypothesis PAYNE : forall pb PA psz, In (pb, PA, psz) LB -> PA <= D -> D + zlength c <= PA + psz -> pb <> sc_blk x.
  Hypothesis HX : rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs).
  Hypothesis V0 : sc_version x = 0.
  Hypothesis SIG0 : sc_sig x = None.
  Hypothesis XIN : forall b, In b (sct_blocks adr x) -> In b LB.
  Hypothesis XND : List.NoDup (map blk_id (sct_blocks adr x)).
  Hypothesis CPIN : cellA_in LB PIN 8.
  Hypothesis ALP : PIN mod 8 = 0.
  Hypothesis PIND : PIN + 8 <= D \/ D + zlength c <= PIN.
  Hypothesis PINX : PIN + 8 <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= PIN.
  Hypothesis HPIN : rw_cells ctasegs m PIN [C8 (wz (D + p))].

  Local Notation A := (adr (sc_blk x)) (only parsing).
  Definition XPs : list (Z * Z) := [(PIN, PIN + 8); (adr (sc_blk x), adr (sc_blk x) + SCT_SIZE)].
  (* [comment removed for export] *)
  Local Notation oinvS := (oinv sp m Σ LB E lo K c D XPs (-80) ERR_SET_ERROR_STACK (O2I_SIG_COST_A len) O2I_SIG_FRAMES_A).
  Definition sg_frameA : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma ctx_factsA :
    Forall (fun b => 0 <= b < 256) c /\ 0 < D /\ D + zlength c < 2 ^ 63 /\ zlength c < 2 ^ 26 /\ D + zlength c <= ACEIL
    /\ ACEIL <= lo /\ 12365824 <= lo /\ lo <= bv_unsigned sp - O2I_SIG_STACK_A /\ 65536 <= ERR_SET_ERROR_STACK
    /\ bv_unsigned sp + 16 <= USTACK_TOP /\ 0 <= bv_unsigned sp < 2 ^ 64 /\ bv_unsigned sp mod 16 = 0
    /\ Z.of_nat (length (to_bytes c)) = zlength c
    /\ 0 < adr (sc_blk x) /\ adr (sc_blk x) + 104 <= ACEIL /\ (adr (sc_blk x) + 104 <= 65536 \/ 12365824 <= adr (sc_blk x))
    /\ ~ In (sc_blk x) (map blk_id OW) /\ List.NoDup (map blk_id (OW ++ LB))
    /\ (exists bq, In bq LB /\ blk_addr bq <= PIN /\ PIN + 8 <= blk_addr bq + blk_size bq /\ 0 < blk_addr bq /\ blk_addr bq + blk_size bq <= ACEIL
                  /\ (blk_addr bq + blk_size bq <= 65536 \/ 12365824 <= blk_addr bq))
    /\ 0 <= mcost len /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP.
  Proof.
    destruct PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    destruct PAY as (_ & HF' & D0 & D63 & D26 & HB).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A in C1.
    assert (DC' : D + zlength c <= ACEIL).
    { destruct HB as [->|(blk & HBLK & BL1 & BL2)]; [exfalso; revert CNE; cbn; unfold zlength; cbn; lia|].
      pose proof (AH_blk _ _ _ _ blk HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (_ & _ & BB & _). lia. }
    pose proof (AH_blk _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HXIN)) as (BX0 & _ & BX3 & BX4). unfold SCT_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    pose proof (AH_nodup _ _ _ _ HEAP) as ND.
    assert (NOW : ~ In (sc_blk x) (map blk_id OW)).
    { rewrite map_app in ND. intros Hin. exact (NoDup_app_disjoint _ _ _ ND Hin (in_map blk_id _ _ HXIN)). }
    destruct CPIN as (bq & HBQ & Q1 & Q2). pose proof (AH_blk _ _ _ _ bq HEAP ltac:(apply in_app_iff; right; exact HBQ)) as (Q3 & _ & Q4 & Q5).
    assert (VP : 65536 <= ERR_SET_ERROR_STACK) by (unfold ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK; clear; lia).
    pose proof (mcost_mono len len ltac:(clear - LEN0; lia)) as [MC _].
    repeat (split; [first [assumption| (clear - CEIL C1; lia)| (unfold to_bytes, zlength; rewrite length_map; reflexivity)]|]).
    split; [exists bq; repeat (split; [assumption|]); exact Q5|]. split; [exact MC| split; [exact C2| exact C3]].
  Qed.

  Local Ltac ctx := pose proof ctx_factsA as (DF & D0 & D63 & D26 & DCEIL & CEIL & GLO & LO & ESS & TOP & SPR & AL16 & DLEN & BX0 & BXC & BXI & NOW & NDL & CELL & MC0 & SHI & SWIN);
                   unfold O2I_SIG_STACK_A in LO; pose proof SEPD as SEPD'; pose proof PINX as PINX'; unfold SCT_SIZE in SEPD', PINX'.

  (* [comment removed for export] *)
  Lemma KHs : kit_hyps sp LB lo c D XPs (-80) ERR_SET_ERROR_STACK.
  Proof.
    ctx. unfold kit_hyps, XPs. split; [exact DF|]. split; [exact CEIL|]. split; [clear - CEIL GLO; lia|]. split; [clear - LO; lia|].
    split; [clear - ESS; lia|]. split; [clear; lia|]. split; [exact TOP|]. split; [exact AL16|]. split; [reflexivity|].
    split. { constructor; [| constructor; [| constructor]]; cbn [fst snd].
             - destruct CPIN as (bq & HBQ & Q1 & Q2). exists bq. split; [exact HBQ| split; [exact Q1| exact Q2]].
             - exists (sc_blk x, adr (sc_blk x), SCT_SIZE). split; [exact HXIN| cbn; clear; lia]. }
    split. { constructor; [| constructor; [| constructor]]; cbn [fst snd]; right; [clear - PIND| clear - SEPD]; lia. }
    split; [| clear - D0; lia].
    destruct PAY as (_ & _ & _ & _ & _ & [E0|([[pb PA] psz] & H1 & H2 & H3)]); [left; exact E0| right].
    exists pb, PA, psz. cbn [blk_addr blk_size fst snd] in H2, H3. split; [exact H1| split; [exact H2| exact H3]].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac kit L := eapply (L AR sp m Σ LB E lo K c D XPs (-80) ERR_SET_ERROR_STACK (O2I_SIG_COST_A len) O2I_SIG_FRAMES_A KHs).
  Local Ltac kitp L H := pose proof (L AR sp m Σ LB E lo K c D XPs (-80) ERR_SET_ERROR_STACK (O2I_SIG_COST_A len) O2I_SIG_FRAMES_A KHs) as H.

  (* [comment removed for export] *)
  Lemma oinv0 : oinvS Σ st m OW bo [] (O2I_SIG_COST_A len).
  Proof.
    destruct PAY as (HB & _).
    kit @oinv_entry; [| exact KOW| exact KIDS| exact HB].
    unfold O2I_SIG_STACK_A in PRE. replace (- -80 + ERR_SET_ERROR_STACK) with (80 + ERR_SET_ERROR_STACK) by (clear; lia). exact PRE.
  Qed.

  (* [comment removed for export] *)
  Definition site_okA (base R : Z) (rs : rsite) : Prop :=
    (base = 0x3354b4 /\ R = 0x3354bc /\ rs = RS_sig_len4) \/ (base = 0x3355a4 /\ R = 0x3355ac /\ rs = RS_sig_overrun)
    \/ (base = 0x3355c4 /\ R = 0x3355cc /\ rs = RS_sig_nid).

  (* [comment removed for export] *)
  Definition raise_postA (x8 x9 x18 x19 x20 x21 x22 x23 : word) (j : list (bv 8)) (cxs : list cell) (vpin : word) (CX : Z)
      (r : unit * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY boY,
      ms' = MS (mkR (Z_to_bv 64 0x3355fc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x3355fc) fc' None mY (seg_rom ctasegs)
      /\ oinvS ΣY (snd r) mY OWY boY [] (CX - GETOBJ_ERR_COST_A)
      /\ rw_cells ctasegs mY (bv_unsigned sp + -80) (CB 8 j :: sg_frameA)
      /\ rw_cells ctasegs mY (adr (sc_blk x)) cxs /\ rw_cells ctasegs mY PIN [C8 vpin].

  Local Ltac ecu := unfold O2I_SIG_FRAMES_A, O2I_SIG_COST_A, GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A, ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK,
                           ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK, ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK,
                           ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, RT_STACK in *.

  (* [comment removed for export] *)
  Lemma cells_keptA : forall mA mB (NEW : list block) j cxs vpin,
    ax_pres (NEW ++ LB) (bv_unsigned sp + -80) LIBW_A mA mB -> cells_size cxs = 104%nat ->
    (rw_cells ctasegs mA (bv_unsigned sp + -80) (CB 8 j :: sg_frameA) -> rw_cells ctasegs mB (bv_unsigned sp + -80) (CB 8 j :: sg_frameA))
    /\ (rw_cells ctasegs mA (adr (sc_blk x)) cxs -> rw_cells ctasegs mB (adr (sc_blk x)) cxs)
    /\ (rw_cells ctasegs mA PIN [C8 vpin] -> rw_cells ctasegs mB PIN [C8 vpin]).
  Proof.
    intros mA mB NEW j cxs vpin AX SZ. ctx. destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5).
    assert (CLs : forall a, bv_unsigned sp + -80 <= a < bv_unsigned sp -> ax_client (NEW ++ LB) (bv_unsigned sp + -80) LIBW_A a).
    { intros a Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CEIL GLO LO ESS; lia| left; clear - Ha TOP; unfold USTACK_TOP in *; lia]. }
    assert (CLb : forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> (blk_addr b + blk_size b <= 65536 \/ 12365824 <= blk_addr b) ->
                  ax_client (NEW ++ LB) (bv_unsigned sp + -80) LIBW_A a).
    { intros b a Hb Ha Hr. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha Hr; lia|]. right; right. exists b. split; [apply in_app_iff; right; exact Hb| exact Ha]. }
    split; [| split].
    - intros H. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. cbn [cells_size csize Nat.add sg_frameA] in Ha. apply CLs. clear - Ha. lia.
    - intros H. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. rewrite SZ in Ha. cbn in Ha. apply (CLb (sc_blk x, adr (sc_blk x), SCT_SIZE)); [exact HXIN| cbn; unfold SCT_SIZE; clear - Ha; lia| cbn; exact BXI].
    - intros H. eapply rw_cells_agree; [exact AX| exact H|]. intros a Ha. cbn in Ha. apply (CLb bq); [exact HBQ| clear - Ha Q1 Q2; lia| exact Q5].
  Qed.

  (* [comment removed for export] *)
  Lemma uw_at_call : forall ΣX stX mX OWX boX NEW CX j,
    oinvS ΣX stX mX OWX boX NEW CX -> rw_cells ctasegs mX (bv_unsigned sp + -80) (CB 8 j :: sg_frameA) ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras).
  Proof.
    intros until j. intros OI FRx. ctx. pose proof OI as (_ & AXc & _). destruct CELL as (bq & _ & Q1 & Q2 & Q3 & Q4 & _).
    unfold sg_frameA in FRx.
    uw_call_axX_tac m 80 UW AXc FRx;
      [ clear; lia
      | intros a Ha; apply rin_ivs_app in Ha as [Ha|Ha];
        [ unfold XPs, SCT_SIZE in Ha; cbn [rin_ivs fst snd app] in Ha; clear - Ha Q1 Q2 Q4 BXC CEIL LO ESS; lia
        | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb GLO LO ESS; lia ]
      | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac err_call Wc Ec OIc FRc :=
    eapply (@oinv_ap_callA AR UK sp m Σ LB E lo K c D XPs (-80) ERR_SET_ERROR_STACK (O2I_SIG_COST_A len) O2I_SIG_FRAMES_A KHs);
    [ exact Wc | exact OIc | ecu; clear; lia | | ecu; clear; lia
    | eapply uw_at_call; [exact OIc| exact FRc]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ Ec CTX)
    | apply cons_ne
    | ].     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac raise_body Enew rs ndbg :=
    lazymatch goal with
    | OI : oinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?ΣX ?stX ?mX ?OWX ?boX [] ?CX, FRx : rw_cells ctasegs ?mX (bv_unsigned sp + -80) (CB 8 ?j :: _),
      HCx : rw_cells ctasegs ?mX (adr (sc_blk x)) ?cxs, HPx : rw_cells ctasegs ?mX PIN [C8 ?vpin], CXle : GETOBJ_ERR_COST_A <= ?CX,
      SZ : cells_size ?cxs = 104%nat, LF : lit_okA A_CT_OCT_C_A ?fs ?fk _, LN : lit_okA A_O2I_SCT_SIGNATURE_A ?ns ?nk _ |- _ =>
      (* [comment removed for export] *)
      eapply implAp_abind;
      [ apply implAp_from_evt; step; apply evt_done; err_call constr:(ERR_new_walkA boX) Enew OI FRx; [ecu; clear - CXle; lia| reflexivity] |];
      let r1 := fresh "r" in let Σ1 := fresh "Σ" in let ms1 := fresh "ms" in let PO1 := fresh "PO" in
      intros r1 Σ1 ms1 PO1; cbv beta in PO1;
      let mA := fresh "mA" in let OWa := fresh "OWa" in let OIa := fresh "OIa" in let AXa := fresh "AXa" in let bo1 := fresh "bo" in let EBO1 := fresh "EBO" in
      let Ta1 := fresh "FRa" in let Ta2 := fresh "HCa" in let Ta3 := fresh "HPa" in
      destruct PO1 as (?q0 & ?q1 & ?q2 & ?q10 & ?q11 & ?q12 & ?q13 & ?q14 & ?q15 & ?q16 & ?q17 & ?q3 & ?q4 & ?q5 & ?q6 & ?F1 & ?fc1 & mA & OWa & bo1
                        & -> & OIa & AXa & EBO1); subst bo1;
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end;
      destruct (cells_keptA mX mA [] j cxs vpin AXa SZ) as (Ta1 & Ta2 & Ta3); specialize (Ta1 FRx); specialize (Ta2 HCx); specialize (Ta3 HPx);
      clear FRx HCx HPx AXa;
      let OC := fresh "OC" in let STa := fresh "STa" in let MIa := fresh "MIa" in
      kitp @oinv_call OC; pose proof (OC _ _ _ _ _ _ _ OIa) as (_ & STa & _ & _ & _ & _ & MIa & _); clear OC;
      repeat match goal with H : munch _ _ _ |- _ => clear H | H : wmono ctasegs _ _ |- _ => clear H end;
      let MU := fresh "MU" in let WM := fresh "WM" in pose proof (munch_refl (@nil (Z * Z)) mA) as MU; pose proof (wmono_refl ctasegs mA) as WM;
      (* [comment removed for export] *)
      eapply implAp_abind;
      [ apply implAp_from_evt; do ndbg step; apply evt_done;
        err_call constr:(ERR_set_debug_walkA STRCPY rs _ _ boX fs fk ns nk LF LN) constr:(E_dbg) OIa Ta1;
        [ pose proof OIa as (PREa & _); pose proof PREa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa & _); ecu; clear - CRa CXle; lia
        | unfold A_CT_OCT_C_A, A_O2I_SCT_SIGNATURE_A, MallocRep.wz; cbn [rs_line RS_sig_len4 RS_sig_overrun RS_sig_nid]; repeat split; reflexivity ] |];
      let r2 := fresh "r" in let Σ2 := fresh "Σ" in let ms2 := fresh "ms" in let PO2 := fresh "PO" in
      intros r2 Σ2 ms2 PO2; cbv beta in PO2;
      let mB := fresh "mB" in let OWb := fresh "OWb" in let OIb := fresh "OIb" in let AXb := fresh "AXb" in let bo2 := fresh "bo" in let EBO2 := fresh "EBO" in
      let Tb1 := fresh "FRb" in let Tb2 := fresh "HCb" in let Tb3 := fresh "HPb" in
      destruct PO2 as (?p0 & ?p1 & ?p2 & ?p10 & ?p11 & ?p12 & ?p13 & ?p14 & ?p15 & ?p16 & ?p17 & ?p3 & ?p4 & ?p5 & ?p6 & ?F2 & ?fc2 & mB & OWb & bo2
                        & -> & OIb & AXb & EBO2); subst bo2;
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end;
      destruct (cells_keptA mA mB [] j cxs vpin AXb SZ) as (Tb1 & Tb2 & Tb3); specialize (Tb1 Ta1); specialize (Tb2 Ta2); specialize (Tb3 Ta3);
      clear Ta1 Ta2 Ta3 AXb;
      let OC2 := fresh "OC" in let STb := fresh "STb" in let MIb := fresh "MIb" in
      kitp @oinv_call OC2; pose proof (OC2 _ _ _ _ _ _ _ OIb) as (_ & STb & _ & _ & _ & _ & MIb & _); clear OC2;
      repeat match goal with H : munch _ _ _ |- _ => clear H | H : wmono ctasegs _ _ |- _ => clear H end;
      let MU2 := fresh "MU" in let WM2 := fresh "WM" in pose proof (munch_refl (@nil (Z * Z)) mB) as MU2; pose proof (wmono_refl ctasegs mB) as WM2;
      (* [comment removed for export] *)
      eapply implAp_mono;
      [ apply implAp_from_evt; do 4 step; apply evt_done;
        err_call constr:(@ERR_set_error_closedA AR UK BE rs 50 107 boX) constr:(E_err) OIb Tb1;
        [ pose proof OIb as (PREb & _); pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _);
          pose proof OIa as (PREa' & _); pose proof PREa' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRa' & _); ecu; clear - CRa' CRb CXle; lia
        | unfold ERR_LIB_SYS, MallocRep.wz; cbn [rs_code RS_sig_len4 RS_sig_overrun RS_sig_nid]; unfold ERR_LIB_CT; repeat split; first [reflexivity | (clear; lia)] ] |];
      let r3 := fresh "r" in let Σ3 := fresh "Σ" in let ms3 := fresh "ms" in let PO3 := fresh "PO" in
      intros r3 Σ3 ms3 PO3; cbv beta in PO3;
      let mC := fresh "mC" in let OWc := fresh "OWc" in let OIc := fresh "OIc" in let AXc := fresh "AXc" in let boC := fresh "boC" in let EBO3 := fresh "EBO" in
      let Tc1 := fresh "FRc" in let Tc2 := fresh "HCc" in let Tc3 := fresh "HPc" in
      destruct PO3 as (?o0 & ?o1 & ?o2 & ?o10 & ?o11 & ?o12 & ?o13 & ?o14 & ?o15 & ?o16 & ?o17 & ?o3 & ?o4 & ?o5 & ?o6 & ?F3 & ?fc3 & mC & OWc & boC
                        & -> & OIc & AXc & EBO3);
      destruct (cells_keptA mB mC [] j cxs vpin AXc SZ) as (Tc1 & Tc2 & Tc3);
      unfold raise_postA; do 17 eexists; exists mC, OWc, boC;
      split; [match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end; reflexivity|];
      split; [ kit @oinv_credit; [exact OIc| pose proof OIc as (PREc & _); pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _); ecu; clear - CRc CXle; lia]
             | split; [exact (Tc1 Tb1)| split; [exact (Tc2 Tb2)| exact (Tc3 Tb3)]]]
    end.

  Lemma raise_siteA : forall base R rs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (FX : bvmap 5 word) (fcX : bv 32) ΣX stX mX OWX boX CX j cxs vpin,
    site_okA base R rs ->
    oinvS ΣX stX mX OWX boX [] CX -> GETOBJ_ERR_COST_A <= CX ->
    rw_cells ctasegs mX (bv_unsigned sp + -80) (CB 8 j :: sg_frameA) ->
    rw_cells ctasegs mX (adr (sc_blk x)) cxs -> cells_size cxs = 104%nat -> rw_cells ctasegs mX PIN [C8 vpin] ->
    implAp (err_raise rs stX) ΣX (raise_postA sp (Z_to_bv 64 PIN) (Z_to_bv 64 (adr (sc_blk x))) x19 x20 x21 x22 x23 j cxs vpin CX)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PIN) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (adr (sc_blk x))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until vpin. intros SITE OI CXle FRx HCx SZ HPx. ctx.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI) as (HEAPX & _). clear OF.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - SPR GLO LO ESS; lia).
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold err_raise.
    (* [comment removed for export] *)
    destruct (lit_okA_auto A_CT_OCT_C_A 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_O2I_SCT_SIGNATURE_A 18 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    destruct SITE as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
      [ raise_body constr:(E_new42) RS_sig_len4 ltac:(7) | raise_body constr:(E_new58) RS_sig_overrun ltac:(7) | raise_body constr:(E_new51) RS_sig_nid ltac:(6) ].
  Qed.

  Local Notation SPOSTx := (o2i_sig_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (O2I_SIG_COST_A len) adr x vs c D p len PIN) (only parsing).

  (* [comment removed for export] *)
  Lemma fin_raiseA : forall (x1 : sctr bptr) (x19 x20 x21 x22 x23 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX (stX : ap_st bptr) mX OWX boX CX j,
    oinvS ΣX stX mX OWX boX [] CX ->
    rw_cells ctasegs mX (bv_unsigned sp + -80) (CB 8 j :: sg_frameA) ->
    rw_cells ctasegs mX (adr (sc_blk x)) (sct_cells adr x1 (-1) vs) -> rw_cells ctasegs mX PIN [C8 (Z_to_bv 64 (D + p))] ->
    sc_blk x1 = sc_blk x -> sc_logid x1 = sc_logid x -> sc_ext x1 = sc_ext x -> sc_blob x1 = sc_blob x -> sc_version x1 = sc_version x -> sc_sig x1 = None ->
    evt ctasegs (SPOSTx ((x1, -1), stX) ΣX)
      (MS (mkR (Z_to_bv 64 0x3355fc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 PIN) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (adr (sc_blk x))) x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          FX (Z_to_bv 64 0x3355fc) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until j. intros OI FR HC HP E1 E2 E3 E4 E5 E6. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI) as (HEAPX & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    unfold sg_frameA in FR.
    step. do 9 step. release_frame FR STX (bv_unsigned sp). step. step.
    apply evt_done.
    match goal with H : stk ctasegs mX lo (bv_unsigned sp) |- _ => rename H into STF end.
    kitp @pre_resp PR. destruct (PR _ _ _ _ _ _ _ OI STF) as (PREF & AXF & CRF & BKF & _ & _). clear PR.
    unfold o2i_sig_postA, MallocRep.wz. cbn [fst snd app].
    do 14 eexists. exists FX, fcX, mX, OWX, boX, adr, (@nil block). cbn [app].
    split; [reflexivity|]. split; [exact PREF|]. split; [unfold XPs in AXF; exact AXF|]. split; [exact CRF|]. split; [exact BKF|].
    split; [intros b Hb; reflexivity|]. split; [constructor|].
    split; [exact HC|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    cbn [Z.leb]. split; [reflexivity|]. split; [reflexivity|]. split; [exact E6| exact HP].
  Qed.

  (* [comment removed for export] *)
  Lemma set1_tail_nzA : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FN : bvmap 5 word) (fcN : bv 32) ΣN mN (pn : bptr) (C : Z) junk,
    let siglen := u16be c (p + 2) in let xS := set_algs (znth c p) (znth c (p + 1)) x in
    siglen <= len - 4 -> siglen <> 0 -> sct_nid xS <> NID_undef -> 0 < C -> C + siglen <= ACEIL ->
    oinvS ΣN st mN OW bo [(pn, C, siglen)] (O2I_SIG_COST_A len - mcost siglen) ->
    rw_cells ctasegs mN (bv_unsigned sp + -80) (CB 8 junk :: sg_frameA) ->
    rw_cells ctasegs mN PIN [C8 (Z_to_bv 64 (D + p))] ->
    rw_cells ctasegs mN (adr (sc_blk x)) (set_sig_cells adr xS (-1) C siglen) ->
    rw_cells ctasegs mN C [CB (Z.to_nat siglen) (to_bytes (slice c (p + 4) siglen))] ->
    evt ctasegs (SPOSTx ((set_sig (Some (pn, siglen)) xS, len - (len - 4 - siglen)), st) ΣN)
      (MS (mkR (Z_to_bv 64 0x33563c) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 PIN) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 (len - 4)) (Z_to_bv 64 (D + p + 4)) (Z_to_bv 64 siglen)
               (Z_to_bv 64 (Z.shiftr PIN 3 + SHB)) (Z_to_bv 64 (2 ^ 64 - 4)) s8 s9 s10 s11 t3 t4 t5 t6)      (* [comment removed for export] *)
          FN (Z_to_bv 64 0x33563c) fcN None mN (seg_rom ctasegs)).
  Proof.
    intros until junk. cbv zeta. intros SLE ZP NIDOK C0 CC OI5 FR HPn HCN BLKN. ctx.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.
    set (siglen := u16be c (p + 2)) in *. set (xS := set_algs (znth c p) (znth c (p + 1)) x) in *.
    pose proof (u16be_range c (p + 2)) as SR. pose proof (znth_range8 c p DF) as R0. pose proof (znth_range8 c (p + 1) DF) as R1.
    pose proof (mcost_mono siglen len ltac:(clear - SLE SR; subst siglen; lia)) as [_ MCle].
    destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5). frz BXI. frz Q5. frz SEPD'. frz PINX'. frz PIND. frz SEPD. frz PINX.
    assert (HBQ' : In bq (OW ++ LB)) by (apply in_app_iff; right; exact HBQ).
    assert (EPIN : bv_unsigned (Z_to_bv 64 PIN) = PIN) by (apply unsigned_lit; clear - Q1 Q2 Q3 Q4 SWIN; alia).
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI5) as (_ & STN & _ & _ & _ & _ & MIN & _). clear OC.
      kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI5) as (HEAP5 & ND5 & _ & FRESH5 & DJL5 & _). clear OF.
      pose proof (proj2 (AH_acc _ _ _ _ bq HEAP5 ltac:(apply in_app_iff; right; right; exact HBQ))) as ACCQ. pose proof (AH_offsh _ _ _ _ bq HEAP5 ltac:(apply in_app_iff; right; right; exact HBQ)) as OFFQ.
      pose proof (munch_refl [(PIN, PIN + 8)]%Z mN) as MU. pose proof (wmono_refl ctasegs mN) as WM.
      assert (OFF : offshW [(PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ.
      unfold MallocRep.wz.
      change (frozen (rw_cells ctasegs mN (adr (sc_blk x)) (set_sig_cells adr xS (-1) C siglen))) in HCN.
      change (frozen (rw_cells ctasegs mN C [CB (Z.to_nat siglen) (to_bytes (slice c (p + 4) siglen))])) in BLKN.
      (* [comment removed for export] *)
      step. step. if_cases K1; zc K1; [exfalso; apply K1; reflexivity|]. clear K1.
      step. setreg 20%Z (Z_to_bv 64 (D + p + 4 + siglen)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL ZP SLE SR; subst siglen; lia); bv_solve).
      step. step. setreg 10%Z (Z_to_bv 64 (len - (len - 4 - siglen)))
        ltac:(rewrite (unsigned_lit siglen) by (clear - SR; lia); try rewrite (unsigned_lit (2 ^ 64 - 4)) by (clear; lia);
              change 18446744073709551612 with (2 ^ 64 - 4); rewrite CtSctP.W_o2i_sig.subw_m4 by (clear - SR; lia); f_equal; clear; lia).   (* [comment removed for export] *)
      step. name_mem m6. unfold frozen in HCN, BLKN.
      match goal with H : munch _ mN m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs mN m6 |- _ => rename H into WM6 end.
      assert (OI6 : oinvS ΣN st m6 OW bo [(pn, C, siglen)] (O2I_SIG_COST_A len - mcost siglen)).
      { kit @oinv_munch; [exact OI5| exact MU6| exact WM6| exact MIN| exact STN|].
        constructor; [| constructor]. right; left. exists (PIN, PIN + 8). split; [unfold XPs; cbn; tauto| cbn [fst snd]; clear; lia]. }
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU6)) in HCN; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha PINX'; unfold frozen in *; lia].
      pose proof (DJL5 (pn, C, siglen) bq ltac:(left; reflexivity) HBQ) as DJQ. cbn [blk_addr blk_size fst snd] in DJQ.
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU6)) in BLKN; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - SR; lia); cbn [outside]; clear - Ha DJQ Q1 Q2; lia].
      unfold sg_frameA in FR. do 9 step. release_frame FR STN (bv_unsigned sp). step. step.
      apply evt_done.
      match goal with H : stk ctasegs m6 lo (bv_unsigned sp) |- _ => rename H into STF end.
      kitp @pre_resp PR. destruct (PR _ _ _ _ _ _ _ OI6 STF) as (PREF & AXF & CRF & BKF & FRF & LBF). clear PR.
      pose proof (FRF (pn, C, siglen) ltac:(left; reflexivity)) as NPN. cbn [blk_id fst snd] in NPN. rewrite map_app in NPN.
      assert (NPL : ~ In pn (map blk_id LB)) by (intros Hin; apply NPN; apply in_app_iff; right; exact Hin).
      unfold o2i_sig_postA, MallocRep.wz. cbn [fst snd].
      do 14 eexists. exists FN, fcN, m6, OW, bo, (fun b => if bptr_eqb b pn then C else adr b), [(pn, C, siglen)].
      split; [reflexivity|]. split; [exact PREF|]. split; [unfold XPs in AXF; exact AXF|]. split; [clear - CRF MCle; ecu; lia|]. split; [exact BKF|].
      split. { intros b Hb. rewrite (bptr_eqb_neq (blk_id b) pn); [reflexivity|]. intros E0. apply NPL. rewrite <- E0. apply in_map. exact Hb. }
      split; [exact LBF|].
      split. { cbn [Z.leb]. replace (len - (len - 4 - siglen) <=? 0) with false by (symmetry; apply Z.leb_gt; clear - ZP SR; subst siglen; lia).
               rewrite (CtSctP.W_o2i_sig.set_sig_cells_rec LB adr x XIN xS pn C siglen (-1)); [exact HCN| reflexivity| reflexivity| reflexivity| reflexivity| exact NPL]. }
      subst xS; cbn [sc_blk sc_logid sc_ext sc_blob sc_version sc_sig sc_siglen sc_ts sc_extlen sc_hash sc_sigalg set_sig set_algs Z.leb fst snd]. repeat (split; [first [reflexivity| (clear - SLE ZP SR; subst siglen; lia)]|]).
      replace (len - (len - 4 - siglen) <=? 0) with false by (symmetry; apply Z.leb_gt; clear - ZP SR; lia).
      split; [clear; lia|]. split; [clear - SLE; lia|].
      split. { match goal with H : rw_cells ctasegs m6 PIN [C8 ?v] |- _ => replace (Z_to_bv 64 (D + p + (len - (len - 4 - siglen)))) with v; [exact H| apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL ZP SLE SR; subst siglen; lia); bv_solve] end. }
      repeat (split; [first [reflexivity| (clear - R0 R1; lia)]|]).
      split; [revert NIDOK; unfold sct_nid; cbn [sc_version sc_hash sc_sigalg set_sig set_algs]; rewrite V0; intros X; exact X|].
      rewrite bptr_eqb_refl. split; [reflexivity|]. split; [clear - ZP SR; lia|]. split; [rewrite map_app; exact NPN| exact BLKN].
  Qed.

  Local Notation SPOST := (o2i_sig_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (O2I_SIG_COST_A len) adr x vs c D p len PIN) (only parsing).

  Theorem sig_mainA : forall (tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tp = wz TP_A ->
    implAp (o2i_sct_signature x c p len st) Σ SPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (adr (sc_blk x))) (wz PIN) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz O2I_SCT_SIGNATURE_A) fc None m (seg_rom ctasegs)).
  Proof.
    intros until t6. intros TP. ctx. subst tp.
    pose proof (conj SHI (conj SWIN TOP)) as CN. unfold SHHI, STACK_WIN, USTACK_TOP in CN.   (* [comment removed for export] *)
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & CRED & FRM).
    pose proof PAY as (HB & _).
    pose proof oinv0 as OI0.
    unfold o2i_sct_signature. rewrite V0. cbn [negb Z.eqb].
    unfold O2I_SCT_SIGNATURE_A, MallocRep.wz.
    pose proof HX as HC. unfold CtSctP.SctRep.sct_cells in HC. rewrite V0, SIG0 in HC.
    cbn [CtSctP.SctRep.u32 Z.modulo optr sc_siglen Z.pow_pos Pos.iter Z.mul] in HC. unfold MallocRep.wz in HC.
    unfold MallocRep.wz in HPIN.
    pose proof ALX as ALX'.
    assert (EA : bv_unsigned (Z_to_bv 64 (adr (sc_blk x))) = adr (sc_blk x)) by (apply unsigned_lit; clear - BX0 BXC SWIN; alia).
    assert (EPIN : bv_unsigned (Z_to_bv 64 PIN) = PIN) by (destruct CELL as (bq & _ & Q1 & Q2 & Q3 & Q4 & _); apply unsigned_lit; clear - Q1 Q2 Q3 Q4 SWIN; alia).
    assert (HXIN' : In (sc_blk x, adr (sc_blk x), 104) (OW ++ LB)) by (apply in_app_iff; right; exact HXIN).
    assert (HXIN'' : In (sc_blk x, adr (sc_blk x), SCT_SIZE) (OW ++ LB)) by (apply in_app_iff; right; exact HXIN).
    ablock HEAP HXIN' ACCX OFFX.
    destruct CELL as (bq & HBQ & Q1 & Q2 & Q3 & Q4 & Q5).
    frz BXI. frz Q5. frz SEPD'. frz PINX'. frz PIND. frz SEPD. frz PINX.
    assert (HBQ' : In bq (OW ++ LB)) by (apply in_app_iff; right; exact HBQ).
    pose proof (proj2 (AH_acc _ _ _ _ bq HEAP HBQ')) as ACCQ. pose proof (AH_offsh _ _ _ _ bq HEAP HBQ') as OFFQ.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]%Z) by (cbn [offshW]; clear - CEIL LO ESS SHI; alia).
    apply implAp_from_evt.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 11 step.
    (* [comment removed for export] *)
    step. step. step. step. ab_shload 4. step. rewrite ?zxb_z8, ?sxb_z8. step. first [if_false | if_true]. step.
    step. if_cases KV; zc KV; [| exfalso; apply KV; reflexivity]. clear KV.
    name_mem m1.
    assert (OI1 : oinvS Σ st m1 OW bo [] (O2I_SIG_COST_A len)).
    { kit @oinv_munch; [exact OI0| exact MU| exact WM| exact MI| exact ST| constructor; [left; cbn [fst snd]; clear - LO ESS; lia| constructor]]. }
    (* [comment removed for export] *)
    step. step. if_cases KL; zc KL.
    2: { (* [comment removed for export] *)
      replace (len <=? 4) with true by (symmetry; apply Z.leb_le; clear - KL; lia).
      apply evt_done. eapply implAp_abind.
      { eapply (raise_siteA 0x3354b4 0x3354bc RS_sig_len4); [left; repeat split; reflexivity| exact OI1| ecu; clear - MC0; lia| exact FR| exact HC| reflexivity| exact HPIN]. }
      intros r ΣF msF RP. unfold raise_postA in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & boF & -> & OIF & FRF & HCF & HPF).
      cbn [fst snd]. apply implAp_aret_evt.
      eapply (fin_raiseA x); [exact OIF| exact FRF| | exact HPF| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact SIG0].
      unfold CtSctP.SctRep.sct_cells. rewrite V0, SIG0. cbn [CtSctP.SctRep.u32 Z.modulo optr sc_siglen Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz. exact HCF. }
    (* [comment removed for export] *)
    replace (len <=? 4) with false by (symmetry; apply Z.leb_gt; clear - KL; lia).
    pose proof PAY as (_ & _ & _ & _ & _ & [E0|(bd & HBD & BD1 & BD2)]); [exfalso; rewrite E0 in CNE; unfold zlength in CNE; cbn in CNE; clear - CNE; lia|].
    assert (HBD' : In bd (OW ++ LB)) by (apply in_app_iff; right; exact HBD).
    pose proof (AH_blk _ _ _ _ bd HEAP HBD') as (BD0 & _ & BD3 & BD4). frz BD4.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI1) as (HEAP1 & _). clear OF. cbn [app] in HEAP1.
    clear ACCX OFFX ACCQ OFFQ MU WM OFF.
    ablock HEAP1 HXIN' ACCX OFFX. ablock HEAP1 HBQ' ACCQ OFFQ. ablock HEAP1 HBD' ACCD OFFD.
    pose proof OI1 as (_ & _ & _ & _ & _ & HB1 & _).
    pose proof (munch_refl [(adr (sc_blk x) + 64, adr (sc_blk x) + 66)]%Z m1) as MU. pose proof (wmono_refl ctasegs m1) as WM.
    assert (OFF : offshW [(adr (sc_blk x) + 64, adr (sc_blk x) + 66)]%Z) by (cbn [offshW]; clear - OFFX; unfold SHLO, SHHI in *; lia). clear OFFX OFFQ OFFD.
    assert (BY : forall i, 0 <= i < zlength c -> CtWire.byte c i = znth c i).
    { intros i Hi. unfold CtWire.byte, u8. apply Z.mod_small. pose proof (znth_range8 c i DF). clear - H Hi; lia. }
    pose proof (znth_range8 c p DF) as R0. pose proof (znth_range8 c (p + 1) DF) as R1.
    step. step. step. step. ab_shload 1.
    pose proof (payload_readA m1 D c p (wa (D + p)) HB1 DF ltac:(clear - P0 PL KL LEN0; lia) eq_refl) as RD. step. clear RD.
    step. rewrite ?zxb_z8, ?sxb_z8. if_false.
    (* [comment removed for export] *)
    unfold frozen in SEPD', PINX', BXI.   (* [comment removed for export] *)
    step. step. rewrite le1_zxb. mem_after_store.       (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    step. step. ab_shload 1.
    pose proof (payload_readA _ D c (p + 1) (wa (D + p + 1)) HB1 DF ltac:(clear - P0 PL KL LEN0; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
    step. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. rewrite le1_zxb. mem_after_store. frz SEPD'. frz PINX'. frz BXI.
    (* [comment removed for export] *)
    step. step. name_mem m2.
    match goal with H : munch _ m1 m2 |- _ => rename H into MU2 end. match goal with H : wmono ctasegs m1 m2 |- _ => rename H into WM2 end.
    assert (OI2 : oinvS Σ st m2 OW bo [] (O2I_SIG_COST_A len)).
    { kit @oinv_munch; [exact OI1| exact MU2| exact WM2| exact MI| exact ST|].
      constructor; [| constructor]. right; left. exists (adr (sc_blk x), adr (sc_blk x) + SCT_SIZE). split; [unfold XPs; cbn; tauto| cbn [fst snd]; unfold SCT_SIZE; clear; lia]. }
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI2) as (HEAP2 & _). clear OF. cbn [app] in HEAP2.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - SPR GLO LO ESS; lia).
    (* [comment removed for export] *)
    assert (RV : ro_cells ctasegs m2 (adr (sc_blk x) + SCTO_VERSION) [C4 (Z_to_bv 64 (CtSctP.SctRep.u32 0))]).
    { unfold SCTO_VERSION. rewrite Z.add_0_r. exact (proj1 (proj1 (proj1 (SctRepA.rw_cells_app ctasegs _ _ [C4 (Z_to_bv 64 (CtSctP.SctRep.u32 0))] _) HC))). }
    assert (RA : ro_cells ctasegs m2 (adr (sc_blk x) + SCTO_ALGS) [C1 (Z_to_bv 8 (znth c p)); C1 (Z_to_bv 8 (znth c (p + 1)))]).
    { unfold SCTO_ALGS.
      lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
        pose proof (proj2 (proj1 (SctRepA.rw_cells_app ctasegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8] _) HC)) as HA9; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HA9;
        exact (proj1 (proj1 (proj1 (SctRepA.rw_cells_app ctasegs _ _ [c9; c10] _) HA9))) end. }
    eapply evt_cut.
    { eapply (SCT_get_signature_nid_specA) with (Σ := Σ) (OW := OW) (LB := LB) (lo := lo) (xb := sc_blk x) (A := adr (sc_blk x)) (v := CtSctP.SctRep.u32 0);
        [exact HEAP2| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; clear - LO ESS; lia| exact HXIN'' | exact ALX| exact RV| exact RA
        | left; reflexivity| exact R0| exact R1| reflexivity]. }
    intros ms' PO. unfold leaf16A_post, leafA_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & _).
    rewrite (ret_pc_even 0x33554c) by (clear; lia).
    change (CtSctP.SctRep.u32 0) with 0. cbn [Z.eqb].
    unfold sct_nid. cbn [sc_version sc_hash sc_sigalg set_algs]. rewrite V0, !BY by (clear - P0 PL KL LEN0; lia).
    set (nid := sig_nid 0 (znth c p) (znth c (p + 1))) in *.
    assert (NR : 0 <= nid <= 794).
    { subst nid. unfold sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption.
      destruct ((0 =? 0) && (znth c p =? 4)); [destruct (znth c (p + 1) =? 3); [| destruct (znth c (p + 1) =? 1)]|]; clear; lia. }
    set (xS := set_algs (znth c p) (znth c (p + 1)) x) in *.
    assert (OI3 : oinvS Σ st m3 OW bo [] (O2I_SIG_COST_A len)).
    { kit @oinv_munch; [exact OI2| exact MU3| exact WM3| exact MI3| exact ST3|]. constructor; [left; cbn [fst snd]; clear - LO ESS; lia| constructor]. }
    assert (OUT3 : forall a, (bv_unsigned sp + -80 <= a \/ a < lo) -> outside [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)]%Z a)
      by (intros a Ha; cbn [outside]; clear - Ha LO ESS; lia).
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in FR; [| intros a Ha; apply OUT3; cbn in Ha; clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in HC; [| intros a Ha; apply OUT3; cbn in Ha; clear - Ha BXC CEIL; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in HPIN; [| intros a Ha; apply OUT3; cbn in Ha; clear - Ha Q1 Q2 Q4 CEIL; lia].
    assert (HCS : rw_cells ctasegs m3 (adr (sc_blk x)) (sct_cells adr xS (-1) vs)).
    { subst xS. unfold CtSctP.SctRep.sct_cells. cbn [sc_version sc_hash sc_sigalg set_algs sc_blk sc_blob sc_logid sc_ts sc_ext sc_extlen sc_sig sc_siglen sc_bloblen].
      rewrite V0, SIG0. cbn [CtSctP.SctRep.u32 Z.modulo optr Z.pow_pos Pos.iter Z.mul]. unfold MallocRep.wz. exact HC. }
    clear OFF MU2 WM2 ACCX ACCQ ACCD HEAP1 HEAP2 RV RA.
    pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    step. if_cases KN; zc KN.
    { (* [comment removed for export] *)
      replace (nid =? NID_undef) with true by (symmetry; apply Z.eqb_eq; unfold NID_undef; revert KN; rewrite ?unsigned_lit by (clear -NR; lia); clear; lia).
      apply evt_done. eapply implAp_abind.
      { eapply (raise_siteA 0x3355c4 0x3355cc RS_sig_nid); [right; right; repeat split; reflexivity| exact OI3| ecu; clear - MC0; lia| exact FR| exact HCS| apply Nat2Z.inj; rewrite CtSctP.SctRep.sct_cells_size; reflexivity| exact HPIN]. }
      intros r ΣF msF RP. unfold raise_postA in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & boF & -> & OIF & FRF & HCF & HPF).
      cbn [fst snd]. apply implAp_aret_evt.
      eapply (fin_raiseA xS); [exact OIF| exact FRF| exact HCF| exact HPF| reflexivity| reflexivity| reflexivity| reflexivity| subst xS; cbn; exact eq_refl| subst xS; cbn; exact SIG0]. }
    (* [comment removed for export] *)
    assert (NIDOK : nid <> NID_undef) by (unfold NID_undef; revert KN; rewrite ?unsigned_lit by (clear - NR; lia); clear; lia).
    replace (nid =? NID_undef) with false by (symmetry; apply Z.eqb_neq; exact NIDOK). clear KN.
    kitp @oinv_facts OF. pose proof (OF _ _ _ _ _ _ _ OI3) as (HEAP3 & _). clear OF. cbn [app] in HEAP3.
    ablock HEAP3 HBQ' ACCQ OFFQ. ablock HEAP3 HBD' ACCD OFFD. clear OFFQ OFFD.
    pose proof OI3 as (_ & _ & _ & _ & _ & HB3 & _).
    pose proof (znth_range8 c (p + 2) DF) as R2. pose proof (znth_range8 c (p + 3) DF) as R3.
    step. step. step. ab_shload 1.
    pose proof (payload_readA _ D c (p + 2) (wa (D + p + 2)) HB3 DF ltac:(clear - P0 PL KL LEN0; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth c (p + 2))) by (clear - R2; lia).
    (* [comment removed for export] *)
    lazymatch goal with H : absh_ok ?b _ _ |- _ => ab_join 12%Z 13%Z 3364220%Z H end.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D c (p + 3) (wa (D + p + 3)) HB3 DF ltac:(clear - P0 PL KL LEN0; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth c (p + 3))) by (clear - R3; lia).
    step. step. step.
    setreg 21%Z (Z_to_bv 64 (u16be c (p + 2)))
      ltac:(unfold u16be; rewrite !BY by (clear - P0 PL KL LEN0; lia); replace (p + 2 + 1) with (p + 3) by (clear; lia); f_equal;
            rewrite (unsigned_lit (znth c (p + 2))), (unsigned_lit (znth c (p + 3))) by (clear - R2 R3; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2 ^ 8) with 256;
            rewrite (unsigned_lit (znth c (p + 2) * 256)) by (clear - R2; lia); symmetry; apply CtSctP.W_o2i_sig.lor_shl8; clear - R2 R3; lia).
    pose proof (u16be_range c (p + 2)) as SR.
    step. setreg 20%Z (Z_to_bv 64 (D + p + 4)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL KL; lia); bv_solve).
    step. setreg 23%Z (Z_to_bv 64 (2 ^ 64 - 4)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL KL; lia); bv_solve).
    step. setreg 19%Z (Z_to_bv 64 (len - 4)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL KL D26; lia); bv_solve).
    step. if_cases KO; zc KO.
    2: { (* [comment removed for export] *)
      replace (len - 4 <? u16be c (p + 2)) with true by (symmetry; apply Z.ltb_lt; clear - KO; lia).
      apply evt_done. eapply implAp_abind.
      { eapply (raise_siteA 0x3355a4 0x3355ac RS_sig_overrun); [right; left; repeat split; reflexivity| exact OI3| ecu; clear - MC0; lia| exact FR| exact HCS| apply Nat2Z.inj; rewrite CtSctP.SctRep.sct_cells_size; reflexivity| exact HPIN]. }
      intros r ΣF msF RP. unfold raise_postA in RP.
      destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & boF & -> & OIF & FRF & HCF & HPF).
      cbn [fst snd]. apply implAp_aret_evt.
      eapply (fin_raiseA xS); [exact OIF| exact FRF| exact HCF| exact HPF| reflexivity| reflexivity| reflexivity| reflexivity| subst xS; cbn; exact eq_refl| subst xS; cbn; exact SIG0]. }
    (* [comment removed for export] *)
    assert (SLE : u16be c (p + 2) <= len - 4) by (clear - KO; lia). clear KO.
    replace (len - 4 <? u16be c (p + 2)) with false by (symmetry; apply Z.ltb_ge; clear - SLE; lia).
    set (siglen := u16be c (p + 2)) in *.
    subst xS. cbn [sc_sig set_algs afree_opt option_map]. rewrite SIG0. cbn [abind apbind aret afree_opt option_map fst snd].
    set (xS := set_algs (znth c p) (znth c (p + 1)) x) in *.
    kitp @oinv_call OC. pose proof (OC _ _ _ _ _ _ _ OI3) as (_ & ST3' & _ & _ & _ & _ & _ & CS3 & _ & CR3 & _). clear OC.
    step. step. step. step.
    destruct (Z.eq_dec siglen 0) as [Z0|ZP].
    - (* [comment removed for export] *)
      rewrite Z0. cbn [Z.ltb abind apbind aret fst snd]. replace (len - (len - 4 - 0)) with 4 by (clear; lia).
      apply evt_done. eapply implAp_step_same.
      { eapply (SCT_set1_signature_zero_cpsA) with (lo := lo) (OW := OW) (LB := LB) (adr := adr) (x := xS) (et := -1) (vs := vs) (P := D + p + 4) (ras := bv_unsigned ra :: ras);
          [exact HEAP3| rewrite ESP; exact ST3| exact CEIL| rewrite ESP; unfold SCT_SET1_SIGNATURE_STACK_A, CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK; ecu; clear - LO; lia
          | rewrite ESP; clear - TOP; unfold USTACK_TOP in *; lia| rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia
          | exact MI3| reflexivity| exact CS3| exact HXIN''| exact HCS| subst xS; cbn; exact SIG0| subst xS; cbn; exact ALX| reflexivity| reflexivity| first [reflexivity| rewrite Z0; reflexivity]
          | rewrite ESP; eapply uw_at_call; [exact OI3| exact FR]
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_set1 CTX)]. }
      intros msS PO. unfold set1sig_zero_postA in PO. rewrite ?ESP in PO.
      destruct PO as (v0' & v1' & v2' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & v3' & v4' & v5' & v6' & FS & fcS & m4 & -> & MI4 & ST4 & AG4 & HEAP4 & CS4 & HC4).
      rewrite (ret_pc_even 0x33563c) by (clear; lia). rewrite Z.ltb_irrefl. cbn [abind apbind aret fst snd]. change (sc_blk xS) with (sc_blk x) in *.
      assert (OI4 : oinvS Σ st m4 OW bo [] (O2I_SIG_COST_A len - 0)).
      { kit @oinv_heap; [exact OI3| | | cbn [app]; exact HEAP4| constructor| exact MI4| exact ST4| clear; lia| clear - CR3; lia].
        - eapply agree_on_mono; [exact AG4|]. intros a [Ha Hx]. split; [exact Ha|]. intros Hin. apply Hx. unfold XPs. cbn [rin_ivs fst snd]. right; left. exact Hin.
        - intros b [Hb|Hb]; apply in_app_iff; [left| right]; exact Hb. }
      rewrite Z.sub_0_r in OI4. unfold apres_but in AG4.
      apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; split; [left; clear - Ha TOP; unfold USTACK_TOP in *; lia| clear - Ha CEIL LO ESS BXC; unfold SCT_SIZE; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HPIN; [| intros a Ha; cbn in Ha; split; [right; right; exists bq; split; [exact HBQ'| clear - Ha Q1 Q2; lia]| clear - Ha PINX'; unfold frozen in *; unfold SCT_SIZE; lia]].
      clear HCS HC ACCQ ACCD MU WM HEAP3.
      ablock HEAP4 HBQ' ACCQ OFFQ.
      pose proof (munch_refl [(PIN, PIN + 8)]%Z m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
      assert (OFF : offshW [(PIN, PIN + 8)]%Z) by (cbn [offshW]; clear - OFFQ Q1 Q2; unfold SHLO, SHHI in *; lia). clear OFFQ.
      apply implAp_aret_evt. unfold MallocRep.wz.
      change (frozen (rw_cells ctasegs m4 (adr (sc_blk x)) (set_sig_cells adr xS (-1) 0 0))) in HC4.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      step. step. if_cases K1; zc K1; [exfalso; apply K1; reflexivity|]. clear K1.
      step. step. step. setreg 10%Z (Z_to_bv 64 4) ltac:(apply bv_eq; vm_compute; reflexivity).
      step. name_mem m5. unfold frozen in HC4.
      match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
      assert (OI5 : oinvS Σ st m5 OW bo [] (O2I_SIG_COST_A len)).
      { kit @oinv_munch; [exact OI4| exact MU5| exact WM5| exact MI4| exact ST4|].
        constructor; [| constructor]. right; left. exists (PIN, PIN + 8). split; [unfold XPs; cbn; tauto| cbn [fst snd]; clear; lia]. }
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU5)) in HC4; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha PINX'; unfold frozen in *; lia].
      do 9 step. release_frame FR ST4 (bv_unsigned sp). step. step.
      apply evt_done.
      match goal with H : stk ctasegs m5 lo (bv_unsigned sp) |- _ => rename H into STF end.
      kitp @pre_resp PR. destruct (PR _ _ _ _ _ _ _ OI5 STF) as (PREF & AXF & CRF & BKF & _ & _). clear PR.
      unfold o2i_sig_postA, MallocRep.wz. cbn [fst snd app].
      do 14 eexists. exists FS, fcS, m5, OW, bo, adr, (@nil block). cbn [app].
      split; [reflexivity|]. split; [exact PREF|]. split; [unfold XPs in AXF; exact AXF|]. split; [exact CRF|]. split; [exact BKF|].
      split; [intros b Hb; reflexivity|]. split; [constructor|].
      split; [subst xS; unfold CtSctP.SctRep.sct_cells, CtSctP.W_sct_set1_signature.set_sig_cells in HC4 |- *; cbn [sc_blk sc_logid sc_ext sc_blob sc_version sc_sig sc_siglen sc_ts sc_extlen sc_hash sc_sigalg set_sig set_algs Z.leb fst snd] in HC4 |- *; cbn [optr CtSctP.SctRep.u32 osz32 CtSctP.SctRep.logid_len Z.leb] in HC4 |- *; exact HC4|].
      subst xS; cbn [sc_blk sc_logid sc_ext sc_blob sc_version sc_sig sc_siglen sc_ts sc_extlen sc_hash sc_sigalg set_sig set_algs Z.leb fst snd]. repeat (split; [first [reflexivity| (clear - KL SLE Z0; lia)]|]).
      split. { match goal with H : rw_cells ctasegs m5 PIN [C8 ?v] |- _ => replace (Z_to_bv 64 (D + p + 4)) with v; [exact H| apply bv_eq; rewrite ?unsigned_lit by (clear - D0 D63 P0 PL KL; lia); bv_solve] end. }
      repeat (split; [first [reflexivity| (clear - R0 R1; lia)]|]).
      split; [unfold sct_nid; cbn [sc_version sc_hash sc_sigalg set_sig set_algs]; rewrite V0; exact NIDOK| reflexivity].
    - (* [comment removed for export] *)
      replace (0 <? siglen) with true by (symmetry; apply Z.ltb_lt; clear - ZP SR; subst siglen; lia). cbn [abind apbind amalloc aret fst snd].
      apply evt_done.
      assert (SRC : bytes_at ctasegs m3 (D + p + 4) (to_bytes (slice c (p + 4) siglen))).
      { unfold slice, to_bytes. rewrite <- firstn_map, <- skipn_map. fold (to_bytes c). apply bytes_at_firstn.
        replace (D + p + 4) with (D + Z.of_nat (Z.to_nat (p + 4))) by (clear - P0; lia). apply bytes_at_skipn; [exact HB3|]. apply Nat2Z.inj_le. rewrite DLEN. clear - P0 PL KL SLE SR; lia. }
      assert (SLEN : length (to_bytes (slice c (p + 4) siglen)) = Z.to_nat siglen) by (unfold to_bytes; rewrite length_map; apply slice_length; clear - P0 PL KL SLE SR ZP; lia).
      pose proof (mcost_mono siglen len ltac:(clear - SLE SR; lia)) as [_ MCle].
      eapply (SCT_set1_signature_walkA) with (lo := lo) (OW := OW) (LB := LB) (adr := adr) (x := xS) (et := -1) (vs := vs) (bsrc := bd)
                                              (P := D + p + 4) (n := siglen) (src := to_bytes (slice c (p + 4) siglen)) (ras := bv_unsigned ra :: ras);
        [exact HEAP3| rewrite ESP; exact ST3| exact CEIL| rewrite ESP; unfold SCT_SET1_SIGNATURE_STACK_A, CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK; ecu; clear - LO; lia
        | rewrite ESP; clear - TOP; unfold USTACK_TOP in *; lia| rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia
        | exact MI3| reflexivity| exact CS3| exact HXIN''| exact HCS| subst xS; cbn; exact SIG0| subst xS; cbn; exact ALX
        | exact HBD'| apply (PAYNE (blk_id bd) (blk_addr bd) (blk_size bd)); [destruct bd as [[? ?] ?]; exact HBD| exact BD1| exact BD2]
        | clear - BD1 P0; lia| clear - BD2 PL SLE KL; lia| exact SRC| exact SLEN| reflexivity| reflexivity| reflexivity| clear - ZP SR; subst siglen; lia
        | ecu; clear - CR3 MCle; lia
        | rewrite ESP; eapply uw_at_call; [exact OI3| exact FR]
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_set1 CTX)|].
      intros pn ΣN msN FRESHN PON. unfold oalloc_postA in PON. rewrite ?ESP in PON.
      destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & FN & fcN & mN & C
                       & -> & MIN & STN & AGN & CRN & BRN & HEAPN & ACCN & (BLKN & SRCN & HCN)).
      rewrite (ret_pc_even 0x33563c) by (clear; lia). change (sc_blk xS) with (sc_blk x) in *. unfold apres_but in AGN.
      pose proof BRN as (C0 & C16 & _ & CC & CI).
      assert (OI5 : oinvS ΣN st mN OW bo [(pn, C, siglen)] (O2I_SIG_COST_A len - mcost siglen)).
      { kit @oinv_allocX; [exact OI3| | cbn [app]; exact HEAPN| exact MIN| exact STN| exact CRN| ecu; clear - CR3 MCle MC0 SLE SR ZP; pose proof (mcost_mono 0 siglen ltac:(subst siglen; lia)); unfold mcost in H at 1; cbn in H; lia].
        eapply agree_on_mono; [exact AGN|]. cbn [app]. intros a [Ha Hx]. split; [exact Ha|]. intros Hin. apply Hx. unfold XPs. cbn [rin_ivs fst snd]. right; left. exact Hin. }
      apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; cbn in Ha; split; [left; clear - Ha TOP; unfold USTACK_TOP in *; lia| clear - Ha CEIL LO ESS BXC; unfold SCT_SIZE; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HPIN; [| intros a Ha; cbn in Ha; split; [right; right; exists bq; split; [exact HBQ'| clear - Ha Q1 Q2; lia]| clear - Ha PINX'; unfold frozen in *; unfold SCT_SIZE; lia]].
      cbn [apbind aret fst snd]. apply implAp_ret_evt. unfold MallocRep.wz.
      rewrite ?EPIN. eapply set1_tail_nzA; [exact SLE| exact ZP| subst nid; unfold sct_nid; cbn [sc_version sc_hash sc_sigalg set_algs]; rewrite V0; exact NIDOK| exact C0| exact CC| exact OI5| exact FR| exact HPIN| exact HCN| exact BLKN].
  Qed.


  End Act.

  (* [comment removed for export] *)
  Definition o2i_sct_signature_specA' (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
           (lo : Z) (K : list block) (ras : list Z)
           (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z),
      ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRM -> tp = wz TP_A ->
      uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx O2I_SCT_SIGNATURE_A (bv_unsigned ra :: ras) -> ras <> nil ->
      (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
      payload_okA m LB D c -> 0 < zlength c -> 0 <= p -> 0 <= len -> p + len <= zlength c ->
      In (sc_blk x, adr (sc_blk x), SCT_SIZE) LB -> adr (sc_blk x) mod 16 = 0 -> (D + zlength c <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= D) ->
      (forall pb PA psz, In (pb, PA, psz) LB -> PA <= D -> D + zlength c <= PA + psz -> pb <> sc_blk x) ->
      rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) ->
      sc_version x = 0 -> sc_sig x = None -> (forall b, In b (sct_blocks adr x) -> In b LB) -> List.NoDup (map blk_id (sct_blocks adr x)) ->
      cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (PIN + 8 <= D \/ D + zlength c <= PIN) -> (PIN + 8 <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= PIN) ->
      rw_cells ctasegs m PIN [C8 (wz (D + p))] ->
      a0 = wz (adr (sc_blk x)) -> a1 = wz PIN -> a2 = wz len ->
      implAp (o2i_sct_signature x c p len st) Σ
             (o2i_sig_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr x vs c D p len PIN)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz O2I_SCT_SIGNATURE_A) fc None m (seg_rom ctasegs)).

  Theorem o2i_sct_signature_walkA : o2i_sct_signature_specA' O2I_SIG_STACK_A O2I_SIG_COST_A O2I_SIG_FRAMES_A.
  Proof.
    unfold o2i_sct_signature_specA'. intros until PIN.
    intros PRE TP UW CTX NE KOW KIDS PAY CNE P0 LEN0 PL HXIN ALX SEPD PAYNE HX V0 SIG0 XIN XND CPIN ALP PIND PINX HPIN -> -> ->.
    eapply sig_mainA; eassumption.
  Qed.
End Proofs.
End WithRT.
