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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim CtSizes.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_err_newA W_err_set_debugA W_err_vsetA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_item_d2i_exA W_item_d2i_tailA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColBudgetA ColDefsA CtlStmtA W_bufmemA W_collectA W_d2iA_stmt W_d2iA_exprim_ctx W_d2iA_exprim_tail W_d2iA_exprim_call.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_asn1_stringA ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Open Scope am_scope.
(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac unhide H := unfold hidden in H.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.
Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.
Notation payload_readA := CtRepA.W_get_object_walkA.payload_readA.

(* [comment removed for export] *)
Definition EX_C2I : Z := 0x241df4.          (* [comment removed for export] *)
Definition EX_FC_TEST : Z := 0x242518.      (* [comment removed for export] *)
Definition EX_TNEW_RA : Z := 0x2424f0.      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation E_ex_tnew := (E_asn1_d2i_ex_primitive_244f68 : uk_call 0x24187c 0x2424f0 0x224b04).    (* [comment removed for export] *)

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
  Hypothesis CSTB : 15 * len + 2 ^ 19 <= CST len.

  Local Ltac ctx := pose proof (exo_ctx STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPAL SPAH STKB)
                      as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & LO0 & LO & ESS & TOP & SPR & DLEN & ESPA & G1 & G2 & G3 & G4 & Ef & G5 & FSH & SHR1 & SHR2
                          & (bd & Hbd & BD1 & BD2 & BD3 & BD4 & BD5 & OD) & (bq & Hbq & BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & OQ)
                          & (bv & Hbv & BV1 & BV2 & BV3 & BV4 & BV5 & OV) & (bt & Hbt & BT1 & BT2 & BT3 & BT4 & BT5 & OT));
                    unfold off_fr in OD, OQ, OV, OT; change (fs_size 2) with 256 in OD, OQ, OV, OT; cbn [blk_addr blk_size fst snd] in OD, OQ, OV, OT.
  Local Notation POST := (exprim_oct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr OPP PV TLC).
  Local Notation linv := (exo_inv STK CST FRMb sp LB E lo K D d OPP PV TLC f spa Σ1).
  Local Notation pbs := (exo_pbs f).
  Local Notation XP := (exo_XP OPP PV TLC f).
  (* [comment removed for export] *)
  Local Ltac kitp L q1 q2 mr0 H :=   (* [comment removed for export] *)
    pose proof (L sp mr0 Σ1 (exo_pbs f q1 q2 ++ LB) E lo K d D (exo_XP OPP PV TLC f) (spa - bv_unsigned sp) (STK - ADEP_FRAME) (CST len - 1) (FRMb - 1)
                  (exo_KH STK CST FRMb sp m Σ st OW LB E bo lo D d OPP PV TLC j31 f spa PRE0 CELLS LEN1 FRESH GEO SPA32 SPAL SPAH STKB q1 q2)) as H.

  (* [comment removed for export] *)
  Lemma exo_new_off : forall qfc qb mr ΣX stX mX OWX boX NEW CX,
    linv qfc qb mr ΣX stX mX OWX boX NEW CX -> forall b, In b NEW -> off_fr f 2 b.
  Proof.
    intros until CX. intros LI b Hb. pose proof LI as (PREX & _ & _ & _ & _ & _ & _ & LBOK). pose proof PREX as (HEAPX & _).
    pose proof (proj1 (Forall_forall _ _) LBOK b Hb) as OK.
    pose proof (@AH_adopt (push AR f 2) _ _ _ _ b HEAPX ltac:(apply in_or_app; left; exact Hb) OK) as H'.
    exact (@AH_ow_off_fr (push AR f 2) _ _ _ _ f 2%nat b H' (or_introl eq_refl) (or_introl eq_refl)).
  Qed.

  (* [comment removed for export] *)
  Definition exo_frw (iv : Z * Z) : Prop :=
    (spa <= fst iv /\ snd iv <= bv_unsigned sp) \/ (f + 32 <= fst iv /\ snd iv <= f + 40) \/ (shad f + 4 <= fst iv /\ snd iv <= shad f + 5).

  Lemma exo_inv_frw : forall qfc qb mr ΣX stX mX OWX boX NEW CX mY W,
    linv qfc qb mr ΣX stX mX OWX boX NEW CX ->
    munch W mX mY -> wmono ctasegs mX mY -> mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    Forall exo_frw W ->
    linv qfc qb mr ΣX stX mY OWX boX NEW CX.
  Proof.
    intros until W. intros LI MU WM MIY STY HW. ctx.
    kitp (@oinv_facts (push AR f 2)) qfc qb mr OFc. pose proof (OFc _ _ _ _ _ _ _ LI) as (HEAPN & ND3 & BND & FRSH & DJL & DJO). clear OFc.
    pose proof (exo_new_off _ _ _ _ _ _ _ _ _ _ LI) as OFN.
    pose proof LI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    pose proof PREX as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16 & MI0 & CRED & FRM').
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + (spa - bv_unsigned sp))) = spa) by (replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact ESPA).
    (* [comment removed for export] *)
    assert (OUTW : forall a, (a < BnHeapA.ACEIL /\ (a < SHLO \/ SHHI <= a) /\ (a + 1 <= f \/ f + 256 <= a)) \/ bv_unsigned sp <= a
                             \/ (f + 64 <= a < f + 65) \/ (f + 80 <= a < f + 112) -> outside W a).
    { intros a Ha. clear - Ha HW CEIL LO ESS SPAL SPAH SHR1 SHR2 CL2 G3 FSH. induction W as [|[x y] W IH]; cbn [outside]; [exact I|].
      apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)]. unfold exo_frw in H1. cbn [fst snd] in H1. unfold SHLO, SHHI in Ha. plia. }
    assert (BLKW : forall b a, In b (OWX ++ NEW ++ exo_pbs f qfc qb ++ LB) -> blk_addr b <= a < blk_addr b + blk_size b -> outside W a).
    { intros b a Hb Hr. apply OUTW. pose proof (BND b Hb) as (_ & _ & R3 & _).
      pose proof (@AH_offsh (push AR f 2) _ _ _ _ b HEAP Hb) as RO.
      apply in_app_iff in Hb as [Hb|Hb]; [| apply in_app_iff in Hb as [Hb|Hb]; [| apply in_app_iff in Hb as [Hb|Hb]]].
      - pose proof (@AH_ow_off_fr (push AR f 2) _ _ _ _ f 2%nat b HEAP (or_introl eq_refl) Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. left. clear - Hr R3 RO O. plia.
      - pose proof (OFN b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. left. clear - Hr R3 RO O. plia.
      - unfold exo_pbs in Hb. destruct Hb as [<-|[<-|[]]]; cbn [blk_addr blk_size fst snd] in Hr; [right; right; left; clear - Hr; lia| right; right; right; clear - Hr; lia].
      - pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. left. clear - Hr R3 RO O. plia. }
    assert (AGL : agree_on (lib_addr OWX) mX mY).
    { eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. intros a [HS|(b & Hb & Hr)].
      - apply OUTW. left. pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. unfold SHLO. clear - HA CL1 CL2 G4. lia.
      - apply (BLKW b a); [apply in_app_iff; left; exact Hb| exact Hr]. }
    assert (HEAPY : @BnHeapA.AHEAP (push AR f 2) ΣX OWX (NEW ++ exo_pbs f qfc qb ++ LB) mY).
    { eapply (@AH_frame_frSA (push AR f 2) ΣX OWX _ mX mY W f 2%nat (or_introl eq_refl) HEAP MU WM).
      - eapply Forall_impl; [| exact HW]. intros [x y] H1. unfold exo_frw in H1. cbn [fst snd] in H1.
        destruct H1 as [H1|[H1|H1]].
        + left. left. cbn [fst snd]. clear - H1 CEIL LO ESS SPAL TOP. plia.
        + right. left. cbn [fst snd]. change (fs_size 2) with 256. clear - H1. lia.
        + right. right. cbn [fst snd]. change (fs_size 2 / 8) with 32. clear - H1. lia.
      - intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [left; exact (OFN b Hb)|]. apply in_app_iff in Hb as [Hb|Hb]; [| left; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))].
        right. eapply Forall_impl; [| exact HW]. intros [x y] H1 [X1 X2]. unfold exo_frw in H1. cbn [fst snd] in H1, X1, X2 |- *. change (fs_size 2 / 8) with 32 in X2.
        assert (SH : shad (f + 64) = shad f + 8 /\ shad (f + 64 + (1 - 1)) = shad f + 8 /\ shad (f + 80) = shad f + 10 /\ shad (f + 80 + (32 - 1)) = shad f + 13)
          by (unfold shad; clear - G2; Z.div_mod_to_equations; lia).
        unfold exo_pbs in Hb. destruct Hb as [<-|[<-|[]]]; cbn [blk_addr blk_size fst snd]; destruct SH as (S1 & S2 & S3 & S4); rewrite ?S1, ?S2, ?S3, ?S4;
          (destruct H1 as [H1|[H1|H1]]; [right; clear - H1 SHR2 CL2 CEIL LO ESS SPAL; plia| clear - H1 X1 X2 FSH; lia| left; clear - H1; lia]). }
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ODs).
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [| split; [exact CR| exact LBOK]]]]]]].
    - unfold ap_preA. split; [exact HEAPY|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGL)|]. split; [exact IDS|].
      split; [exact (data_cells_agree _ _ _ _ DC AGL ODs)|]. split; [rewrite ESP; exact STY|]. split; [exact CEIL'|]. split; [exact LOSP|]. split; [exact TOP'|].
      split; [exact AL16|]. split; [exact MIY|]. split; [exact CRED| exact FRM'].
    - eapply ax_pres_trans; [exact AX|]. unfold ax_pres. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|].
      intros a [_ Ha]. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [apply OUTW; right; left; clear - Ha; lia| apply OUTW; left; pose proof (client_static_below a Ha) as HA; unfold SHLO; clear - HA CL1 CL2 G4; lia|].
      apply (BLKW b a); [apply in_app_iff; right; apply in_app_iff; right; exact Hb| exact Hr].
    - eapply CtRepP.ApErrKit.kept_trans; [exact KP|]. intros a Ha Hin. apply MU. unfold wa. rewrite unsigned_lit by exact Ha.
      destruct Hin as (b & Hb & Hr). exact (BLKW b a ltac:(apply in_app_iff; left; exact (KO b Hb)) Hr).
    - eapply bytes_at_agree; [exact (agree_on_of_munch_nw _ _ _ MU)| exact HB|]. intros a Ha. rewrite DLEN in Ha. apply (BLKW bd a); [apply in_app_iff; right; apply in_app_iff; right; apply in_or_app; right; exact Hbd| clear - Ha BD1 BD2; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition exo_lowE (j0 j8 j16 j64 j72 j80 : list byte) : list cell :=      (* [comment removed for export] *)
    [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 (f + 64)); C8 (Z_to_bv 64 (Z.shiftr OPP 3 + SHB)); C8 (Z_to_bv 64 PV); C8 (Z_to_bv 64 (f + 80)); C8 (Z_to_bv 64 OPP);
     CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f)].
  (* [comment removed for export] *)
  Definition exo_lowF (j0 j8 j64 j72 j80 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 (Z.shiftr PV 3 + SHB)); C8 (Z_to_bv 64 (f + 64)); C8 (Z_to_bv 64 (Z.shiftr OPP 3 + SHB)); C8 (Z_to_bv 64 PV); C8 (Z_to_bv 64 (f + 80)); C8 (Z_to_bv 64 OPP);
     CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f)].

  (* [comment removed for export] *)
  Definition c2i_post (qfc qb : bptr) (mr mX : mem) (stX : ap_st bptr) (NEW : list block) (CXY CV L PEND fcv : Z) (bufc : list cell)
      (j0 j8 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (bi bc : byte) (vpl : word) (vb : byte)
      (p : bptr) (ΣY : rts RT) (ms' : machine_state) : Prop :=
    exists (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x28 x29 x30 x31 : word) (FY : bvmap 5 word) (fcY : bv 32) mY (A : Z) (OWX : list block) (boX : Z * Z),
      (* [comment removed for export] *)
      ms' = MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 (Z_to_bv 64 CV) x12 (Z_to_bv 64 A) x14 x15 x16 x17
                     (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 L) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 L) (Z_to_bv 64 (f + 64))
                     (Z_to_bv 64 (f + 32)) x28 x29 x30 x31)
               FY (Z_to_bv 64 EX_FC_TEST) fcY None mY (seg_rom ctasegs)
      /\ bv_unsigned x10 = fcv
      /\ linv qfc qb mr ΣY stX mY OWX boX ((p, A, ASN1_STRING_SIZE) :: NEW) CXY
      /\ ~ In p (map blk_id (OWX ++ NEW ++ pbs qfc qb ++ LB)) /\ ablock_range A ASN1_STRING_SIZE /\ A mod 16 = 0
      /\ rw_cells ctasegs mY A (asn1_string_cells 0 V_ASN1_OCTET_STRING 0 0)
      /\ uw_chain USTACK_TOP mY spa (bv_unsigned sp) (bv_unsigned ra :: ras)
      /\ rw_cells ctasegs mY spa (exo_lowF j0 j8 j64 j72 j80)
      /\ rw_cells ctasegs mY (spa + 96) [C8 (Z_to_bv 64 PEND)] /\ rw_cells ctasegs mY (spa + 104) [CB 6 j104]
      /\ rw_cells ctasegs mY (spa + 110) [C1 bi] /\ rw_cells ctasegs mY (spa + 111) [C1 bc] /\ rw_cells ctasegs mY (spa + 112) [C8 vpl]
      /\ rw_cells ctasegs mY (spa + 120) [CB 4 j120; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING)]
      /\ rw_cells ctasegs mY (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] /\ rw_cells ctasegs mY (bv_unsigned sp + -16) [C8 s0; C8 ra]
      /\ rw_cells ctasegs mY (f + 32) [C8 (Z_to_bv 64 CV)] /\ rw_cells ctasegs mY (f + 64) [C1 (Z_to_bv 8 fcv)] /\ rw_cells ctasegs mY (f + 80) bufc
      /\ rw_cells ctasegs mY OPP [C8 (Z_to_bv 64 D)] /\ rw_cells ctasegs mY PV [C8 (Z_to_bv 64 A)] /\ rw_cells ctasegs mY TLC [C1 vb; CB 31 jt]
      /\ (forall b cs, In b NEW -> rw_cells ctasegs mX (blk_addr b) cs -> Z.of_nat (cells_size cs) <= blk_size b -> rw_cells ctasegs mY (blk_addr b) cs).
  (* [comment removed for export] *)

  Lemma exo_c2i : forall qfc qb mr ΣX stX mX OWX boX NEW CX (REST : bptr -> AM (option (CtModel.octet bptr)))
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x27 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      (CV L PEND fcv : Z) (bufc : list cell) (j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (bi bc : byte) (vpl : word) (vb : byte),
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mr ->
    linv qfc qb mr ΣX stX mX OWX boX NEW CX -> 1 <= CX ->
    uw_chain USTACK_TOP mX spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
    0 <= L < 2 ^ 31 -> 0 <= CV < 2 ^ 64 -> 0 <= fcv < 256 -> Z.of_nat (cells_size bufc) = 32 ->
    rw_cells ctasegs mX spa (exo_lowE j0 j8 j16 j64 j72 j80) ->
    rw_cells ctasegs mX (spa + 96) [C8 (Z_to_bv 64 PEND)] -> rw_cells ctasegs mX (spa + 104) [CB 6 j104] ->
    rw_cells ctasegs mX (spa + 110) [C1 bi] -> rw_cells ctasegs mX (spa + 111) [C1 bc] -> rw_cells ctasegs mX (spa + 112) [C8 vpl] ->
    rw_cells ctasegs mX (spa + 120) [CB 4 j120; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING)] ->
    rw_cells ctasegs mX (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] -> rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells ctasegs mX (f + 64) [C1 (Z_to_bv 8 fcv)] -> rw_cells ctasegs mX (f + 80) bufc ->
    rw_cells ctasegs mX OPP [C8 (Z_to_bv 64 D)] -> rw_cells ctasegs mX PV [C8 (Z_to_bv 64 0)] -> rw_cells ctasegs mX TLC [C1 vb; CB 31 jt] ->
    (forall p ΣY ms', c2i_post qfc qb mr mX stX NEW CX CV L PEND fcv bufc j0 j8 j64 j72 j80 j104 j120 j128 j136 j144 jt bi bc vpl vb p ΣY ms' -> @implAp (push AR f 2) _ (REST p stX) ΣY POST ms') ->
    @implAp (push AR f 2) _ ((blk <- amalloc SZ_ASN1_STRING ;; REST blk) stX) ΣX POST
      (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 ITEM_OCTET_A) (Z_to_bv 64 CV) (Z_to_bv 64 L) x26 x27 x28 x29 x30 x31)
          FX (Z_to_bv 64 EX_C2I) fcX None mX (seg_rom ctasegs)).      (* [comment removed for export] *)
  Proof.
    intros until vb. intros AGFr LI HCX UWX LR CVR FCR BSZ FRLA F96 F104 F110 F111 F112 F120 FRLB FRH HFC HBUF HOPP HPV HTLC HK. ctx.
    pose proof PRE0 as (HEAP & _).
    pose proof CELLS as (_ & _ & _ & _ & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & _).
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    kitp (@oinv_call (push AR f 2)) qfc qb mr OC. kitp (@oinv_facts (push AR f 2)) qfc qb mr OFc.
    pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & LOX & _ & _ & MIX & CSX & ASX & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STX, LOX by (clear; lia).
    pose proof (OFc _ _ _ _ _ _ _ LI) as (_ & NDX & BND & FRSH & DJL & DJO).
    pose proof (exo_new_off _ _ _ _ _ _ _ _ _ _ LI) as OFN.
    (* [comment removed for export] *)
    destruct (@AH_fr_wr (push AR f 2) _ _ _ _ f 2%nat HEAPX (or_introl eq_refl)) as [WF WS]. change (fs_size 2 - 8) with 248 in WF. change (fs_size 2 / 8) with 32 in WS.
    destruct (wr_at_rw_CB mX f 248 WF ltac:(clear; lia)) as [jf FRF]. destruct (wr_at_rw_CB mX (shad f) 32 WS ltac:(clear; lia)) as [js FRS]. clear WF WS.
    change (Z.to_nat 248) with 248%nat in FRF. change (Z.to_nat 32) with 32%nat in FRS.
    apply (rw_cells_split_CB ctasegs _ _ [] 248 _ [] [32; 8; 208]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
    apply (rw_cells_split_CB ctasegs _ _ [] 32 _ [] [4; 1; 27]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
    lazymatch type of FRF with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in FRF end.
    apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [HCONT _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HCONT.
    replace (f + Z.of_nat 32) with (f + 32) in HCONT by (clear; lia).
    lazymatch type of FRS with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in FRS end.
    apply rw_cells_app in FRS as [_ FRS]. apply rw_cells_app in FRS as [HSH4 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HSH4.
    replace (shad f + Z.of_nat 4) with (shad f + 4) in HSH4 by (clear; lia). destruct (cb_byteA _ _ _ HSH4) as [sb4 HSH4']. clear HSH4. rename HSH4' into HSH4.
    (* [comment removed for export] *)
    destruct (@item_cellsA_octet (push AR f 2) _ _ _ _ HEAPX) as (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT). unfold ITEM_OCTET_A in *.
    replace (5535264 + 8) with 5535272 in IT8, IT8L by reflexivity. replace (5535264 + 16) with 5535280 in IT16 by reflexivity. replace (5535264 + 32) with 5535296 in IT32 by reflexivity.
    hide DOV. hide DOT. hide DVT. hide DOD. hide DVD. hide DTD. hide OD. hide OQ. hide OV. hide OT. hide BD5. hide BQ5. hide BV5. hide BT5. hide G5.
    unfold exo_lowE, EX_C2I, MallocRep.wz in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(spa, spa + 168); (shad f + 4, shad f + 5); (f + 32, f + 40)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    freeze HOPP. freeze HPV. freeze HTLC. freeze HFC. freeze HBUF. freeze FRH.
    apply implAp_from_evt.
    step. step. rewrite ?(sx32_small ApPrim.V_ASN1_OCTET_STRING), ?(sx32_small CtSizes.V_ASN1_OCTET_STRING) by (unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING; clear; lia). step.
    (* [comment removed for export] *)
    name_mem m8b. match goal with H : munch _ mX m8b |- _ => rename H into MU8b end. match goal with H : wmono ctasegs mX m8b |- _ => rename H into WM8b end.
    assert (ACCIT' : acc ctasegs m8b 5535264 56).
    { eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU8b)| exact ACCIT|]. intros i Hi. cbn [outside fst snd].
      unhide G5. unfold shad, SHB. clear - Hi G5 G4 CL2 CEIL LO ESS SPAL. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(spa, spa + 168); (f + 32, f + 40)]%Z m8b) as MUb. clear ACCIT.
    assert (OFFW : offshW [(spa, spa + 168); (f + 32, f + 40)]%Z).
    { unhide G5. cbn [offshW]. unfold SHLO, SHHI. clear - G5 CL2 CEIL LO ESS SPAL. lia. }
    (* [comment removed for export] *)
    step. step. step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. if_cases KA; zc KA; [| exfalso; unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING in KA; rewrite ?land64_neg_small, ?land64_pos_small in KA by (clear; lia); clear - KA; lia]. clear KA.
    step. step.
    (* [comment removed for export] *)
    unfold ApPrim.V_ASN1_OCTET_STRING, CtSizes.V_ASN1_OCTET_STRING. step. step. step. if_false.
    step. step. step. zstep.
    name_mem m9. match goal with H : mem_inv ctasegs m9 |- _ => pose proof (jt_ex_prim_octA m9 H) as JT end.
    step. clear JT. rewrite (sx32_small 1898084) by (clear; lia).   (* [comment removed for export] *) step. step.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit L) by (clear - LR; lia). rewrite Z.add_0_r, (bk_swrap32_small L) by (clear - LR; lia). if_false.
    step. step. if_true. step. step. if_true.
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
      let pt := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
      eapply (evt_cut segs (fun ms => exists vt : word, ms = MS (tset pt vt R) F (Z_to_bv 64 0x2424a8) fc rv mm ro)) end.   (* [comment removed for export] *)
    { step. step. if_cases K14; zc K14.
      - step. step. if_cases K12; zc K12; [apply evt_done; eexists; map_cbv_set; reflexivity|]. step. step. if_true. apply evt_done; eexists; map_cbv_set; reflexivity.
      - step. step. if_true. step. step. if_cases K12; zc K12; [apply evt_done; eexists; map_cbv_set; reflexivity|]. step. step. if_true. apply evt_done; eexists; map_cbv_set; reflexivity. }
    intros ms1 (vt & ->). map_cbv_set.
    (* [comment removed for export] *)
    match goal with H : stk ctasegs m9 lo _ |- _ => rename H into ST9 end. match goal with H : mem_inv ctasegs m9 |- _ => rename H into MI9 end. rewrite ?ESPA in ST9.
    pose proof MU8b as MU09.
    assert (OFFLB_ : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    assert (LI9 : linv qfc qb mr ΣX stX m9 OWX boX NEW CX).
    { eapply (exo_inv_frw qfc qb mr); [exact LI| exact MU8b| exact WM8b| exact MI9| exact ST9|].
      constructor; [left; cbn [fst snd]; clear - SPAH; lia|]. constructor; [right; right; cbn [fst snd]; clear; lia|]. constructor; [right; left; cbn [fst snd]; clear; lia| constructor]. }
    (* [comment removed for export] *)
    pose proof (AH_offsh _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as ROQ. pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV.
    pose proof (AH_offsh _ _ _ _ bt HEAP (in_or_app _ _ _ (or_intror Hbt))) as ROT. unfold SHLO, SHHI in ROQ, ROV, ROT.
    thaw HPV. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8b)) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unhide OV; clear - Ha BV1 BV2 BV4 OV ROV SHR1 SHR2 CEIL LO ESS SPAL; plia].
    thaw HOPP. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8b)) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unhide OQ; clear - Ha BQ1 BQ2 BQ4 OQ ROQ SHR1 SHR2 CEIL LO ESS SPAL; plia].
    thaw HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8b)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; unhide OT; clear - Ha BT1 BT2 BT4 OT ROT SHR1 SHR2 CEIL LO ESS SPAL; plia].
    thaw HFC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8b)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha FSH G3 CEIL LO ESS SPAL; plia].
    thaw HBUF. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8b)) in HBUF; [| intros a Ha; rewrite BSZ in Ha; cbn [outside fst snd]; clear - Ha FSH G3 CEIL LO ESS SPAL; plia].
    thaw FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU8b)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH SHR2 CL2 G3 CEIL LO ESS SPAL; plia].
    freeze HPV. freeze HOPP. freeze HTLC. freeze HFC. freeze HBUF. freeze FRH.
    clear MU8b WM8b MUb LI.
    pose proof (OC _ _ _ _ _ _ _ LI9) as (HEAP9 & _). 
    assert (EPV : bv_unsigned (Z_to_bv 64 PV) = PV) by (apply unsigned_lit; clear - BV1 BV2 BV3 BV4 CL3; unfold BnHeapA.ACEIL in *; lia).
    pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ bv HEAP9 ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hbv))) as ACCV.
    pose proof (munch_refl [(spa, spa + 96)]%Z m9) as MU. pose proof (wmono_refl ctasegs m9) as WM.
    assert (OFFW2 : offshW [(spa, spa + 96)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CL2 CEIL LO ESS SPAL; lia).
    thaw HPV.
    (* [comment removed for export] *)
    step. rewrite ?EPV. step. step. step.
    step. step. step. if_true.
    name_mem ma.
    match goal with H : munch _ m9 ma |- _ => rename H into MUa end. match goal with H : wmono ctasegs m9 ma |- _ => rename H into WMa end.
    match goal with H : stk ctasegs ma lo _ |- _ => rename H into STa end. match goal with H : mem_inv ctasegs ma |- _ => rename H into MIa end. rewrite ?ESPA in STa.
    (* [comment removed for export] *)
    step. step. apply evt_done.
    assert (LIa : linv qfc qb mr ΣX stX ma OWX boX NEW CX).
    { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LI9| exact MUa| exact WMa| exact MIa| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STa|].
      constructor; [left; cbn [fst snd]; clear - SPAH CEIL LO ESS SPAL; lia| constructor]. }
    pose proof (OC _ _ _ _ _ _ _ LIa) as (HEAPa & _ & _ & _ & _ & _ & _ & CSa & _).
    (* [comment removed for export] *)
    destruct (bptr_fresh (map blk_id (OWX ++ NEW ++ pbs qfc qb ++ LB))) as [qc Hqc].
    assert (HEAPc : @BnHeapA.AHEAP (push AR f 2) ΣX OWX ((qc, f + 32, 8) :: NEW ++ pbs qfc qb ++ LB) ma).
    { apply (@frame_obj_open (push AR f 2) ΣX OWX _ ma f 2%nat qc (f + 32) 8 (or_introl eq_refl) HEAPa); [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqc|].
      - eapply (acc_of_shadow_cells ma (shad f + 4) _ 0 (f + 32) 8 HSH4); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
          | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [pose proof (OFN b Hb) as O| apply in_app_iff in Hb as [Hb|Hb]; [| pose proof (OFFLB_ b Hb) as O]].
        + unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia.
        + unfold exo_pbs in Hb. destruct Hb as [<-|[<-|[]]]; unfold blk_apart; cbn [blk_addr blk_size fst snd]; clear; lia.
        + unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    assert (UWa : uw_chain USTACK_TOP ma spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { (* [comment removed for export] *)
      eapply uw_chain_agree16; [exact UWX|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU09)|].
      intros a Ha; cbv beta in Ha; cbn [outside fst snd]; clear - Ha SPAH SHR2 CL2 G3 CEIL LO ESS SPAL; plia. }
    unfold abind, amalloc. cbn [apbind].
    eapply (@ASN1_STRING_type_new_walkA (push AR f 2) UK BE) with (lo := lo) (ty := 4); rewrite ?ESPA;
      [exact HEAPc| exact STa| exact CEIL| unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LOX STKB KC1; unfold ADEP_FRAME in *; lia
      | clear - TOP SPAH; lia| clear - SPA32; Z.div_mod_to_equations; lia| exact MIa| reflexivity| exact CSa| reflexivity| clear; lia
      | exact UWa| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_tnew CTX)|].
    intros p Σb msb NIp POb.
    destruct POb as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Fb & fcb & mb & A & -> & MIb & STb & AGb & CRb & BRA & HEAPb & ACCA & CELLb).
    cbn [apbind fst snd]. rewrite ?ESPA in *. unfold EX_TNEW_RA. rewrite (ret_pc_even 0x2424f0) by (clear; lia). cbn [ar_RT push amb] in CRb.
    pose proof BRA as (BA0 & BA16 & _ & BAC & BAS). change (@BnHeapA.ACEIL (push AR f 2)) with (@BnHeapA.ACEIL AR) in BAC.
    (* [comment removed for export] *)
    assert (HEAPb' : @BnHeapA.AHEAP (push AR f 2) Σb ((p, A, 24) :: OWX) (NEW ++ pbs qfc qb ++ LB) mb).
    { eapply (@frame_obj_close (push AR f 2)); [left; reflexivity| exact HEAPb|]. unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 2) with 256. clear; lia. }
    assert (LIb : linv qfc qb mr Σb stX mb OWX boX ((p, A, ASN1_STRING_SIZE) :: NEW) (CX - 0)).
    { kitp (@oinv_alloc (push AR f 2)) qfc qb mr OA. unfold ASN1_STRING_SIZE. eapply OA; [exact LIa| | exact HEAPb'| exact MIb| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STb| change (mcost 24) with 0 in CRb; cbn [ar_RT push amb]; clear - CRb; lia| clear - HCX; lia].
      replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia). eapply agree_on_mono; [exact AGb|].
      intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
      apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left; exact Hb| right; right; exact Hb]. }
    replace (CX - 0) with CX in LIb by (clear; lia). clear HEAPb HEAPc.
    assert (NIp' : ~ In p (map blk_id (OWX ++ NEW ++ pbs qfc qb ++ LB))) by (intros X; apply NIp; rewrite map_app in X |- *; cbn [map app]; apply in_app_iff in X as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]).
    (* [comment removed for export] *)
    assert (AGS : forall A0 cs, rw_cells ctasegs ma A0 cs -> spa <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs mb A0 cs).
    { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact AGb| exact HC|]. intros a Ha. left. clear - Ha H1 H2. lia. }
    apply AGS in FRLA; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F96; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in F104; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F110; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in F111; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F112; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in F120; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
    apply AGS in FRLB; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
    Local Ltac blkb AGb H b MEM RNG := apply (rw_cells_agree _ _ _ _ _ AGb) in H; [| intros a Ha; cbn in Ha; right; right; exists b; split; [MEM| cbn [blk_addr blk_size fst snd]; RNG]].
    thaw FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH; lia].
    apply AGS in FRH; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AGS.
    thaw HOPP. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LO ESS SPAL; lia].
    blkb AGb HOPP bq ltac:(apply in_or_app; right; right; apply in_or_app; right; apply in_or_app; right; exact Hbq) ltac:(clear - Ha BQ1 BQ2; lia).
    blkb AGb HPV bv ltac:(apply in_or_app; right; right; apply in_or_app; right; apply in_or_app; right; exact Hbv) ltac:(clear - Ha BV1 BV2; lia).
    thaw HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LO ESS SPAL; lia].
    blkb AGb HTLC bt ltac:(apply in_or_app; right; right; apply in_or_app; right; apply in_or_app; right; exact Hbt) ltac:(clear - Ha BT1 BT2; lia).
    thaw HFC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LO ESS SPAL; plia].
    blkb AGb HFC (qfc, f + 64, 1) ltac:(apply in_or_app; right; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity) ltac:(clear - Ha; lia).
    thaw HBUF. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HBUF; [| intros a Ha; rewrite BSZ in Ha; cbn [outside fst snd]; clear - Ha G3 CEIL LO ESS SPAL; plia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HBUF; [| intros a Ha; rewrite BSZ in Ha; right; right; exists (qb, f + 80, 32); split; [apply in_or_app; right; right; apply in_or_app; right; apply in_or_app; left; right; left; reflexivity| cbn; clear - Ha; lia]].
    blkb AGb HCONT (qc, f + 32, 8) ltac:(apply in_or_app; right; left; reflexivity) ltac:(clear - Ha; lia).
    assert (UWb : uw_chain USTACK_TOP mb spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply uw_chain_agree16; [exact UWa|]. eapply agree_on_mono; [exact AGb|]. intros a Ha. cbv beta in Ha. left. clear - Ha SPAH. lia. }
    (* [comment removed for export] *)
    assert (KEEPb : forall b cs, In b NEW -> rw_cells ctasegs mX (blk_addr b) cs -> Z.of_nat (cells_size cs) <= blk_size b -> rw_cells ctasegs mb (blk_addr b) cs).
    { intros b cs Hb H SZ. pose proof (BND b ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)) as (B0 & _ & B3 & _).
      pose proof (@AH_offsh (push AR f 2) _ _ _ _ b HEAPX ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)) as RO. unfold SHLO, SHHI in RO.
      pose proof (OFN b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O.
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU09)) in H; [| intros a Ha; cbn [outside fst snd]; clear - Ha SZ B3 RO O SHR1 SHR2 CEIL LO ESS SPAL; plia].
      eapply rw_cells_agree; [exact AGb| exact H|]. intros a Ha. right; right. exists b. split; [apply in_or_app; right; right; apply in_or_app; left; exact Hb| clear - Ha SZ; lia]. }
    pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ bv HEAPb' ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hbv))) as ACCV2. clear ACCV.
    clear MUa WMa MU09. try clear MU WM. pose proof (munch_refl [(PV, PV + 8)]%Z mb) as MU. pose proof (wmono_refl ctasegs mb) as WM.
    assert (OFFW3 : offshW [(PV, PV + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - ROV BV1 BV2; lia).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - BA0 BAC CL3; lia).
    (* [comment removed for export] *)
    freeze HOPP. freeze HTLC. freeze HFC. freeze HBUF. freeze FRH. freeze HCONT. freeze CELLb.
    apply implAp_from_evt.
    step. if_cases KA0; zc KA0; [exfalso; rewrite ?EA in KA0; clear - KA0 BA0; lia|]. clear KA0.
    step. step. rewrite ?EPV. ab_shload 8. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false. step. rewrite ?EPV. step.
    name_mem mc. match goal with H : munch _ mb mc |- _ => rename H into MUc end. match goal with H : wmono ctasegs mb mc |- _ => rename H into WMc end.
    match goal with H : stk ctasegs mc lo _ |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end. rewrite ?ESPA in STc.
    assert (LIc : linv qfc qb mr Σb stX mc OWX boX ((p, A, ASN1_STRING_SIZE) :: NEW) CX).
    { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LIb| exact MUc| exact WMc| exact MIc| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STc|].
      constructor; [right; left; exists (PV, PV + 8); split; [unfold exo_XP; cbn [In]; right; left; reflexivity| cbn [fst snd]; clear; lia]| constructor]. }
    (* [comment removed for export] *)
    unhide DOV. unhide DVT. pose proof (OFc _ _ _ _ _ _ _ LIb) as (_ & _ & _ & _ & DJL' & _). pose proof (DJL' (p, A, ASN1_STRING_SIZE) bv (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hbv)) as DJAV. unfold ASN1_STRING_SIZE in DJAV. cbn [blk_addr blk_size fst snd] in DJAV.
    thaw HOPP. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HOPP; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DOV; lia].
    thaw HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DVT; lia].
    unhide OV.
    thaw HFC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha OV BV1 BV2; lia].
    thaw HBUF. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HBUF; [| intros a Ha; rewrite BSZ in Ha; cbn [outside fst snd]; clear - Ha OV BV1 BV2; lia].
    thaw HCONT. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HCONT; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha OV BV1 BV2; lia].
    thaw FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LO ESS SPAH; lia].
    thaw CELLb. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in CELLb; [| intros a Ha; unfold asn1_string_cells in Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DJAV BV1 BV2; lia].
    assert (UWc : uw_chain USTACK_TOP mc spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply uw_chain_agree16; [exact UWb|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUc)|]. intros a Ha. cbv beta in Ha. cbn [outside fst snd]. clear - Ha BV1 BV2 BV4 CEIL LO ESS SPAH. lia. }
    assert (KEEPc : forall b cs, In b NEW -> rw_cells ctasegs mX (blk_addr b) cs -> Z.of_nat (cells_size cs) <= blk_size b -> rw_cells ctasegs mc (blk_addr b) cs).
    { intros b cs Hb H SZ. pose proof (DJL b bv Hb ltac:(apply in_or_app; right; exact Hbv)) as DJ. eapply rw_cells_agree; [exact (agree_on_of_munch_nw _ _ _ MUc)| exact (KEEPb b cs Hb H SZ)|].
      intros a Ha. cbn [outside fst snd]. clear - Ha SZ DJ BV1 BV2. lia. }
    (* [comment removed for export] *)
    step. step. step. apply evt_done.
    eapply HK. unfold c2i_post, EX_FC_TEST, exo_lowF.
    do 16 eexists. exists mc, A, OWX, boX. split; [reflexivity|].
    split; [rewrite (zxb_lit fcv) by (clear - FCR; lia); apply unsigned_lit; clear - FCR; lia|].
    split; [exact LIc|]. split; [exact NIp'|]. split; [exact BRA|]. split; [exact BA16|]. split; [exact CELLb|]. split; [exact UWc|].
    split; [rewrite ?EPV in FRLA; exact FRLA|]. split; [exact F96|]. split; [exact F104|]. split; [exact F110|]. split; [exact F111|]. split; [exact F112|]. split; [exact F120|].
    split; [exact FRLB|]. split; [exact FRH|]. split; [exact HCONT|]. split; [exact HFC|]. split; [exact HBUF|]. split; [exact HOPP|]. split; [exact HPV|].
    split; [exact HTLC| exact KEEPc].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma oct_rep_agreeA : forall (mA mB : mem) (L : list block) (adr' : bptr -> Z) (os : CtModel.octet bptr),
    octet_repA mA L adr' os -> agree_on (fun a => exists b, In b (oct_blocks adr' os) /\ blk_addr b <= a < blk_addr b + blk_size b) mA mB -> octet_repA mB L adr' os.
  Proof.
    intros mA mB L adr' [ob od ol obs] (RIN & RAL & RC & RL & RF & R31 & RD) AG. cbn [CtModel.os_blk CtModel.os_data CtModel.os_len CtModel.os_bytes] in *.
    split; [exact RIN|]. split; [exact RAL|]. split; [| split; [exact RL| split; [exact RF| split; [exact R31|]]]].
    - eapply rw_cells_agree; [exact AG| exact RC|]. intros a Ha. exists (ob, adr' ob, ASN1_STRING_SIZE). split; [unfold oct_blocks; left; reflexivity|].
      unfold asn1_string_cells in Ha. cbn in Ha. cbn [blk_addr blk_size fst snd]. unfold ASN1_STRING_SIZE. clear - Ha. lia.
    - destruct od as [[dp n]|]; [| exact RD]. destruct RD as (RD1 & RD2 & RD3 & RB). split; [exact RD1|]. split; [exact RD2|]. split; [exact RD3|].
      eapply bytes_at_agree; [exact AG| exact RB|]. intros a Ha. exists (dp, adr' dp, n). split; [unfold oct_blocks; cbn [CtModel.os_blk CtModel.os_data]; right; left; reflexivity|].
      cbn [blk_addr blk_size fst snd CtModel.os_bytes] in Ha |- *. unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in RL. clear - Ha RL RD3. lia.
  Qed.

  Lemma exo_oktail : forall qfc qb mr ΣX stX mX OWX boX CX (os : CtModel.octet bptr) (adr' : bptr -> Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FX : bvmap 5 word) (fcX : bv 32)
      (PEND : Z) (bufc : list cell) (j0 j8 j64 j72 j80 j104 j120 j128 j136 j144 jt : list byte) (bi bc : byte) (vpl : word) (vb : byte),
    agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m mr ->
    linv qfc qb mr ΣX stX mX OWX boX (oct_blocks adr' os) CX -> 0 <= CX ->
    (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b)) ->
    octet_repA mX (OWX ++ oct_blocks adr' os ++ LB) adr' os ->
    Z.of_nat (cells_size bufc) = 32 ->
    rw_cells ctasegs mX spa (exo_lowF j0 j8 j64 j72 j80) ->
    rw_cells ctasegs mX (spa + 96) [C8 (Z_to_bv 64 PEND)] -> rw_cells ctasegs mX (spa + 104) [CB 6 j104] ->
    rw_cells ctasegs mX (spa + 110) [C1 bi] -> rw_cells ctasegs mX (spa + 111) [C1 bc] -> rw_cells ctasegs mX (spa + 112) [C8 vpl] ->
    rw_cells ctasegs mX (spa + 120) [CB 4 j120; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING)] ->
    rw_cells ctasegs mX (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] -> rw_cells ctasegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells ctasegs mX (f + 64) [C1 (Z_to_bv 8 0)] -> rw_cells ctasegs mX (f + 80) bufc ->
    rw_cells ctasegs mX OPP [C8 (Z_to_bv 64 D)] -> rw_cells ctasegs mX PV [C8 (Z_to_bv 64 (adr' (CtModel.os_blk os)))] -> rw_cells ctasegs mX TLC [C1 vb; CB 31 jt] ->
    @implAp (push AR f 2) _ (ARet (Some os, stX)) ΣX POST
      (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) x23 x24 x25 x26 x27 x28 x29 x30 x31)      (* [comment removed for export] *)
          FX (Z_to_bv 64 EX_OK_TAIL) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until vb. intros AGFr LI HCX ADR' REP BSZ FRLA F96 F104 F110 F111 F112 F120 FRLB FRH HFC HBUF HOPP HPV HTLC. ctx.
    pose proof PRE0 as (HEAP & _).
    pose proof CELLS as (_ & _ & _ & _ & ALO & ALV & ALT & DOV & DOT & DVT & DOD & DVD & DTD & _).
    kitp (@oinv_call (push AR f 2)) qfc qb mr OC. kitp (@oinv_facts (push AR f 2)) qfc qb mr OFc.
    pose proof (OC _ _ _ _ _ _ _ LI) as (HEAPX & STX & _ & _ & _ & _ & MIX & _). replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa in STX by (clear; lia).
    pose proof (OFc _ _ _ _ _ _ _ LI) as (_ & _ & BND & _ & DJL & _).
    pose proof (exo_new_off _ _ _ _ _ _ _ _ _ _ LI) as OFN.
    pose proof (AH_offsh _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as ROQ. unfold SHLO, SHHI in ROQ.
    assert (EOPP : bv_unsigned (Z_to_bv 64 OPP) = OPP) by (apply unsigned_lit; clear - BQ1 BQ2 BQ3 BQ4 CL3; unfold BnHeapA.ACEIL in *; lia).
    (* [comment removed for export] *)
    destruct (@AH_fr_wr (push AR f 2) _ _ _ _ f 2%nat HEAPX (or_introl eq_refl)) as [_ WS]. change (fs_size 2 / 8) with 32 in WS.
    destruct (wr_at_rw_CB mX (shad f) 32 WS ltac:(clear; lia)) as [js HS]. clear WS. change (Z.to_nat 32) with 32%nat in HS.
    apply (rw_cells_split_CB ctasegs _ _ [] 32 _ [] [4; 1; 27]%nat) in HS; [| reflexivity]. cbn [mk_CB_cells app] in HS.
    lazymatch type of HS with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in HS end.
    apply rw_cells_app in HS as [_ HS]. apply rw_cells_app in HS as [HSH4 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HSH4.
    replace (shad f + Z.of_nat 4) with (shad f + 4) in HSH4 by (clear; lia). destruct (cb_byteA _ _ _ HSH4) as [sb4 HSH4']. clear HSH4. rename HSH4' into HSH4.
    hide DOD. hide DVD. hide DTD. hide OD. hide OV. hide OT. hide BD5. hide BQ5. hide BV5. hide BT5. hide G5.
    unfold exo_lowF, EX_OK_TAIL, MallocRep.wz in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(shad f + 4, shad f + 5)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ bq HEAPX ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hbq))) as ACCQ.
    freeze HPV. freeze HTLC. freeze HBUF. freeze FRH. freeze HFC.
    apply implAp_from_evt.
    step. sbstep. name_mem ma.
    match goal with H : munch _ mX ma |- _ => rename H into MUa end. match goal with H : wmono ctasegs mX ma |- _ => rename H into WMa end.
    match goal with H : stk ctasegs ma lo _ |- _ => rename H into STa end. match goal with H : mem_inv ctasegs ma |- _ => rename H into MIa end. rewrite ?ESPA in STa.
    assert (LIa : linv qfc qb mr ΣX stX ma OWX boX (oct_blocks adr' os) CX).
    { eapply (exo_inv_frw qfc qb mr); [exact LI| exact MUa| exact WMa| exact MIa| exact STa|]. constructor; [right; right; cbn [fst snd]; clear; lia| constructor]. }
    assert (REPa : octet_repA ma (OWX ++ oct_blocks adr' os ++ LB) adr' os).
    { eapply oct_rep_agreeA; [exact REP|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUa)|]. intros a (b & Hb & Hr). cbn [outside fst snd].
      pose proof (BND b ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)) as (_ & _ & B3 & _).
      pose proof (@AH_offsh (push AR f 2) _ _ _ _ b HEAPX ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)) as RO. unfold SHLO, SHHI in RO. clear - Hr B3 RO SHR1 SHR2. lia. }
    (* [comment removed for export] *)
    assert (ACCQ' : acc ctasegs ma (blk_addr bq) (blk_size bq)).
    { eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MUa)| exact ACCQ|]. intros i Hi. cbn [outside fst snd]. unfold shad, SHB. clear - Hi ROQ OQ BQ1 BQ2 BQ3 BQ4 CL2 CL3 G1 G2 G3. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV. pose proof (AH_offsh _ _ _ _ bt HEAP (in_or_app _ _ _ (or_intror Hbt))) as ROT. unfold SHLO, SHHI in ROV, ROT.
    thaw HPV. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha ROV BV1 BV2 SHR1 SHR2; lia].
    thaw HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha ROT BT1 BT2 SHR1 SHR2; lia].
    thaw HBUF. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HBUF; [| intros a Ha; rewrite BSZ in Ha; cbn [outside fst snd]; clear - Ha FSH; lia].
    thaw FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH SHR2 CL2 CEIL LO ESS SPAL; lia].
    thaw HFC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha FSH; lia].
    clear ACCQ MUa WMa LI REP. try clear MU WM. pose proof (munch_refl [(OPP, OPP + 8)]%Z ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
    assert (OFFW : offshW [(OPP, OPP + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - ROQ BQ1 BQ2; lia).
    freeze HPV. freeze HTLC. freeze HBUF. freeze FRH. freeze HFC.
    step. step. rewrite ?EOPP. ab_shload 8. rstep. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. step. rewrite ?EOPP. step. name_mem mb.      (* [comment removed for export] *)
    match goal with H : munch _ ma mb |- _ => rename H into MUb end. match goal with H : wmono ctasegs ma mb |- _ => rename H into WMb end.
    match goal with H : stk ctasegs mb lo _ |- _ => rename H into STb end. match goal with H : mem_inv ctasegs mb |- _ => rename H into MIb end. rewrite ?ESPA in STb.
    assert (LIb : linv qfc qb mr ΣX stX mb OWX boX (oct_blocks adr' os) CX).
    { kitp (@oinv_munch (push AR f 2)) qfc qb mr OM. eapply OM; [exact LIa| exact MUb| exact WMb| exact MIb| replace (bv_unsigned sp + (spa - bv_unsigned sp)) with spa by (clear; lia); exact STb|].
      constructor; [right; left; exists (OPP, OPP + 8); split; [unfold exo_XP; cbn [In]; left; reflexivity| cbn [fst snd]; clear; lia]| constructor]. }
    assert (REPb : octet_repA mb (OWX ++ oct_blocks adr' os ++ LB) adr' os).
    { eapply oct_rep_agreeA; [exact REPa|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUb)|]. intros a (b & Hb & Hr). cbn [outside fst snd].
      pose proof (DJL b bq Hb ltac:(apply in_or_app; right; exact Hbq)) as DJ. clear - Hr DJ BQ1 BQ2. lia. }
    unhide DOV. unhide DOT. unhide OQ.
    thaw HPV. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DOV; lia].
    thaw HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DOT; lia].
    thaw HBUF. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in HBUF; [| intros a Ha; rewrite BSZ in Ha; cbn [outside fst snd]; clear - Ha OQ BQ1 BQ2; lia].
    thaw FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BQ1 BQ2 BQ4 CEIL LO ESS SPAH; lia].
    thaw HFC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUb)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha OQ BQ1 BQ2; lia].
    step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true. apply evt_done.
    (* [comment removed for export] *)
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    apply rw_cells_CB_ofA in F112. cbn [cells_size csize Nat.add] in F112.
    pose proof (rw_cells_app_join mb _ _ _ F110 ltac:(cbn [cells_size csize Nat.add]; replace (spa + 110 + Z.of_nat 1) with (spa + 111) by (clear; lia); exact F111)) as FP1.
    pose proof (rw_cells_app_join mb _ _ _ FP1 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + 110 + Z.of_nat 2) with (spa + 112) by (clear; lia); exact F112)) as FPIC.
    cbn [app] in FPIC. clear FP1.
    destruct (exo_join20 f spa g junk mb _ _ _ _ _ _ _ _ _ _ _ (C8 (Z_to_bv 64 (Z.shiftr PV 3 + SHB))) (C8 (Z_to_bv 64 (f + 64))) _ _ _ _ _ _ _ _ eq_refl eq_refl FRLA F96 F104 FPIC F120 FRLB)
      as (k16 & k24 & k32 & k40 & k48 & k96 & k104 & k120 & FRL).
    apply rw_cells_CB_ofA in HTLC. cbn [cells_size csize Nat.add cells_bytes cbytes app] in HTLC.
    eapply (exo_exit STK CST FRMb ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo lo K adr D d OPP PV TLC j31 f spa g junk gj Σ1) with (res := Some os) (mr := mr) (adr' := adr');
      [exact PRE0| exact KOW| exact CELLS| exact LEN1| exact FRESH| exact GEO| exact CR1| exact SPA32| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact STKB
      | exact AGFr| exact LIb| exact HCX| exact ADR'| exact (exo_new_off _ _ _ _ _ _ _ _ _ _ LIb)
      | exact HOPP| exact HTLC| split; [reflexivity| split; [exact REPb| exact HPV]]| exact FRL| exact FRH].
  Qed.
End Body.
End WithRT.
