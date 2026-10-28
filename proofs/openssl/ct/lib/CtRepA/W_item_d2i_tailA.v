(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA
     W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive W_item_d2i_exA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
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
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.



(* [comment removed for export] *)
Definition EX_OK_TAIL : Z := 0x242234.
Definition EX_FAIL_TAIL : Z := 0x2421bc.
Definition ASN1_TYPE_FREE_A : Z := 0x24716c.
(* [comment removed for export] *)
Definition TFN_STACK_A : Z := 16 + 128 + 128 + 32 + RT_STACK.

(* [comment removed for export] *)
Lemma str_repA_agree : forall m m' OW x A ty, str_repA m OW x A ty -> agree_on (lib_addr OW) m m' -> str_repA m' OW x A ty.
Proof.
  intros m m' OW x A ty (EA & A0 & HIN & HD) AG. split; [exact EA|]. split; [exact A0|]. split; [exact HIN|].
  destruct (str_data x) as [[dp n]|].
  - destruct HD as (N1 & N2 & N3 & N4 & HC & (bytes & HB)). split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split.
    + eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha. right. exists (str_blk x, A, ASN1_STRING_SIZE). split; [exact HIN| cbn; unfold ASN1_STRING_SIZE; lia].
    + exists bytes. eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
      right. exists (dp, badr OW dp, n). split; [exact N3| cbn; lia].
  - eapply rw_cells_agree; [exact AG| exact HD|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha. right. exists (str_blk x, A, ASN1_STRING_SIZE). split; [exact HIN| cbn; unfold ASN1_STRING_SIZE; lia].
Qed.

Lemma blocks_kept_cons : forall K (st' : ap_st bptr) OW' b m m', blocks_kept K st' OW' m m' -> blocks_kept K st' (b :: OW') m m'.
Proof. intros K st' OW' b m m' (B1 & B2 & B3). split; [intros b' Hb'; right; exact (B1 b' Hb')|]. split; [exact B2| exact B3]. Qed.

Lemma blocks_kept_lib : forall K (st' : ap_st bptr) OW' m m' m'', blocks_kept K st' OW' m m' -> agree_on (lib_addr OW') m' m'' -> blocks_kept K st' OW' m m''.
Proof.
  intros K st' OW' m m' m'' (B1 & B2 & B3) AG. split; [exact B1|]. split; [exact B2|].
  intros a Ha Hin. rewrite <- (B3 a Ha Hin). apply AG; [exact Ha|]. right. eapply in_block_mono; [exact B1| exact Hin].
Qed.

Section WithRT0.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfree_null_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem)
    (Σ1 : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ AHEAP Σ1 OW LB m' /\ rt_credit RT Σ - 1 <= rt_credit RT Σ1 /\ stk ctasegs m' lo (bv_unsigned sp) /\ mem_inv ctasegs m'
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'.

Definition type_free_null_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
    AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + TFN_STACK_A <= bv_unsigned sp ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv ctasegs m -> tp = wz TP_A ->
    (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ -> a0 = wz 0 ->
    cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz ASN1_TYPE_FREE_A) fc None m (seg_rom ctasegs))))
        (fun c => exists Σ1, ASTA RT Σ1 PMc (tfree_null_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m Σ1) c
                             /\ rt_live RT Σ1 = rt_live RT Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exprim_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block)
    (OPP PV TLC utype plen : Z) (r : option (astr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (ov : word),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - EXPRIM_SPENT_A plen <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ rw_cells ctasegs m' OPP [C8 ov]
    /\ match fst r with
       | None => a0 = wz 0 /\ rw_cells ctasegs m' PV [C8 (wz 0)]
       | Some x => a0 = wz 1 /\ exists A ty, rw_cells ctasegs m' PV [C8 (wz A)] /\ str_repA m' OW' x A ty /\ str_ty_ok utype ty
                   /\ (forall q, In q (str_ids x) -> ~ In q (map blk_id K ++ es_ids (snd r) ++ env_ids E))
       end.
End WithRT0.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Body.

  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (D : Z) (d : list Z) (op totlen utype e OPP PV TLC : Z) (j31 : list byte).
  Variables (f spa : Z) (g : nat) (junk gj : list byte) (Σ1 : rts RT) (m3 : mem).
  Let gr := get_object d op totlen.
  Let plen := go_len gr.
  Let cont := go_p gr.

  (* [comment removed for export] *)
  Hypothesis PRE0 : ap_preA Σ st m OW LB E bo sp lo EXPRIM_STACK_A (EXPRIM_COST_A plen) EXPRIM_FRAMES_A.
  Hypothesis ENT : d2i_entryA e utype.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D d.
  Hypothesis OP0 : 0 <= op.
  Hypothesis TL0 : 0 < totlen.
  Hypothesis OPT : op + totlen <= zlength d.
  Hypothesis EG : go_err gr = None.
  Hypothesis ETAG : go_tag gr = utype.
  Hypothesis ECLS : go_cls gr = 0.
  Hypothesis ERET : Z.land (go_ret gr) 32 = 0.
  Hypothesis COPP : cellA_in LB OPP 8.
  Hypothesis CPV : cellA_in LB PV 8.
  Hypothesis CTLC : cellA_in LB TLC 32.
  Hypothesis ALO : OPP mod 8 = 0.
  Hypothesis ALV : PV mod 8 = 0.
  Hypothesis ALT : TLC mod 8 = 0.
  Hypothesis DOV : OPP + 8 <= PV \/ PV + 8 <= OPP.
  Hypothesis DOT : OPP + 8 <= TLC \/ TLC + 32 <= OPP.
  Hypothesis DVT : PV + 8 <= TLC \/ TLC + 32 <= PV.
  Hypothesis DOD : OPP + 8 <= D \/ D + zlength d <= OPP.
  Hypothesis DVD : PV + 8 <= D \/ D + zlength d <= PV.
  Hypothesis DTD : TLC + 32 <= D \/ D + zlength d <= TLC.
  Hypothesis HOPP : rw_cells ctasegs m OPP [C8 (wz (D + op))].
  Hypothesis HPV : rw_cells ctasegs m PV [C8 (wz 0)].
  Hypothesis HTLC : rw_cells ctasegs m TLC (tlc_in j31).

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

  Local Ltac ctx := pose proof (ex_ctx sp m Σ st OW LB E bo lo D d op totlen utype e OPP PV TLC f spa g PRE0 ENT PAY OP0 TL0 OPT EG ETAG ECLS ERET COPP CPV CTLC FRESH GEO SPAL SPAH)
                      as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & LO0 & LO & ESS & TOP & SPR & DLEN & ESPA & G1 & G2 & G3 & G4 & Ef & G5 & FSH & SHR1 & SHR2 & GB1 & GB2 & GB3 & UTR
                                             & (bd & Hbd & BD1 & BD2 & BD3 & BD4 & BD5 & OD) & (bq & Hbq & BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & OQ)
                                             & (bv & Hbv & BV1 & BV2 & BV3 & BV4 & BV5 & OV) & (bt & Hbt & BT1 & BT2 & BT3 & BT4 & BT5 & OT));
                    unfold off_fr in OD, OQ, OV, OT; change (fs_size 2) with 256 in OD, OQ, OV, OT; cbn [blk_addr blk_size fst snd] in OD, OQ, OV, OT;
                    hide BD5; hide BQ5; hide BV5; hide BT5; hide OD; hide OQ; hide OV; hide OT; hide G5.
  Local Ltac hide_disj := hide DOV; hide DOT; hide DVT; hide DOD; hide DVD; hide DTD.
  (* [comment removed for export] *)
  Definition ex_lowT (v40 : word) (j0 j8 j16 j64 j72 j80 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 (f + 64)); C8 (Z_to_bv 64 (Z.shiftr OPP 3 + SHB)); C8 v40; C8 (Z_to_bv 64 (f + 80)); C8 (Z_to_bv 64 OPP);
     CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f)].
  Local Notation POST := (exprim_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K OPP PV TLC utype plen).
  Local Notation XIV := ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A).

  (* [comment removed for export] *)
  Definition ex_exit_facts (Σk : rts RT) (OWk : list block) (mk : mem) (st' : ap_st bptr) (res : option (astr bptr)) (rv : Z) (ov : word) : Prop :=
    @BnHeapA.AHEAP (push AR f 2) Σk OWk LB mk
    /\ ap_state st' mk OWk E bo /\ ids_ok E st' /\ data_cells mk OWk st'
    /\ stk ctasegs mk lo spa /\ mem_inv ctasegs mk
    /\ ax_pres LB (bv_unsigned sp) XIV m mk
    /\ rt_credit RT Σ - EXPRIM_SPENT_A plen <= rt_credit RT Σk
    /\ blocks_kept K st' OWk m mk
    /\ rw_cells ctasegs mk OPP [C8 ov]
    /\ match res with
       | None => rv = 0 /\ rw_cells ctasegs mk PV [C8 (wz 0)]
       | Some x => rv = 1 /\ exists A ty, rw_cells ctasegs mk PV [C8 (wz A)] /\ str_repA mk OWk x A ty /\ str_ty_ok utype ty
                   /\ (forall q, In q (str_ids x) -> ~ In q (map blk_id K ++ es_ids st' ++ env_ids E))
       end.

  (* [comment removed for export] *)
  Lemma exprim_exitA : forall Σk OWk mk st' res rv ov
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 : list byte) (v96 v40 : word),
    ex_exit_facts Σk OWk mk st' res rv ov ->
    rw_cells ctasegs mk spa (ex_lowT v40 j0 j8 j16 j64 j72 j80) ->
    rw_cells ctasegs mk (spa + 96) [C8 v96] -> rw_cells ctasegs mk (spa + 104) [CB 6 (firstn 6 j104)] ->
    rw_cells ctasegs mk (spa + 110) [C1 (Z_to_bv 8 0)] -> rw_cells ctasegs mk (spa + 111) [C1 (Z_to_bv 8 0)] ->
    rw_cells ctasegs mk (spa + 112) [C8 (Z_to_bv 64 plen)] -> rw_cells ctasegs mk (spa + 120) [CB 4 (firstn 4 j120); C4 (Z_to_bv 64 utype)] ->
    rw_cells ctasegs mk (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] ->
    rw_cells ctasegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    @implAp (push AR f 2) _ (ARet (res, st')) Σk POST
      (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 f) x20 x21 (Z_to_bv 64 (shad f)) x23 x24 (Z_to_bv 64 rv) x26 x27 x28 x29 x30 x31)
          F (wz ADEP_EXIT) fc None mk (seg_rom ctasegs)).
  Proof.
    intros until v40. intros XF FRLA F96 F104 F110 F111 F112 F120 FRLB FRH. hide_disj. ctx.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
    destruct XF as (HEAPk & ASk & IDSk & DCk & STk & MIk & AXk & CRk & KEPTk & HOPPk & RESk).
    (* [comment removed for export] *)
    unfold ex_lowT in FRLA. apply (rw_cells_cb_first mk spa _ 8) in FRLA. cbn [cb_first csize cbytes] in FRLA. (* [comment removed for export] *)
    apply rw_cells_CB_ofA in F96. apply rw_cells_CB_ofA in F112. apply rw_cells_CB_ofA in F120. cbn [cells_size csize Nat.add] in F96, F112, F120.
    pose proof (rw_cells_app_join mk _ _ _ F104 ltac:(cbn [cells_size csize Nat.add]; replace (spa + 104 + Z.of_nat 6) with (spa + 110) by (clear; lia); exact F110)) as FM.
    pose proof (rw_cells_app_join mk _ _ _ FM ltac:(cbn [cells_size csize Nat.add app]; replace (spa + 104 + Z.of_nat 7) with (spa + 111) by (clear; lia); exact F111)) as FM2.
    apply rw_cells_CB_ofA in FM2. cbn [cells_size csize Nat.add app] in FM2. clear FM F104 F110 F111.
    pose proof (rw_cells_app_join mk _ _ _ FRLA ltac:(cbn [cells_size csize Nat.add]; replace (spa + Z.of_nat 96) with (spa + 96) by (clear; lia); exact F96)) as T1.
    pose proof (rw_cells_app_join mk _ _ _ T1 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 104) with (spa + 104) by (clear; lia); exact FM2)) as T2.
    pose proof (rw_cells_app_join mk _ _ _ T2 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 112) with (spa + 112) by (clear; lia); exact F112)) as T3.
    pose proof (rw_cells_app_join mk _ _ _ T3 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 120) with (spa + 120) by (clear; lia); exact F120)) as T4.
    pose proof (rw_cells_app_join mk _ _ _ T4 ltac:(cbn [cells_size csize Nat.add app]; replace (spa + Z.of_nat 128) with (spa + 128) by (clear; lia); exact FRLB)) as FRL.
    cbn [app] in FRL. clear T1 T2 T3 T4 FRLA F96 FM2 F112 F120 FRLB.
    assert (OFFLB : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    (* [comment removed for export] *)
    unfold MallocRep.wz. intros X2 Φ2 D2 SAFE2 LINK2.
    eapply (@adep_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAPk | exact OFFLB | exact STk | exact CEIL | clear - CEIL LO SPAL ESS; lia | exact TOP | clear - SPAL; lia | clear - SPAH; lia
      | exact GSZ | exact SAVJ | exact MIk | exact FRL | exact FRH | reflexivity |].
    intros Σ' m' HEAP' CR' EL' ST' MI' AG'.
    eapply (@implAp_elim (push AR f 2) _ (ARet (res, st'))); [| exact SAFE2 | exact LINK2 | exact EL'].
    apply implAp_ret.
    (* [comment removed for export] *)
    assert (AGL : agree_on (lib_addr OWk) mk m') by (eapply agree_on_mono; [exact AG'|]; intros a Ha; exact (lib_addr_aclient OWk LB spa a Ha)).
    assert (AGB : forall b A n, In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> agree_on (fun a => A <= a < A + n) mk m').
    { intros b A n Hb H1 H2. eapply agree_on_mono; [exact AG'|]. intros a Ha. right; right. exists b. split; [apply in_or_app; right; exact Hb| clear - Ha H1 H2; lia]. }
    unfold exprim_postA. cbn [fst snd].
    do 17 eexists. exists m', OWk, ov. split; [reflexivity|].
    split.
    { unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASk | exact AG']|]. split; [exact IDSk|].
      split; [eapply data_cells_rt; [exact ASk | exact DCk | exact AG']|]. split; [exact ST'|]. split; [exact CEIL'|]. split; [clear - LOSP LO ESS; lia|].
      split; [exact TOP'|]. split; [exact AL16|]. split; [exact MI'|].
      split; [pose proof (af_credit_nonneg RT (@ar_AF AR) Σ' m' (AH_art _ _ _ _ HEAP')) as CNN; clear - CNN; lia|]. clear - FRM. lia. }
    split.
    { eapply ax_pres_trans; [exact AXk|]. eapply (ax_pres_of_aclient OWk LB); [exact AG'| clear - SPAH; lia]. }
    split; [clear - CRk CR'; lia|].
    split; [eapply (blocks_kept_post K st' OWk LB); [exact KEPTk| exact AG']|].
    split; [eapply rw_cells_agree; [exact (AGB bq OPP 8 Hbq BQ1 BQ2)| exact HOPPk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia]|].
    destruct res as [x|].
    - destruct RESk as (-> & A & ty & HPVk & SR & TY & IDX). split; [reflexivity|]. exists A, ty.
      split; [eapply rw_cells_agree; [exact (AGB bv PV 8 Hbv BV1 BV2)| exact HPVk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia]|].
      split; [exact (str_repA_agree _ _ _ _ _ _ SR AGL)|]. split; [exact TY| exact IDX].
    - destruct RESk as (-> & HPVk). split; [reflexivity|].
      eapply rw_cells_agree; [exact (AGB bv PV 8 Hbv BV1 BV2)| exact HPVk| intros a Ha; cbn in Ha; cbv beta; clear - Ha; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ex_libout : forall Σk OWk mk L,
    @BnHeapA.AHEAP (push AR f 2) Σk OWk (L ++ LB) mk ->
    forall a, lib_addr OWk a -> outside [(shad f + 4, shad f + 5)]%Z a /\ outside [(OPP, OPP + 8)]%Z a.
  Proof.
    intros Σk OWk mk L HEAPk a HL. hide_disj. ctx. cbn [outside fst snd].
    destruct HL as [HS|(b & Hb & Hr)].
    - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. pose proof BQ5 as X. unfold hidden in X. unfold SEGTOP_A in X. clear - HA X BQ1 BQ2 SHR1. lia.
    - assert (Hb' : In b (OWk ++ L ++ LB)) by (apply in_or_app; left; exact Hb).
      pose proof (@AH_offsh (push AR f 2) _ _ _ _ b HEAPk Hb') as RO. unfold SHLO, SHHI in RO.
      pose proof (@AH_nodup (push AR f 2) _ _ _ _ HEAPk) as ND. destruct b as [[q A] n].
      pose proof (ids_disj OWk (L ++ LB) q A n ND Hb bq ltac:(apply in_or_app; right; exact Hbq)) as NE.
      pose proof (@AH_disjoint_gen (push AR f 2) _ _ _ _ bq (q, A, n) HEAPk ltac:(apply in_or_app; right; apply in_or_app; right; exact Hbq) Hb' NE) as DJ.
      cbn [blk_addr blk_size fst snd] in Hr, RO, DJ. clear - Hr RO DJ BQ1 BQ2 SHR1 SHR2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exprim_oktailA : forall Σk OWk mk st' (x : astr bptr) (A ty : Z) (qfc : bptr)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 : list byte) (v40 : word),
    @BnHeapA.AHEAP (push AR f 2) Σk OWk ((qfc, f + 64, 1) :: LB) mk ->
    ap_state st' mk OWk E bo -> ids_ok E st' -> data_cells mk OWk st' -> stk ctasegs mk lo spa -> mem_inv ctasegs mk ->
    ax_pres LB (bv_unsigned sp) XIV m mk -> rt_credit RT Σ - EXPRIM_SPENT_A plen <= rt_credit RT Σk -> blocks_kept K st' OWk m mk ->
    rw_cells ctasegs mk OPP [C8 (Z_to_bv 64 (D + op))] ->
    rw_cells ctasegs mk PV [C8 (Z_to_bv 64 A)] -> str_repA mk OWk x A ty -> str_ty_ok utype ty ->
    (forall q, In q (str_ids x) -> ~ In q (map blk_id K ++ es_ids st' ++ env_ids E)) ->
    rw_cells ctasegs mk spa (ex_lowT v40 j0 j8 j16 j64 j72 j80) ->
    rw_cells ctasegs mk (spa + 96) [C8 (Z_to_bv 64 (D + cont + plen))] -> rw_cells ctasegs mk (spa + 104) [CB 6 (firstn 6 j104)] ->
    rw_cells ctasegs mk (spa + 110) [C1 (Z_to_bv 8 0)] -> rw_cells ctasegs mk (spa + 111) [C1 (Z_to_bv 8 0)] ->
    rw_cells ctasegs mk (spa + 112) [C8 (Z_to_bv 64 plen)] -> rw_cells ctasegs mk (spa + 120) [CB 4 (firstn 4 j120); C4 (Z_to_bv 64 utype)] ->
    rw_cells ctasegs mk (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] ->
    rw_cells ctasegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells ctasegs mk (f + 64) [C1 (Z_to_bv 8 0)] ->
    @implAp (push AR f 2) _ (ARet (Some x, st')) Σk POST
      (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (wz EX_OK_TAIL) fc None mk (seg_rom ctasegs)).
  Proof.
    intros until v40. intros HEAPk ASk IDSk DCk STk MIk AXk CRk KEPTk HOPPk HPVk SR TY IDX FRLA F96 F104 F110 F111 F112 F120 FRLB FRH HFC. hide_disj. ctx.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
    unfold ex_lowT in FRLA. unfold EX_OK_TAIL, MallocRep.wz in *.
    assert (OFFLB : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    assert (EOPP : bv_unsigned (Z_to_bv 64 OPP) = OPP) by (apply unsigned_lit; clear - BQ1 BQ2 BQ3 BQ4 CL3; unfold BnHeapA.ACEIL in *; lia).
    pose proof (AH_offsh _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as ROQ. pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV. unfold SHLO, SHHI in ROQ, ROV.
    (* [comment removed for export] *)
    destruct (@AH_fr_wr (push AR f 2) _ _ _ _ f 2%nat HEAPk (or_introl eq_refl)) as [_ WS]. change (fs_size 2 / 8) with 32 in WS.
    destruct (wr_at_rw_CB mk (shad f) 32 WS ltac:(clear; lia)) as [js HS]. clear WS. change (Z.to_nat 32) with 32%nat in HS.
    apply (rw_cells_split_CB ctasegs _ _ [] 32 _ [] [4; 1; 27]%nat) in HS; [| reflexivity]. cbn [mk_CB_cells app] in HS.
    lazymatch type of HS with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in HS end.
    apply rw_cells_app in HS as [_ HS]. apply rw_cells_app in HS as [HSH4 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HSH4.
    replace (shad f + Z.of_nat 4) with (shad f + 4) in HSH4 by (clear; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(shad f + 4, shad f + 5)]%Z mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    freeze HOPPk. freeze HPVk. freeze HFC.
    apply implAp_from_evt. step. sbstep. name_mem ma.
    match goal with H : munch _ mk ma |- _ => rename H into MUa end. match goal with H : wmono ctasegs mk ma |- _ => rename H into WMa end.
    assert (SH8 : shad (f + 64) = shad f + 8 /\ shad (f + 64 + (1 - 1)) = shad f + 8) by (unfold shad; clear - G2; Z.div_mod_to_equations; lia).
    assert (HEAPa : @BnHeapA.AHEAP (push AR f 2) Σk OWk ((qfc, f + 64, 1) :: LB) ma).
    { eapply (@AH_frame_frSA (push AR f 2) Σk OWk _ mk ma _ f 2%nat (or_introl eq_refl) HEAPk MUa WMa).
      - constructor; [right; right; cbn [fst snd]; change (fs_size 2 / 8) with 32; clear; lia| constructor].
      - intros b [<-|Hb]; [right| left; exact (OFFLB b Hb)]. constructor; [cbn [fst snd blk_addr blk_size]; intros _; left; clear - SH8; lia| constructor]. }
    unfold frozen in HOPPk, HPVk.
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HOPPk; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha ROQ BQ1 BQ2 SHR1 SHR2; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HPVk; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha ROV BV1 BV2 SHR1 SHR2; lia].
    try clear HSH4.
    (* [comment removed for export] *)
    pose proof (proj2 (@AH_acc (push AR f 2) _ _ _ _ bq HEAPa ltac:(apply in_or_app; right; right; exact Hbq))) as ACCQ.
    assert (OFFW : offshW [(OPP, OPP + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - ROQ BQ1 BQ2; lia).
    pose proof (agree_on_of_munch_nw _ _ _ MUa) as AGa. clear MUa WMa. pose proof (munch_refl [(OPP, OPP + 8)]%Z ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
    step. step. rewrite ?EOPP.
    ab_shload 8.
    step.
    step. rewrite ?zxb_z8, ?sxb_z8. if_false.
    freeze HPVk.
    step. rewrite ?EOPP. step. rewrite ?EOPP. step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold frozen in HFC, HPVk. pose proof OQ as OQ'. unfold hidden in OQ'. pose proof DOV as DOV'. unfold hidden in DOV'.
    apply (rw_cells_agree _ _ _ _ _ AGa) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha FSH; lia].
    match goal with H : munch _ ma ?mx |- _ => apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ H)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha OQ' BQ1 BQ2; lia] end.
    match goal with H : munch _ ma ?mx |- _ => apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ H)) in HPVk; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DOV'; lia] end.
    step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true. name_mem mb.
    match goal with H : munch _ ma mb |- _ => rename H into MUb end. match goal with H : wmono ctasegs ma mb |- _ => rename H into WMb end.
    match goal with H : stk ctasegs mb lo _ |- _ => rename H into STb end. match goal with H : mem_inv ctasegs mb |- _ => rename H into MIb end.
    apply evt_done. unfold ADEP_EXIT.
    (* [comment removed for export] *)
    assert (HEAPb : @BnHeapA.AHEAP (push AR f 2) Σk OWk ((qfc, f + 64, 1) :: LB) mb).
    { eapply (@AH_frame (push AR f 2)); [exact HEAPa| exact MUb| exact WMb|]. constructor; [| constructor].
      right; right. exists bq. split; [apply in_or_app; right; right; exact Hbq| cbn [fst snd]; clear - BQ1 BQ2; lia]. }
    assert (HEAPc : @BnHeapA.AHEAP (push AR f 2) Σk OWk LB mb).
    { eapply (@frame_obj_close (push AR f 2)); [left; reflexivity| exact HEAPb|]. unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 2) with 256. clear; lia. }
    assert (AGLk : agree_on (lib_addr OWk) mk mb).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AGa|]; intros a Ha; exact (proj1 (ex_libout _ _ _ [(qfc, f + 64, 1)] HEAPk a Ha))|].
      eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUb)|]. intros a Ha. exact (proj2 (ex_libout _ _ _ [(qfc, f + 64, 1)] HEAPk a Ha)). }
    pose proof ASk as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODk)).
    assert (XF : ex_exit_facts Σk OWk mb st' (Some x) 1 (Z_to_bv 64 (D + cont + plen))).
    { split; [exact HEAPc|]. split; [exact (ap_state_agree _ _ _ _ _ _ ASk AGLk)|]. split; [exact IDSk|]. split; [exact (data_cells_agree _ _ _ _ DCk AGLk ODk)|].
      split; [exact STb|]. split; [exact MIb|].
      split.
      { eapply ax_pres_trans; [exact AXk|]. unfold ax_pres.
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGa|]|eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MUb)|]].
        - intros a [HX Ha]. cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
          + clear - H1 SPAH SHR2 CL2 CEIL LO SPAL ESS. lia.
          + assert (a < 12365824) by (destruct H1 as [(l & h & Hin & Hlh) _]; unfold CLIENT_STATIC in Hin; cbn [In] in Hin; clear - Hin Hlh; destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia).
            clear - H SHR1. lia.
          + pose proof (AH_offsh _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as RO. unfold SHLO, SHHI in RO. clear - Hr RO SHR1 SHR2. lia.
        - intros a [HX Ha]. unfold LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. cbn [outside fst snd]. clear - HX. lia. }
      split; [exact CRk|]. split; [exact (blocks_kept_lib _ _ _ _ _ _ KEPTk AGLk)|]. split; [exact HOPPk|].
      split; [reflexivity|]. exists A, ty. split; [exact HPVk|]. split; [exact (str_repA_agree _ _ _ _ _ _ SR AGLk)|]. split; [exact TY| exact IDX]. }
    eapply exprim_exitA; [exact XF| unfold ex_lowT; exact FRLA| exact F96| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH].
  Qed.

  Section Fail.
    (* [comment removed for export] *)
    Hypothesis HTF : forall AR' : ARun, @type_free_null_specA AR'.

    (* [comment removed for export] *)
    Lemma exprim_failA : forall Σk OWk mk st' (qfc : bptr)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
        (j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 : list byte) (v40 : word),
      @BnHeapA.AHEAP (push AR f 2) Σk OWk ((qfc, f + 64, 1) :: LB) mk ->
      ap_state st' mk OWk E bo -> ids_ok E st' -> data_cells mk OWk st' -> stk ctasegs mk lo spa -> mem_inv ctasegs mk ->
      ax_pres LB (bv_unsigned sp) XIV m mk -> rt_credit RT Σ - (EXPRIM_SPENT_A plen - 1) <= rt_credit RT Σk -> blocks_kept K st' OWk m mk ->
      rw_cells ctasegs mk OPP [C8 (Z_to_bv 64 (D + op))] -> rw_cells ctasegs mk PV [C8 (Z_to_bv 64 0)] ->
      rw_cells ctasegs mk spa (ex_lowT v40 j0 j8 j16 j64 j72 j80) ->
      rw_cells ctasegs mk (spa + 96) [C8 (Z_to_bv 64 (D + cont + plen))] -> rw_cells ctasegs mk (spa + 104) [CB 6 (firstn 6 j104)] ->
      rw_cells ctasegs mk (spa + 110) [C1 (Z_to_bv 8 0)] -> rw_cells ctasegs mk (spa + 111) [C1 (Z_to_bv 8 0)] ->
      rw_cells ctasegs mk (spa + 112) [C8 (Z_to_bv 64 plen)] -> rw_cells ctasegs mk (spa + 120) [CB 4 (firstn 4 j120); C4 (Z_to_bv 64 utype)] ->
      rw_cells ctasegs mk (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk] ->
      rw_cells ctasegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells ctasegs mk (f + 64) [C1 (Z_to_bv 8 0)] ->
      @implAp (push AR f 2) _ (ARet (@None (astr bptr), st')) Σk POST
        (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 0) (Z_to_bv 64 0) x25 x26 x27 x28 x29 x30 x31)
            F (wz EX_FAIL_TAIL) fc None mk (seg_rom ctasegs)).
    Proof.
      intros until v40. intros HEAPk ASk IDSk DCk STk MIk AXk CRk KEPTk HOPPk HPVk FRLA F96 F104 F110 F111 F112 F120 FRLB FRH HFC. hide_disj. ctx.
      pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
      unfold ex_lowT in FRLA. unfold EX_FAIL_TAIL, MallocRep.wz in *.
      assert (OFFLB : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
      pose proof (AH_offsh _ _ _ _ bq HEAP (in_or_app _ _ _ (or_intror Hbq))) as ROQ. pose proof (AH_offsh _ _ _ _ bv HEAP (in_or_app _ _ _ (or_intror Hbv))) as ROV. unfold SHLO, SHHI in ROQ, ROV.
      assert (EF : EXPRIM_FRAMES_A = 7) by reflexivity. assert (EC : GETOBJ_ERR_COST_A = 13) by reflexivity.
      assert (ESF : 66320 <= CHECK_TLEN_STACK_A /\ TFN_STACK_A = 65840) by (split; [exact ESS| reflexivity]). (* [comment removed for export] *)
      pose proof (mcost_nonneg plen ltac:(cbv delta [plen gr] in *; clear - GB2; lia)) as MC0.
      (* [comment removed for export] *)
      pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
      apply implAp_from_evt. step. step. apply evt_done. clear MU WM.
      eapply implAp_step.
      { eapply cps_conseq; [eapply (HTF (push AR f 2)) with (lo := lo); rewrite ?ESPA;
          [exact HEAPk| exact STk| clear - CEIL; plia| clear - LO SPAL ESF; lia| clear - TOP SPAH; unfold USTACK_TOP in *; lia
          | clear - SPA32; Z.div_mod_to_equations; lia| exact MIk| reflexivity
          | cbn [ar_FR push amb length]; clear - FRM EF; lia
          | cbn [ar_RT push amb]; unfold EXPRIM_COST_A, EXPRIM_SPENT_A in *; clear - CRED CRk EC MC0; lia| reflexivity]
        | intros c Hc; exact Hc| intros c (Σ5 & Hc & EL5); exists Σ5; split; [exact Hc| rewrite EL5; reflexivity]]. }
      intros Σ5 ms5 PO5. destruct PO5 as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & m5 & -> & HEAP5 & CR5 & ST5 & MI5 & AG5).
      rewrite ?ESPA in *. rewrite (ret_pc_even 0x2421c4) by (clear; lia).
      (* [comment removed for export] *)
      assert (AGS : forall A cs, rw_cells ctasegs mk A cs -> spa <= A -> A + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs m5 A cs).
      { intros A cs HC H1 H2. eapply rw_cells_agree; [exact AG5| exact HC|]. intros a Ha. left. clear - Ha H1 H2. lia. }
      apply AGS in FRLA; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F96; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AGS in F104; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F110; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AGS in F111; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia]. apply AGS in F112; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AGS in F120; [| clear; lia| cbn; clear - SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AGS in FRLB; [| clear; lia| cbn [cells_size csize Nat.add]; rewrite ?Nat2Z.inj_add; clear - GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
      apply AGS in FRH; [| clear - SPAH; lia| cbn; clear - TOP; unfold USTACK_TOP in *; lia]. clear AGS.
      apply (rw_cells_agree _ _ _ _ _ AG5) in HOPPk; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; right; exact Hbq| clear - Ha BQ1 BQ2; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in HPVk; [| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; right; exact Hbv| clear - Ha BV1 BV2; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in HFC; [| intros a Ha; cbn in Ha; right; right; exists (qfc, f + 64, 1); split; [apply in_or_app; right; left; reflexivity| cbn; clear - Ha; lia]].
      assert (AGL5 : agree_on (lib_addr OWk) mk m5) by (eapply agree_on_mono; [exact AG5|]; intros a Ha; exact (lib_addr_aclient OWk _ spa a Ha)).
      (* [comment removed for export] *)
      destruct (@AH_fr_wr (push AR f 2) _ _ _ _ f 2%nat HEAP5 (or_introl eq_refl)) as [_ WS]. change (fs_size 2 / 8) with 32 in WS.
      destruct (wr_at_rw_CB m5 (shad f) 32 WS ltac:(clear; lia)) as [js HS]. clear WS. change (Z.to_nat 32) with 32%nat in HS.
      apply (rw_cells_split_CB ctasegs _ _ [] 32 _ [] [4; 1; 27]%nat) in HS; [| reflexivity]. cbn [mk_CB_cells app] in HS.
      lazymatch type of HS with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in HS end.
      apply rw_cells_app in HS as [_ HS]. apply rw_cells_app in HS as [HSH4 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HSH4.
      replace (shad f + Z.of_nat 4) with (shad f + 4) in HSH4 by (clear; lia).
      (* [comment removed for export] *)
      pose proof (munch_refl [(shad f + 4, shad f + 5)]%Z m5) as MU. pose proof (wmono_refl ctasegs m5) as WM.
      freeze HOPPk. freeze HPVk. freeze HFC.
      apply implAp_from_evt. step. step. if_true. step. step. sbstep. name_mem ma.
      match goal with H : munch _ m5 ma |- _ => rename H into MUa end. match goal with H : wmono ctasegs m5 ma |- _ => rename H into WMa end.
      assert (SH8 : shad (f + 64) = shad f + 8 /\ shad (f + 64 + (1 - 1)) = shad f + 8) by (unfold shad; clear - G2; Z.div_mod_to_equations; lia).
      assert (HEAPa : @BnHeapA.AHEAP (push AR f 2) Σ5 OWk ((qfc, f + 64, 1) :: LB) ma).
      { eapply (@AH_frame_frSA (push AR f 2) Σ5 OWk _ m5 ma _ f 2%nat (or_introl eq_refl) HEAP5 MUa WMa).
        - constructor; [right; right; cbn [fst snd]; change (fs_size 2 / 8) with 32; clear; lia| constructor].
        - intros b [<-|Hb]; [right| left; exact (OFFLB b Hb)]. constructor; [cbn [fst snd blk_addr blk_size]; intros _; left; clear - SH8; lia| constructor]. }
      pose proof (agree_on_of_munch_nw _ _ _ MUa) as AGa.
      unfold frozen in HOPPk, HPVk, HFC.
      apply (rw_cells_agree _ _ _ _ _ AGa) in HOPPk; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha ROQ BQ1 BQ2 SHR1 SHR2; lia].
      apply (rw_cells_agree _ _ _ _ _ AGa) in HPVk; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha ROV BV1 BV2 SHR1 SHR2; lia].
      apply (rw_cells_agree _ _ _ _ _ AGa) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha FSH; lia].
      try clear HSH4.
      step. step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true.
      match goal with H : stk ctasegs ma lo _ |- _ => rename H into STa end. match goal with H : mem_inv ctasegs ma |- _ => rename H into MIa end.
      apply evt_done. unfold ADEP_EXIT.
      (* [comment removed for export] *)
      assert (HEAPc : @BnHeapA.AHEAP (push AR f 2) Σ5 OWk LB ma).
      { eapply (@frame_obj_close (push AR f 2)); [left; reflexivity| exact HEAPa|]. unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 2) with 256. clear; lia. }
      assert (AGLa : agree_on (lib_addr OWk) mk ma).
      { eapply agree_on_trans; [exact AGL5|]. eapply agree_on_mono; [exact AGa|]. intros a Ha. exact (proj1 (ex_libout _ _ _ [(qfc, f + 64, 1)] HEAP5 a Ha)). }
      pose proof ASk as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODk)).
      assert (XF : ex_exit_facts Σ5 OWk ma st' None 0 (Z_to_bv 64 (D + op))).
      { split; [exact HEAPc|]. split; [exact (ap_state_agree _ _ _ _ _ _ ASk AGLa)|]. split; [exact IDSk|]. split; [exact (data_cells_agree _ _ _ _ DCk AGLa ODk)|].
        split; [exact STa|]. split; [exact MIa|].
        split.
        { eapply ax_pres_trans; [exact AXk|]. eapply ax_pres_trans.
          - unfold ax_pres. eapply agree_on_mono; [exact AG5|]. intros a [_ Ha]. eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; right; exact Hb| clear - SPAH; lia].
          - unfold ax_pres. eapply agree_on_mono; [exact AGa|]. intros a [HX Ha]. cbn [outside fst snd]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
            + clear - H1 SPAH SHR2 CL2 CEIL LO SPAL ESS. lia.
            + assert (a < 12365824) by (destruct H1 as [(l & h & Hin & Hlh) _]; unfold CLIENT_STATIC in Hin; cbn [In] in Hin; clear - Hin Hlh; destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia).
              clear - H SHR1. lia.
            + pose proof (AH_offsh _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as RO. unfold SHLO, SHHI in RO. clear - Hr RO SHR1 SHR2. lia. }
        split; [cbn [ar_RT push amb] in CR5; unfold EXPRIM_SPENT_A in *; clear - CRk CR5; lia|].
        split; [exact (blocks_kept_lib _ _ _ _ _ _ KEPTk AGLa)|]. split; [exact HOPPk|]. split; [reflexivity| exact HPVk]. }
      eapply exprim_exitA; [exact XF| unfold ex_lowT; exact FRLA| exact F96| exact F104| exact F110| exact F111| exact F112| exact F120| exact FRLB| exact FRH].
    Qed.
  End Fail.
End Body.
End WithRT.
