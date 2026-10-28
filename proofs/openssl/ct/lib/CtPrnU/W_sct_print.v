(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApBase ApState ApBridge CtSizes CtWire CtTime CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_prefix_create W_obj_free W_asn1_string W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_hex_string W_sct_print_nv1 PrnSct PrnKit PrnTimeIface W_sct_print_A W_sct_print_B1 W_sct_print_B2 W_sct_print_B3 W_sct_print_C PrnSctV1.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SCT_PRINT_STACK (TSTK : Z) : Z := 96 + Z.max 8320 TSTK.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition sct_print_res (st : ap_st bptr) (OW : list block) (out pv : Z) : unit * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop :=
  fun r OW' m' _ _ => r = (tt, st) /\ OW' = OW /\ exists nw', 0 <= nw' < 2^64 /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv nw').

Definition SCT_print_spec (TSTK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (x : sctr bptr) (pbio : bptr) (out pv nw : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary (SCT_PRINT_STACK TSTK) -> tp = wz RATP -> frm0 fc ->
    a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
    sct_rep m (OW ++ LB) adr x ->
    In (pbio, out, BIO_SIZE) OW -> ~ In pbio (es_ids st ++ env_ids E) -> ~ In pbio (map blk_id (sct_blocks adr x)) ->
    rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) -> (forall b, In b K -> blk_id b <> pbio) ->
    implM ctusegs (interp (ap_embed (sct_print x st))) s
          (ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K (sct_print_res st OW out pv))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz SCT_PRINT) fc None m (seg_rom ctusegs)).

Section Proofs.
  Variable TSTK : Z.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis T_ADJ_OK : gentime_adj_ok_stmt TSTK.
  Hypothesis T_ADJ_FAIL : gentime_adj_fail_stmt TSTK.
  Hypothesis T_SETSTR_OK : gentime_setstr_ok_stmt TSTK.
  Hypothesis T_SETSTR_FAIL : gentime_setstr_fail_stmt TSTK.
  Hypothesis T_PRINT : gentime_print_stmt TSTK.

  (* [comment removed for export] *)
  Lemma sct_print_finish : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F F' : bvmap 5 word) (fc fc' : bv 32)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (s s' : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv' canary : word) (m m' : mem) (K : list block)
      (out pv nw' : Z),
    pn_pre s' st m' OW LB E bo [] (bv_unsigned sp) lo B errv' canary -> bv_unsigned sp mod 16 = 0 ->
    pn_acc LB (bv_unsigned sp) K s s' m m' -> (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    frm0 fc' -> sp_F F F' -> 0 <= nw' < 2^64 -> rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv nw') ->
    ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K (sct_print_res st OW out pv) (tt, st) s'
      (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom ctusegs)).
  Proof.
    intros until nw'. intros PN SP16 (LX & KP & SO & FA) KOW KID FRM HFC NW HB.
    unfold ap_post. do 15 eexists. exists F', fc', m', OW, errv', bo. split; [reflexivity|].
    split; [exact FRM|]. split; [exact HFC|]. split; [eapply ap_pre_of_pn; [exact PN| exact SP16]|].
    split; [exact LX|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KOW| split; [intros b Hb Hin; apply (KID b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [reflexivity|]. split; [reflexivity|]. exists nw'. split; [exact NW| exact HB].
  Qed.

  Theorem SCT_print_walk : SCT_print_spec TSTK.
  Proof using HF HM T_ADJ_FAIL T_ADJ_OK T_PRINT T_SETSTR_FAIL T_SETSTR_OK.
    intros until nw. intros PRE TP FRM -> -> -> -> REP HBIN NI HID HB NW KOW KID KNB.
    destruct (pn_pre_of_ap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE ltac:(unfold SCT_PRINT_STACK; lia)) as (PN0 & LO0 & SP16). unfold SCT_PRINT_STACK in LO0.
    pose proof PN0 as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & _ & ERR & SSP & MI).
    pose proof AS as (_ & IMG & _).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold GLOBALS_TOP in GLO.
    assert (HBL : In (pbio, out, BIO_SIZE) (OW ++ LB)) by (apply in_app_iff; left; exact HBIN).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP HBL) as (OB0 & OB1 & OB2 & OB3 & OB4). unfold BIO_SIZE in OB2, OB3.
    assert (KF : frozen (forall b, In b K -> In b (OW ++ LB) /\ blk_id b <> pbio)) by (intros b Hb; split; [apply in_app_iff; left; apply KOW; exact Hb| apply KNB; exact Hb]).
    subst tp. unfold sct_print.
    destruct (Z.eqb_spec (sc_version x) 0) as [V0|NV].
    - (* [comment removed for export] *)
      cbn [ap_embed timestamp_print abind amalloc areallocI afree aret apbind].
      destruct (sct_v1_of_rep _ _ _ _ _ _ _ HEAP REP V0 HBL HID) as (HA & CELLS & (LIW & EXW & SGW & TSW & HSH & SGA) & NID & (lib & LIN1 & LIN2 & HS1 & LIR) & (exb & EXN1 & EXN2 & HS2 & EXR) & (sgb & SGN1 & SGN2 & HS3 & SGR)).
      assert (WK : forall (n P : Z) (Q : Prop), frozen (0 < n -> 0 < P /\ P + n <= alloc_ceiling /\ Q) -> frozen (0 < n -> 0 < P /\ P + n <= lo /\ Q)).
      { intros n P Q H Hn. destruct (H Hn) as (H1 & H2 & H3). split; [exact H1|]. split; [lia| exact H3]. }
      apply WK in LIR. apply WK in EXR. apply WK in SGR.
      assert (KSF : frozen (forall b, In b (sct_blocks adr x) -> In b (OW ++ LB) /\ blk_id b <> pbio)).
      { intros b Hb. split; [exact (sct_rep_blocks_in _ _ _ _ REP _ Hb)|]. intros E0. apply HID. rewrite <- E0. apply in_map. exact Hb. }
      assert (AAL : adr (sc_blk x) mod 16 = 0).
      { refine (proj2 (proj2 (proj2 (proj2 (blk_bounds _ _ _ (sc_blk x) (adr (sc_blk x)) SCT_SIZE HEAP (sct_rep_blocks_in _ _ _ _ REP _ _)))))).
        unfold sct_blocks. do 4 (apply in_or_app; right). left; reflexivity. }
      unfold implM. iprefix. unfold MallocRep.wz.
      eapply (seg_A sp gp (Z_to_bv 64 RATP) F m lo out pv canary (adr (sc_blk x)) _ _ (sc_ts x) _ _ (sc_hash x) (sc_sigalg x) _ _ lib exb sgb
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
        [lia| lia| lia| exact SP16| lia| clear - OB4; Z.div_mod_to_equations; lia| lia| clear - AAL; Z.div_mod_to_equations; lia
        | split; [exact LIN1| exact LIN2]| exact LIR| exact LIW| split; [exact EXN1| exact EXN2]| exact EXR| exact EXW
        | split; [exact SGN1| exact SGN2]| exact SGR| exact SGW| exact TSW| exact HSH| exact SGA
        | exact ST| exact MI| exact FRM| exact HB| exact NW| |].
      { split; [exact SSP|]. split; [apply null_meth_of_img; [exact MI| exact IMG]|]. split; [split; [exact HS1| split; [exact HS2| exact HS3]]|]. split; [exact CELLS| exact IMG]. }
      intros x1 u0 u1 u2 w0 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 Fc fc1 m1 nw1 clo INV1 BIO1 FRM1 HFC1.
      destruct INV1 as (MI1 & ST1 & PS1 & MU1 & WM1 & FRH1 & FRL1 & SZ1). destruct BIO1 as [NW1 HB1]. unfold W0 in MU1.
      (* [comment removed for export] *)
      destruct (pn_seg_bio s st m m1 OW LB E bo [] (bv_unsigned sp) (bv_unsigned sp + -96) lo B errv canary _ (bv_unsigned sp) pbio out K
                  PN0 HBIN NI MU1 WM1 ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                  ltac:(lia) ltac:(lia) ltac:(lia) MI1 ST1 ltac:(exact KF)) as (PN1 & LX1 & KP1).
      assert (REP1 : sct_rep m1 (OW ++ LB) adr x) by (eapply (sct_rep_munch s (OW ++ LB) m m1); [exact HEAP| exact REP| exact HBL| exact HID| exact CEIL| exact MU1| exact WM1]).
      apply evt_done.
      lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
      assert (INVB : pb_inv sp m1 s st OW LB E bo lo B canary K (sct_blocks adr x) out pv s m1 [] errv clo nw1).
      { split; [exact PN1|]. split; [apply pn_acc_refl|]. split; [apply rheap_pres_refl|]. split; [exact FRL1|]. split; [exact SZ1|]. split; [exact NW1| exact HB1]. }
      unfold SZ_ASN1_STRING.
      eapply (seg_B1 sp gp m1 s st OW LB E bo lo B canary K (sct_blocks adr x) pbio out pv (sc_ts x) TSTK
                ltac:(lia) ltac:(lia) HBIN NI KF KSF TSW HM);
        [exact INVB| exact FRM1| reflexivity|].
      intros g G sB m2 errv2 x1' u0' u1' u2' w4' w5' w6' w7' u3' u4' u5' u6' INV2 BRG HG.
      cbn [ap_embed apbind abind amalloc areallocI afree aret fst snd].
      destruct (gentime_adj (sc_ts x)) as [t|] eqn:ADJ.
      (* [comment removed for export] *)
      1: replace (printable (sc_ts x)) with true by (unfold printable; rewrite ADJ; reflexivity); unfold SZ_GEN_DATA, SZ_GENSTR.
      1: eapply (seg_B_ok sp gp m1 s st OW LB E bo lo B canary K (sct_blocks adr x) pbio out pv (sc_ts x) TSTK
                  ltac:(lia) ltac:(lia) HBIN NI KF KSF TSW HF SP16 T_ADJ_OK T_SETSTR_OK T_PRINT
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc1 sB m2 errv2 clo nw1 g G t
                  _ (fun dp r => ap_embed (apbind match r with Some p0 => ARet (p0, st) | None => AUnr end (fun p0 => (afree (fst p0) ;;; afree g) (snd p0))))
                  (LRet (tt, st)));
          [exact INV2| exact FRM1| exact BRG| exact HG| exact ADJ| reflexivity| intros; reflexivity| intros; reflexivity| intros; reflexivity|].
      (* [comment removed for export] *)
      2: replace (printable (sc_ts x)) with false by (unfold printable; rewrite ADJ; reflexivity).
      2: eapply (seg_B_fail sp gp m1 s st OW LB E bo lo B canary K (sct_blocks adr x) pbio out pv (sc_ts x) TSTK
                  ltac:(lia) ltac:(lia) HBIN NI KF KSF TSW HF SP16 T_ADJ_FAIL T_SETSTR_FAIL
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc1 sB m2 errv2 clo nw1 g G (LRet (tt, st)));
          [exact INV2| exact FRM1| exact BRG| exact HG| exact ADJ|].
      1: intros sC m3 errv3 x1'' v0 v1 v2 b0 b1 b2 b3 b4 b5 b6 b7 x21'' v3 v4 v5 v6 Fc' fc' clo' nw' INV3 FRM3 HFC3.
      2: intros sC m3 errv3 x1'' v0 v1 v2 b0 b1 b2 b3 b4 b5 b6 b7 x21'' v3 v4 v5 v6 Fc' fc' clo' INV3 FRM3 HFC3; set (nw' := nw1) in INV3.
      all: clear INV2 BRG HG.
      all: destruct INV3 as (PN3 & ACC3 & REL3 & FRL3 & SZ3 & NW3 & HB3).
      all: apply implM_interp_ret.
      (* [comment removed for export] *)
      all: pose proof PN3 as (HEAP3 & AS3 & _ & _ & _ & _ & _ & ST3 & _ & _ & _ & _ & SSP3 & MI3); cbn [app] in HEAP3; pose proof AS3 as (_ & IMG3 & _).
      all: assert (REP3 : sct_rep m3 (OW ++ LB) adr x) by (eapply (sct_rep_pres m1 m3 (OW ++ LB) (sct_blocks adr x)); [exact REL3| intros b Hb; exact Hb| exact REP1]).
      all: destruct (sct_v1_of_rep _ _ _ _ _ _ _ HEAP3 REP3 V0 HBL HID) as (_ & CELLS3 & _ & _ & (lib3 & LIN31 & LIN32 & HS31 & LIR3) & (exb3 & EXN31 & EXN32 & HS32 & EXR3) & (sgb3 & SGN31 & SGN32 & HS33 & SGR3));
           apply WK in LIR3; apply WK in EXR3; apply WK in SGR3.
      all: assert (FRH3 : rw_cells ctusegs m3 (bv_unsigned sp + -64) (pv_hi ra s0 s1 s2 s3 s4 s5 s6))
             by (eapply rw_cells_agree; [apply (agree_of_heap_pres _ _ _ _ REL3)| exact FRH1| intros a Ha; left; cbn in Ha; lia]).
      all: eapply evt_cut; [eapply (seg_C sp gp (Z_to_bv 64 RATP) F m3 lo out pv canary (adr (sc_blk x)) _ _ (sc_ts x) _ _ (sc_hash x) (sc_sigalg x) _ _ lib3 exb3 sgb3
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ltac:(lia) ltac:(lia) ltac:(lia) SP16 ltac:(lia) ltac:(clear - OB4; Z.div_mod_to_equations; lia) ltac:(lia)
                ltac:(clear - AAL; Z.div_mod_to_equations; lia)
                (conj LIN31 LIN32) LIR3 LIW (conj EXN31 EXN32) EXR3 EXW (conj SGN31 SGN32) SGR3 SGW TSW HSH SGA NID
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc' fc' m3 nw' clo');
             [| split; [exact NW3| exact HB3]| exact FRM3| intros r Hr; rewrite (HFC3 r Hr); apply HFC1; exact Hr]|].
      1,3: split; [exact MI3|]; split; [exact ST3|]; split; [| split; [apply munch_refl| split; [apply wmono_refl| split; [exact FRH3| split; [exact FRL3| exact SZ3]]]]];
           split; [exact SSP3|]; split; [apply null_meth_of_img; [exact MI3| exact IMG3]|]; split; [split; [exact HS31| split; [exact HS32| exact HS33]]|]; split; [exact CELLS3| exact IMG3].
      all: cbv beta; unfold segC_post; intros ms' PO.
      all: destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & nw4 & -> & MU4 & WM4 & MI4 & FRM4 & HFC4 & ST4 & _ & [NW4 HB4] & _).
      all: unfold W0 in MU4.
      all: destruct (pn_seg_bio sC st m3 m4 OW LB E bo [] (bv_unsigned sp + -96) (bv_unsigned sp) lo B errv3 canary _ (bv_unsigned sp) pbio out K
                  PN3 HBIN NI MU4 WM4 ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                  ltac:(lia) ltac:(lia) ltac:(lia) MI4 ST4 ltac:(exact KF)) as (PN4 & LX4 & KP4).
      all: apply evt_done; eapply sct_print_finish; [exact PN4| exact SP16| | exact KOW| exact KID| exact FRM4| | exact NW4| exact HB4].
      1,3: eapply pn_acc_trans; [split; [exact LX1| split; [exact KP1| split; reflexivity]]|]; eapply pn_acc_trans; [exact ACC3|]; split; [exact LX4| split; [exact KP4| split; reflexivity]].
      all: exact HFC4.
    - (* [comment removed for export] *)
      apply implM_aret.
      pose proof HEAP as HEAP'. rewrite <- (app_nil_r (OW ++ LB)) in HEAP'.
      eapply evt_cut.
      { eapply (SCT_print_nv1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s (OW ++ LB) [] adr x pbio out pv nw lo canary);
          [exact HEAP'| exact REP| exact NV| exact HBL| exact HID| exact ST| exact MI| unfold GLOBALS_TOP; lia| exact CEIL
          | unfold SCT_PRINT_NV1_STACK, HX_STACK; lia| lia| exact SP16| exact SSP| exact FRM| exact HB| exact NW| apply null_meth_of_img; [exact MI| exact IMG]
          | reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. unfold hexstring_post. intros ms' PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & nw4 & -> & MU4 & WM4 & MI4 & FRM4 & HFC4 & ST4 & SSP4 & HB4 & NW4).
      destruct (pn_seg_bio s st m m4 OW LB E bo [] (bv_unsigned sp) (bv_unsigned sp) lo B errv canary _ (bv_unsigned sp) pbio out K
                  PN0 HBIN NI MU4 WM4 ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                  ltac:(lia) ltac:(lia) ltac:(lia) MI4 ST4 ltac:(exact KF)) as (PN4 & LX4 & KP4).
      apply evt_done. unfold MallocRep.wz. eapply sct_print_finish; [exact PN4| exact SP16| | exact KOW| exact KID| exact FRM4| exact HFC4| exact NW4| exact HB4].
      split; [exact LX4|]. split; [exact KP4|]. split; reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
