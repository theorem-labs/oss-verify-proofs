(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2 W_bio_vprintfG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnFmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => first [clear; lia| lia] end | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

Import ListNotations.
Open Scope Z_scope.

Definition BIO_HEX_STRING_A : Z := 0x23aa50.
Definition HX_LOOP_A : Z := 0x23aaf8.     (* [comment removed for export] *)
Definition HX_MID_A : Z := 0x23ab14.      (* [comment removed for export] *)
Definition HX_END8_A : Z := 0x23ab4c.     (* [comment removed for export] *)
Definition HX_TAIL_A : Z := 0x23ab70.
Definition HX_LAST_A : Z := 0x23ab98.
Definition HX_RET_A : Z := 0x23abc0.
(* [comment removed for export] *)
Definition HX_STACK_A : Z := 144 + BIO_PRINTF_NULL_STACK.
(* [comment removed for export] *)
Definition HX_CRED (len : Z) : Z := 9 * len.

(* [comment removed for export] *)
Lemma wz_mod64 : forall z, Z_to_bv 64 (z mod 2^64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  apply Z.mod_mod. lia.
Qed.
Lemma bio_null_cells_mod : forall meth pv nw, bio_null_cells meth pv (nw mod 2^64) = bio_null_cells meth pv nw.
Proof. intros. unfold bio_null_cells, bio_cells, MallocRep.wz. rewrite wz_mod64. reflexivity. Qed.

Lemma hx_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
Lemma hx_data_read : forall m S n bs t a, rw_cells ctasegs m S [CB n bs] -> 0 <= t < Z.of_nat n -> a = wa (S + t) ->
  exists b : byte, nth_error bs (Z.to_nat t) = Some b /\ ov_read_bytes ctasegs m a 1 = Some [b].
Proof.
  intros m S n bs t a H Ht ->. pose proof (proj1 (proj1 H)) as WF. cbn in WF. destruct WF as [L _].
  pose proof (proj2 (proj1 H)) as HB. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  destruct (nth_error bs (Z.to_nat t)) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
  exists b. split; [reflexivity|]. exact (u8ro_read ctasegs m S bs t b _ HB E ltac:(lia) eq_refl).
Qed.

Section HX.
Context {AR : ARun}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.

Variables (sp gp : word) (m0 : mem) (Σ0 : rts RTS) (OW LB : list block) (lo : Z) (pb bd : bptr) (out pv D len : Z) (bs : list byte).
(* [comment removed for export] *)
Variables (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word).
Variable Q : config -> Prop.

Hypothesis HEAP0 : AHEAP Σ0 OW LB m0.
Hypothesis CEIL : ACEIL <= lo.
Hypothesis LO : lo + HX_STACK_A <= bv_unsigned sp.
Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis AL16 : bv_unsigned sp mod 16 = 0.
Hypothesis FLEN : (S (S (length FRM)) < FRAMES_MAX)%nat.
Hypothesis HBIN : In (pb, out, BIO_SIZE) OW.
Hypothesis HLEN : 0 < len < 2^31.
Hypothesis HDIN : In (bd, D, len) (OW ++ LB).
Hypothesis NE : bd <> pb.

(* [comment removed for export] *)
Definition hx_hi : list cell := [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra].
(* [comment removed for export] *)
Definition hx_invA (clo : list cell) (Σc : rts RTS) (m : mem) : Prop :=
  AHEAP Σc OW LB m /\ rt_live RTS Σc = rt_live RTS Σ0 /\ mem_inv ctasegs m /\ stk ctasegs m lo (bv_unsigned sp + -144)
  /\ apres_ex LB OW (bv_unsigned sp) [(out, out + 128)]%Z m0 m
  /\ rw_cells ctasegs m (bv_unsigned sp + -104) hx_hi /\ rw_cells ctasegs m (bv_unsigned sp + -144) clo /\ cells_size clo = 40%nat
  /\ rw_cells ctasegs m D [CB (Z.to_nat len) bs].
Definition hx_bioA (m : mem) (nw : Z) : Prop := 0 <= nw < 2^64 /\ rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw).

(* [comment removed for export] *)
Hypothesis KRET : forall (Σ' : rts RTS) (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (nw' : Z),
  AHEAP Σ' OW LB m' -> rt_live RTS Σ' = rt_live RTS Σ0 -> rt_credit RTS Σ0 - HX_CRED len <= rt_credit RTS Σ' ->
  stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' -> apres_ex LB OW (bv_unsigned sp) [(out, out + 128)]%Z m0 m' ->
  0 <= nw' < 2^64 -> rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv nw') ->
  cps ctasegs (ASTA RTS Σ' PMc (eq
    (MS (mkR vra sp gp (wz TP_A) t0 t1 t2 v8 v9 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F' (ret_pc vra) fc' None m' (seg_rom ctasegs)))) Q.

Local Ltac open_inv H := try match goal with H' : cells_size _ = 40%nat |- _ => clear H' end; destruct H as (HEAP & LIVE & MI & ST & AGR & FRH & FRL & SZ & HS).

(* [comment removed for export] *)
Lemma hx_factsA :
  0 < out /\ out + 128 <= ACEIL /\ 0 < D /\ D + len <= ACEIL /\ (D + len <= out \/ out + 128 <= D)
  /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP.
Proof.
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP0 HBIN') as (B0 & _ & _ & BC & _). cbn [blk_addr blk_size fst snd] in B0, BC.
  pose proof (AH_range_gen _ _ _ _ _ HEAP0 HDIN) as (D0 & _ & _ & DC & _). cbn [blk_addr blk_size fst snd] in D0, DC.
  pose proof (AH_disjoint_gen _ _ _ _ (bd, D, len) (pb, out, 128) HEAP0 HDIN HBIN' NE) as SEP. cbn [blk_addr blk_size fst snd] in SEP.
  pose proof (AH_ceil _ _ _ _ HEAP0) as (C1 & C2 & C3).
  repeat split; assumption.
Qed.

Local Ltac facts :=
  pose proof hx_factsA as (OB0 & OBC & S0 & SC & SEP & Cq1 & Cq2 & Cq3); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3;
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  pose proof LO as LO'; unfold HX_STACK_A, BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK in LO';
  pose proof CEIL as CEILu; unfold BnHeapA.ACEIL in CEILu; pose proof TOP as TOPu; unfold USTACK_TOP in TOPu;
  pose proof OBC as OBCu; unfold BnHeapA.ACEIL in OBCu; pose proof SC as SCu; unfold BnHeapA.ACEIL in SCu;
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0; lia).

(* [comment removed for export] *)
Lemma hx_callA : forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (clo : list cell) (A : Z) (fmt : list Z) (args : list parg) (o : list Z)
    (retpc used : Z),
  hx_invA clo Σc m -> hx_bioA m nw -> rt_credit RTS Σ0 - used <= rt_credit RTS Σc -> 0 <= used -> used + 3 <= HX_CRED len -> HX_CRED len <= rt_credit RTS Σ0 ->
  vfmtA_ok A fmt args o -> 0 < zlength o < 512 -> vargsA_ok OW LB m [a2; a3; a4; a5; a6; a7] args ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 A -> x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS),
     hx_invA clo Σc' m' -> hx_bioA m' ((nw + zlength o) mod 2^64) -> rt_credit RTS Σ0 - (used + 3) <= rt_credit RTS Σc' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0' t1' t2' x8 x9 (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7'
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
           Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 BIO_PRINTF_A) fc None m (seg_rom ctasegs)))) Q.
Proof using AL16 CEIL FLEN HBIN HDIN HEAP0 HLEN LO NE PFC TOP.
  intros until used. intros INV BIO CR U0 U3 CRED VF OLEN VARGS -> -> -> Hret EVEN K. destruct BIO as [NW HB]. open_inv INV. facts.
  eapply cps_step_rt.
  { eapply (BIO_printf_null_cpsA PFC) with (lo := lo) (OW := OW) (LB := LB) (pb := pb) (out := out) (pv := pv) (nw := nw) (A := A) (o := o);
      rewrite ?ESP; try reflexivity.
    - exact HEAP.
    - exact ST.
    - exact CEIL.
    - unfold BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu. lia.
    - clear - AL16. Z.div_mod_to_equations. lia.
    - exact MI.
    - exact FLEN.
    - clear - CR U0 U3 CRED. lia.
    - exact HBIN.
    - exact HB.
    - exact NW.
    - exact VF.
    - exact OLEN.
    - exact VARGS. }
  intros Σ1 msP PO LIVE1. unfold bio_printf_null_post in PO. rewrite ?ESP in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & -> & MI1 & ST1 & AP1 & HEAP1 & _ & CR1 & HB1).
  rewrite (ret_pc_even retpc) by (first [exact EVEN | clear - Hret EVEN; lia]). unfold MallocRep.wz.
  unfold apres_ex, BIO_SIZE in AP1. unfold hx_hi in FRH.
  apply (rw_cells_agree _ _ _ _ _ AP1) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu; lia| split; [clear - Hxa OBCu CEILu LO'; lia| exact I]]].
  apply (rw_cells_agree _ _ _ _ _ AP1) in FRL; [| intros xa Hxa; cbn in Hxa; rewrite SZ in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu; lia| split; [clear - Hxa OBCu CEILu LO'; lia| exact I]]].
  apply (rw_cells_agree _ _ _ _ _ AP1) in HS; [| intros xa Hxa; cbn in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by (clear - HLEN; lia); cbn [outside fst snd]; split; [right; right; exists (bd, D, len); split; [exact HDIN| cbn; clear - Hxa; lia]| split; [clear - Hxa SEP; lia| exact I]]].
  eapply K.
  - split; [exact HEAP1|]. split; [rewrite LIVE1; exact LIVE|]. split; [exact MI1|]. split; [exact ST1|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AP1|]. intros a [Ha Ho]. split; [| exact Ho].
             destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]. }
    split; [exact FRH|]. split; [exact FRL|]. split; [exact SZ| exact HS].
  - split; [apply Z.mod_pos_bound; clear; lia| rewrite bio_null_cells_mod; exact HB1].
  - clear - CR CR1. lia.
Qed.

(* [comment removed for export] *)
Lemma hx_lastA : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 x23 x25 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (clo : list cell) (used : Z),
  hx_invA clo Σc m -> hx_bioA m nw -> rt_credit RTS Σ0 - used <= rt_credit RTS Σc -> 0 <= used -> used + 3 <= HX_CRED len -> HX_CRED len <= rt_credit RTS Σ0 ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 (len + -1)) x20 x21 x22 x23 (Z_to_bv 64 D) x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 HX_LAST_A) fc None m (seg_rom ctasegs)))) Q.
Proof using AL16 CEIL FLEN HBIN HDIN HEAP0 HLEN KRET LO NE PFC TOP.
  intros until used. intros INV BIO CR U0 U3 CRED. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  ablock HEAP HDIN ACC OFF.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m) as MU.
  assert (OFFW : offshW [(bv_unsigned sp + -144, bv_unsigned sp)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu; alia).
  destruct (hx_data_read m D (Z.to_nat len) bs (len + -1) (wa (D + (len + -1))) HS ltac:(rewrite Z2Nat.id by (clear - HLEN; lia); clear - HLEN; lia) eq_refl) as (b & NTH & RD).
  pose proof (hx_byte_range b) as BR.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HB.
  apply cps_from_evt'. unfold HX_LAST_A.
  (* [comment removed for export] *)
  apre. setreg 10%Z (Z_to_bv 64 (D + (len + -1))) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by (clear - S0 SCu HLEN; lia); bv_solve).
  zstep. clear RD.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply hx_callA with (nw := nw) (clo := clo) (A := A_C15_A) (fmt := FMT_C15) (args := [PA_u (bv_unsigned b)]) (o := hex2 (bv_unsigned b)) (retpc := 0x23abc0) (used := used);
    [exact INV'| exact BIO'| exact CR| exact U0| exact U3| exact CRED
    | apply vfmtA_C15; exact BR
    | change (zlength (hex2 (bv_unsigned b))) with 2; clear; lia
    | cbn [vargsA_ok]; split; [| exact I]; cbn [vargA_ok]; rewrite unsigned_lit by (clear - BR; lia); clear - BR; split; [lia| apply Z.mod_small; lia]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  clear dependent m. clear dependent Σc. clear SZ.
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fc' m Σc INV [NW' HB'] CR.
  open_inv INV. unfold hx_hi in FRH. unfold bio_null_cells, bio_cells, MallocRep.wz in HB'.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. do 13 zstep.
  (* [comment removed for export] *)
  assert (FR : rw_cells ctasegs m (bv_unsigned sp + -144) (clo ++ [C8 v27; C8 v26; C8 v25; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra])).
  { apply rw_cells_app. split; [exact FRL|]. rewrite SZ. replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by (clear; lia). exact FRH. }
  clear FRL FRH.
  zstep. (* [comment removed for export] *)
  eapply stk_release in FR; [| exact ST| clear - SPR LO' CEILu OBCu OB0; lia]. clear ST. rename FR into ST.
  rewrite cells_size_app, SZ in ST. cbn [cells_size csize Nat.add] in ST.
  replace (bv_unsigned sp + -144 + Z.of_nat 144) with (bv_unsigned sp) in ST by (clear; lia).
  zstep. (* [comment removed for export] *)
  apply evt_done.
  eapply (KRET Σc m _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc' fc' ((nw + zlength (hex2 (bv_unsigned b))) mod 2^64));
    [exact HEAP| exact LIVE| clear - CR U3; lia| exact ST| exact MI| exact AGR| exact NW'| unfold bio_null_cells, bio_cells, MallocRep.wz; exact HB'].
Qed.

(* [comment removed for export] *)
Definition hx_lo (pad : list byte) : list cell := [CB 8 pad; C8 (Z_to_bv 64 (len + -1)); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 A_C12_A); C8 (Z_to_bv 64 20)].

Section LOOP.

(* [comment removed for export] *)
Definition at_head (i used : Z) : Prop :=
  forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (pad : list byte) (nw : Z),
    hx_invA (hx_lo pad) Σc m -> hx_bioA m nw -> rt_credit RTS Σ0 - used <= rt_credit RTS Σc ->
    cps ctasegs (ASTA RTS Σc PMc (eq
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (- i)) (Z_to_bv 64 (- (len + -1))) (Z_to_bv 64 16) (Z_to_bv 64 (D + i)) (Z_to_bv 64 A_EMPTYH_A) (Z_to_bv 64 A_C13_A)
               (Z_to_bv 64 (D + i)) (Z_to_bv 64 A_C14_A) (Z_to_bv 64 SHB) (Z_to_bv 64 (i mod 16)) t3 t4 t5 t6)
          Fc (Z_to_bv 64 HX_LOOP_A) fc None m (seg_rom ctasegs)))) Q.
(* [comment removed for export] *)
Definition at_tail (used : Z) : Prop :=
  forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (pad : list byte) (nw j : Z),
    hx_invA (hx_lo pad) Σc m -> hx_bioA m nw -> rt_credit RTS Σ0 - used <= rt_credit RTS Σc -> 0 <= j < 16 ->
    cps ctasegs (ASTA RTS Σc PMc (eq
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
               x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 SHB) (Z_to_bv 64 j) t3 t4 t5 t6)
          Fc (Z_to_bv 64 HX_TAIL_A) fc None m (seg_rom ctasegs)))) Q.

(* [comment removed for export] *)
Lemma hx_tailA : forall used, 0 <= used -> used + 6 <= HX_CRED len -> HX_CRED len <= rt_credit RTS Σ0 -> at_tail used.
Proof using AL16 CEIL FLEN HBIN HDIN HEAP0 HLEN KRET LO NE PFC TOP.
  intros used U0 U6 CRED. unfold at_tail. intros until j. intros INV BIO CR HJ. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  unfold hx_lo in FRL.
  apply cps_from_evt'. unfold HX_TAIL_A.
  (* [comment removed for export] *)
  zstep. zstep.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    apply evt_done. eapply hx_lastA; [exact INV'| exact BIO'| exact CR| exact U0| clear - U6; lia| exact CRED].
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done.
    eapply hx_callA with (nw := nw) (clo := hx_lo pad) (A := A_C12_A) (fmt := FMT_C12) (args := [PA_i 20; PA_s []]) (o := zrepeat 32 20) (retpc := 0x23ab98) (used := used);
      [exact INV'| exact BIO'| exact CR| exact U0| clear - U6; lia| exact CRED
      | exact vfmtA_C12
      | change (zlength (zrepeat 32 20)) with 20; clear; lia
      | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyh_vargA| exact I]
      | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
    clear dependent m. clear dependent Σc.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fc' m Σc INV BIO CR.
    eapply hx_lastA; [exact INV| exact BIO| exact CR| clear - U0; lia| clear - U6; lia| exact CRED].
Qed.

(* [comment removed for export] *)
Lemma hx_end8A : forall (i u j4 : Z), 0 <= i < len - 1 -> j4 = (i + 1) mod 16 ->
  (i + 1 < len - 1 -> at_head (i + 1) u) -> (i + 1 = len - 1 -> at_tail u) ->
  forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (pad : list byte) (nw : Z),
    hx_invA (hx_lo pad) Σc m -> hx_bioA m nw -> rt_credit RTS Σ0 - u <= rt_credit RTS Σc ->
    cps ctasegs (ASTA RTS Σc PMc (eq
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (- i)) (Z_to_bv 64 (- (len + -1))) (Z_to_bv 64 16) (Z_to_bv 64 (D + i)) (Z_to_bv 64 A_EMPTYH_A) (Z_to_bv 64 A_C13_A)
               (Z_to_bv 64 (D + i)) (Z_to_bv 64 A_C14_A) (Z_to_bv 64 SHB) (Z_to_bv 64 j4) t3 t4 t5 t6)
          Fc (Z_to_bv 64 HX_END8_A) fc None m (seg_rom ctasegs)))) Q.
Proof using CEIL FLEN HBIN HDIN HEAP0 HLEN NE.
  intros i u j4 HI HJ4 KH KT. intros until nw. intros INV BIO CR. pose proof BIO as [NW _].
  pose proof hx_factsA as (OB0 & OBC & S0 & SC & _). pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu. pose proof SC as SCu. unfold BnHeapA.ACEIL in SCu.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (HJ4' : 0 <= j4 < 16) by (subst j4; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  apply cps_from_evt'. unfold HX_END8_A.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit_wrap in K; try change 18446744073709551615 with (Z.ones 64) in K;
    rewrite ?Z.land_ones in K by (clear; lia); rewrite ?E64 in K.
  - (* [comment removed for export] *)
    jump (apply evt_done; eapply (KH ltac:(clear - K HI HLEN; Z.div_mod_to_equations; lia)); [exact INV| exact BIO| exact CR]).
  - (* [comment removed for export] *)
    zstep. jump (apply evt_done; eapply (KT ltac:(clear - K HI HLEN; Z.div_mod_to_equations; lia)); [exact INV| exact BIO| exact CR| exact HJ4']).
Qed.

(* [comment removed for export] *)
Lemma hx_midA : forall (i used : Z), 0 <= i < len - 1 -> 0 <= used -> used + 9 <= HX_CRED len -> HX_CRED len <= rt_credit RTS Σ0 ->
  (i + 1 < len - 1 -> at_head (i + 1) (used + 9)) -> (i + 1 = len - 1 -> at_tail (used + 9)) ->
  forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (pad : list byte) (nw : Z),
    hx_invA (hx_lo pad) Σc m -> hx_bioA m nw -> rt_credit RTS Σ0 - (used + 3) <= rt_credit RTS Σc ->
    cps ctasegs (ASTA RTS Σc PMc (eq
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (- i)) (Z_to_bv 64 (- (len + -1))) (Z_to_bv 64 16) (Z_to_bv 64 (D + i)) (Z_to_bv 64 A_EMPTYH_A) (Z_to_bv 64 A_C13_A)
               (Z_to_bv 64 (D + i)) (Z_to_bv 64 A_C14_A) (Z_to_bv 64 SHB) (Z_to_bv 64 (i mod 16)) t3 t4 t5 t6)
          Fc (Z_to_bv 64 HX_MID_A) fc None m (seg_rom ctasegs)))) Q.
Proof using AL16 CEIL FLEN HBIN HDIN HEAP0 HLEN LO NE PFC TOP.
  intros i used HI U0 U9 CRED KH KT. intros until nw. intros INV BIO CR. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  assert (HJ : 0 <= i mod 16 < 16) by (clear; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  ablock HEAP HDIN ACC OFF.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m) as MU.
  assert (OFFW : offshW [(bv_unsigned sp + -144, bv_unsigned sp)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu; alia).
  destruct (hx_data_read m D (Z.to_nat len) bs i (wa (D + i)) HS ltac:(rewrite Z2Nat.id by (clear - HLEN; lia); clear - HLEN HI; lia) eq_refl) as (b & NTH & RD).
  pose proof (hx_byte_range b) as BR.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HB. unfold hx_lo in FRL.
  apply cps_from_evt'. unfold HX_MID_A.
  (* [comment removed for export] *)
  zstep. clear RD.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  apply evt_done.
  eapply hx_callA with (nw := nw) (clo := hx_lo pad) (A := A_C13_A) (fmt := FMT_C13) (args := [PA_u (bv_unsigned b)]) (o := hex2 (bv_unsigned b) ++ [58]) (retpc := 0x23ab34) (used := used + 3);
    [exact INV'| exact BIO'| exact CR| clear - U0; lia| clear - U9; lia| exact CRED
    | apply vfmtA_C13; exact BR
    | change (zlength (hex2 (bv_unsigned b) ++ [58])) with 3; clear; lia
    | cbn [vargsA_ok]; split; [| exact I]; cbn [vargA_ok]; rewrite unsigned_lit by (clear - BR; lia); clear - BR; split; [lia| apply Z.mod_small; lia]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  clear dependent m. clear dependent Σc.
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m Σc INV BIO CR. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW3 HB3]. open_inv INV.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HB3. unfold hx_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. rewrite (swrap32_small (i mod 16 + 1)) by (clear - HJ; lia). zstep. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by (clear - HJ; lia).
  - (* [comment removed for export] *)
    apply evt_done. eapply (hx_end8A i (used + 9) (i mod 16 + 1) HI _ KH KT); [exact INV'| exact BIO'| clear - CR; lia].
    Unshelve. rewrite <- (Z.add_mod_idemp_l i 1 16) by (clear; lia). symmetry. apply Z.mod_small. clear - HJ K. lia.
  - (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply evt_done.
    eapply hx_callA with (nw := (nw + zlength (hex2 (bv_unsigned b) ++ [58])) mod 2^64) (clo := hx_lo pad) (A := A_C14_A) (fmt := FMT_C14) (args := []) (o := [10]) (retpc := 0x23ab48) (used := used + 6);
      [exact INV'| exact BIO'| clear - CR; lia| clear - U0; lia| clear - U9; lia| exact CRED
      | exact vfmtA_C14
      | change (zlength [10]) with 1; clear; lia
      | exact I
      | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
    clear dependent m. clear dependent Σc.
    intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fc5 fc5 m Σc INV BIO CR.
    apply cps_from_evt'.
    zstep. (* [comment removed for export] *)
    apply evt_done. eapply (hx_end8A i (used + 9) 0 HI _ KH KT); [exact INV| exact BIO| clear - CR; lia].
    Unshelve. rewrite <- (Z.add_mod_idemp_l i 1 16) by (clear; lia). replace (i mod 16 + 1) with 16 by (clear - HJ K; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hx_iterA : forall (i used : Z), 0 <= i < len - 1 -> 0 <= used -> used + 9 <= HX_CRED len -> HX_CRED len <= rt_credit RTS Σ0 ->
  (i + 1 < len - 1 -> at_head (i + 1) (used + 9)) -> (i + 1 = len - 1 -> at_tail (used + 9)) -> at_head i used.
Proof using AL16 CEIL FLEN HBIN HDIN HEAP0 HLEN LO NE PFC TOP.
  intros i used HI U0 U9 CRED KH KT. unfold at_head. intros until nw. intros INV BIO CR. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  assert (HJ : 0 <= i mod 16 < 16) by (clear; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HB. unfold hx_lo in FRL.
  apply cps_from_evt'. unfold HX_LOOP_A.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *) apply evt_done. eapply (hx_midA i used HI U0 U9 CRED KH KT); [exact INV'| exact BIO'| clear - CR; lia].
  - (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *) apply evt_done. eapply (hx_midA i used HI U0 U9 CRED KH KT); [exact INV'| exact BIO'| clear - CR; lia].
    + (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply evt_done.
      eapply hx_callA with (nw := nw) (clo := hx_lo pad) (A := A_C12_A) (fmt := FMT_C12) (args := [PA_i 20; PA_s []]) (o := zrepeat 32 20) (retpc := 0x23ab14) (used := used);
        [exact INV'| exact BIO'| exact CR| exact U0| clear - U9; lia| exact CRED
        | exact vfmtA_C12
        | change (zlength (zrepeat 32 20)) with 20; clear; lia
        | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyh_vargA| exact I]
        | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
      clear dependent m. clear dependent Σc.
      intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fc5 fc5 m Σc INV BIO CR5.
      eapply (hx_midA i used HI U0 U9 CRED KH KT); [exact INV| exact BIO| exact CR5].
Qed.

(* [comment removed for export] *)
Lemma hx_loopA : forall (k : nat) (i used : Z), Z.of_nat k = len - 1 - i -> 0 <= i < len - 1 -> 0 <= used <= 9 * i -> HX_CRED len <= rt_credit RTS Σ0 ->
  at_head i used.
Proof.
  induction k as [|k IH]; intros i used HK HI HU CRED; [lia|].
  apply (hx_iterA i used HI ltac:(lia) ltac:(unfold HX_CRED; lia) CRED).
  - intros Hlt. apply (IH (i + 1) (used + 9)); [lia| lia| lia| exact CRED].
  - intros Heq. apply (hx_tailA (used + 9)); [lia| unfold HX_CRED; lia| exact CRED].
Qed.

End LOOP.

(* [comment removed for export] *)
Lemma hx_stkW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(bv_unsigned sp + -144, bv_unsigned sp)]%Z a.
Proof using CEIL HEAP0 LO.
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP0) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof LO as LO'. unfold HX_STACK_A, BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK in LO'.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  cbn [outside fst snd]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - clear - Ha; lia.
  - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' C1; unfold BnHeapA.ACEIL in *; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP0 Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia.
Qed.

(* [comment removed for export] *)
Lemma hx_mainA : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (nw : Z),
  stk ctasegs m0 lo (bv_unsigned sp) -> mem_inv ctasegs m0 -> HX_CRED len <= rt_credit RTS Σ0 ->
  rw_cells ctasegs m0 out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 -> rw_cells ctasegs m0 D [CB (Z.to_nat len) bs] ->
  cps ctasegs (ASTA RTS Σ0 PMc (eq
    (MS (mkR vra sp gp (wz TP_A) t0 t1 t2 v8 v9 (Z_to_bv 64 out) (Z_to_bv 64 20) (Z_to_bv 64 16) (Z_to_bv 64 D) (Z_to_bv 64 len) a5 a6 a7
             v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_HEX_STRING_A) fc None m0 (seg_rom ctasegs)))) Q.
Proof using AL16 CEIL FLEN HBIN HDIN HEAP0 HLEN KRET LO NE PFC TOP.
  intros until nw. intros ST MI CRED HB NW HS. facts.
  assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m0) as MU. pose proof (wmono_refl ctasegs m0) as WM.
  assert (OFFW : offshW [(bv_unsigned sp + -144, bv_unsigned sp)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu; alia).
  pose proof HEAP0 as HEAP.
  apply cps_from_evt'. unfold BIO_HEX_STRING_A.
  (* [comment removed for export] *)
  carve_frame 144%nat ST. zstep. do 13 zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit, ?signed_of_Z in K by (clear - HLEN; lia); clear - K HLEN; lia|]. try clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep. rewrite (swrap32_small (len + -1)) by (clear - HLEN; lia).
  name_mem m1.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells _ m1 (bv_unsigned sp + -144) (?c0 :: ?c1 :: ?rest) |- _ =>
      pose proof (proj1 (rw_cells_app m1 _ [c0; c1] rest) FR) as [FRL FRH]; clear FR end.
    cbn [cells_size csize Nat.add] in FRH. replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) in FRH by (clear; lia).
    match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end.
    match goal with H : munch _ m0 m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m0 m1 |- _ => rename H into WM1 end.
    apply evt_done. lazymatch type of FRL with rw_cells _ _ _ ?cl =>
    eapply hx_lastA with (nw := nw) (clo := cl) (used := 0) end;
      [| split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]| clear; lia| clear; lia| unfold HX_CRED; clear - HLEN; lia| exact CRED].
    split. { eapply AH_frame; [exact HEAP0| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|].
    split; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a [Ha _]; exact (hx_stkW a Ha)]|].
    split; [exact FRH|]. split; [exact FRL|]. split; [reflexivity| exact HS].
  - (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. zstep.
    zstep. setreg 10%Z (Z_to_bv 64 (len + -1))
            ltac:(symmetry; f_equal; change 4294967295 with (Z.ones 32); rewrite Z.land_ones by (clear; lia); rewrite Z.mod_small by (clear - HLEN; lia); reflexivity).
    zstep. zstep. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    name_mem m2.
    lazymatch goal with FR : rw_cells _ m2 (bv_unsigned sp + -144) (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
      pose proof (proj1 (rw_cells_app m2 _ [c0; c1; c2; c3; c4] rest) FR) as [FRL FRH]; clear FR end.
    cbn [cells_size csize Nat.add] in FRH. replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) in FRH by (clear; lia).
    match goal with H : mem_inv ctasegs m2 |- _ => rename H into MI2 end. match goal with H : stk ctasegs m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : munch _ m0 m2 |- _ => rename H into MU2 end. match goal with H : wmono ctasegs m0 m2 |- _ => rename H into WM2 end.
    assert (HK : Z.of_nat (Z.to_nat (len - 1)) = len - 1 - 0) by (clear - HLEN K; lia). assert (HI : 0 <= 0 < len - 1) by (revert K; rewrite ?unsigned_lit by (clear - HLEN E64; lia); clear - HLEN; lia).
    assert (HU : 0 <= 0 <= 9 * 0) by (clear; lia).
    pose proof (hx_loopA _ 0 0 HK HI HU CRED) as HL. unfold at_head in HL.
    jump (apply evt_done; eapply HL; [| split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]| clear; lia]).
    split. { eapply AH_frame; [exact HEAP0| exact MU2| exact WM2|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
    split; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU2)| intros a [Ha _]; exact (hx_stkW a Ha)]|].
    split; [exact FRH|]. split; [exact FRL|]. split; [reflexivity| exact HS].
Qed.

(* [comment removed for export] *)
Lemma hx_zeroA : forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (nw : Z),
  stk ctasegs m0 lo (bv_unsigned sp) -> mem_inv ctasegs m0 -> 0 <= HX_CRED len ->
  rw_cells ctasegs m0 out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  cps ctasegs (ASTA RTS Σ0 PMc (eq
    (MS (mkR vra sp gp (wz TP_A) t0 t1 t2 v8 v9 (Z_to_bv 64 out) a1 a2 a3 (Z_to_bv 64 0) a5 a6 a7
             v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_HEX_STRING_A) fc None m0 (seg_rom ctasegs)))) Q.
Proof using CEIL FLEN HBIN HEAP0 KRET LO TOP.
  intros until nw. intros ST MI CR0 HB NW.
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP0 HBIN') as (OB0 & _ & _ & OBC & _). cbn [blk_addr blk_size fst snd] in OB0, OBC. pose proof OBC as OBCu. unfold BnHeapA.ACEIL in OBCu.
  pose proof (AH_ceil _ _ _ _ HEAP0) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof LO as LO'. unfold HX_STACK_A, BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK in LO'.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m0) as MU. pose proof (wmono_refl ctasegs m0) as WM.
  apply cps_from_evt'. unfold BIO_HEX_STRING_A.
  carve_frame 144%nat ST. zstep. do 13 zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit, ?signed_of_Z in K by (clear; lia); clear - K; lia]. try clear K.
  name_mem m1.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end. match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end.
  match goal with H : munch _ m0 m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m0 m1 |- _ => rename H into WM1 end.
  (* [comment removed for export] *)
  zstep. do 13 zstep.
  zstep.
  eapply stk_release in FR; [| exact ST1| clear - SPR LO' CEILu OBCu OB0; lia]. clear ST1. rename FR into ST1.
  cbn [cells_size csize Nat.add length] in ST1.
  lazymatch type of ST1 with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in ST1 by (clear; cbn; lia) end.
  zstep.
  apply evt_done.
  eapply (KRET Σ0 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc nw); [| reflexivity| clear - CR0; lia| exact ST1| exact MI1| | exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB].
  - eapply AH_frame; [exact HEAP0| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor].
  - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a [Ha _]; exact (hx_stkW a Ha)].
Qed.

End HX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem BIO_hex_string_cpsA {AR : ARun} (PFC : printf_contracts (@ar_RT AR)) :
  forall (Q : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR)) (OW LB : list block) (lo : Z) (pb bd : bptr) (out pv nw D len : Z) (bs : list byte),
  @BnHeapA.AHEAP AR Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> @BnHeapA.ACEIL AR <= lo -> lo + HX_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (length (@ar_FR AR))) < FRAMES_MAX)%nat -> HX_CRED len <= rt_credit (@ar_RT AR) Σ ->
  In (pb, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  0 <= len < 2^31 ->
  (0 < len -> In (bd, D, len) (OW ++ LB) /\ bd <> pb /\ rw_cells ctasegs m D [CB (Z.to_nat len) bs]) ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 20 -> a2 = Z_to_bv 64 16 -> a3 = Z_to_bv 64 D -> a4 = Z_to_bv 64 len ->
  (forall (Σ' : rts (@ar_RT AR)) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (nw' : Z),
     @BnHeapA.AHEAP AR Σ' OW LB m' -> rt_live (@ar_RT AR) Σ' = rt_live (@ar_RT AR) Σ -> rt_credit (@ar_RT AR) Σ - HX_CRED len <= rt_credit (@ar_RT AR) Σ' ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' -> apres_ex LB OW (bv_unsigned sp) [(out, out + 128)]%Z m m' ->
     0 <= nw' < 2^64 -> rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv nw') ->
     cps ctasegs (ASTA (@ar_RT AR) Σ' (@ar_PMc AR) (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA (@ar_RT AR) Σ (@ar_PMc AR) (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_HEX_STRING_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bs. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED HBIN HB NW HLEN DFACTS -> -> -> -> -> K.
  destruct (Z.eq_dec len 0) as [L0|L0].
  - subst len. eapply hx_zeroA; [exact HEAP| exact CEIL| exact LO| exact TOP| exact FLEN| exact HBIN| exact K| exact ST| exact MI| unfold HX_CRED; clear; lia| exact HB| exact NW].
  - destruct (DFACTS ltac:(clear - HLEN L0; lia)) as (HDIN & NE & HS).
    eapply (hx_mainA PFC); [exact HEAP| exact CEIL| exact LO| exact TOP| exact AL16| exact FLEN| exact HBIN| clear - HLEN L0; lia| exact HDIN| exact NE| exact K
      | exact ST| exact MI| exact CRED| exact HB| exact NW| exact HS].
Qed.
