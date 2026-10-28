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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_obj_free ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

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

Definition SCT_FREE_A : Z := 0x337578.
Definition SCT_FREE_STACK_A : Z := 32 + CRYPTO_FREE_STACK.
(* [comment removed for export] *)
Definition A_CT_SCT_C_A : Z := 0xa7a40.

Local Notation E_f1 := (E_SCT_free_34ba4c : uk_call 0x337578 0x3375d0 0x1fd334).   (* [comment removed for export] *)
Local Notation E_f2 := (E_SCT_free_34ba78 : uk_call 0x337578 0x3375fc 0x1fd334).   (* [comment removed for export] *)
Local Notation E_f3 := (E_SCT_free_34baa4 : uk_call 0x337578 0x337628 0x1fd334).   (* [comment removed for export] *)
Local Notation E_f4 := (E_SCT_free_34bad4 : uk_call 0x337578 0x337658 0x1fd334).   (* [comment removed for export] *)
Local Notation E_ft := (E_SCT_free_34bafc : uk_tail 0x337578 0x1fd334).            (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)

Lemma SCT_free_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (psct : bptr) (A : Z) (oL oE oS oB : option (bptr * Z)) (adr : bptr -> Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  let L1 := lremove oL OW in let L2 := lremove oE L1 in let L3 := lremove oS L2 in let L4 := lremove oB L3 in
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SCT_FREE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (psct, A, SCT_SIZE) OW ->
  match oL with Some (q, n) => In (q, adr q, n) OW | None => True end ->
  match oE with Some (q, n) => In (q, adr q, n) L1 | None => True end ->
  match oS with Some (q, n) => In (q, adr q, n) L2 | None => True end ->
  match oB with Some (q, n) => In (q, adr q, n) L3 | None => True end ->
  In (psct, A, SCT_SIZE) L4 ->
  ro_cells ctasegs m (A + SCTO_SCT) [C8 (wz (optr adr oB))] ->
  ro_cells ctasegs m (A + SCTO_LOG_ID) [C8 (wz (optr adr oL))] ->
  ro_cells ctasegs m (A + SCTO_EXT) [C8 (wz (optr adr oE))] ->
  ro_cells ctasegs m (A + SCTO_SIG) [C8 (wz (optr adr oS))] ->
  a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_FREE_A (bv_unsigned ra :: ras) ->
  (forall Σ' ms', ofree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove psct L4) LB lo m Σ' ms' -> implAp k Σ' Q ms') ->
  implAp (ofree (option_map fst oL) (ofree (option_map fst oE) (ofree (option_map fst oS) (ofree (option_map fst oB) (AFree psct k))))) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_FREE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. cbn zeta. intros HEAP ST CEIL LO SPT SP16 MI -> CS HSCT HINL HINE HINS HINB HSCT4 HPB HPL HPE HPS -> UW CTX K.
  unfold SCT_FREE_STACK_A, CRYPTO_FREE_STACK, RT_STACK, SCT_FREE_A, MallocRep.wz in *.
  unfold SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG, SCT_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HSCT' : In (psct, A, 104) (OW ++ LB)) by (apply in_or_app; left; exact HSCT).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSCT') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HSCT)) as ALB.
  cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  assert (SEPB : A + 104 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) by (unfold BnHeapA.ACEIL in *; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HSCT' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 32, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 6 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EA in K0; lia|]. clear K0.
  step. step. step. step. step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { uw_call_mu_tac m 32 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]. }
  (* [comment removed for export] *)
  assert (TRro : forall (L' : list block) mA mB AX cs, agree_on (aclient_addr (L' ++ LB) (bv_unsigned sp + -32)) mA mB -> In (psct, A, 104) L' ->
                 A <= AX -> AX + Z.of_nat (cells_size cs) <= A + 104 -> ro_cells ctasegs mA AX cs -> ro_cells ctasegs mB AX cs).
  { intros L' mA mB AX cs AG IN X1 X2 H. eapply (ro_cells_agree _ _ _ _ _ AG); [exact H|].
    intros a Ha. right. right. exists (psct, A, 104). split; [apply in_or_app; left; exact IN|]. cbn. lia. }
  assert (TRfr : forall (L' : list block) mA mB cs, agree_on (aclient_addr (L' ++ LB) (bv_unsigned sp + -32)) mA mB ->
                 rw_cells ctasegs mA (bv_unsigned sp + -32) cs -> Z.of_nat (cells_size cs) = 32 -> rw_cells ctasegs mB (bv_unsigned sp + -32) cs).
  { intros L' mA mB cs AG H SZ. eapply (rw_cells_agree _ _ _ _ _ AG); [exact H|]. intros a Ha. left. rewrite SZ in Ha. unfold USTACK_TOP. lia. }
  assert (TRcs : forall (L' : list block) mA mB, agree_on (aclient_addr (L' ++ LB) (bv_unsigned sp + -32)) mA mB -> crypto_statics mA -> crypto_statics mB).
  { intros L' mA mB AG H. eapply crypto_statics_agree; [exact AG| | exact H].
    intros a Ha. right; left; apply client_static_intro. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. lia. }
  assert (TRuw : forall (L' : list block) mA mB, agree_on (aclient_addr (L' ++ LB) (bv_unsigned sp + -32)) mA mB ->
                 uw_chain USTACK_TOP mA (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras) ->
                 uw_chain USTACK_TOP mB (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { intros L' mA mB AG H. eapply uw_chain_agreeP; [exact AG| exact H|]. intros a H1 Ha. left. unfold USTACK_TOP in *. lia. }
  assert (IN1 : In (psct, A, 104) (lremove oL OW)) by (apply lremove_incl with (od := oE); apply lremove_incl with (od := oS); apply lremove_incl with (od := oB); exact HSCT4).
  assert (IN2 : In (psct, A, 104) (lremove oE (lremove oL OW))) by (apply lremove_incl with (od := oS); apply lremove_incl with (od := oB); exact HSCT4).
  assert (IN3 : In (psct, A, 104) (lremove oS (lremove oE (lremove oL OW)))) by (apply lremove_incl with (od := oB); exact HSCT4).
  (* [comment removed for export] *)
  apply evt_done.
  eapply CRYPTO_free_opt_walkAp with (od := oL) (adr := adr) (lo := lo) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity;
    [exact HEAP1| exact HINL| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
    | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI| exact CS1| rewrite ESP; exact UW1
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_f1 CTX)|].
  intros Σ2 ms2 PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
  unfold MallocRep.wz in *. rewrite ESP in ST2, AG2. rewrite (ret_pc_even 0x3375d0) by (clear; lia).
  apply (TRfr _ _ _ _ AG2) in FR; [| reflexivity].
  apply (TRro _ _ _ _ _ AG2 IN1) in HPB; [|lia|cbn; lia]. apply (TRro _ _ _ _ _ AG2 IN1) in HPE; [|lia|cbn; lia]. apply (TRro _ _ _ _ _ AG2 IN1) in HPS; [|lia|cbn; lia].
  pose proof (TRcs _ _ _ AG2 CS1) as CS2. pose proof (TRuw _ _ _ AG2 UW1) as UW2.
  assert (IN1' : In (psct, A, 104) (lremove oL OW ++ LB)) by (apply in_or_app; left; exact IN1).
  ablock HEAP2 IN1' ACCB2 OFFB2. destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  clear HEAP1 CS1 UW1 ACCB SHB1 SHB2 HPL.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. step. step. step. step.
  apply evt_done.
  eapply CRYPTO_free_opt_walkAp with (od := oE) (adr := adr) (lo := lo) (OW := lremove oL OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity;
    [exact HEAP2| exact HINE| rewrite ESP; exact ST2| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
    | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI2| exact CS2| rewrite ESP; exact UW2
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_f2 CTX)|].
  intros Σ3 ms3 PO.
  destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
  unfold MallocRep.wz in *. rewrite ESP in ST3, AG3. rewrite (ret_pc_even 0x3375fc) by (clear; lia).
  apply (TRfr _ _ _ _ AG3) in FR; [| reflexivity].
  apply (TRro _ _ _ _ _ AG3 IN2) in HPB; [|lia|cbn; lia]. apply (TRro _ _ _ _ _ AG3 IN2) in HPS; [|lia|cbn; lia].
  pose proof (TRcs _ _ _ AG3 CS2) as CS3. pose proof (TRuw _ _ _ AG3 UW2) as UW3.
  assert (IN2' : In (psct, A, 104) (lremove oE (lremove oL OW) ++ LB)) by (apply in_or_app; left; exact IN2).
  ablock HEAP3 IN2' ACCB3 OFFB3. destruct (AH_shb _ _ _ _ HEAP3) as [SHB1'' SHB2''].
  clear HEAP2 CS2 UW2 ACCB2 SHB1' SHB2' MU2 WM2 HPE MI2 ST2.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. step. step. step. step.
  apply evt_done.
  eapply CRYPTO_free_opt_walkAp with (od := oS) (adr := adr) (lo := lo) (OW := lremove oE (lremove oL OW)) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity;
    [exact HEAP3| exact HINS| rewrite ESP; exact ST3| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
    | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI3| exact CS3| rewrite ESP; exact UW3
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_f3 CTX)|].
  intros Σ4 ms4 PO.
  destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
  unfold MallocRep.wz in *. rewrite ESP in ST4, AG4. rewrite (ret_pc_even 0x337628) by (clear; lia).
  apply (TRfr _ _ _ _ AG4) in FR; [| reflexivity].
  apply (TRro _ _ _ _ _ AG4 IN3) in HPB; [|lia|cbn; lia].
  pose proof (TRcs _ _ _ AG4 CS3) as CS4. pose proof (TRuw _ _ _ AG4 UW3) as UW4.
  assert (IN3' : In (psct, A, 104) (lremove oS (lremove oE (lremove oL OW)) ++ LB)) by (apply in_or_app; left; exact IN3).
  ablock HEAP4 IN3' ACCB4 OFFB4. destruct (AH_shb _ _ _ _ HEAP4) as [SHB1x SHB2x].
  clear HEAP3 CS3 UW3 ACCB3 SHB1'' SHB2'' MU3 WM3 HPS MI3 ST3.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  apply evt_done.
  eapply CRYPTO_free_opt_walkAp with (od := oB) (adr := adr) (lo := lo) (OW := lremove oS (lremove oE (lremove oL OW))) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity;
    [exact HEAP4| exact HINB| rewrite ESP; exact ST4| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
    | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI4| exact CS4| rewrite ESP; exact UW4
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_f4 CTX)|].
  intros Σ5 ms5 PO.
  destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F5 & fc5 & m5 & -> & MI5 & ST5 & AG5 & CR5 & HEAP5).
  unfold MallocRep.wz in *. rewrite ESP in ST5, AG5. rewrite (ret_pc_even 0x337658) by (clear; lia).
  apply (TRfr _ _ _ _ AG5) in FR; [| reflexivity].
  pose proof (TRcs _ _ _ AG5 CS4) as CS5. pose proof (TRuw _ _ _ AG5 UW4) as UW5.
  clear HEAP4 CS4 UW4 ACCB4 SHB1x SHB2x MU4 WM4 HPB MI4 ST4.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. step. step. do 4 step. release_frame FR ST5 (bv_unsigned sp). step. step.
  apply evt_done.
  eapply CRYPTO_free_walkAp with (p := psct) (A := A) (n := 104) (lo := lo) (OW := lremove oB (lremove oS (lremove oE (lremove oL OW)))) (LB := LB) (ras := ras); try reflexivity;
    [exact HEAP5| exact HSCT4| exact ST5| exact CEIL| unfold CRYPTO_FREE_STACK, RT_STACK; lia| unfold USTACK_TOP; lia| exact SP16| exact MI5| exact CS5
    | | exact (uk_ctx_tail _ _ _ E_ft CTX)|].
  { eapply uw_chain_munchP; [exact MU5 | | intros a H1 Ha; cbn [outside fst snd]; lia].
    eapply uw_chain_agreeP; [exact AG5 | | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
    eapply uw_chain_agreeP; [exact AG4 | | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
    eapply uw_chain_agreeP; [exact AG3 | | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
    eapply uw_chain_agreeP; [exact AG2 | | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
    eapply uw_chain_munchP; [exact MU1 | exact UW | intros a H1 Ha; cbn [outside fst snd]; lia]. }
  intros Σ6 ms6 PO. apply K. unfold ofree_postA.
  destruct PO as (z0 & z1 & z2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & F6 & fc6 & m6 & -> & MI6 & ST6 & AG6 & CR6 & HEAP6).
  do 17 eexists. exists m6. split; [reflexivity|].
  split; [exact MI6|]. split; [exact ST6|].
  split.
  { set (L5 := lb_remove psct (lremove oB (lremove oS (lremove oE (lremove oL OW))))).
    assert (I5 : forall b, In b (L5 ++ LB) -> In b OW \/ In b LB).
    { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left| right; exact Hb]. subst L5.
      apply lb_remove_incl in Hb. do 4 (apply lremove_incl in Hb). exact Hb. }
    assert (FRM : forall a, aclient_addr (L5 ++ LB) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)]%Z a).
    { intros a Ha. cbn [outside]. split; [| exact I].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
      - lia.
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - assert (Hb' : In b (OW ++ LB)) by (apply in_app_iff; exact (I5 b Hb)). pose proof (AH_range_gen _ _ _ _ b HEAP Hb') as (_ & _ & _ & B3' & _). unfold BnHeapA.ACEIL in *. lia. }
    assert (SUB : forall (L' : list block) mA mB, (forall b, In b L5 -> In b L') ->
              agree_on (aclient_addr (L' ++ LB) (bv_unsigned sp + -32)) mA mB -> agree_on (aclient_addr (L5 ++ LB) (bv_unsigned sp)) mA mB).
    { intros L' mA mB HL AG. eapply agree_on_mono; [exact AG|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (HL b Hb)| right; exact Hb]. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact FRM]|].
    eapply agree_on_trans; [eapply (SUB (lremove oL OW)); [subst L5; intros b Hb; apply lb_remove_incl in Hb; do 3 (apply lremove_incl in Hb); exact Hb| exact AG2]|].
    eapply agree_on_trans; [eapply (SUB (lremove oE (lremove oL OW))); [subst L5; intros b Hb; apply lb_remove_incl in Hb; do 2 (apply lremove_incl in Hb); exact Hb| exact AG3]|].
    eapply agree_on_trans; [eapply (SUB (lremove oS (lremove oE (lremove oL OW)))); [subst L5; intros b Hb; apply lb_remove_incl in Hb; apply lremove_incl in Hb; exact Hb| exact AG4]|].
    eapply agree_on_trans; [eapply (SUB (lremove oB (lremove oS (lremove oE (lremove oL OW))))); [subst L5; intros b Hb; apply lb_remove_incl in Hb; exact Hb| exact AG5]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU5)| exact FRM]|].
    rewrite (BnHeapA.lb_remove_app_l psct _ LB (AH_nodup _ _ _ _ HEAP5) ltac:(change psct with (blk_id (psct, A, 104)); apply in_map; exact HSCT4)) in AG6.
    subst L5. eapply agree_on_mono; [exact AG6|]. intros a Ha. exact Ha. }
  split; [rewrite CR6, CR5, CR4, CR3, CR2; reflexivity| exact HEAP6].
Qed.

End WithRT.
