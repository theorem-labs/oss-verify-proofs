(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApWalkTac W_prefix_create ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Lemma lremove_incl : forall od L b, In b (lremove od L) -> In b L.
Proof. intros [[q n]|] L b H; cbn [lremove] in H; [eapply lb_remove_incl; exact H | exact H]. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition SCT_FREE_STACK : Z := 32 + CRYPTO_FREE_STACK.

  (* [comment removed for export] *)
  Lemma SCT_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (psct : bptr) (A : Z) (oL oE oS oB : option (bptr * Z)) (adr : bptr -> Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    let L1 := lremove oL L in let L2 := lremove oE L1 in let L3 := lremove oS L2 in let L4 := lremove oB L3 in
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SCT_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (psct, A, SCT_SIZE) L ->
    match oL with Some (q, n) => In (q, adr q, n) L | None => True end ->
    match oE with Some (q, n) => In (q, adr q, n) L1 | None => True end ->
    match oS with Some (q, n) => In (q, adr q, n) L2 | None => True end ->
    match oB with Some (q, n) => In (q, adr q, n) L3 | None => True end ->
    In (psct, A, SCT_SIZE) L4 ->
    ro_cells ctusegs m (A + SCTO_SCT) [C8 (wz (optr adr oB))] ->
    ro_cells ctusegs m (A + SCTO_LOG_ID) [C8 (wz (optr adr oL))] ->
    ro_cells ctusegs m (A + SCTO_EXT) [C8 (wz (optr adr oE))] ->
    ro_cells ctusegs m (A + SCTO_SIG) [C8 (wz (optr adr oS))] ->
    a0 = wz A ->
    (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove psct L4) lo B errv m s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (lofree (option_map fst oL) (lofree (option_map fst oE) (lofree (option_map fst oS) (lofree (option_map fst oB) (LFree psct k))))))
      s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz SCT_FREE) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. cbn zeta. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HSCT HINL HINE HINS HINB HSCT4 HPB HPL HPE HPS -> K.
    unfold SCT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, SCT_FREE, GLOBALS_TOP, MallocRep.wz in *.
    unfold SCTO_SCT, SCTO_LOG_ID, SCTO_EXT, SCTO_SIG, SCT_SIZE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HSCT) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : A + 104 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) by lia.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    (* [comment removed for export] *)
    step. step. uchk.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    (* [comment removed for export] *)
    assert (TRro : forall (L' : list block) mA mB AX cs, rheap_pres L' (bv_unsigned sp + -32) mA mB -> In (psct, A, 104) L' ->
                   A <= AX -> AX + Z.of_nat (cells_size cs) <= A + 104 -> ro_cells ctusegs mA AX cs -> ro_cells ctusegs mB AX cs).
    { intros L' mA mB AX cs HP IN X1 X2 H. eapply (ro_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)); [exact H|].
      intros a Ha. right. right. exists (psct, A, 104). split; [exact IN|]. cbn. lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    (* [comment removed for export] *)
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv) (od := oL) (adr := adr);
      [exact HEAP1 | exact HINL | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | ].
    intros st1 ms1 PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP1 & FA1 & SO1 & HEAP2).
    replace (ret_pc (Z_to_bv 64 1693004)) with (Z_to_bv 64 1693004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (IN1 : In (psct, A, 104) (lremove oL L)) by (apply lremove_incl with (od := oE); apply lremove_incl with (od := oS); apply lremove_incl with (od := oB); exact HSCT4).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP1)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (TRro _ _ _ _ _ HP1 IN1) in HPB; [|lia|cbn; lia]. apply (TRro _ _ _ _ _ HP1 IN1) in HPE; [|lia|cbn; lia]. apply (TRro _ _ _ _ _ HP1 IN1) in HPS; [|lia|cbn; lia].
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP1)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv) (od := oE) (adr := adr);
      [exact HEAP2 | exact HINE | exact AUX2 | rewrite ESP; lia | rewrite ESP; exact ST2 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI2 | reflexivity
      | exact CS2 | reflexivity | ].
    intros st2 ms2 PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP2 & FA2 & SO2 & HEAP3).
    replace (ret_pc (Z_to_bv 64 1693020)) with (Z_to_bv 64 1693020) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (IN2 : In (psct, A, 104) (lremove oE (lremove oL L))) by (apply lremove_incl with (od := oS); apply lremove_incl with (od := oB); exact HSCT4).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP2)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (TRro _ _ _ _ _ HP2 IN2) in HPB; [|lia|cbn; lia]. apply (TRro _ _ _ _ _ HP2 IN2) in HPS; [|lia|cbn; lia].
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP2)| | exact CS2].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv) (od := oS) (adr := adr);
      [exact HEAP3 | exact HINS | exact AUX3 | rewrite ESP; lia | rewrite ESP; exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR3 | exact MI3 | reflexivity
      | exact CS3 | reflexivity | ].
    intros st3 ms3 PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP3 & FA3 & SO3 & HEAP4).
    replace (ret_pc (Z_to_bv 64 1693036)) with (Z_to_bv 64 1693036) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (IN3 : In (psct, A, 104) (lremove oS (lremove oE (lremove oL L)))) by (apply lremove_incl with (od := oB); exact HSCT4).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP3)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (TRro _ _ _ _ _ HP3 IN3) in HPB; [|lia|cbn; lia].
    assert (CS4 : crypto_statics m4).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP3)| | exact CS3].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (errv := errv) (od := oB) (adr := adr);
      [exact HEAP4 | exact HINB | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | reflexivity
      | exact CS4 | reflexivity | ].
    intros st4 ms4 PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP4 & FA4 & SO4 & HEAP5).
    replace (ret_pc (Z_to_bv 64 1693052)) with (Z_to_bv 64 1693052) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (CS5 : crypto_statics m5).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP4)| | exact CS4].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. step. step. do 4 step. step. release_frame FR ST5 (bv_unsigned sp). step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 104);
      [exact HEAP5 | exact HSCT4 | exact AUX5 | lia | exact ST5 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR5 | exact MI5 | reflexivity
      | exact CS5 | reflexivity | ].
    intros st5 ms5 PO. apply K. unfold cfree_post in PO. unfold ofree_post.
    destruct PO as (n5 & n6 & n7 & n10 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & HP5 & FA5 & SO5 & HEAP6).
    do 15 eexists. exists m6. split; [reflexivity|].
    split; [exact MI6|]. split; [exact ST6|]. split; [exact ERR6|]. split; [exact AUX6|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lremove_incl; eapply lremove_incl; eapply lremove_incl; eapply lremove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP1| lia| intros b Hb; eapply lremove_incl; eapply lremove_incl; eapply lremove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; eapply lremove_incl; eapply lremove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP3| lia| intros b Hb; eapply lremove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP4| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             exact HP5. }
    split; [congruence|]. split; [congruence|]. exact HEAP6.
  Qed.
End Proofs.
End WithCeiling0.
