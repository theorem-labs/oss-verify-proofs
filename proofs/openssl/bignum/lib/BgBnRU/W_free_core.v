(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG BnBase BnModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3 W_alloc3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HF : rfree_stmt.

  Lemma BN_free_walk_dq_n : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (pd q : bptr) (A D n lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L -> In (q, A, n) L -> 24 <= n -> pd <> q -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 1 ->
    a0 = wz A ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pd L) q lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (LFree pd (LFree q k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP IND INQ HN24 NE AUX SPB ST CEIL GLO LO ERR MI -> CS BN HF8 EL8 EL2 EL1 -> K.
    unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP INQ) as (BQ0 & BQ16 & _ & BQC & BQI). cbn [blk_addr blk_size fst snd] in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof BN as BN0. unfold bn_cells in BN.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    assert (QA8 : A mod 8 = 0) by (clear - BQ16; Z.div_mod_to_equations; lia).
    step. rewrite (land7_wrap _ QA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL2 by lia. step. if_false.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' L) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (bn_free_d0_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (D := D) (b := b) (pd := pd);
      [exact HEAP1 | exact IND | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1
      | exact BN | exact HF8 | exact EL8 | rewrite ESP; lia | exact QA8 | reflexivity | reflexivity | ].
    intros st1 ms1 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    replace (ret_pc (Z_to_bv 64 1040392)) with (Z_to_bv 64 1040392) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INQ4 : In (q, A, n) (lb_remove pd L)) by (apply lb_remove_In; split; [exact INQ | cbn; intros E; apply NE; symmetry; exact E]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in BN.
    2: { intros a Ha. cbn in Ha. right. right. exists (q, A, n). split; [exact INQ4 | cbn; lia]. }
    assert (CS4 : crypto_statics m4).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP4) | intros a Ha; apply libw_client; exact Ha | exact CS1]. }
    assert (HP0 : rheap_pres (lb_remove pd L) (bv_unsigned sp) m m4).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP4| lia| auto]. }
    clear HEAP1 AUX1 CS1 HEAP AUX CS MI ERR MU WM ST.
    unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4. unfold MallocRep.wz.
    unfold implM. iprefix.
    step. unfold wz at 1. rewrite (sx32_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL1 by lia. step. if_true.
    do 3 step. step.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl bgusegs m4) as WM4.
    do 4 step. release_frame FR ST4 (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (HEAP5 : RHEAP st1 (lb_remove pd L) m5).
    { eapply LH_frame; [exact HEAP4| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX5 : rauxv_ok m5 B).
    { eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS5 : crypto_statics m5).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU4 WM4)| | exact CS4].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI5 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove q (lb_remove pd L)) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' (lb_remove pd L)) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP4 Hb2) as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := n);
      [exact HEAP5 | exact INQ4 | exact AUX5 | exact SPB | exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | reflexivity | exact CS5 | reflexivity | ].
    intros st6 ms6 PO. apply K. unfold cfree_post in PO |- *.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
    do 15 eexists. exists m6. split; [reflexivity|].
    split; [exact MI6|]. split; [exact ST6|]. split; [exact ERR6|]. split; [exact AUX6|].
    split. { eapply rheap_pres_trans; [| exact HP6].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0 | lia | intros b0 Hb0; eapply lb_remove_incl; exact Hb0] |].
             eapply heap_pres_of_munch; [exact MU4| exact WM4| apply CLI5]. }
    split; [rewrite FA6; exact FA4|]. split; [rewrite SO6; exact SO4|]. exact HEAP6.
  Qed.

  Lemma BN_free_walk_q_n : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (q : bptr) (A n lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (q, A, n) L -> 24 <= n -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells 0 b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 1 ->
    a0 = wz A ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L q lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (LFree q k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP INQ HN24 AUX SPB ST CEIL GLO LO ERR MI -> CS BN HF8 EL8 EL2 EL1 -> K.
    unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP INQ) as (BQ0 & BQ16 & _ & BQC & BQI). cbn [blk_addr blk_size fst snd] in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BN.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    assert (QA8 : A mod 8 = 0) by (clear - BQ16; Z.div_mod_to_equations; lia).
    step. rewrite (land7_wrap _ QA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL2 by lia. step. if_false.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (bn_free_d0_null_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A) (b := b);
        [ exact BN | exact HF8 | exact EL8 | rewrite ESP; exact ST | unfold GLOBALS_TOP; lia | rewrite ESP; lia | exact MI | rewrite ESP; lia
        | exact QA8 | exact CS1 | reflexivity | reflexivity ]. }
    cbv beta. intros ms2 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite ESP in MU2, ST2. replace (ret_pc (Z_to_bv 64 1040392)) with (Z_to_bv 64 1040392) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MU12 : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; lia. }
    assert (WM12 := wmono_trans bgusegs _ _ _ WM WM2).
    assert (FR2 := rw_cells_transport bgusegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (BN2 := rw_cells_transport bgusegs _ m1 m2 _ _ BN MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (ERR2 := rw_cells_transport bgusegs _ m1 m2 _ _ ERR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (HEAP2 : RHEAP s L m2).
    { eapply LH_frame; [exact HEAP| exact MU12| exact WM12|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU12| exact WM12|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU12 WM12)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove q L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' L) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _). lia. }
    clear CS1 MU WM FR BN ERR ST MI MU2 WM2.
    step. unfold wz at 1. rewrite (sx32_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL1 by lia. step. if_true.
    do 3 step. step.
    do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := n);
      [exact HEAP2 | exact INQ | exact AUX2 | exact SPB | exact ST2 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI2 | reflexivity | exact CS2 | reflexivity | ].
    intros st6 ms6 PO. apply K. unfold cfree_post in PO |- *.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
    do 15 eexists. exists m6. split; [reflexivity|].
    split; [exact MI6|]. split; [exact ST6|]. split; [exact ERR6|]. split; [exact AUX6|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU12| exact WM12| apply CLI]| exact HP6]. }
    split; [exact FA6|]. split; [exact SO6|]. exact HEAP6.
  Qed.

  Lemma BN_free_walk_mal_n : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (q : bptr) (A D n lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (q, A, n) L -> 24 <= n ->
    (forall pd, bn_d b = Some pd -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L /\ pd <> q) ->
    (bn_d b = None -> D = 0) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 1 ->
    a0 = wz A ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove_opt (bn_d b) L) q lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lbind (lfree_opt (bn_d b)) (fun _ => LFree q k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP INQ HN24 HS HN AUX SPB ST CEIL GLO LO ERR MI Etp CS BN HF8 EL8 EL2 EL1 Ea0 K.
    destruct (bn_d b) as [pd|] eqn:Ed.
    - destruct (HS pd eq_refl) as [IND NE]. cbn [lfree_opt lfree lbind lb_remove_opt] in K |- *.
      eapply BN_free_walk_dq_n; try eassumption.
    - specialize (HN eq_refl). subst D. cbn [lfree_opt lbind lb_remove_opt] in K |- *.
      eapply BN_free_walk_q_n; try eassumption.
  Qed.

End Proofs.
End WithCeiling0.
