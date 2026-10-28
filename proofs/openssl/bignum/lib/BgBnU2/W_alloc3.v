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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
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
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition BN_NEW : Z := 0xfe07c.
  Definition BN_NEW_STACK : Z := 16 + CRYPTO_ZALLOC_STACK.

  Lemma zero_bn_cells : forall m A,
    rw_cells bgusegs m A [CB 24%nat (repeat (Z_to_bv 8 0) 24%nat)] -> rw_cells bgusegs m A (bn_cells 0 (bn_nil 0)).
  Proof.
    intros m A [[Hwf Hb] Hw]. split; [split|].
    - cbn. repeat split.
    - cbn [cells_bytes cbytes bn_cells] in *. exact Hb.
    - cbn [cells_size csize] in *. exact Hw.
  Qed.

  Lemma BN_new_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_NEW_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP ->
    crypto_statics m ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 24 lo B m
                   (fun A m' => rw_cells bgusegs m' A (bn_cells 0 (bn_nil BN_FLG_MALLOCED))) p s' ms' ->
       implM bgusegs (interp (k (Some p))) s' Q ms') ->
    implM bgusegs (interp (LMalloc 24 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NEW) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS KN K.
    unfold BN_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, BN_NEW, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold implM. iprefix.
    carve_frame 16%nat ST. do 4 step. do 4 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 24);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 1040544)) with (Z_to_bv 64 1040544) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    apply zero_bn_cells in BLK. unfold bn_cells, bn_nil in BLK. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags length Z.of_nat Z.b2z] in BLK.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 24 lo B m
                   (fun A m' => rw_cells bgusegs m' A (bn_cells 0 (bn_nil BN_FLG_MALLOCED))) p st1); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m3) as MU3. pose proof (wmono_refl bgusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, 24) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, 24) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. rewrite (land7_wrap A) by (clear - BA16; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    step. step.
    do 3 step. release_frame FR ST3 (bv_unsigned sp). step.
    apply evt_done. unfold calloc_post, MallocRep.wz.
    do 14 eexists. exists m0, A, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [unfold LX_ERRNO, RATP; exact ERR3|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             pose proof AUX3 as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB & _).
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, 24)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    unfold bn_cells, bn_nil, BN_FLG_MALLOCED. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags length Z.of_nat Z.b2z]. exact BLK.
  Qed.

  Definition BN_FREE_D : Z := 0xfdf34.

  Definition BN_FREE_D_STACK : Z := CRYPTO_CLEAR_FREE_STACK.

  Lemma bn_free_d0_null_spec : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (b : bignum bptr),
    rw_cells bgusegs m A (bn_cells 0 b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 ->
    stk bgusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv bgusegs m ->
    (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) -> A mod 8 = 0 ->
    crypto_statics m -> a0 = wz A -> a1 = wz 0 ->
    evt bgusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom bgusegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
                 /\ stk bgusegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE_D) fc None m (seg_rom bgusegs)).
  Proof.
    intros until b. intros BN HF8 EL8 ST GLO LO MI SEP PM CS -> ->.
    unfold BN_FREE_D, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF8].
    carve_frame 16%nat ST. do 4 step. step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. rewrite (zxb_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL8 by lia. step. if_false.
    step. if_true.
    step. unfold wz at 1. do 3 step.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    eapply evt_cut.
    { eapply (CRYPTO_free_null_spec ra sp) with (lo := lo); [exact ST | unfold GLOBALS_TOP; lia | lia | exact MI | exact CS1 | reflexivity]. }
    intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MIc & STc).
    apply evt_done. do 15 eexists. exists m2. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU | exact MUc]|]. split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc | exact STc].
  Qed.

  Lemma bn_free_d0_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (pd : bptr) (A D lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_D_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 ->
    (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) -> A mod 8 = 0 ->
    a0 = wz A -> a1 = wz 0 ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pd lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (LFree pd k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE_D) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP IN AUX SPB ST CEIL GLO LO ERR MI -> CS BN HF8 EL8 SEP PM -> -> K.
    unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_FREE_D, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF8].
    unfold implM. iprefix.
    carve_frame 16%nat ST. do 4 step. step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. rewrite (zxb_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL8 by lia. step. if_false.
    step. if_true.
    step. unfold wz at 1. do 3 step.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' L) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := D) (n := 8 * Z.of_nat (bn_dmax b));
      [exact HEAP1 | exact IN | exact AUX1 | exact SPB | exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1 | reflexivity | ].
    intros st1 ms1 PO. apply K. unfold cfree_post in PO |- *.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    do 15 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]| exact HP4]. }
    repeat (split; [assumption|]). exact HEAP4.
  Qed.

  Lemma bn_free_d1_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (pd : bptr) (A D c lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_D_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> u64arr bgusegs m D (wlimbs (bn_buf b)) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 ->
    Z.of_nat (bn_dmax b) < 2^31 ->
    (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) -> A mod 8 = 0 ->
    a0 = wz A -> a1 = wz c -> 0 < c < 2^64 ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pd lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (LFree pd k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE_D) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP IN AUX SPB ST CEIL GLO LO ERR MI -> CS BN U0 HF8 EL8 HD SEP PM -> -> HCC K.
    unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_FREE_D, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP IN) as (BA0 & BA16 & _ & BAC & BAI). cbn [blk_addr blk_size fst snd] in *.
    assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
    unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF8].
    unfold implM. iprefix.
    carve_frame 16%nat ST. do 4 step. step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. rewrite (zxb_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL8 by lia. step. if_false.
    step. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by lia; [exfalso; lia|].
    step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax b))) by lia.
    step. unfold wz at 1.
    do 2 step. step. rewrite ?(unsigned_lit (Z.of_nat (bn_dmax b))) by lia.
    replace (Z.shiftl (Z.of_nat (bn_dmax b)) 3) with (Z.of_nat (bn_dmax b) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    step.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' L) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _). lia. }
    pose proof (limbarr_CB bgusegs m1 D (bn_buf b) U0) as OLD.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_clear_free_walk HF) with (B := B) (lo := lo) (errv := errv) (p := pd) (A := D) (n := 8 * Z.of_nat (bn_dmax b))
        (num := Z.of_nat (bn_dmax b) * 8) (junk := u64s (wlimbs (bn_buf b)));
      [exact HEAP1 | exact IN | exact AUX1 | exact SPB | exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1
      | replace (Z.to_nat (Z.of_nat (bn_dmax b) * 8)) with (8 * length (bn_buf b))%nat by (unfold bn_dmax; lia); exact OLD
      | lia | reflexivity | reflexivity | ].
    intros st1 ms1 PO. apply K. unfold cfree_post in PO |- *.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    do 15 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]| exact HP4]. }
    repeat (split; [assumption|]). exact HEAP4.
  Qed.

  Definition BN_FREE : Z := 0xfdfd0.

  Definition BN_FREE_STACK : Z := 32 + BN_FREE_D_STACK.

  Lemma BN_free_walk_d : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (pd : bptr) (A D lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L -> (forall a, A <= a < A + 24 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 0 ->
    (A + 24 <= bv_unsigned sp - BN_FREE_STACK \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 ->
    a0 = wz A ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pd lo B errv m s' ms' ->
                    rw_cells bgusegs (ms_mem ms') A (bn_cells D b) ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (LFree pd k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP IND SC AUX SPB ST CEIL GLO LO ERR MI -> CS BN HF8 EL8 EL2 EL1 SEP PA PM -> K.
    unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN0 _]; apply cells_at_bound in BN0; cbn in BN0; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BN.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    step. rewrite (land7_wrap _ PM).
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
    eapply (bn_free_d0_walk) with (B := B) (lo := lo) (errv := errv) (A := A) (D := D) (b := b) (pd := pd);
      [exact HEAP1 | exact IND | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1
      | exact BN | exact HF8 | exact EL8 | rewrite ESP; lia | exact PM | reflexivity | reflexivity | ].
    intros st1 ms1 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    replace (ret_pc (Z_to_bv 64 1040392)) with (Z_to_bv 64 1040392) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (HP0 : rheap_pres (lb_remove pd L) (bv_unsigned sp) m m4).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP4| lia| auto]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in BN.
    2: { intros a Ha. cbn in Ha. pose proof (SC a ltac:(lia)) as Hc. unfold rclient_addr in Hc |- *.
         destruct Hc as [Hc|[Hc|Hc]]; [left; lia | right; left; exact Hc | right; right; exact Hc]. }
    clear HEAP1 AUX1 CS1 HEAP AUX CS MI ERR MU WM ST.
    unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4. unfold MallocRep.wz.
    eapply implM_evt with (P := fun ms' => cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pd lo B errv m st1 ms'
                                         /\ rw_cells bgusegs (ms_mem ms') A (bn_cells D b));
      [| intros ms' [PO' BN']; apply K; [exact PO' | exact BN']].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl bgusegs m4) as WM4.
    assert (CLI4 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP4 Hb') as (_ & _ & _ & B3' & _). lia. }
    step. unfold wz at 1. rewrite (sx32_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL1 by lia. step. if_false.
    do 4 step. release_frame FR ST4 (bv_unsigned sp). step.
    apply evt_done. cbn [ms_mem]. split.
    - unfold cfree_post, MallocRep.wz. do 15 eexists. eexists. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; exact ERR4|].
      split. { eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
      split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU4| exact WM4| apply CLI4]. }
      split; [exact FA4|]. split; [exact SO4|].
      eapply LH_frame; [exact HEAP4| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
    - unfold bn_cells. exact BN.
  Qed.

  Lemma flags_cell_join : forall m a (d t x n : word) f, 0 <= f < 256 ->
    rw_cells bgusegs m a [C8 d; C4 t; C4 x; C4 n; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]] ->
    rw_cells bgusegs m a [C8 d; C4 t; C4 x; C4 n; C4 (Z_to_bv 64 f)].
  Proof.
    intros m a d t x n f Hf [[Hwf Hb] Hw]. split; [split|].
    - cbn [cells_wf cell_wf]. repeat split.
    - cbn [cells_bytes cbytes] in *. rewrite (le4_byte f Hf). exact Hb.
    - exact Hw.
  Qed.

  Lemma BN_free_spec_0 : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (b : bignum bptr),
    rw_cells bgusegs m A (bn_cells 0 b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 0 ->
    stk bgusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv bgusegs m ->
    (A + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 ->
    crypto_statics m -> a0 = wz A ->
    evt bgusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom bgusegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
                 /\ stk bgusegs m' lo (bv_unsigned sp) /\ rw_cells bgusegs m' A (bn_cells 0 b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until b. intros BN HF8 EL8 EL2 EL1 ST GLO LO MI SEP PA PM CS ->.
    unfold BN_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN0 _]; apply cells_at_bound in BN0; cbn in BN0; lia).
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold bn_cells in BN.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    step. rewrite (land7_wrap _ PM).
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
        | exact PM | exact CS1 | reflexivity | reflexivity ]. }
    cbv beta. intros ms2 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite ESP in MU2, ST2. replace (ret_pc (Z_to_bv 64 1040392)) with (Z_to_bv 64 1040392) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MU12 : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; lia. }
    assert (WM12 := wmono_trans bgusegs _ _ _ WM WM2).
    assert (FR2 := rw_cells_transport bgusegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (BN2 := rw_cells_transport bgusegs _ m1 m2 _ _ BN MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    clear CS1 MU WM FR BN ST MI MU2 WM2.
    step. unfold wz at 1. rewrite (sx32_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL1 by lia. step. if_false.
    do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step.
    apply evt_done. do 15 eexists. eexists. split; [reflexivity|].
    split; [exact MU12|]. split; [exact WM12|]. split; [assumption|]. split; [assumption|]. unfold bn_cells. exact BN2.
  Qed.

  Definition BN_CLEAR_FREE : Z := 0xfde64.
  Definition BN_CLEAR_FREE_STACK : Z := 32 + BN_FREE_D_STACK.

  Lemma BN_clear_free_walk_d : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (pd : bptr) (A D lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L -> (forall a, A <= a < A + 24 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> u64arr bgusegs m D (wlimbs (bn_buf b)) ->
    0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 0 -> Z.of_nat (bn_dmax b) < 2^31 ->
    (A + 24 <= bv_unsigned sp - BN_CLEAR_FREE_STACK \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 -> 0 < D ->
    a0 = wz A ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pd lo B errv m s' ms' ->
                    rw_cells bgusegs (ms_mem ms') A (bn_cells D b) ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (LFree pd k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CLEAR_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP IND SC AUX SPB ST CEIL GLO LO ERR MI -> CS BN U0 HF8 EL8 EL2 EL1 HD SEP PA PM PD -> K.
    unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_CLEAR_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN0 _]; apply cells_at_bound in BN0; cbn in BN0; lia).
    pose proof (LH_block_range _ _ _ _ HEAP IND) as (BD0 & BD16 & _ & BDC & BDI). cbn [blk_addr blk_size fst snd] in *.
    assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF8].
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. unfold wz at 1.
    step. if_cases KD; zify_cond KD; [exfalso; rewrite ?unsigned_lit in KD by lia; lia|]. clear KD.
    step. rewrite (zxb_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL2 by lia. step. if_false.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    pose proof (flags_cell_join _ _ _ _ _ _ _ HF8 BN) as BNC1.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' L) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (bn_free_d1_walk) with (B := B) (lo := lo) (errv := errv) (A := A) (D := D) (b := b) (pd := pd) (c := 1);
      [exact HEAP1 | exact IND | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1
      | exact BNC1 | exact U0 | exact HF8 | exact EL8 | exact HD | rewrite ESP; lia | exact PM | reflexivity | reflexivity | lia | ].
    intros st1 ms1 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    replace (ret_pc (Z_to_bv 64 1040040)) with (Z_to_bv 64 1040040) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    assert (HP0 : rheap_pres (lb_remove pd L) (bv_unsigned sp) m m4).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP4| lia| auto]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in BN.
    2: { intros a Ha. cbn in Ha. pose proof (SC a ltac:(lia)) as Hc. unfold rclient_addr in Hc |- *.
         destruct Hc as [Hc|[Hc|Hc]]; [left; lia | right; left; exact Hc | right; right; exact Hc]. }
    clear HEAP1 AUX1 CS1 HEAP AUX CS MI ERR MU WM ST BNC1 U0.
    unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4. unfold MallocRep.wz.
    eapply implM_evt with (P := fun ms' => cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pd lo B errv m st1 ms'
                                         /\ rw_cells bgusegs (ms_mem ms') A (bn_cells D b));
      [| intros ms' [PO' BN']; apply K; [exact PO' | exact BN']].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl bgusegs m4) as WM4.
    assert (CLI4 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP4 Hb') as (_ & _ & _ & B3' & _). lia. }
    step. rewrite (zxb_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL1 by lia. step. if_false.
    do 4 step. release_frame FR ST4 (bv_unsigned sp). step.
    apply evt_done. cbn [ms_mem]. split.
    - unfold cfree_post, MallocRep.wz. do 15 eexists. eexists. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; exact ERR4|].
      split. { eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
      split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU4| exact WM4| apply CLI4]. }
      split; [exact FA4|]. split; [exact SO4|].
      eapply LH_frame; [exact HEAP4| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
    - unfold bn_cells. apply flags_cell_join; [exact HF8 | exact BN].
  Qed.

  Lemma BN_clear_free_spec_0 : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (b : bignum bptr),
    rw_cells bgusegs m A (bn_cells 0 b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 1 = 0 ->
    stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> mem_inv bgusegs m ->
    (A + 24 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 ->
    a0 = wz A ->
    evt bgusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom bgusegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
                 /\ stk bgusegs m' lo (bv_unsigned sp) /\ rw_cells bgusegs m' A (bn_cells 0 b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CLEAR_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until b. intros BN HF8 EL1 ST LO MI SEP PA PM ->.
    unfold BN_CLEAR_FREE, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN0 _]; apply cells_at_bound in BN0; cbn in BN0; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF8].
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. unfold wz at 1.
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [|exfalso; lia]. clear KD.
    step. rewrite (zxb_small (bn_flags b)) by lia.
    step. rewrite (unsigned_lit (bn_flags b)), EL1 by lia. step. if_false.
    do 4 step. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. do 15 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    unfold bn_cells. apply flags_cell_join; [exact HF8 | exact BN].
  Qed.

  Definition lb_remove_opt (o : option bptr) (L : list block) : list block :=
    match o with Some p => lb_remove p L | None => L end.

  Definition ofree_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L : list block) (o : option bptr) (lo B : Z) (errv : word) (m : mem)
      (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bgusegs)
      /\ mem_inv bgusegs m' /\ stk bgusegs m' lo (bv_unsigned sp)
      /\ rw_cells bgusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres (lb_remove_opt o L) (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' (lb_remove_opt o L) m'.

  Lemma BN_free_walk_emb : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (A D lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m ->
    (forall pd, bn_d b = Some pd -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L /\ (forall a, A <= a < A + 24 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a)) ->
    (bn_d b = None -> D = 0) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 0 ->
    (A + 24 <= bv_unsigned sp - BN_FREE_STACK \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 ->
    a0 = wz A ->
    (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L (bn_d b) lo B errv m s' ms' ->
                    rw_cells bgusegs (ms_mem ms') A (bn_cells D b) ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lbind (lfree_opt (bn_d b)) (fun _ => k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP HS HN AUX SPB ST CEIL GLO LO ERR MI Etp CS BN HF8 EL8 EL2 EL1 SEP PA PM Ea0 K.
    destruct (bn_d b) as [pd|] eqn:Ed.
    - destruct (HS pd eq_refl) as [IND SC]. cbn [lfree_opt lfree lbind].
      eapply BN_free_walk_d; try eassumption.
    - specialize (HN eq_refl). subst D. cbn [lfree_opt lbind].
      unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, GLOBALS_TOP in *.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
      eapply implM_evt with (P := fun ms' => ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L None lo B errv m s ms'
                                           /\ rw_cells bgusegs (ms_mem ms') A (bn_cells 0 b));
        [| intros ms' [PO' BN']; apply K; [exact PO' | exact BN']].
      eapply evt_mono; [eapply (BN_free_spec_0 ra sp) with (lo := lo) (A := A) (b := b); try eassumption; unfold GLOBALS_TOP; lia |].
      intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & BN2).
      cbn [ms_mem]. split; [|exact BN2].
      unfold ofree_post, lb_remove_opt. subst tp. do 15 eexists. exists m2. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|].
      split; [eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | unfold LX_ERRNO, RATP; cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU2| exact WM2|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
      split. { eapply heap_pres_of_munch; [exact MU2| exact WM2|].
               intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
               pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
      split; [reflexivity|]. split; [reflexivity|].
      eapply LH_frame; [exact HEAP| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
  Qed.

  Lemma BN_clear_free_walk_emb : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (A D lo B : Z) (b : bignum bptr) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m ->
    (forall pd, bn_d b = Some pd -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) L /\ 0 < D /\ u64arr bgusegs m D (wlimbs (bn_buf b))
                                /\ (forall a, A <= a < A + 24 -> rclient_addr (lb_remove pd L) (bv_unsigned sp) a)) ->
    (bn_d b = None -> D = 0) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D b) -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 8 = 0 -> Z.land (bn_flags b) 2 = 0 -> Z.land (bn_flags b) 1 = 0 ->
    Z.of_nat (bn_dmax b) < 2^31 ->
    (A + 24 <= bv_unsigned sp - BN_CLEAR_FREE_STACK \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 ->
    a0 = wz A ->
    (forall s' ms', ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L (bn_d b) lo B errv m s' ms' ->
                    rw_cells bgusegs (ms_mem ms') A (bn_cells D b) ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lbind (lfree_opt (bn_d b)) (fun _ => k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CLEAR_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP HS HN AUX SPB ST CEIL GLO LO ERR MI Etp CS BN HF8 EL8 EL2 EL1 HD SEP PA PM Ea0 K.
    destruct (bn_d b) as [pd|] eqn:Ed.
    - destruct (HS pd eq_refl) as (IND & PD & U0 & SC). cbn [lfree_opt lfree lbind].
      eapply BN_clear_free_walk_d; try eassumption.
    - specialize (HN eq_refl). subst D. cbn [lfree_opt lbind].
      unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, GLOBALS_TOP in *.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
      eapply implM_evt with (P := fun ms' => ofree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L None lo B errv m s ms'
                                           /\ rw_cells bgusegs (ms_mem ms') A (bn_cells 0 b));
        [| intros ms' [PO' BN']; apply K; [exact PO' | exact BN']].
      eapply evt_mono; [eapply (BN_clear_free_spec_0 ra sp) with (lo := lo) (A := A) (b := b); try eassumption; lia |].
      intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & BN2).
      cbn [ms_mem]. split; [|exact BN2].
      unfold ofree_post, lb_remove_opt. subst tp. do 15 eexists. exists m2. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|].
      split; [eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | unfold LX_ERRNO, RATP; cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU2| exact WM2|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
      split. { eapply heap_pres_of_munch; [exact MU2| exact WM2|].
               intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
               pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
      split; [reflexivity|]. split; [reflexivity|].
      eapply LH_frame; [exact HEAP| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
  Qed.
End Proofs.
End WithCeiling0.
