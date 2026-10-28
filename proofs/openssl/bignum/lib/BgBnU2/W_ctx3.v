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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep W_crypto W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3 W_alloc3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition mont_cells0 (fl : Z) : list cell :=
  bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz fl)].

Definition recp_cells0 : list cell :=
  bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)].

Lemma stk_transport_rw : forall W m m' lo hi A cs,
  stk bgusegs m lo hi -> munch W m m' -> wmono bgusegs m m' -> rw_cells bgusegs m' A cs ->
  (forall x, lo <= x < hi -> outside W x \/ A <= x < A + Z.of_nat (cells_size cs)) -> stk bgusegs m' lo hi.
Proof.
  intros W m m' lo hi A cs ST MU WM RW CASES.
  pose proof (stk_of_rw_cells bgusegs _ _ _ RW) as STA.
  destruct ST as (H1 & H2 & H). split; [lia|]. split; [lia|].
  intros a Ha. destruct (CASES a Ha) as [Ho | Hin].
  - destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply WM; exact Hwa|].
    exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exact ((proj2 (proj2 STA)) a Hin).
Qed.

Definition ctx_cells0 : list cell :=
  [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition BN_MONT_CTX_INIT : Z := 0x100450.

  Lemma BN_MONT_CTX_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo A : Z) (junk : list byte),
    rw_cells bgusegs m A [CB 96 junk] -> (0 < A /\ A mod 8 = 0) ->
    stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv bgusegs m ->
    (A + 96 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) ->
    a0 = wz A ->
    evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 96)]%Z lo m
                 (fun _ m' => rw_cells bgusegs m' A (mont_cells0 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_INIT) fc None m (seg_rom bgusegs)).
  Proof.
    intros until junk. intros BLK [PA PM] ST LO MI SEP ->. unfold BN_MONT_CTX_INIT, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 96)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    pose proof (rw_cells_split_CB bgusegs m A [] 96 junk [] [24; 24; 24; 24]%nat BLK eq_refl) as B4. cbn [mk_CB_cells app] in B4. clear BLK.
    pose proof (proj1 ST) as LO0.
    carve_frame 32%nat ST. do 5 step.
    chk ltac:(fun C => clear - C PA BB; lia).
    step. step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step.
    lazymatch type of B4 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?rest) =>
      destruct (proj1 (bk_rw_cells_app bgusegs m1 A [c1] (c2 :: c3 :: rest)) B4) as [P1 B4'];
      destruct (proj1 (bk_rw_cells_app bgusegs m1 _ [c2] (c3 :: rest)) B4') as [P2 B4''];
      destruct (proj1 (bk_rw_cells_app bgusegs m1 _ [c3] rest) B4'') as [P3 P4]; clear B4 B4' B4'' end.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in P2, P3, P4.
    replace (A + 24 + 24) with (A + 48) in P3 by lia. replace (A + 24 + 24 + 24) with (A + 72) in P4 by lia.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).

    step. step. eapply evt_cut.
    { eapply (bn_init_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A);
        [ exact P1 | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; lia | reflexivity ]. }
    cbv beta. intros ms2 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & _ & R1).
    rewrite ESP in MU2, ST2. rewrite (ret_pc_even 1049728) by lia.
    assert (FR2 := rw_cells_transport bgusegs _ _ m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (P22 := rw_cells_transport bgusegs _ _ m2 _ _ P2 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (P32 := rw_cells_transport bgusegs _ _ m2 _ _ P3 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (P42 := rw_cells_transport bgusegs _ _ m2 _ _ P4 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add length take drop]; lia)).
    assert (MU12 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 96)]%Z m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM12 := wmono_trans bgusegs _ _ _ WM WM2).
    clear FR P1 P2 P3 P4 MU WM MU2 WM2 ST MI.

    step. step. eapply evt_cut.
    { eapply (bn_init_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A + 24);
        [ exact P22 | rewrite ESP; exact ST2 | rewrite ESP; lia | exact MI2 | rewrite ESP; lia | f_equal; lia ]. }
    cbv beta. intros ms3 (u0' & u1' & u2' & v0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & m3 & -> & MU3 & WM3 & MI3 & ST3 & _ & R2).
    rewrite ESP in MU3, ST3. rewrite (ret_pc_even 1049736) by lia.
    assert (FR3 := rw_cells_transport bgusegs _ _ m3 _ _ FR2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (R13 := rw_cells_transport bgusegs _ _ m3 _ _ R1 MU3 WM3 ltac:(cbn [disjoint_from bn_cells cells_size csize Nat.add]; lia)).
    assert (P33 := rw_cells_transport bgusegs _ _ m3 _ _ P32 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (P43 := rw_cells_transport bgusegs _ _ m3 _ _ P42 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length take drop]; lia)).
    assert (MU13 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 96)]%Z m m3).
    { eapply munch_trans; [exact MU12|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM13 := wmono_trans bgusegs _ _ _ WM12 WM3).
    clear FR2 R1 P22 P32 P42 MU12 WM12 MU3 WM3 ST2 MI2.

    step. step. eapply evt_cut.
    { eapply (bn_init_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A + 48);
        [ exact P33 | rewrite ESP; exact ST3 | rewrite ESP; lia | exact MI3 | rewrite ESP; lia | f_equal; lia ]. }
    cbv beta. intros ms4 (u0'' & u1'' & u2'' & v0'' & v1'' & v2'' & v3'' & v4'' & v5'' & v6'' & v7'' & u3'' & u4'' & u5'' & u6'' & m4 & -> & MU4 & WM4 & MI4 & ST4 & _ & R3).
    rewrite ESP in MU4, ST4. rewrite (ret_pc_even 1049744) by lia.
    assert (FR4 := rw_cells_transport bgusegs _ _ m4 _ _ FR3 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (R14 := rw_cells_transport bgusegs _ _ m4 _ _ R13 MU4 WM4 ltac:(cbn [disjoint_from bn_cells cells_size csize Nat.add]; lia)).
    assert (R24 := rw_cells_transport bgusegs _ _ m4 _ _ R2 MU4 WM4 ltac:(cbn [disjoint_from bn_cells cells_size csize Nat.add]; lia)).
    assert (P44 := rw_cells_transport bgusegs _ _ m4 _ _ P43 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add length take drop]; lia)).
    assert (MU14 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 96)]%Z m m4).
    { eapply munch_trans; [exact MU13|]. eapply munch_weaken; [|exact MU4]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM14 := wmono_trans bgusegs _ _ _ WM13 WM4).
    clear FR3 R13 R2 P33 P43 MU13 WM13 MU4 WM4 ST3 MI3.
    unfold bn_cells, bn_nil in R14, R24, R3. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags length Z.of_nat Z.b2z] in R14, R24, R3.
    step. step.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; clear - C BB; lia).
    step. step. step.
    do 4 step. release_frame FR4 ST4 (bv_unsigned sp). step.
    finish.
    unfold mont_cells0, bn_cells, bn_nil. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags length Z.of_nat Z.b2z app].
    Ltac take5 R := lazymatch goal with |- rw_cells ?sg ?mm ?AA (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
      apply (proj2 (bk_rw_cells_app sg mm AA [c1; c2; c3; c4; c5] rest)); split; [exact R|];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry] end.
    take5 R14. take5 R24. replace (A + 24 + 24) with (A + 48) by lia. take5 R3. replace (A + 48 + 24) with (A + 72) by lia. exact P44.
  Qed.

  Definition BN_MONT_CTX_NEW : Z := 0x1003ec.

  Definition BN_MONT_CTX_NEW_STACK : Z := 32 + CRYPTO_MALLOC_STACK.

  Lemma BN_MONT_CTX_new_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MONT_CTX_NEW_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP ->
    crypto_statics m ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 96 lo B m
                   (fun A m' => rw_cells bgusegs m' A (mont_cells0 BN_FLG_MALLOCED)) p s' ms' ->
       implM bgusegs (interp (k (Some p))) s' Q ms') ->
    implM bgusegs (interp (LMalloc 96 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_NEW) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS KN K.
    unfold BN_MONT_CTX_NEW_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, BN_MONT_CTX_NEW, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step. do 4 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 96);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkA & BLK)).
    replace (ret_pc (Z_to_bv 64 1049620)) with (Z_to_bv 64 1049620) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 96 lo B m
                   (fun A m' => rw_cells bgusegs m' A (mont_cells0 BN_FLG_MALLOCED)) p st1); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 96)]%Z m3) as MU3. pose proof (wmono_refl bgusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, 96) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 96)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, 96) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step.

    eapply evt_cut.
    { eapply (BN_MONT_CTX_init_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A) (junk := junkA);
        [ exact BLK | split; [lia | clear - BA16; Z.div_mod_to_equations; lia] | rewrite ESP; exact ST3 | rewrite ESP; lia | exact MI3 | rewrite ESP; lia | reflexivity ]. }
    cbv beta. intros ms4 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & MC).
    rewrite ESP in MU4, ST4. rewrite (ret_pc_even 1049636) by lia.
    assert (FR4 := rw_cells_transport bgusegs _ _ m4 _ _ FR MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (ERR4 := rw_cells_transport bgusegs _ _ m4 _ _ ERR3 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (MU34 : munch [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 96)]%Z m3 m4).
    { eapply munch_trans; [exact MU3|]. eapply munch_weaken; [|exact MU4]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM34 := wmono_trans bgusegs _ _ _ WM3 WM4).
    clear FR BLK MU3 WM3 MU4 WM4 ST3 MI3 ERR3.
    unfold mont_cells0, bn_cells, bn_nil in MC. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags length Z.of_nat Z.b2z app] in MC.
    step. rewrite (land7_wrap A) by (clear - BA16; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    step. step. step.
    do 4 step. release_frame FR4 ST4 (bv_unsigned sp). step.
    apply evt_done. unfold calloc_post, MallocRep.wz.
    do 14 eexists. exists m0, A, errv2. split; [reflexivity|].
    split; [assumption|]. split; [exact ST4|]. split; [unfold LX_ERRNO, RATP; exact ERR4|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU34| exact WM34|].
             pose proof AUX3 as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB & _).
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU34| exact WM34| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU34| exact WM34|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, 96)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    unfold mont_cells0, bn_cells, bn_nil, BN_FLG_MALLOCED. cbn [bn_top bn_dmax bn_buf bn_neg bn_flags length Z.of_nat Z.b2z app]. exact MC.
  Qed.

  Definition BN_RECP_CTX_INIT : Z := 0x151c70.

  Lemma zero16_cells : forall m A,
    rw_cells bgusegs m A [CB 16%nat (repeat (Z_to_bv 8 0) 16%nat)] -> rw_cells bgusegs m A [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)].
  Proof.
    intros m A [[Hwf Hb] Hw]. split; [split|].
    - cbn. repeat split.
    - cbn [cells_bytes cbytes app repeat] in *. exact Hb.
    - cbn [cells_size csize Nat.add] in *. exact Hw.
  Qed.

  Lemma BN_RECP_CTX_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo A : Z) (junk : list byte),
    rw_cells bgusegs m A [CB 64 junk] -> (0 < A /\ A mod 8 = 0) ->
    stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv bgusegs m ->
    (A + 64 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) ->
    a0 = wz A ->
    evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 64)]%Z lo m
                 (fun _ m' => rw_cells bgusegs m' A recp_cells0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECP_CTX_INIT) fc None m (seg_rom bgusegs)).
  Proof.
    intros until junk. intros BLK [PA PM] ST LO MI SEP ->. unfold BN_RECP_CTX_INIT, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 64)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    pose proof (proj1 ST) as LO0.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    carve_frame 32%nat ST. do 5 step.
    do 3 step. step. step.

    eapply evt_cut.
    { eapply (memset_callZ _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (D := A) (C := 0) (N := 64) (junk := junk);
        [ exact BLK | exact MI | lia | lia | lia | lia ]. }
    cbv beta. intros ms1 (u0 & u1 & u2 & w1 & w2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & Z1).
    rewrite (ret_pc_even 1383576) by lia.
    assert (FR1 := rw_cells_transport bgusegs _ _ m1 _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (ST1 : stk bgusegs m1 lo (bv_unsigned sp - 32)).
    { lazymatch goal with [ H : stk bgusegs _ lo _ |- _ ] => rewrite ?ESP in H; replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in H by lia;
        eapply (stk_transport_rw _ m0 m1); [exact H | exact MU1 | exact WM1 | exact Z1 |] end.
      cbn [cells_size csize Nat.add]. intros x Hx. destruct (Z_lt_dec x A); [left; cbn; split; [lia| exact I]|].
      destruct (Z_lt_dec x (A + 64)); [right; lia| left; cbn; split; [lia| exact I]]. }
    assert (MU01 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 64)]%Z m m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM01 := wmono_trans bgusegs _ _ _ WM WM1).
    pose proof (rw_cells_split_CB bgusegs m1 A [] 64 _ [] [24; 24; 16]%nat Z1 eq_refl) as B3. cbn [mk_CB_cells app repeat firstn skipn] in B3.
    lazymatch type of B3 with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) =>
      destruct (proj1 (bk_rw_cells_app bgusegs m1 A [c1] (c2 :: rest)) B3) as [P1 B3'];
      destruct (proj1 (bk_rw_cells_app bgusegs m1 _ [c2] rest) B3') as [P2 P3]; clear B3 B3' end.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in P2, P3.
    replace (A + 24 + 24) with (A + 48) in P3 by lia. apply zero16_cells in P3.
    clear FR BLK MU WM MU1 WM1 Z1 MI.

    chk ltac:(fun C => clear - C PA BB; lia).
    step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. step. eapply evt_cut.
    { eapply (bn_init_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A);
        [ exact P1 | rewrite ESP; exact ST1 | rewrite ESP; lia | exact MI1 | rewrite ESP; lia | reflexivity ]. }
    cbv beta. intros ms2 (u0' & u1' & u2' & v0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & _ & R1).
    rewrite ESP in MU2, ST2. rewrite (ret_pc_even 1383596) by lia.
    assert (FR2 := rw_cells_transport bgusegs _ _ m2 _ _ FR1 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (P22 := rw_cells_transport bgusegs _ _ m2 _ _ P2 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (P32 := rw_cells_transport bgusegs _ _ m2 _ _ P3 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    assert (MU02 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 64)]%Z m m2).
    { eapply munch_trans; [exact MU01|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    assert (WM02 := wmono_trans bgusegs _ _ _ WM01 WM2).
    clear FR1 P1 P2 P3 MU01 WM01 MU2 WM2 ST1 MI1.

    step. do 3 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    eapply evt_mono.
    { eapply (bn_init_spec ra sp) with (lo := lo) (A := A + 24);
        [ exact P22 | exact ST2 | lia | exact MI2 | lia | f_equal; lia ]. }
    cbv beta. intros ms3 (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & _ & R2).
    unfold bn_small_post. do 15 eexists. exists m3. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split; [exact (wmono_trans bgusegs _ _ _ WM02 WM3)|]. split; [exact MI3|]. split; [exact ST3|].
    assert (R13 := rw_cells_transport bgusegs _ _ m3 _ _ R1 MU3 WM3 ltac:(cbn [disjoint_from bn_cells cells_size csize Nat.add]; lia)).
    assert (P33 := rw_cells_transport bgusegs _ _ m3 _ _ P32 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
    unfold recp_cells0.
    apply (proj2 (bk_rw_cells_app bgusegs m3 A (bn_cells 0 (bn_nil 0)) _)). split; [exact R13|].
    cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry].
    apply (proj2 (bk_rw_cells_app bgusegs m3 (A + 24) (bn_cells 0 (bn_nil 0)) _)). split; [exact R2|].
    cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.add_carry].
    replace (A + 24 + 24) with (A + 48) by lia. exact P33.
  Qed.

  Definition gfree_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L' : list block) (lo B : Z) (errv : word) (m : mem) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bgusegs)
      /\ mem_inv bgusegs m' /\ stk bgusegs m' lo (bv_unsigned sp)
      /\ rw_cells bgusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres L' (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' L' m'.

  Lemma rclient_addr_mono : forall L L' SP SP' a,
    rclient_addr L SP a -> SP' <= SP -> (forall b, In b L -> In b L') -> rclient_addr L' SP' a.
  Proof.
    intros L L' SP SP' a H HS HL. destruct H as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
    exists b. split; [apply HL; exact Hb| exact Hr].
  Qed.

  Lemma lb_remove_opt_incl : forall o L b, In b (lb_remove_opt o L) -> In b L.
  Proof. intros [p|] L b H; [eapply lb_remove_incl; exact H| exact H]. Qed.

  Lemma recp_flags_split : forall m a (nb sh pad : word) f, 0 <= f < 256 ->
    rw_cells bgusegs m a [C4 nb; C4 sh; C4 (Z_to_bv 64 f); C4 pad] ->
    rw_cells bgusegs m a [C4 nb; C4 sh; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 pad].
  Proof.
    intros m a nb sh pad f Hf [[Hwf Hb] Hw]. split; [split|].
    - cbn [cells_wf cell_wf length]. repeat split.
    - cbn [cells_bytes cbytes app] in *. rewrite (le4_byte f Hf) in Hb. exact Hb.
    - exact Hw.
  Qed.
  Lemma recp_flags_join : forall m a (nb sh pad : word) f, 0 <= f < 256 ->
    rw_cells bgusegs m a [C4 nb; C4 sh; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 pad] ->
    rw_cells bgusegs m a [C4 nb; C4 sh; C4 (Z_to_bv 64 f); C4 pad].
  Proof.
    intros m a nb sh pad f Hf [[Hwf Hb] Hw]. split; [split|].
    - cbn [cells_wf cell_wf length]. repeat split.
    - cbn [cells_bytes cbytes app] in *. rewrite (le4_byte f Hf). exact Hb.
    - exact Hw.
  Qed.

  Definition BN_RECP_CTX_FREE : Z := 0x151cc8.

  Definition BN_RECP_CTX_FREE_STACK : Z := 32 + BN_FREE_STACK.

  Lemma BN_RECP_CTX_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (A D1 D2 lo B : Z) (bN bNr : bignum bptr)
      (nb sh pad : word) (fl : Z) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    let L2 := lb_remove_opt (bn_d bNr) (lb_remove_opt (bn_d bN) L) in
    RHEAP s L m ->
    (forall pd, bn_d bN = Some pd -> In (pd, D1, 8 * Z.of_nat (bn_dmax bN)) L) -> (bn_d bN = None -> D1 = 0) ->
    (forall pd, bn_d bNr = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax bNr)) (lb_remove_opt (bn_d bN) L)) -> (bn_d bNr = None -> D2 = 0) ->
    (forall a, A <= a < A + 64 -> rclient_addr L2 (bv_unsigned sp) a) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_RECP_CTX_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D1 bN) ->
    0 <= bn_flags bN < 256 -> Z.land (bn_flags bN) 8 = 0 -> Z.land (bn_flags bN) 2 = 0 -> Z.land (bn_flags bN) 1 = 0 ->
    rw_cells bgusegs m (A + 24) (bn_cells D2 bNr) ->
    0 <= bn_flags bNr < 256 -> Z.land (bn_flags bNr) 8 = 0 -> Z.land (bn_flags bNr) 2 = 0 -> Z.land (bn_flags bNr) 1 = 0 ->
    rw_cells bgusegs m (A + 48) [C4 nb; C4 sh; C4 (wz fl); C4 pad] -> 0 <= fl < 256 -> Z.land fl 1 = 0 ->
    (A + 64 <= bv_unsigned sp - BN_RECP_CTX_FREE_STACK \/ bv_unsigned sp <= A) -> 0 < A -> A mod 8 = 0 ->
    a0 = wz A ->
    (forall s' ms', gfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L2 lo B errv m s' ms' ->
                    rw_cells bgusegs (ms_mem ms') A (bn_cells D1 bN) ->
                    rw_cells bgusegs (ms_mem ms') (A + 24) (bn_cells D2 bNr) ->
                    rw_cells bgusegs (ms_mem ms') (A + 48) [C4 nb; C4 sh; C4 (wz fl); C4 pad] ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lbind (lfree_opt (bn_d bN)) (fun _ => lbind (lfree_opt (bn_d bNr)) (fun _ => k)))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECP_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros L2 HEAP HS1 HN1 HS2 HN2 SC AUX SPB ST CEIL GLO LO ERR MI -> CS BN1 F1a F1b F1c F1d BN2 F2a F2b F2c F2d SCL Hfl Efl SEP PA PM -> K.
    unfold BN_RECP_CTX_FREE_STACK, BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_RECP_CTX_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (rw_cells_bound _ _ _ _ SCL) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (INC1 : forall b, In b L2 -> In b (lb_remove_opt (bn_d bN) L)) by (intros b Hb; eapply lb_remove_opt_incl; exact Hb).
    assert (INC0 : forall b, In b L2 -> In b L) by (intros b Hb; eapply lb_remove_opt_incl; apply INC1; exact Hb).
    unfold bn_cells in BN1, BN2.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
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
    assert (CLI : forall LL, (forall b, In b LL -> In b L) -> forall a, 0 <= a < 2^64 -> rclient_addr LL (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros LL HLL a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP (HLL _ Hb')) as (_ & _ & _ & B3' & _). lia. }

    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (BN_free_walk_emb HF) with (B := B) (lo := lo) (errv := errv) (A := A) (D := D1) (b := bN) (L := L);
      [ exact HEAP1
      | intros pd Hpd; split; [exact (HS1 pd Hpd)|]; intros a Ha; eapply rclient_addr_mono; [apply SC; lia| rewrite ESP; lia|];
        intros b Hb; unfold L2 in Hb; rewrite Hpd in INC1; cbn [lb_remove_opt] in INC1; apply INC1; exact Hb
      | exact HN1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1
      | unfold bn_cells; exact BN1 | exact F1a | exact F1b | exact F1c | exact F1d
      | rewrite ESP; unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | exact PA | exact PM | reflexivity | ].
    intros st1 ms1 PO BNa. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    cbn [ms_mem] in BNa.
    replace (ret_pc (Z_to_bv 64 1383668)) with (Z_to_bv 64 1383668) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in BN2.
    2: { intros a Ha. cbn in Ha. eapply rclient_addr_mono; [apply SC; lia| lia| exact INC1]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in SCL.
    2: { intros a Ha. cbn in Ha. eapply rclient_addr_mono; [apply SC; lia| lia| exact INC1]. }
    assert (CS4 : crypto_statics m4).
    { eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP4)| intros a Ha; apply libw_client; exact Ha| exact CS1]. }
    assert (HP0 : rheap_pres (lb_remove_opt (bn_d bN) L) (bv_unsigned sp) m m4).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply (CLI _ (lb_remove_opt_incl (bn_d bN) L))]|].
      eapply rheap_pres_weaken; [exact HP4| lia| auto]. }
    clear HEAP1 AUX1 CS1 AUX CS MI ERR ST.
    unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4. unfold MallocRep.wz.

    unfold implM. iprefix.
    step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (BN_free_walk_emb HF) with (B := B) (lo := lo) (errv := errv) (A := A + 24) (D := D2) (b := bNr) (L := lb_remove_opt (bn_d bN) L);
      [ exact HEAP4
      | intros pd Hpd; split; [exact (HS2 pd Hpd)|]; intros a Ha; eapply rclient_addr_mono; [apply SC; lia| rewrite ESP; lia|];
        intros b Hb; unfold L2 in Hb; rewrite Hpd in Hb; cbn [lb_remove_opt] in Hb; exact Hb
      | exact HN2 | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | reflexivity | exact CS4
      | exact BN2 | exact F2a | exact F2b | exact F2c | exact F2d
      | rewrite ESP; unfold BN_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | lia | clear - PM; Z.div_mod_to_equations; lia | reflexivity | ].
    intros st2 ms2 PO BNb. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    cbn [ms_mem] in BNb. fold L2 in HP5, HEAP5.
    replace (ret_pc (Z_to_bv 64 1383676)) with (Z_to_bv 64 1383676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in BNa.
    2: { intros a Ha. cbn in Ha. eapply rclient_addr_mono; [apply SC; lia| lia| auto]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in SCL.
    2: { intros a Ha. cbn in Ha. eapply rclient_addr_mono; [apply SC; lia| lia| auto]. }
    assert (HP05 : rheap_pres L2 (bv_unsigned sp) m m5).
    { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| exact INC1]|]. eapply rheap_pres_weaken; [exact HP5| lia| auto]. }
    clear HEAP4 AUX4 CS4 MI4 ERR4 ST4 HP4 HP0.
    unfold LX_ERRNO, RATP in ERR5. change (3346328 - 164) with 3346164 in ERR5. unfold MallocRep.wz.
    eapply implM_evt with (P := fun ms' => gfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L2 lo B errv m st2 ms'
                                         /\ rw_cells bgusegs (ms_mem ms') A (bn_cells D1 bN)
                                         /\ rw_cells bgusegs (ms_mem ms') (A + 24) (bn_cells D2 bNr)
                                         /\ rw_cells bgusegs (ms_mem ms') (A + 48) [C4 nb; C4 sh; C4 (Z_to_bv 64 fl); C4 pad]);
      [| intros ms' (PO' & X1 & X2 & X3); apply K; [exact PO' | exact X1 | exact X2 | exact X3]].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m5) as MU5. pose proof (wmono_refl bgusegs m5) as WM5.
    apply (recp_flags_split _ _ _ _ _ _ Hfl) in SCL.
    step. rewrite (zxb_small fl) by lia. step. rewrite (unsigned_lit fl), Efl by lia. step. if_false.
    do 4 step. release_frame FR ST5 (bv_unsigned sp). step.
    apply evt_done. cbn [ms_mem]. split; [| split; [unfold bn_cells; exact BNa| split; [unfold bn_cells; exact BNb| apply (recp_flags_join _ _ _ _ _ _ Hfl); exact SCL]]].
    unfold gfree_post, MallocRep.wz. do 15 eexists. eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; exact ERR5|].
    split. { eapply rauxv_ok_frame; [exact AUX5| exact MU5| exact WM5|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    split. { eapply rheap_pres_trans; [exact HP05|]. eapply heap_pres_of_munch; [exact MU5| exact WM5|].
             intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
             pose proof (LH_block_range _ _ _ _ HEAP5 Hb') as (_ & _ & _ & B3' & _). lia. }
    split; [rewrite FA5; exact FA4|]. split; [rewrite SO5; exact SO4|].
    eapply LH_frame; [exact HEAP5| exact MU5| exact WM5|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
  Qed.

  Lemma mont_flags_split : forall m a (n0 n1 ri : word) f, 0 <= f < 256 ->
    rw_cells bgusegs m a [C8 n0; C8 n1; C4 ri; C4 (Z_to_bv 64 f)] ->
    rw_cells bgusegs m a [C8 n0; C8 n1; C4 ri; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  Proof.
    intros m a n0 n1 ri f Hf [[Hwf Hb] Hw]. split; [split|].
    - cbn [cells_wf cell_wf length]. repeat split.
    - cbn [cells_bytes cbytes app] in *. rewrite (le4_byte f Hf) in Hb. exact Hb.
    - exact Hw.
  Qed.

  Definition BN_MONT_CTX_FREE : Z := 0x1004c0.

  Definition BN_MONT_CTX_FREE_STACK : Z := 32 + BN_CLEAR_FREE_STACK.

  Lemma BN_MONT_CTX_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (q : bptr) (A D1 D2 D3 lo B : Z) (bRR bN bNi : bignum bptr)
      (n0 n1 ri : word) (fl : Z) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    let L1 := lb_remove_opt (bn_d bRR) L in
    let L2 := lb_remove_opt (bn_d bN) L1 in
    let L3 := lb_remove_opt (bn_d bNi) L2 in
    RHEAP s L m ->
    (forall pd, bn_d bRR = Some pd -> In (pd, D1, 8 * Z.of_nat (bn_dmax bRR)) L /\ 0 < D1 /\ u64arr bgusegs m D1 (wlimbs (bn_buf bRR))) -> (bn_d bRR = None -> D1 = 0) ->
    (forall pd, bn_d bN = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax bN)) L1 /\ 0 < D2 /\ u64arr bgusegs m D2 (wlimbs (bn_buf bN))) -> (bn_d bN = None -> D2 = 0) ->
    (forall pd, bn_d bNi = Some pd -> In (pd, D3, 8 * Z.of_nat (bn_dmax bNi)) L2 /\ 0 < D3 /\ u64arr bgusegs m D3 (wlimbs (bn_buf bNi))) -> (bn_d bNi = None -> D3 = 0) ->
    In (q, A, 96) L3 ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MONT_CTX_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    rw_cells bgusegs m A (bn_cells D1 bRR) ->
    0 <= bn_flags bRR < 256 -> Z.land (bn_flags bRR) 8 = 0 -> Z.land (bn_flags bRR) 2 = 0 -> Z.land (bn_flags bRR) 1 = 0 -> Z.of_nat (bn_dmax bRR) < 2^31 ->
    rw_cells bgusegs m (A + 24) (bn_cells D2 bN) ->
    0 <= bn_flags bN < 256 -> Z.land (bn_flags bN) 8 = 0 -> Z.land (bn_flags bN) 2 = 0 -> Z.land (bn_flags bN) 1 = 0 -> Z.of_nat (bn_dmax bN) < 2^31 ->
    rw_cells bgusegs m (A + 48) (bn_cells D3 bNi) ->
    0 <= bn_flags bNi < 256 -> Z.land (bn_flags bNi) 8 = 0 -> Z.land (bn_flags bNi) 2 = 0 -> Z.land (bn_flags bNi) 1 = 0 -> Z.of_nat (bn_dmax bNi) < 2^31 ->
    rw_cells bgusegs m (A + 72) [C8 n0; C8 n1; C4 ri; C4 (wz fl)] -> 0 <= fl < 256 -> Z.land fl 1 = 1 ->
    a0 = wz A ->
    (forall s' ms', gfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove q L3) lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lbind (lfree_opt (bn_d bRR)) (fun _ => lbind (lfree_opt (bn_d bN)) (fun _ =>
                           lbind (lfree_opt (bn_d bNi)) (fun _ => LFree q k))))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros L1 L2 L3 HEAP HS1 HN1 HS2 HN2 HS3 HN3 INQ AUX SPB ST CEIL GLO LO ERR MI -> CS
           BN1 F1a F1b F1c F1d HD1 BN2 F2a F2b F2c F2d HD2 BN3 F3a F3b F3c F3d HD3 SCL Hfl Efl -> K.
    unfold BN_MONT_CTX_FREE_STACK, BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_MONT_CTX_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (INC1 : forall b, In b L1 -> In b L) by (intros b Hb; eapply lb_remove_opt_incl; exact Hb).
    assert (INC2 : forall b, In b L2 -> In b L1) by (intros b Hb; eapply lb_remove_opt_incl; exact Hb).
    assert (INC3 : forall b, In b L3 -> In b L2) by (intros b Hb; eapply lb_remove_opt_incl; exact Hb).
    pose proof (LH_block_range _ _ _ _ HEAP (INC1 _ (INC2 _ (INC3 _ INQ)))) as (QA0 & QA16 & _ & QAC & QAI). cbn [blk_addr blk_size fst snd] in QA0, QA16, QAC, QAI.

    assert (SCq : forall LL SP a, In (q, A, 96) LL -> A <= a < A + 96 -> rclient_addr LL SP a).
    { intros LL SP a HIn Ha. right. right. exists (q, A, 96). split; [exact HIn|]. cbn [blk_addr blk_size fst snd]. lia. }
    unfold bn_cells in BN1, BN2, BN3.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 5 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step. rewrite (land7_wrap A) by (clear - QA16; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
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
    assert (CLI : forall LL, (forall b, In b LL -> In b L) -> forall a, 0 <= a < 2^64 -> rclient_addr LL (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros LL HLL a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP (HLL _ Hb')) as (_ & _ & _ & B3' & _). lia. }

    assert (UA : forall D ws, u64arr bgusegs m D ws -> D + 8 * Z.of_nat (length ws) <= alloc_ceiling -> u64arr bgusegs m1 D ws).
    { intros D ws U HB. eapply u64arr_agree; [apply (agree_on_of_munch _ _ _ MU WM)| exact U|]. intros a Ha. cbn. split; [lia| exact I]. }

    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (BN_clear_free_walk_emb HF) with (B := B) (lo := lo) (errv := errv) (A := A) (D := D1) (b := bRR) (L := L);
      [ exact HEAP1
      | intros pd Hpd; destruct (HS1 pd Hpd) as (I1 & P1 & U1); split; [exact I1|]; split; [exact P1|]; split;
        [ apply (UA _ _ U1); rewrite wlimbs_length; pose proof (LH_block_range _ _ _ _ HEAP I1) as (_ & _ & _ & Bc & _); cbn [blk_addr blk_size fst snd] in Bc; unfold bn_dmax in Bc; lia
        | intros a Ha; apply SCq; [| lia]; unfold L3, L2, L1 in INQ; rewrite Hpd in INQ; cbn [lb_remove_opt] in INQ;
          eapply lb_remove_opt_incl; eapply lb_remove_opt_incl; exact INQ ]
      | exact HN1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1
      | unfold bn_cells; exact BN1 | exact F1a | exact F1b | exact F1c | exact F1d | exact HD1
      | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | lia | clear - QA16; Z.div_mod_to_equations; lia | reflexivity | ].
    intros st1 ms1 PO BNa. unfold ofree_post in PO. rewrite ?ESP in PO. fold L1 in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    clear BNa.
    replace (ret_pc (Z_to_bv 64 1049836)) with (Z_to_bv 64 1049836) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in BN2; [| intros a Ha; cbn in Ha; apply SCq; [apply INC2; apply INC3; exact INQ| lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in BN3; [| intros a Ha; cbn in Ha; apply SCq; [apply INC2; apply INC3; exact INQ| lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in SCL; [| intros a Ha; cbn in Ha; apply SCq; [apply INC2; apply INC3; exact INQ| lia]].
    assert (CS4 : crypto_statics m4).
    { eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP4)| intros a Ha; apply libw_client; exact Ha| exact CS1]. }
    assert (HP0 : rheap_pres L1 (bv_unsigned sp) m m4).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply (CLI _ INC1)]|].
      eapply rheap_pres_weaken; [exact HP4| lia| auto]. }

    assert (UA4 : forall p D ws, u64arr bgusegs m1 D ws -> In (p, D, 8 * Z.of_nat (length ws)) L1 -> u64arr bgusegs m4 D ws).
    { intros p D ws U HIn. eapply u64arr_agree; [exact (agree_of_heap_pres _ _ _ _ HP4)| exact U|].
      intros a Ha. right. right. exists (p, D, 8 * Z.of_nat (length ws)). split; [exact HIn|]. cbn [blk_addr blk_size fst snd]. lia. }
    clear HEAP1 AUX1 CS1 AUX CS MI ERR ST.
    unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4. unfold MallocRep.wz.

    unfold implM. iprefix.
    step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (BN_clear_free_walk_emb HF) with (B := B) (lo := lo) (errv := errv) (A := A + 24) (D := D2) (b := bN) (L := L1);
      [ exact HEAP4
      | intros pd Hpd; destruct (HS2 pd Hpd) as (I1 & P1 & U1); split; [exact I1|]; split; [exact P1|]; split;
        [ apply (UA4 pd); [| rewrite wlimbs_length; unfold bn_dmax in I1; exact I1]; apply (UA _ _ U1); rewrite wlimbs_length;
          pose proof (LH_block_range _ _ _ _ HEAP (INC1 _ I1)) as (_ & _ & _ & Bc & _); cbn [blk_addr blk_size fst snd] in Bc; unfold bn_dmax in Bc; lia
        | intros a Ha; apply SCq; [| lia]; unfold L3, L2 in INQ; rewrite Hpd in INQ; cbn [lb_remove_opt] in INQ; eapply lb_remove_opt_incl; exact INQ ]
      | exact HN2 | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | reflexivity | exact CS4
      | exact BN2 | exact F2a | exact F2b | exact F2c | exact F2d | exact HD2
      | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | lia | clear - QA16; Z.div_mod_to_equations; lia | reflexivity | ].
    intros st2 ms2 PO BNb. unfold ofree_post in PO. rewrite ?ESP in PO. fold L2 in PO.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    clear BNb.
    replace (ret_pc (Z_to_bv 64 1049844)) with (Z_to_bv 64 1049844) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in BN3; [| intros a Ha; cbn in Ha; apply SCq; [apply INC3; exact INQ| lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in SCL; [| intros a Ha; cbn in Ha; apply SCq; [apply INC3; exact INQ| lia]].
    assert (CS5 : crypto_statics m5).
    { eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP5)| intros a Ha; apply libw_client; exact Ha| exact CS4]. }
    assert (HP05 : rheap_pres L2 (bv_unsigned sp) m m5).
    { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| exact INC2]|]. eapply rheap_pres_weaken; [exact HP5| lia| auto]. }
    assert (UA5 : forall p D ws, u64arr bgusegs m4 D ws -> In (p, D, 8 * Z.of_nat (length ws)) L2 -> u64arr bgusegs m5 D ws).
    { intros p D ws U HIn. eapply u64arr_agree; [exact (agree_of_heap_pres _ _ _ _ HP5)| exact U|].
      intros a Ha. right. right. exists (p, D, 8 * Z.of_nat (length ws)). split; [exact HIn|]. cbn [blk_addr blk_size fst snd]. lia. }
    clear HEAP4 AUX4 CS4 MI4 ERR4 ST4 HP4 HP0.
    unfold LX_ERRNO, RATP in ERR5. change (3346328 - 164) with 3346164 in ERR5. unfold MallocRep.wz.

    unfold implM. iprefix.
    step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (BN_clear_free_walk_emb HF) with (B := B) (lo := lo) (errv := errv) (A := A + 48) (D := D3) (b := bNi) (L := L2);
      [ exact HEAP5
      | intros pd Hpd; destruct (HS3 pd Hpd) as (I1 & P1 & U1); split; [exact I1|]; split; [exact P1|]; split;
        [ apply (UA5 pd); [| rewrite wlimbs_length; unfold bn_dmax in I1; exact I1];
          apply (UA4 pd); [| rewrite wlimbs_length; unfold bn_dmax in I1; apply INC2; exact I1]; apply (UA _ _ U1); rewrite wlimbs_length;
          pose proof (LH_block_range _ _ _ _ HEAP (INC1 _ (INC2 _ I1))) as (_ & _ & _ & Bc & _); cbn [blk_addr blk_size fst snd] in Bc; unfold bn_dmax in Bc; lia
        | intros a Ha; apply SCq; [| lia]; unfold L3 in INQ; rewrite Hpd in INQ; cbn [lb_remove_opt] in INQ; exact INQ ]
      | exact HN3 | exact AUX5 | rewrite ESP; lia | rewrite ESP; exact ST5 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR5 | exact MI5 | reflexivity | exact CS5
      | exact BN3 | exact F3a | exact F3b | exact F3c | exact F3d | exact HD3
      | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | lia | clear - QA16; Z.div_mod_to_equations; lia | reflexivity | ].
    intros st3 ms3 PO BNc. unfold ofree_post in PO. rewrite ?ESP in PO. fold L3 in PO.
    destruct PO as (o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & m6
                    & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
    clear BNc.
    replace (ret_pc (Z_to_bv 64 1049852)) with (Z_to_bv 64 1049852) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP6)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP6)) in SCL; [| intros a Ha; cbn in Ha; apply SCq; [exact INQ| lia]].
    assert (CS6 : crypto_statics m6).
    { eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP6)| intros a Ha; apply libw_client; exact Ha| exact CS5]. }
    assert (HP06 : rheap_pres L3 (bv_unsigned sp) m m6).
    { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP05| lia| exact INC3]|]. eapply rheap_pres_weaken; [exact HP6| lia| auto]. }
    clear HEAP5 AUX5 CS5 MI5 ERR5 ST5 HP5 HP05.
    unfold LX_ERRNO, RATP in ERR6. change (3346328 - 164) with 3346164 in ERR6. unfold MallocRep.wz.

    unfold implM. iprefix.
    apply (mont_flags_split _ _ _ _ _ _ Hfl) in SCL.
    step. rewrite (zxb_small fl) by lia. step. rewrite (unsigned_lit fl), Efl by lia. step. if_true.
    step. step. step. step.
    do 3 step. release_frame FR ST6 (bv_unsigned sp). step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 96) (L := L3);
      [ exact HEAP6 | exact INQ | exact AUX6 | lia | exact ST6 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR6 | exact MI6 | reflexivity | exact CS6 | reflexivity | ].
    intros st4 ms4 PO. apply K. unfold cfree_post in PO. unfold gfree_post.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m7
                    & -> & MI7 & ST7 & ERR7 & AUX7 & HP7 & FA7 & SO7 & HEAP7).
    do 15 eexists. exists m7. split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST7|]. split; [exact ERR7|]. split; [exact AUX7|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP06| lia| intros b Hb; eapply lb_remove_incl; exact Hb]| exact HP7]. }
    split; [rewrite FA7, FA6, FA5; exact FA4|]. split; [rewrite SO7, SO6, SO5; exact SO4|]. exact HEAP7.
  Qed.

  Definition BN_CTX_NEW : Z := 0x100a5c.

  Definition BN_CTX_NEW_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.

  Lemma zero_ctx_cells : forall m A,
    rw_cells bgusegs m A ([CB 48%nat (repeat (Z_to_bv 8 0) 48%nat)] ++ [CB 24%nat (repeat (Z_to_bv 8 0) 24%nat)]) -> rw_cells bgusegs m A ctx_cells0.
  Proof.
    intros m A [[Hwf Hb] Hw]. split; [split|].
    - cbn. repeat split.
    - cbn [cells_bytes cbytes ctx_cells0 app repeat] in *. exact Hb.
    - cbn [cells_size csize Nat.add app] in *. exact Hw.
  Qed.

  Lemma BN_CTX_new_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_CTX_NEW_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP ->
    crypto_statics m ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 72 lo B m
                   (fun A m' => rw_cells bgusegs m' A ctx_cells0) p s' ms' ->
       implM bgusegs (interp (k (Some p))) s' Q ms') ->
    implM bgusegs (interp (LMalloc 72 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_NEW) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS KN K.
    unfold BN_CTX_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, BN_CTX_NEW, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold implM. iprefix.
    carve_frame 16%nat ST. do 4 step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    carve_frame 32%nat ST. do 5 step. do 5 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 72);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 1051164)) with (Z_to_bv 64 1051164) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 72 lo B m
                   (fun A m' => rw_cells bgusegs m' A ctx_cells0) p st1); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 72)]%Z m3) as MU3. pose proof (wmono_refl bgusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, 72) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 72)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, 72) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    assert (BLKu : rw_cells bgusegs m3 A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { eapply bk_rw_cells_recast; [exact BLK | cbn; repeat split | reflexivity | reflexivity]. }
    clear BLK.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. rewrite (land7_wrap A) by (clear - BA16; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    do 7 step. do 3 step. release_frame FR ST3 (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. unfold calloc_post, MallocRep.wz.
    do 14 eexists. exists mF, A, errv2. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             pose proof AUX3 as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB & _).
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, 72)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    unfold ctx_cells0, MallocRep.wz.
    lazymatch goal with H : rw_cells bgusegs mF A _ |- _ =>
      eapply bk_rw_cells_recast; [exact H | cbn; repeat split | reflexivity | reflexivity] end.
  Qed.
End Proofs.
End WithCeiling0.
