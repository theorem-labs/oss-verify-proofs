(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Drv_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnArith W_num_bits_word.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnArr DivModel DivLoopPure FuzzPure.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_expand W_ctx BnLeaves BnCall DivLA DivBody DivLoop W_lshift W_rshift W_ctx_end W_small W_small2 W_top BnAssoc BnRep2 W_calls W_div_tail W_div W_bndiv BnUAlign.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].







(* [comment removed for export] *)
Ltac fix_ret :=
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

(* [comment removed for export] *)
Lemma lib_state_statics : forall cxo hs ls m OW AD EA, lib_state_hc cxo hs ls m OW AD EA -> ro_cells usegs m BN_STATICS (ad_cells AD).
Proof. intros cxo hs ls m OW AD EA (_ & _ & _ & (_ & _ & (H & _))). exact H. Qed.

(* [comment removed for export] *)
Ltac br_lit :=
  let K := fresh "KBR" in
  zstep; if_cases K; zify_cond K; try (exfalso; rewrite ?unsigned_lit in K by lia; lia); try clear K.

Ltac get_stat LS STAT :=
  pose proof (lib_state_statics _ _ _ _ _ _ _ LS) as STAT; unfold ad_cells, BN_STATICS, MallocRep.wz in STAT.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition LX_FUZZ_ENTRY : Z := 0xe1a44.
Definition FUZZ_STACK : Z := 64 + 32768.
Definition ERR_CLEAR_ERROR : Z := 0xe53ec.
Definition BN_BIN2BN : Z := 0xe287c.
Definition BN_MUL : Z := 0x116c6c.
Definition BN_ADD : Z := 0x119b14.
Definition BN_CMP : Z := 0xe32f4.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Variables (BN_BIN2BN_STACK BN_MUL_STACK BN_ADD_STACK ECE_STACK : Z).
  Hypothesis STK_B2B : BN_BIN2BN_STACK <= 32768.
  Hypothesis STK_MUL : BN_MUL_STACK <= 32768.
  Hypothesis STK_ADD : BN_ADD_STACK <= 32768.
  Hypothesis STK_ECE : 0 <= ECE_STACK <= 32768.

  Hypothesis BN_bin2bn_walk_h : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (r : bnref) (a D : Z) (n : list Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_BIN2BN_STACK -> tp = wz RATP -> ref_at ls OW AD r a ->
    bytes_at usegs m D (to_bytes n) -> Forall (fun c => 0 <= c < 256) n -> 0 < D -> D + zlength n < 2^63 -> zlength n < 2^31 ->
    (n = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength n <= blk_addr b + blk_size b) ->
    a0 = wz D -> a1 = wz (zlength n) -> a2 = wz a ->
    implM usegs (interp (embed (BN_bin2bn (tree_ops bptr) n r ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz a))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_BIN2BN) fc None m (seg_rom usegs)).

  Hypothesis BN_mul_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_MUL_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> ref_at ls OW AD ry ay ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz (ad_ctx AD) ->
    nonpool rr -> nonpool rx -> nonpool ry ->
    implM usegs (interp (embed (BN_mul (tree_ops bptr) rr rx ry ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL) fc None m (seg_rom usegs)).

  Hypothesis BN_add_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_ADD_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> ref_at ls OW AD ry ay ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay ->
    implM usegs (interp (embed (BN_add (tree_ops bptr) rr rx ry ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_ADD) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Hypothesis BN_cmp_evt : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv 16 -> tp = wz RATP ->
    ref_at ls OW AD r1 a -> ref_at ls OW AD r2 b -> a0 = wz a -> a1 = wz b ->
    evt usegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
                       (fun c ls' OW' a0' => a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ ls' = ls /\ OW' = OW)
                       (cmp_pure (getbn r1 ls) (getbn r2 ls), ls) s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz BN_CMP) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Hypothesis ERR_clear_error_spec : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : PState) (L OW : list block) (EA : err_addrs),
    stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ECE_STACK ->
    bv_unsigned sp mod 16 = 0 -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
    RHEAP s L m -> (forall b, In b OW -> In b L) ->
    crypto_statics m -> err_inv m OW EA ->
    evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(ea_ES EA, ea_ES EA + 904); (bv_unsigned sp - ECE_STACK, bv_unsigned sp)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' (ea_ES EA) [CB 904 ES_CLEARED])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ERR_CLEAR_ERROR) fc None m (seg_rom usegs)).

  Section Env.
    (* [comment removed for export] *)
    Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO : GLOBALS_TOP <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - (64 + 32768).
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.

    Notation FB := (bv_unsigned sp + -64).
    Notation FRM := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Notation CENV st' ls' m' OW' := (cenv LB AD lo B (bv_unsigned sp) FB s ls OW m FRM st' ls' m' OW').
    Notation QPOST := (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
                               (fun (rc : Z) (_ : lstate bptr) (_ : list block) (a0' : word) => rc = 0 /\ a0' = wz 0)).

    Lemma SPRf : bv_unsigned sp < 2 ^ 64.
    Proof. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. lia. Qed.

    (* [comment removed for export] *)
    Lemma fuzz_done : forall st' ls' m' OW' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
      CENV st' ls' m' OW' -> lib_state ls' m' OW' AD EA ->
      evt usegs (QPOST (0, ls') st')
        (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xe1c40) fc None m' (seg_rom usegs)).
    Proof using CEIL GLO LO SPB SP16 STK_ECE ERR_clear_error_spec.
      intros until x31. intros ENV LS'.
      pose proof SPRf as SPR2.
      pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
      pose proof LS' as (CS & EI & _).
      destruct (lib_state_h_parts _ _ _ _ _ _ LS') as (IDS & ADB & (_ & _ & _ & EB4) & SOK).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP EB4) as (E0 & _ & _ & EC & EI').
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
      unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR. unfold GLOBALS_TOP in GLO.
      zstep.
      eapply evt_cut.
      { eapply ERR_clear_error_spec with (lo := lo) (s := st') (L := OW' ++ LB) (OW := OW') (EA := EA);
          [rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; exact GLO | rewrite ESP; lia | rewrite ESP; replace (bv_unsigned sp + -64) with (bv_unsigned sp + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact SP16 | exact MI | reflexivity
          | exact HEAP | intros b Hb; apply in_or_app; left; exact Hb | exact CS | exact EI]. }
      intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ESc).
      rewrite ESP in *.
      replace (ret_pc (Z_to_bv 64 924740)) with (Z_to_bv 64 924740) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport usegs _ m' m2) in FR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [right; lia|]; split; [right; lia| exact I]].
      eapply (rw_cells_transport usegs _ m' m2) in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [lia|]; split; [left; lia| exact I]].
      assert (WOK : Forall (w_ok OW' LB ls' AD EA []) [(FB - ECE_STACK, FB)]) by (constructor; [apply w_stack; cbn [fst]; lia| constructor]).
      assert (HWL : Forall (w_lib OW' lo (bv_unsigned sp)) [(ea_ES EA, ea_ES EA + 904); (FB - ECE_STACK, FB)]).
      { constructor; [right; exists (ea_pe EA, ea_ES EA, 904); cbn; split; [exact EB4| lia]|]. constructor; [left; cbn [fst snd]; lia| constructor]. }
      pose proof (lib_state_err_cleared st' LB ls' m' m2 OW' AD EA _ HEAP LS' MUc WMc WOK ESc) as LS2.
      assert (ENV2 : CENV st' ls' m2 OW').
      { eapply (cenv_silent LB AD lo B (bv_unsigned sp) FB s ls OW m CEIL ltac:(unfold GLOBALS_TOP; exact GLO) ltac:(lia) ltac:(lia) SPB FRM FRM);
          [exact ENV | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ]. }
      pose proof (cenv_final LB AD EA lo B (bv_unsigned sp) FB s ls OW m _ _ _ _ _ ENV2 LS2)
        as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
      clear ERR. pose proof (munch_refl [(FB, bv_unsigned sp)]%Z m2) as MUe. pose proof (wmono_refl usegs m2) as WMe.
      zstep. do 8 step.
      release_frame FR STc (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m2, OW', errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STc|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
    Qed.
    (* [comment removed for export] *)
    Definition fz_success (lsx : lstate bptr) : bool :=
      let b1 := getbn RB1 lsx in let b2 := getbn RB2 lsx in let b3 := getbn RB3 lsx in let b4 := getbn RB4 lsx in
      let z (b : bignum bptr) := (bn_top b =? 0)%nat in
      if z b1 then z b3 && z b4
      else if bn_neg b1 then (negb (Bool.eqb (bn_neg b3) (bn_neg b2)) || z b3) && (bn_neg b4 || z b4)
      else (Bool.eqb (bn_neg b3) (bn_neg b2) || z b3) && (negb (bn_neg b4) || z b4).

    Lemma fuzz_check : forall (POST : machine_state -> Prop) st' ls' m' OW' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31,
      CENV st' ls' m' OW' -> lib_state ls' m' OW' AD EA ->
      (forall m2 v y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
         CENV st' ls' m2 OW' -> lib_state ls' m2 OW' AD EA -> v = Z.b2z (fz_success ls') ->
         evt usegs POST (MS (mkR y1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 v) y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21
                                 (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 y28 y29 y30 y31)
                            F (Z_to_bv 64 0xe1d28) fc None m2 (seg_rom usegs))) ->
      evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                              (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0xe1c8c) fc None m' (seg_rom usegs)).
    Proof using CEIL GLO LO SPB.
      intros until x31. intros ENV LS' K.
      pose proof SPRf as SPR2.
      assert (LOFB : lo <= FB - 16) by lia. assert (FBSP : FB <= bv_unsigned sp) by lia.
      pose proof (is_zero_call LB AD EA lo B (bv_unsigned sp) FB s ls OW m CEIL GLO LOFB FBSP SPB SPR2) as IZC.
      pose proof (is_neg_call LB AD EA lo B (bv_unsigned sp) FB s ls OW m CEIL GLO LOFB FBSP SPB SPR2) as INC.
      unfold BN_IS_ZERO, BN_IS_NEGATIVE in *.
      remember (bn_top (getbn RB1 ls') =? 0)%nat as z1 eqn:EZ1. remember (bn_top (getbn RB3 ls') =? 0)%nat as z3 eqn:EZ3.
      remember (bn_top (getbn RB4 ls') =? 0)%nat as z4 eqn:EZ4.
      remember (bn_neg (getbn RB1 ls')) as n1 eqn:EN1. remember (bn_neg (getbn RB2 ls')) as n2 eqn:EN2.
      remember (bn_neg (getbn RB3 ls')) as n3 eqn:EN3. remember (bn_neg (getbn RB4 ls')) as n4 eqn:EN4.
      assert (ESUC : fz_success ls' = if z1 then z3 && z4 else if n1 then (negb (Bool.eqb n3 n2) || z3) && (n4 || z4) else (Bool.eqb n3 n2 || z3) && (negb n4 || z4))
        by (unfold fz_success; rewrite <- EZ1, <- EZ3, <- EZ4, <- EN1, <- EN2, <- EN3, <- EN4; reflexivity).
      (* [comment removed for export] *)
      assert (BZ4 : forall mx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
                 CENV st' ls' mx OW' -> lib_state ls' mx OW' AD EA -> Z.b2z z4 = Z.b2z (fz_success ls') ->
                 evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                         (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                    F (Z_to_bv 64 0xe1ca4) fc None mx (seg_rom usegs))).
      { intros mx q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx EQ.
        get_stat LSx STAT.
        step. zstep.
        eapply (IZC POST FRM st' ls' mx OW' RB4 (ad_b4 AD)); [exact ENVx | exact LSx | exact eq_refl |].
        intros m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2. fix_ret. rewrite <- EZ4.
        do 2 zstep.
        eapply K; [exact ENV2 | exact LS2 | rewrite <- EQ; destruct z4; reflexivity]. }
      (* [comment removed for export] *)
      assert (B1 : forall mx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
                 CENV st' ls' mx OW' -> lib_state ls' mx OW' AD EA -> fz_success ls' = true ->
                 evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                         (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                    F (Z_to_bv 64 0xe1d1c) fc None mx (seg_rom usegs))).
      { intros mx q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx EQ.
        do 2 zstep. eapply K; [exact ENVx | exact LSx | rewrite EQ; reflexivity]. }
      assert (B0 : forall mx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
                 CENV st' ls' mx OW' -> lib_state ls' mx OW' AD EA -> fz_success ls' = false ->
                 evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                         (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                    F (Z_to_bv 64 0xe1d24) fc None mx (seg_rom usegs))).
      { intros mx q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx EQ.
        zstep. eapply K; [exact ENVx | exact LSx | rewrite EQ; reflexivity]. }
      (* [comment removed for export] *)
      get_stat LS' STAT0.
      step. zstep.
      eapply (IZC POST FRM st' ls' m' OW' RB1 (ad_b1 AD)); [exact ENV | exact LS' | exact eq_refl |].
      intros ma ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVa LSa. fix_ret. rewrite <- EZ1. clear STAT0.
      get_stat LSa STATa.
      destruct z1; cbn [Z.b2z].
      - (* [comment removed for export] *)
        br_lit. step. zstep.
        eapply (IZC POST FRM st' ls' ma OW' RB3 (ad_b3 AD)); [exact ENVa | exact LSa | exact eq_refl |].
        intros mb ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVb LSb. fix_ret. rewrite <- EZ3. clear STATa.
        destruct z3; cbn [Z.b2z].
        + br_lit. eapply BZ4; [exact ENVb | exact LSb | rewrite ESUC; reflexivity].
        + br_lit. eapply B0; [exact ENVb | exact LSb | rewrite ESUC; reflexivity].
      - (* [comment removed for export] *)
        br_lit. step. zstep.
        eapply (INC POST FRM st' ls' ma OW' RB1 (ad_b1 AD)); [exact ENVa | exact LSa | exact eq_refl |].
        intros mb ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVb LSb. fix_ret. rewrite <- EN1. clear STATa.
        get_stat LSb STATb. step. do 3 zstep.
        eapply (INC POST FRM st' ls' mb OW' RB3 (ad_b3 AD)); [exact ENVb | exact LSb | exact eq_refl |].
        intros mc ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVc LSc. fix_ret. rewrite <- EN3. clear STATb.
        get_stat LSc STATc. step. do 3 zstep.
        eapply (INC POST FRM st' ls' mc OW' RB2 (ad_b2 AD)); [exact ENVc | exact LSc | exact eq_refl |].
        intros md ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVd LSd. fix_ret. rewrite <- EN2. clear STATc.
        destruct n1; cbn [Z.b2z].
        + (* [comment removed for export] *)
          assert (B310 : forall mx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
                   CENV st' ls' mx OW' -> lib_state ls' mx OW' AD EA -> (negb (Bool.eqb n3 n2) || z3) = true ->
                   evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                           (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                      F (Z_to_bv 64 0xe1cf0) fc None mx (seg_rom usegs))).
          { intros mx q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx HP.
            get_stat LSx STAT. step. zstep.
            eapply (INC POST FRM st' ls' mx OW' RB4 (ad_b4 AD)); [exact ENVx | exact LSx | exact eq_refl |].
            intros my ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVy LSy. fix_ret. rewrite <- EN4. clear STAT.
            destruct n4; cbn [Z.b2z].
            - br_lit. zstep. eapply B1; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity].
            - br_lit. eapply BZ4; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity]. }
          br_lit.
          destruct (Bool.eqb n3 n2) eqn:E32.
          * (* [comment removed for export] *)
            zstep. if_cases KN; zify_cond KN.
            { exfalso. apply KN. rewrite (Bool.eqb_prop _ _ E32). reflexivity. }
            clear KN. get_stat LSd STATd. step. zstep.
            eapply (IZC POST FRM st' ls' md OW' RB3 (ad_b3 AD)); [exact ENVd | exact LSd | exact eq_refl |].
            intros me ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVe LSe. fix_ret. rewrite <- EZ3. clear STATd.
            destruct z3; cbn [Z.b2z].
            -- br_lit. eapply B310; [exact ENVe | exact LSe | reflexivity].
            -- br_lit. eapply B0; [exact ENVe | exact LSe | rewrite ESUC; reflexivity].
          * zstep. if_cases KN; zify_cond KN.
            2:{ exfalso. destruct n3, n2; cbn in E32, KN; try discriminate; rewrite ?unsigned_lit in KN by lia; lia. }
            clear KN. eapply B310; [exact ENVd | exact LSd | reflexivity].
        + (* [comment removed for export] *)
          assert (B330 : forall mx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
                   CENV st' ls' mx OW' -> lib_state ls' mx OW' AD EA -> (Bool.eqb n3 n2 || z3) = true ->
                   evt usegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                           (Z_to_bv 64 3342112) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                      F (Z_to_bv 64 0xe1d10) fc None mx (seg_rom usegs))).
          { intros mx q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVx LSx HP.
            get_stat LSx STAT. step. zstep.
            eapply (INC POST FRM st' ls' mx OW' RB4 (ad_b4 AD)); [exact ENVx | exact LSx | exact eq_refl |].
            intros my ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVy LSy. fix_ret. rewrite <- EN4. clear STAT.
            destruct n4; cbn [Z.b2z].
            - br_lit. eapply BZ4; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity].
            - br_lit. eapply B1; [exact ENVy | exact LSy | rewrite ESUC, HP; reflexivity]. }
          br_lit.
          destruct (Bool.eqb n3 n2) eqn:E32.
          * zstep. if_cases KN; zify_cond KN.
            2:{ exfalso. apply KN. rewrite (Bool.eqb_prop _ _ E32). reflexivity. }
            clear KN. eapply B330; [exact ENVd | exact LSd | reflexivity].
          * (* [comment removed for export] *)
            zstep. if_cases KN; zify_cond KN.
            { exfalso. destruct n3, n2; cbn in E32, KN; try discriminate; rewrite ?unsigned_lit in KN by lia; lia. }
            clear KN. get_stat LSd STATd. step. zstep.
            eapply (IZC POST FRM st' ls' md OW' RB3 (ad_b3 AD)); [exact ENVd | exact LSd | exact eq_refl |].
            intros me ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVe LSe. fix_ret. rewrite <- EZ3. clear STATd.
            destruct z3; cbn [Z.b2z].
            -- br_lit. eapply B330; [exact ENVe | exact LSe | reflexivity].
            -- br_lit. eapply B0; [exact ENVe | exact LSe | rewrite ESUC; reflexivity].
    Qed.
    (* [comment removed for export] *)
    Lemma bytes_client : forall st' ls' mx OW' A bs,
      CENV st' ls' mx OW' -> bytes_at usegs m A bs ->
      (bs = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length bs) <= blk_addr b + blk_size b) ->
      bytes_at usegs mx A bs.
    Proof.
      intros st' ls' mx OW' A bs (HEAP & _ & _ & _ & _ & LXP & _) BY [->|(b & Hb & Hb1 & Hb2)].
      - destruct BY as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - eapply bytes_at_agree; [apply agree_of_lx_pres; exact LXP | exact BY |].
        intros a Ha.
        pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & BI).
        split; [| right; left; exists b; split; [exact Hb| lia]].
        unfold LIBW_bn. cbn [rin_ivs fst snd]. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_main : forall (buf : Z) (n1 n2 : list Z) (v1 v2 : Z) m1
        x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31,
      CENV s ls m1 OW -> lib_state ls m1 OW AD EA ->
      bytes_at usegs m buf (to_bytes n1) -> bytes_at usegs m (buf + zlength n1) (to_bytes n2) ->
      Forall (fun c => 0 <= c < 256) n1 -> Forall (fun c => 0 <= c < 256) n2 ->
      0 < buf -> buf + zlength n1 + zlength n2 < 2^63 -> zlength n1 < 2^31 -> zlength n2 < 2^31 ->
      (n1 = [] \/ exists b, In b LB /\ blk_addr b <= buf /\ buf + zlength n1 <= blk_addr b + blk_size b) ->
      (n2 = [] \/ exists b, In b LB /\ blk_addr b <= buf + zlength n1 /\ buf + zlength n1 + zlength n2 <= blk_addr b + blk_size b) ->
      0 <= v1 < 2^64 -> 0 <= v2 < 2^64 ->
      implM usegs (interp (embed (fuzz_body (negb (v1 =? 0)) (negb (v2 =? 0)) n1 n2 ls))) s QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 buf) (Z_to_bv 64 v2) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (zlength n2)) (Z_to_bv 64 v1) (Z_to_bv 64 (zlength n1)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xe1bd0) fc None m1 (seg_rom usegs)).
    Proof.
      intros until x31. intros ENV0 LS0 BY1 BY2 BF1 BF2 BUF0 BUF63 L1 L2 CB1 CB2 RV1 RV2.
      pose proof SPRf as SPR2.
      assert (FBlo : lo <= FB) by lia. assert (FBsp : FB <= bv_unsigned sp) by lia.
      assert (LOFB : lo <= FB - 16) by lia.
      pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) FB s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
      pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) FB s ls OW m CEIL GLO FBlo FBsp) as CPOST.
      pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) FB CEIL FBlo FBsp SPR2 A) as BPC.
      pose proof (is_zero_call LB AD EA lo B (bv_unsigned sp) FB s ls OW m CEIL GLO LOFB FBsp SPB SPR2) as IZC.
      pose proof (set_neg_call LB AD EA lo B (bv_unsigned sp) FB s ls OW m CEIL GLO LOFB FBsp SPB SPR2) as SNC.
      unfold BN_IS_ZERO in *.
      unfold fuzz_body. cbv zeta.
      (* [comment removed for export] *)
      get_stat LS0 STAT0.
      unfold implM. iprefix.
      do 2 zstep. step. do 3 zstep.
      assert (CBx : forall A n, (n = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + zlength n <= blk_addr b + blk_size b) ->
                    (to_bytes n = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length (to_bytes n)) <= blk_addr b + blk_size b)).
      { intros A n [->|H]; [left; reflexivity| right]. rewrite zlength_to_bytes. exact H. }
      destruct (CPRE _ _ _ _ _ BN_BIN2BN_STACK ENV0 LS0 ltac:(lia)) as (errv1 & PRE1).
      ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply BN_bin2bn_walk_h with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA) (r := RB1) (a := ad_b1 AD) (D := buf) (n := n1);
          [exact PRE1 | reflexivity | exact eq_refl | eapply bytes_client; [exact ENV0 | exact BY1 | apply CBx; exact CB1]
          | exact BF1 | exact BUF0 | unfold zlength in *; lia | exact L1 | exact CB1 | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros [u1 ls1] st1 ms1 PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW1 & -> & CP1 & ->).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV0 CP1) as (ENV1 & LS1).
      cbn [fst snd] in *. fix_ret. clear PRE1 CP1 STAT0.
      (* [comment removed for export] *)
      get_stat LS1 STAT1.
      unfold MallocRep.wz. unfold implM. iprefix.
      step.
      zstep. if_cases KN; zify_cond KN. { exfalso. apply KN. reflexivity. }
      clear KN. do 3 zstep.
      eapply (SNC _ FRM st1 ls1 m2 OW1 RB1 (ad_b1 AD)); [exact ENV1 | exact LS1 | exact eq_refl |].
      intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. fix_ret. clear STAT1.
      rewrite (unsigned_lit v1) in ENV2, LS2 by lia.
      lazymatch type of LS2 with lib_state ?l _ _ _ _ => set (ls2 := l) in * end.
      (* [comment removed for export] *)
      get_stat LS2 STAT2.
      zstep.
      chk ltac:(fun C => clear - C BUF0 BUF63 L1; unfold zlength in *; rewrite !land64_small in C by lia; lia).
      do 3 zstep.
      rewrite !land64_small by (clear - BUF0 BUF63 L1; unfold zlength in *; lia).
      replace (0 <? buf) with true by (symmetry; apply Z.ltb_lt; exact BUF0).
      replace (zlength n1 + buf <? 1) with false by (symmetry; apply Z.ltb_ge; clear - BUF0; unfold zlength; lia).
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      chk_lit.
      replace (zlength n1 + buf) with (buf + zlength n1) by (clear; lia).
(* [comment removed for export] *)
      step. do 2 zstep.
      destruct (CPRE _ _ _ _ _ BN_BIN2BN_STACK ENV2 LS2 ltac:(lia)) as (errv3 & PRE3).
      ihere. to_implM. unfold BN_set_negative at 1. rewrite bbind_get_set. fold ls2.
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply BN_bin2bn_walk_h with (lo := lo) (B := B) (errv := errv3) (OW := OW1) (LB := LB) (AD := AD) (EA := EA) (r := RB2) (a := ad_b2 AD) (D := buf + zlength n1) (n := n2);
          [exact PRE3 | reflexivity | exact eq_refl | eapply bytes_client; [exact ENV2 | exact BY2 | apply CBx; exact CB2]
          | exact BF2 | unfold zlength in *; lia | lia | exact L2 | exact CB2 | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros [u3 ls3] st3 ms3 PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW3 & -> & CP3 & ->).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV2 CP3) as (ENV3 & LS3).
      cbn [fst snd] in *. fix_ret. clear PRE3 CP3 STAT2.
      (* [comment removed for export] *)
      get_stat LS3 STAT3.
      unfold MallocRep.wz. unfold implM. iprefix.
      step.
      zstep. if_cases KN; zify_cond KN. { exfalso. apply KN. reflexivity. }
      clear KN. do 3 zstep.
      eapply (SNC _ FRM st3 ls3 m4 OW3 RB2 (ad_b2 AD)); [exact ENV3 | exact LS3 | exact eq_refl |].
      intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4. fix_ret. clear STAT3.
      rewrite (unsigned_lit v2) in ENV4, LS4 by lia.
      lazymatch type of LS4 with lib_state ?l _ _ _ _ => set (ls4 := l) in * end.
      (* [comment removed for export] *)
      get_stat LS4 STAT4.
      step. zstep.
      eapply (IZC _ FRM st3 ls4 m5 OW3 RB2 (ad_b2 AD)); [exact ENV4 | exact LS4 | exact eq_refl |].
      intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV5 LS5. fix_ret. clear STAT4.
      ihere. cbv beta. to_implM. unfold BN_set_negative at 1. rewrite bbind_get_set. fold ls4. rewrite bbind_get.
      destruct (bn_top (getbn RB2 ls4) =? 0)%nat eqn:Z2; cbn [Z.b2z].
      { (* [comment removed for export] *)
        unfold bbind, bret. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_ret.
        br_lit. eapply fuzz_done; [exact ENV5 | exact LS5]. }
      (* [comment removed for export] *)
      get_stat LS5 STAT5.
      unfold implM. iprefix. br_lit.
      do 5 step. zstep.
      destruct (CPRE _ _ _ _ _ BN_DIV_TOP_STACK ENV5 LS5 ltac:(unfold BN_DIV_TOP_STACK, BN_DIV_STACK; lia)) as (errv6 & PRE6).
      ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops]. unfold bbind at 1. cbn [bind tree_ops].
      apply implM_embed_assoc.
      eapply implM_embed_bind.
      { eapply (BN_div_walk HM HF) with (lo := lo) (B := B) (errv := errv6) (OW := OW3) (LB := LB) (AD := AD) (EA := EA)
                 (dv := RB3) (rm := RB4) (num := RB1) (dvs := RB2) (adv := ad_b3 AD) (arm := ad_b4 AD) (anum := ad_b1 AD) (advs := ad_b2 AD);
          [exact PRE6 | reflexivity | exact eq_refl | exact eq_refl | exact eq_refl | exact eq_refl
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | intros i; discriminate | intros i; discriminate | intros i; discriminate | intros i; discriminate | discriminate | discriminate]. }
      cbv beta. intros [u6 ls6] st6 ms6 PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & OW6 & -> & CP6 & ->).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV5 CP6) as (ENV6 & LS6).
      cbn [fst snd] in *. fix_ret. clear PRE6 CP6 STAT5.
      (* [comment removed for export] *)
      unfold MallocRep.wz. unfold implM. iprefix.
      br_lit.
      eapply (fuzz_check _ st6 ls6 m7 OW6); [exact ENV6 | exact LS6 |].
      intros m8 v ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 EV.
      (* [comment removed for export] *)
      get_stat LS7 STAT7.
      do 4 step. zstep.
      destruct (CPRE _ _ _ _ _ BN_MUL_STACK ENV7 LS7 ltac:(lia)) as (errv8 & PRE8).
      ihere. cbv beta. to_implM. cbn [fst snd]. rewrite !bbind_get. cbv zeta.
      unfold bbind at 1. cbn [bind tree_ops].
      apply implM_embed_assoc.
      eapply implM_embed_bind.
      { eapply BN_mul_walk with (lo := lo) (B := B) (errv := errv8) (OW := OW6) (LB := LB) (AD := AD) (EA := EA)
                 (rr := RB5) (rx := RB3) (ry := RB2) (ar := ad_b5 AD) (ax := ad_b3 AD) (ay := ad_b2 AD);
          [exact PRE8 | reflexivity | exact eq_refl | exact eq_refl | exact eq_refl | reflexivity | reflexivity | reflexivity | reflexivity
          | intros i; discriminate | intros i; discriminate | intros i; discriminate]. }
      cbv beta. intros [u8 ls8] st8 ms8 PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW8 & -> & CP8 & ->).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV7 CP8) as (ENV8 & LS8).
      cbn [fst snd] in *. fix_ret. clear PRE8 CP8 STAT7.
      (* [comment removed for export] *)
      get_stat LS8 STAT8.
      unfold MallocRep.wz. unfold implM. iprefix.
      br_lit.
      do 2 step. do 2 zstep.
      destruct (CPRE _ _ _ _ _ BN_ADD_STACK ENV8 LS8 ltac:(lia)) as (errv9 & PRE9).
      ihere. to_implM.
      unfold bbind at 1. cbn [bind tree_ops].
      apply implM_embed_assoc.
      eapply implM_embed_bind.
      { eapply BN_add_walk with (lo := lo) (B := B) (errv := errv9) (OW := OW8) (LB := LB) (AD := AD) (EA := EA)
                 (rr := RB5) (rx := RB5) (ry := RB4) (ar := ad_b5 AD) (ax := ad_b5 AD) (ay := ad_b4 AD);
          [exact PRE9 | reflexivity | exact eq_refl | exact eq_refl | exact eq_refl | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros [u9 ls9] st9 ms9 PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m10 & OW9 & -> & CP9 & ->).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV8 CP9) as (ENV9 & LS9).
      cbn [fst snd] in *. fix_ret. clear PRE9 CP9 STAT8.
      (* [comment removed for export] *)
      rewrite !bbind_get.
      lazymatch goal with |- context [if (?e && (cmp_pure _ _ =? 0)) then _ else _] => change e with (fz_success ls6) end.
      set (c := cmp_pure (getbn RB5 ls9) (getbn RB1 ls9)).
      get_stat LS9 STAT9.
      unfold MallocRep.wz. unfold implM. iprefix.
      br_lit.
      subst v. destruct (fz_success ls6); cbn [Z.b2z].
      2:{ (* [comment removed for export] *)
          br_lit. ihere. cbv beta. to_implM. cbn [andb].
          unfold bbind, bunr. cbn [bind unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
      br_lit. do 2 step. zstep.
      destruct (CPRE _ _ _ _ _ 16 ENV9 LS9 ltac:(lia)) as (errv10 & PRE10).
      eapply evt_cut.
      { eapply BN_cmp_evt with (lo := lo) (B := B) (errv := errv10) (OW := OW9) (LB := LB) (AD := AD) (EA := EA)
                 (r1 := RB5) (r2 := RB1) (a := ad_b5 AD) (b := ad_b1 AD);
          [exact PRE10 | reflexivity | exact eq_refl | exact eq_refl | reflexivity | reflexivity]. }
      intros ms' PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW10 & -> & CP10 & (-> & RC & _ & ->)).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENV9 CP10) as (ENV10 & LS10).
      cbn [fst snd] in *. fix_ret. fold c in RC |- *. clear PRE10 CP10 STAT9.
      zstep. if_cases KC; zify_cond KC.
      - (* [comment removed for export] *)
        assert (C0 : c = 0).
        { change 18446744073709551615 with (Z.ones 64) in KC. rewrite Z.land_ones in KC by lia. change (2 ^ 64) with 18446744073709551616 in KC.
          destruct (Z.eq_dec c 0) as [E|NE]; [exact E| exfalso].
          destruct (Z.lt_ge_cases c 0); [rewrite <- (Z.mod_add c 1) in KC by lia; rewrite Z.mod_small in KC by lia; lia | rewrite Z.mod_small in KC by lia; lia]. }
        ihere. cbv beta. to_implM. rewrite C0. cbn [andb Z.eqb].
        unfold bbind, bret. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_ret.
        eapply fuzz_done; [exact ENV10 | exact LS10].
      - (* [comment removed for export] *)
        ihere. cbv beta. to_implM.
        replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; intros E; apply KC; rewrite E; reflexivity).
        cbn [andb]. unfold bbind, bunr. cbn [bind unreachable tree_ops tbind embed interp]. apply implM_interp_unr.
    Qed.
  End Env.

  (* [comment removed for export] *)
  Lemma fuzz_one_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (D : Z) (d : list Z),
    bn_pre s ls m OW LB AD EA sp lo B errv FUZZ_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    payload_ok m LB D d -> a0 = wz D -> a1 = wz (zlength d) ->
    implM usegs (interp (embed (fuzz_one (tree_ops bptr) d ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun rc _ _ a0' => rc = 0 /\ a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ_ENTRY) fc None m (seg_rom usegs)).
  Proof.
    intros until d. intros PRE -> SP16 PL -> ->.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    pose proof PL as (PLB & PLF & PLD & PLD63 & PLN & PLK).
    unfold FUZZ_STACK, LX_FUZZ_ENTRY, MallocRep.wz in *.
    pose proof GLO as GLO2. unfold GLOBALS_TOP in GLO2.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    (* [comment removed for export] *)
    assert (PLHI : d = [] \/ D + zlength d <= alloc_ceiling).
    { destruct PLK as [E|(b & Hb & Hb1 & Hb2)]; [left; exact E| right].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _). lia. }
    apply hide_intro in PLB.
    unfold implM. iprefix.
    zstep.
    carve_frame 64%nat ST. do 9 step. zstep.
    apply hide_elim in PLB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp - 64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] s ls m1 OW).
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); exact GLO|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); [exact GLO| lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (LO' : lo <= bv_unsigned sp - (64 + 32768)) by lia.
    zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      assert (E0 : d = []).
      { rewrite land_m64_small in KE by (unfold zlength in *; lia). destruct d; [reflexivity| exfalso; unfold zlength in KE; cbn [length] in KE; lia]. }
      subst d.
      do 4 zstep.
      ihere. to_implM. rewrite fuzz_one_nil.
      eapply (fuzz_main ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B CEIL GLO LO' SPB SP16 D [] [] 0 0 m1);
        [exact ENV | exact LS1 | exact PLB | | constructor | constructor | exact PLD | | | | left; reflexivity | left; reflexivity | lia | lia].
      + replace (D + zlength []) with D by (unfold zlength; cbn [length]; lia). exact PLB.
      + unfold zlength in *; cbn [length] in *; lia.
      + unfold zlength; cbn [length]; lia.
      + unfold zlength; cbn [length]; lia.
    - (* [comment removed for export] *)
      destruct d as [|b0 d']. { exfalso. apply KE. reflexivity. }
      assert (Rb0 : 0 <= b0 < 256) by (inversion PLF; assumption).
      assert (ZL : zlength (b0 :: d') = zlength d' + 1) by (unfold zlength; cbn [length]; lia).
      assert (ZL0 : 0 <= zlength d') by (unfold zlength; lia).
      zstep.
      chk ltac:(fun C => clear - C PLD63 ZL ZL0; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - PLD PLD63 ZL ZL0; lia); clear - C PLD; lia).
      do 2 zstep.
      assert (PLB1 : bytes_at usegs m1 D (to_bytes (b0 :: d'))).
      { eapply bytes_at_transport; [exact PLB | exact MU |]. cbn [disjoint_from]. rewrite zlength_to_bytes. split; [left; destruct PLHI as [E|H]; [discriminate E| lia]| exact I]. }
      assert (RD : ov_read_bytes usegs m1 (Z_to_bv 64 D) 1 = Some [Z_to_bv 8 b0]).
      { eapply (Drv_kit.bytes_at_read1 m1 D (to_bytes (b0 :: d')) 0); [exact PLB1 | lia | reflexivity | unfold wa; f_equal; lia]. }
      eassert (CJ : _); [ |
        zstep; if_cases KC; zify_cond KC;
        [ zstep; setreg 11%Z (Z_to_bv 64 (Z.min (zlength (b0 :: d')) 256000)) ltac:(f_equal; rewrite ?unsigned_lit in KC by lia; lia); exact CJ
        | zstep; zstep; setreg 11%Z (Z_to_bv 64 (Z.min (zlength (b0 :: d')) 256000)) ltac:(f_equal; rewrite ?unsigned_lit in KC by lia; lia); exact CJ ] ].
      clear RD.
      replace (bv_unsigned (Z_to_bv 8 b0)) with b0 by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_small; lia).
      set (len' := Z.min (zlength (b0 :: d')) 256000 - 1).
      zstep. replace (Z.min (zlength (b0 :: d')) 256000 + -1) with len' by (unfold len'; lia).
      assert (RL : 0 <= len' <= 255999) by (unfold len'; lia).
      set (x := Z.land b0 63 * len').
      assert (RB63 : 0 <= Z.land b0 63 <= 63) by (apply land63_range; lia).
      assert (RX : 0 <= x <= 16127937) by (unfold x; nia).
      do 7 zstep.
      replace (Z.land (Z.land b0 63 * len') 18446744073709551615) with x by (fold x; symmetry; apply land_m64_small; lia).
      do 2 zstep. rewrite (magic63_hi x RX).
      zstep.
      rewrite (magic63_q x RX).
      pose proof (div63_le (Z.land b0 63) len' RB63 ltac:(lia)) as RQ. fold x in RQ.
      set (l1 := x / 63) in *.
      zstep. fold x. rewrite (bk_swrap32_small (x - l1)) by lia.
      zstep.
      replace (bv_wrap 32 (x - l1)) with (x - l1) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small; [reflexivity | lia]).
      rewrite (bk_swrap32_small ((x - l1) ≫ 1))
        by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; split; [apply (Z.le_trans _ 0); [lia| apply Z.div_pos; lia] | apply Z.div_lt_upper_bound; lia]).
      do 2 zstep.
      assert (RT : 0 <= (x - l1) ≫ 1 + l1 < 18446744073709551616)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; pose proof (Z.div_pos (x - l1) 2 ltac:(lia) ltac:(lia));
            pose proof (Z.div_lt_upper_bound (x - l1) 2 16127938 ltac:(lia) ltac:(lia)); lia).
      rewrite (land_m64_small _ RT). change l1 with (x / 63). rewrite (magic63_t x RX). fold l1.
      do 2 zstep. rewrite (bk_swrap32_small (len' - l1)) by lia.
      zstep.
      (* [comment removed for export] *)
      set (rest := firstn (MAX_LEN - 1) d').
      assert (Lrest : Z.of_nat (length rest) = len') by (unfold rest, len'; rewrite firstn_MAX1_len, ZL; reflexivity).
      set (l1n := Z.to_nat ((Z.land b0 63 * Z.of_nat (length rest)) / 63)).
      assert (El1 : Z.of_nat l1n = l1) by (unfold l1n; rewrite Lrest; fold x; fold l1; lia).
      assert (Hl1n : (l1n <= length rest)%nat) by lia.
      set (n1 := firstn l1n rest). set (n2 := skipn l1n rest).
      assert (ZN1 : zlength n1 = l1) by (unfold zlength, n1; rewrite firstn_length_le by exact Hl1n; exact El1).
      assert (ZN2 : zlength n2 = len' - l1) by (unfold zlength, n2; rewrite length_skipn; lia).
      pose proof (payload_split d' l1n Hl1n) as SPLIT. cbv zeta in SPLIT. fold rest in SPLIT. fold n1 n2 in SPLIT.
      assert (PLBs : bytes_at usegs m (D + 1) (to_bytes n1) /\ bytes_at usegs m (D + 1 + zlength n1) (to_bytes n2)).
      { change (b0 :: d') with ([b0] ++ d') in PLB. rewrite SPLIT in PLB. unfold to_bytes in PLB. rewrite !map_app in PLB.
        apply bytes_at_app in PLB. destruct PLB as [_ PLB]. cbn [length map] in PLB.
        apply bytes_at_app in PLB. destruct PLB as [P1 PLB]. apply bytes_at_app in PLB. destruct PLB as [P2 _].
        rewrite length_map in P2. split; [exact P1| exact P2]. }
      destruct PLBs as [P1 P2].
      assert (PLFs : Forall (fun c => 0 <= c < 256) n1 /\ Forall (fun c => 0 <= c < 256) n2).
      { inversion PLF as [|? ? _ PLF']. subst. rewrite SPLIT in PLF'. apply Forall_app in PLF'. destruct PLF' as [F1 PLF'].
        apply Forall_app in PLF'. destruct PLF' as [F2 _]. split; assumption. }
      destruct PLFs as [F1 F2].
      assert (ZD : len' <= zlength d') by (unfold len'; lia).
      assert (PLKs : exists b, In b LB /\ blk_addr b <= D /\ D + zlength (b0 :: d') <= blk_addr b + blk_size b)
        by (destruct PLK as [E|H]; [discriminate E| exact H]).
      destruct PLKs as (bb & Hbb & Hbb1 & Hbb2).
      assert (RV1 : 0 <= Z.land b0 64 < 2 ^ 64) by (pose proof (land_byte_range b0 64 Rb0 ltac:(lia)); lia).
      assert (RV2 : 0 <= Z.land b0 128 < 2 ^ 64) by (pose proof (land_byte_range b0 128 Rb0 ltac:(lia)); lia).
      ihere. to_implM. rewrite fuzz_one_cons. cbv zeta. fold rest. fold l1n. fold n1 n2.
      rewrite <- ZN2, <- ZN1.
      eapply (fuzz_main ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B CEIL GLO LO' SPB SP16 (D + 1) n1 n2 (Z.land b0 64) (Z.land b0 128) m1);
        [exact ENV | exact LS1 | exact P1 | exact P2 | exact F1 | exact F2 | lia | lia | lia | lia | | | exact RV1 | exact RV2].
      + right. exists bb. split; [exact Hbb|]. lia.
      + right. exists bb. split; [exact Hbb|]. lia.
  Qed.
End Proofs.
End WithCeiling0.
