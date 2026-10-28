(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWords BgArith BgMont BgExp BgTree.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require HxuCall.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves BnCall W_calls W_cmp W_bin2bn FuzzKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_new W_free W_ctx_free.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_mod_exp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Definition fuzz_suffix (p1 p2 p3 p4 p5 pc : bptr) : BM (M := btree bptr) Z :=
  bbind ops (BN_free ops RB1 (Some p1)) (fun _ =>
  bbind ops (BN_free ops RB2 (Some p2)) (fun _ =>
  bbind ops (BN_free ops RB3 (Some p3)) (fun _ =>
  bbind ops (BN_free ops RB4 (Some p4)) (fun _ =>
  bbind ops (BN_free ops RB5 (Some p5)) (fun _ =>
  bbind ops (BN_CTX_free_g ops pc) (fun _ =>
  bret ops 0)))))).

Definition fuzz_body (p1 p2 p3 p4 p5 pc : bptr) (n1 n2 n3 : list Z) (s1 s3 : bool) : BM (M := btree bptr) Z :=
  bbind ops (BN_bin2bn ops n1 RB1) (fun _ =>
  bbind ops (BN_set_negative ops RB1 s1) (fun _ =>
  bbind ops (BN_bin2bn ops n2 RB2) (fun _ =>
  bbind ops (BN_bin2bn ops n3 RB3) (fun _ =>
  bbind ops (BN_set_negative ops RB3 s3) (fun _ =>
  bbind ops (bget ops RB3) (fun b3 =>
  bbind ops (if is_zero_pure b3 then bret ops tt
             else bbind ops (BN_mod_exp ops RB4 RB1 RB2 RB3) (fun _ =>
                  bbind ops (BN_mod_exp_simple ops RB5 RB1 RB2 RB3) (fun _ =>
                  bbind ops (bget ops RB4) (fun b4 =>
                  bbind ops (bget ops RB5) (fun b5 =>
                  if cmp_pure b4 b5 =? 0 then bret ops tt else bunr ops)))))
        (fun _ => fuzz_suffix p1 p2 p3 p4 p5 pc))))))).

Definition fuzz_rest (p1 p2 p3 p4 p5 pc : bptr) (data : list Z) : BM (M := btree bptr) Z :=
  let '(n1, n2, n3, s1, s3) := bg_split data in fuzz_body p1 p2 p3 p4 p5 pc n1 n2 n3 s1 s3.

Lemma fuzz_one_g_eq : forall (d : list Z),
  fuzz_one_g ops d =
  bbind ops (BN_new ops RB1) (fun p1 => bbind ops (BN_new ops RB2) (fun p2 => bbind ops (BN_new ops RB3) (fun p3 =>
  bbind ops (BN_new ops RB4) (fun p4 => bbind ops (BN_new ops RB5) (fun p5 => bbind ops (BN_CTX_new ops) (fun pc =>
  fuzz_rest p1 p2 p3 p4 p5 pc d)))))).
Proof. intros d. unfold fuzz_one_g, fuzz_rest, fuzz_body, fuzz_suffix. destruct (bg_split d) as [[[[n1 n2] n3] s1] s3]. reflexivity. Qed.

Lemma bg_split_cons3 : forall k0 k1 k2 (buf : list Z), 0 <= k0 < 256 -> 0 <= k1 < 256 -> 0 <= k2 < 256 ->
  let len := zlength buf in
  let l1 := ((len * k0) / 255) mod 512 in
  let q2 := ((len - l1) * k1) / 255 in
  let l2 := q2 mod 512 in
  let l3 := (len - l1 - q2) mod 512 in
  bg_split (k0 :: k1 :: k2 :: buf)
  = (firstn (Z.to_nat l1) buf, firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf), firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf),
     Z.testbit k2 0, Z.testbit k2 2).
Proof.
  intros k0 k1 k2 buf R0 R1 R2. cbv zeta. unfold bg_split. cbn [length nth skipn Nat.ltb Nat.leb].
  rewrite (Z.mod_small k0 256 R0), (Z.mod_small k1 256 R1), (Z.mod_small k2 256 R2).
  replace (Z.of_nat (S (S (S (length buf)))) - 3) with (zlength buf) by (unfold zlength; lia).
  rewrite (Z.mul_comm k0 (zlength buf)).
  set (l1 := (zlength buf * k0 / 255) mod 512). rewrite (Z.mul_comm k1 (zlength buf - l1)).
  set (q2 := (zlength buf - l1) * k1 / 255).
  replace ((zlength buf - l1 - q2 mod 512) mod 512) with ((zlength buf - l1 - q2) mod 512) by (rewrite Zminus_mod_idemp_r; reflexivity).
  reflexivity.
Qed.

Lemma split_parts : forall (buf : list Z) l1 l2 l3, 0 <= l1 -> 0 <= l2 -> 0 <= l3 -> l1 + l2 + l3 <= zlength buf ->
  let n1 := firstn (Z.to_nat l1) buf in
  let n2 := firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf) in
  let n3 := firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf) in
  zlength n1 = l1 /\ zlength n2 = l2 /\ zlength n3 = l3 /\ exists rest, buf = n1 ++ n2 ++ n3 ++ rest.
Proof.
  intros buf l1 l2 l3 H1 H2 H3 HL. cbv zeta. unfold zlength in *.
  split; [rewrite firstn_length_le by lia; lia|].
  split; [rewrite firstn_length_le by (rewrite length_skipn; lia); lia|].
  split; [rewrite firstn_length_le by (rewrite length_skipn; lia); lia|].
  exists (skipn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf)).
  rewrite (firstn_skipn (Z.to_nat l3)).
  replace (skipn (Z.to_nat (l1 + l2)) buf) with (skipn (Z.to_nat l2) (skipn (Z.to_nat l1) buf)) by (rewrite skipn_skipn; f_equal; lia).
  rewrite (firstn_skipn (Z.to_nat l2)). rewrite (firstn_skipn (Z.to_nat l1)). reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition LX_FUZZ_ENTRY : Z := 0xe1ab4.
Definition FUZZ_ONE : Z := 0xe1ae0.
Definition FUZZ_STACK : Z := 65536.
Definition FUZZ_CALLEE_MAX : Z := 65536 - 112.
Definition ERR_CLEAR_ERROR : Z := 0xe80ac.
Definition BN_MOD_EXP : Z := 0x14fae0.
Definition BN_MOD_EXP_SIMPLE : Z := 0x151770.

Definition fuzz_frame (jb : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition MAGIC255_BYTES : list byte := Eval vm_compute in (cells_bytes [C8 (Z_to_bv 64 9259542123273814145)]).
Lemma magic255_cells : forall m, mem_inv bgusegs m -> ro_cells bgusegs m 0x3a588 [C8 (wz 9259542123273814145)].
Proof.
  intros m MI. pose proof (ro_cells_image bgusegs m 0x3a588 MAGIC255_BYTES MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.
  eapply ro_cells_recast; [exact H| cbn; tauto| vm_compute; reflexivity].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Variables (MEXP_STACK MEXPS_STACK : Z).
  Hypothesis STK_MEXP : MEXP_STACK <= FUZZ_CALLEE_MAX.
  Hypothesis STK_MEXPS : MEXPS_STACK <= FUZZ_CALLEE_MAX.
  Hypothesis BN_mod_exp_walk : W_mod_exp.exp_stmt_f BN_MOD_EXP MEXP_STACK (BN_mod_exp ops) None.
  Hypothesis BN_mod_exp_simple_walk : W_mod_exp.exp_stmt BN_MOD_EXP_SIMPLE MEXPS_STACK (BN_mod_exp_simple ops) None.

  Section Env.

    Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (m : mem) (s : PState) (OW LB : list block) (EA : BnRep.err_addrs) (lo B : Z) (jb : list byte).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO : GLOBALS_TOP <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - FUZZ_STACK.
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.

    Notation SPv := (bv_unsigned sp).
    Notation FB := (bv_unsigned sp + -112).
    Notation FRM := (fuzz_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
    Notation CENV PL st' bs' m' OW' := (cenv LB PL lo B (bv_unsigned sp) FB s st_init OW m FRM st' bs' m' OW').
    Notation QPOST := (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s st_init OW LB lo B m pl_empty EA
                               (fun (rc : Z) (_ : ST) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0)).

    Lemma SPRf : bv_unsigned sp < 2 ^ 64.
    Proof. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. lia. Qed.
    Lemma FBlo : lo <= FB. Proof using LO. unfold FUZZ_STACK in LO. lia. Qed.
    Lemma FBsp : FB <= bv_unsigned sp. Proof. lia. Qed.
    Lemma ESPf : bv_unsigned (Z_to_bv 64 FB) = FB.
    Proof using CEIL LO. pose proof SPRf. unfold FUZZ_STACK in LO. apply unsigned_lit. lia. Qed.
    Lemma FROKh : forall PL, hpl_only PL -> frames_ok PL (bv_unsigned sp) B.
    Proof using CEIL LO B63. intros PL H. unfold FUZZ_STACK in LO. split; [|lia]. intros iv Hiv. unfold hpl_only in H. rewrite H in Hiv. destruct Hiv. Qed.

    Lemma free_call : forall (Q : Z * ST -> PState -> machine_state -> Prop) (K : BM (M := btree bptr) Z)
        (PL : placement) (st : PState) (bs : ST) (mx : mem) (OWx : list block) (r : bnref) (a : Z) (q : bptr)
        (rax t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      hpl_only PL -> CENV PL st bs mx OWx -> lib_state bs mx OWx PL EA -> pl_bn PL r = Some (PHeap a q 0) ->
      (forall st' m' OW' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
          CENV (pl_set PL r None) st' (setbn r (bn_nil 0) bs) m' OW' -> lib_state (setbn r (bn_nil 0) bs) m' OW' (pl_set PL r None) EA ->
          implM bgusegs (interp (embed (K (setbn r (bn_nil 0) bs)))) st' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F (ret_pc rax) fc None m' (seg_rom bgusegs))) ->
      implM bgusegs (interp (embed (bbind ops (BN_free ops r (Some q)) (fun _ => K) bs))) st Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 (wz a) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz W_free.BN_FREE) fc None mx (seg_rom bgusegs)).
    Proof using HF CEIL GLO LO SPB B63.
      intros until t6. intros HPL ENV LS E K1.
      pose proof SPRf as SPR2. pose proof FBlo as FBL. pose proof FBsp as FBS. pose proof (FROKh PL HPL) as FROK.
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ W_free.BN_FREE_STACK ENV LS) as (errv1 & PRE1).
      { unfold W_free.BN_FREE_STACK, W_alloc3.BN_FREE_STACK, W_alloc3.BN_FREE_D_STACK, W_crypto.CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, FUZZ_STACK in *. lia. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (W_free.BN_free_walk HF) with (r := r) (a := a) (q := q); [exact PRE1 | reflexivity | exact E | reflexivity]. }
      cbv beta. intros [u bs'] st' ms' PO. unfold bn_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & OW' & PL' & errv'
                      & -> & HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS' & (-> & EBS)).
      cbn [fst snd] in *. subst bs'. rewrite ESPf in *.
      eapply K1; [|exact LS'].
      eapply (cenv_call_raw LB PL (pl_set PL r None)); [exact CEIL| exact GLO| exact FBL| exact FBS| exact FROK
        | apply xw_hpl_only; [exact HPL| apply hpl_only_set_none; exact HPL] | exact ENV | exact HEAP' | exact AUX' | exact ST' | exact ERR' | exact MI' | exact LXP' | exact FA' | exact SO'|].
      apply refs_stable_noitems. reflexivity.
    Qed.

    Lemma fuzz_done : forall (stE : PState) (bsE : ST) (mE : mem) (OWE : list block) (PL : placement)
        (p1 p2 p3 p4 p5 pc : bptr) (a1 a2 a3 a4 a5 ac : Z)
        (x1 t0 t1 t2 a0 b1 b2 b3 b4 b5 b6 b7 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      hpl_only PL ->
      pl_bn PL RB1 = Some (PHeap a1 p1 0) -> pl_bn PL RB2 = Some (PHeap a2 p2 0) -> pl_bn PL RB3 = Some (PHeap a3 p3 0) ->
      pl_bn PL RB4 = Some (PHeap a4 p4 0) -> pl_bn PL RB5 = Some (PHeap a5 p5 0) -> pl_ctx PL = Some (ac, pc) ->
      CENV PL stE bsE mE OWE -> lib_state bsE mE OWE PL EA ->
      implM bgusegs (interp (embed (fuzz_suffix p1 p2 p3 p4 p5 pc bsE))) stE QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (wz a1) (wz a2) a0 b1 b2 b3 b4 b5 b6 b7
                 (wz a3) (wz a4) (wz a5) (wz ac) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe1c80) fc None mE (seg_rom bgusegs)).
    Proof using HF CEIL GLO LO SPB B63 SP16.
      intros until t6. intros HPL E1 E2 E3 E4 E5 EC ENV LS.
      pose proof SPRf as SPR2. pose proof FBlo as FBL. pose proof FBsp as FBS. pose proof ESPf as ESP.
      pose proof LO as LO'. unfold FUZZ_STACK in LO'. pose proof GLO as GLO2. unfold GLOBALS_TOP in GLO2.
      unfold fuzz_suffix, MallocRep.wz.

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (free_call QPOST _ PL stE bsE mE OWE RB1 a1 p1); [exact HPL | exact ENV | exact LS | exact E1 |].
      intros st1 m1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENV LS.
      set (PL1 := pl_set PL RB1 None) in *. set (bs1 := setbn RB1 (bn_nil 0) bsE) in *.
      pose proof (hpl_only_set_none PL RB1 HPL) as HPL1. fold PL1 in HPL1.
      replace (ret_pc (Z_to_bv 64 924808)) with (Z_to_bv 64 924808) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (free_call QPOST _ PL1 st1 bs1 m1 OW1 RB2 a2 p2); [exact HPL1 | exact ENV1 | exact LS1 | exact E2 |].
      intros st2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
      set (PL2 := pl_set PL1 RB2 None) in *. set (bs2 := setbn RB2 (bn_nil 0) bs1) in *.
      pose proof (hpl_only_set_none PL1 RB2 HPL1) as HPL2. fold PL2 in HPL2.
      replace (ret_pc (Z_to_bv 64 924816)) with (Z_to_bv 64 924816) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (free_call QPOST _ PL2 st2 bs2 m2 OW2 RB3 a3 p3); [exact HPL2 | exact ENV2 | exact LS2 | exact E3 |].
      intros st3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3. clear ENV2 LS2.
      set (PL3 := pl_set PL2 RB3 None) in *. set (bs3 := setbn RB3 (bn_nil 0) bs2) in *.
      pose proof (hpl_only_set_none PL2 RB3 HPL2) as HPL3. fold PL3 in HPL3.
      replace (ret_pc (Z_to_bv 64 924824)) with (Z_to_bv 64 924824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (free_call QPOST _ PL3 st3 bs3 m3 OW3 RB4 a4 p4); [exact HPL3 | exact ENV3 | exact LS3 | exact E4 |].
      intros st4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4. clear ENV3 LS3.
      set (PL4 := pl_set PL3 RB4 None) in *. set (bs4 := setbn RB4 (bn_nil 0) bs3) in *.
      pose proof (hpl_only_set_none PL3 RB4 HPL3) as HPL4. fold PL4 in HPL4.
      replace (ret_pc (Z_to_bv 64 924832)) with (Z_to_bv 64 924832) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (free_call QPOST _ PL4 st4 bs4 m4 OW4 RB5 a5 p5); [exact HPL4 | exact ENV4 | exact LS4 | exact E5 |].
      intros st5 m5 OW5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV5 LS5. clear ENV4 LS4.
      set (PL5 := pl_set PL4 RB5 None) in *. set (bs5 := setbn RB5 (bn_nil 0) bs4) in *.
      pose proof (hpl_only_set_none PL4 RB5 HPL4) as HPL5. fold PL5 in HPL5.
      replace (ret_pc (Z_to_bv 64 924840)) with (Z_to_bv 64 924840) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      pose proof (FROKh PL5 HPL5) as FROK5.
      unfold implM. iprefix. zstep.
      destruct (cenv_pre LB PL5 EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK5 _ _ _ _ _ W_ctx_free.BN_CTX_FREE_STACK ENV5 LS5) as (errv5 & PRE5).
      { unfold W_ctx_free.BN_CTX_FREE_STACK, W_ctxfree3.BN_CTX_FREE_STACK, W_alloc3.BN_CLEAR_FREE_STACK, W_alloc3.BN_FREE_D_STACK, W_crypto.CRYPTO_CLEAR_FREE_STACK, RFREE_STACK. clear - LO'. lia. }
      zstep. ihere. to_implM.
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (W_ctx_free.BN_CTX_free_walk HF) with (ac := ac) (qc := pc); [exact PRE5 | reflexivity | exact EC | reflexivity]. }
      cbv beta. intros [u bs6] st6 ms6 PO. unfold W_ctx_free.ctxf_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & errv6
                      & -> & HEAP6 & LS6 & AUX6 & ST6 & ERR6 & MI6 & LXP6 & FA6 & SO6 & EBS6).
      cbn [fst snd] in *. rewrite ESP in *.
      set (PL6 := pl_set_ctx PL5 None) in *.
      assert (HPL6 : hpl_only PL6) by exact HPL5.
      assert (ENV6 : CENV PL6 st6 bs6 m6 OW6).
      { eapply (cenv_call_raw LB PL5 PL6); [exact CEIL| exact GLO| exact FBL| exact FBS| exact FROK5
          | apply xw_hpl_only; [exact HPL5| exact HPL6] | exact ENV5 | exact HEAP6 | exact AUX6 | exact ST6 | exact ERR6 | exact MI6 | exact LXP6 | exact FA6 | exact SO6|].
        apply refs_stable_noitems. reflexivity. }
      clear ENV5 LS5 PRE5 HEAP6 AUX6 ST6 ERR6 MI6 LXP6 FA6 SO6.
      replace (ret_pc (Z_to_bv 64 924848)) with (Z_to_bv 64 924848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold bret. cbn [ret tree_ops embed interp]. apply implM_ret.
      pose proof (FROKh PL6 HPL6) as FROK6.
      pose proof ENV6 as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
      pose proof LS6 as (CS & EI & _).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS6) as PARTS6. pose proof PARTS6 as (_ & _ & _ & _ & (_ & _ & _ & EB4)).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP EB4) as (E0 & _ & _ & ECc & EI').
      unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
      zstep.
      eapply evt_cut.
      { eapply HxuCall.ERR_clear_error_spec with (lo := lo) (s := st6) (L := OW6 ++ LB) (OW := OW6) (EA := EA);
          [rewrite ESP; exact ST | exact CEIL | exact GLO | rewrite ESP; unfold HxuCall.ECE_STACK; clear - LO'; lia
          | rewrite ESP; replace (bv_unsigned sp + -112) with (bv_unsigned sp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SP16 | exact MI | reflexivity
          | exact HEAP | intros b Hb; apply in_or_app; left; exact Hb | exact CS | exact EI]. }
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m7 & -> & MUc & WMc & MIc & STc & ESc).
      rewrite ESP in *. unfold HxuCall.ECE_STACK in *.
      replace (ret_pc (Z_to_bv 64 924852)) with (Z_to_bv 64 924852) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold fuzz_frame in FR.
      eapply (rw_cells_transport bgusegs _ m6 m7) in FR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [right; clear - ECc CEIL LO'; lia|]; split; [right; clear; lia| exact I]].
      eapply (rw_cells_transport bgusegs _ m6 m7) in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - EI' E0; lia|]; split; [left; clear - GLO2 LO'; lia| exact I]].
      assert (WOK : Forall (w_okc OW6 LB bs6 PL6 EA (bv_unsigned sp) false []) [(FB - 16384, FB)]) by (constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LO'; lia| constructor]).
      assert (HWL : Forall (w_lib bs6 OW6 PL6 lo (bv_unsigned sp)) [(BnRep.ea_ES EA, BnRep.ea_ES EA + 904); (FB - 16384, FB)]).
      { constructor; [right; left; exists (BnRep.ea_pe EA, BnRep.ea_ES EA, 904); cbn; split; [exact EB4| clear; lia]|]. constructor; [left; cbn [fst snd]; clear - LO'; lia| constructor]. }
      pose proof (lib_state_err_cleared st6 LB (bv_unsigned sp) B bs6 m6 m7 OW6 PL6 EA _ HEAP LS6 FROK6 MUc WMc WOK ESc) as LS7.
      assert (ENV7 : CENV PL6 st6 bs6 m7 OW6).
      { eapply (cenv_silent LB PL6 EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB FROK6) with (errv' := errv);
          [exact ENV6 | exact LS6 | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | unfold fuzz_frame; exact FR | exact FSZ]. }
      pose proof (cenv_final LB PL6 EA lo B (bv_unsigned sp) FB s st_init OW m _ _ _ _ _ ENV7 LS7)
        as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
      clear ERR.
      zstep. do 13 zstep.
      release_frame FR STc (bv_unsigned sp). zstep. zstep.
      apply evt_done. unfold bn_post. do 15 eexists. exists m7, OW6, PL6, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STc|]. split; [exact F4|]. split; [exact F5|].
      split; [rewrite <- (xw_hpl_only pl_empty PL6 hpl_only_empty HPL6); exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
    Qed.

    Lemma bytes_client : forall PL st' bs' mx OW' A bs,
      hpl_only PL -> CENV PL st' bs' mx OW' -> bytes_at bgusegs m A bs ->
      (bs = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length bs) <= blk_addr b + blk_size b) ->
      bytes_at bgusegs mx A bs.
    Proof using GLO.
      intros PL st' bs' mx OW' A bs HPL (HEAP & _ & _ & _ & _ & LXP & _) BY [->|(b & Hb & Hb1 & Hb2)].
      - destruct BY as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - eapply bytes_at_agree; [apply agree_of_lx_pres; exact LXP | exact BY |].
        intros a Ha.
        pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & BI).
        split; [| right; left; exists b; split; [exact Hb| lia]].
        unfold XW. unfold hpl_only in HPL. rewrite HPL, app_nil_r.
        unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in GLO. lia.
    Qed.

    Lemma b2b_call : forall (Q : Z * ST -> PState -> machine_state -> Prop) (K : BM (M := btree bptr) Z)
        (PL : placement) (st : PState) (bs : ST) (mx : mem) (OWx : list block) (r : bnref) (a : Z) (q : bptr) (P : Z) (n : list Z)
        (rax t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      hpl_only PL -> CENV PL st bs mx OWx -> lib_state bs mx OWx PL EA -> pl_bn PL r = Some (PHeap a q 0) ->
      bytes_at bgusegs m P (to_bytes n) -> Forall (fun c => 0 <= c < 256) n -> 0 < P -> P + zlength n < 2^63 -> zlength n < 2^31 ->
      (n = [] \/ exists b, In b LB /\ blk_addr b <= P /\ P + zlength n <= blk_addr b + blk_size b) ->
      (forall st' bs' m' OW' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
          CENV PL st' bs' m' OW' -> lib_state bs' m' OW' PL EA ->
          implM bgusegs (interp (embed (K bs'))) st' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) y0 y1 y2 x8 x9 (wz a) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F (ret_pc rax) fc None m' (seg_rom bgusegs))) ->
      implM bgusegs (interp (embed (bbind ops (BN_bin2bn ops n r) (fun _ => K) bs))) st Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 (wz P) (wz (zlength n)) (wz a) a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz 0xfe568) fc None mx (seg_rom bgusegs)).
    Proof using HM HF CEIL GLO LO SPB B63.
      intros until t6. intros HPL ENV LS E BY FR D0 DH LEN HBK K1.
      pose proof SPRf as SPR2. pose proof FBlo as FBL. pose proof FBsp as FBS. pose proof (FROKh PL HPL) as FROK.
      pose proof (pl_wf_stored PL r _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS))) E) as SR.
      assert (EO : pl_of PL r = Some (PHeap a q 0)) by (rewrite pl_of_stored by exact SR; exact E).
      assert (HA : ref_at bs OWx PL r a) by (apply ref_at_fixed; [exact (proj1 SR)|]; exists (PHeap a q 0); split; [exact EO| reflexivity]).
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ BN_BIN2BN_STACK ENV LS) as (errv1 & PRE1).
      { unfold BN_BIN2BN_STACK, W_expand.BN_EXPAND2_STACK, FUZZ_STACK in *. lia. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (BN_bin2bn_walk_h HM HF) with (r := r) (a := a) (D := P) (n := n);
          [exact PRE1 | reflexivity | exact HA | exact (wref_heap PL r a q 0 EO)
          | eapply (bytes_client PL); [exact HPL | exact ENV | exact BY | unfold zlength in HBK; unfold to_bytes; rewrite length_map; destruct HBK as [->|HBK]; [left; reflexivity| right; exact HBK]]
          | exact FR | exact D0 | exact DH | exact LEN | exact HBK | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros [u bs'] st' ms' PO.
      apply (bn_post_cpost LB PL EA lo B (bv_unsigned sp) FB CEIL FBL FBS SPR2) in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & OW' & PL' & -> & CP & (-> & ->)).
      specialize (CP eq_refl).
      destruct (cenv_post LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS FROK _ _ _ _ _ _ _ _ _ ENV CP) as (ENV' & LS').
      cbn [fst snd] in *. eapply K1; [exact ENV'| exact LS'].
    Qed.

    Lemma fuzz_main : forall (st6 : PState) (bs6 : ST) (m6 : mem) (OW6 : list block) (PL : placement)
        (p1 p2 p3 p4 p5 pc : bptr) (a1 a2 a3 a4 a5 ac : Z) (P : Z) (n1 n2 n3 : list Z) (s1v s3v : Z)
        (x1 t0 t1 t2 a0 b1 b2 b3 b4 b5 b6 b7 t3 t4 t5 t6 : word),
      hpl_only PL ->
      pl_bn PL RB1 = Some (PHeap a1 p1 0) -> pl_bn PL RB2 = Some (PHeap a2 p2 0) -> pl_bn PL RB3 = Some (PHeap a3 p3 0) ->
      pl_bn PL RB4 = Some (PHeap a4 p4 0) -> pl_bn PL RB5 = Some (PHeap a5 p5 0) -> pl_ctx PL = Some (ac, pc) -> W_mod_exp.pl_fresh PL ->
      CENV PL st6 bs6 m6 OW6 -> lib_state bs6 m6 OW6 PL EA ->
      bytes_at bgusegs m P (to_bytes n1) -> bytes_at bgusegs m (P + zlength n1) (to_bytes n2) -> bytes_at bgusegs m (P + zlength n1 + zlength n2) (to_bytes n3) ->
      Forall (fun c => 0 <= c < 256) n1 -> Forall (fun c => 0 <= c < 256) n2 -> Forall (fun c => 0 <= c < 256) n3 ->
      0 < P -> P + zlength n1 + zlength n2 + zlength n3 < 2^63 -> zlength n1 < 2^31 -> zlength n2 < 2^31 -> zlength n3 < 2^31 ->
      (n1 = [] \/ exists b, In b LB /\ blk_addr b <= P /\ P + zlength n1 <= blk_addr b + blk_size b) ->
      (n2 = [] \/ exists b, In b LB /\ blk_addr b <= P + zlength n1 /\ P + zlength n1 + zlength n2 <= blk_addr b + blk_size b) ->
      (n3 = [] \/ exists b, In b LB /\ blk_addr b <= P + zlength n1 + zlength n2 /\ P + zlength n1 + zlength n2 + zlength n3 <= blk_addr b + blk_size b) ->
      0 <= s1v < 2^64 -> 0 <= s3v < 2^64 ->
      implM bgusegs (interp (embed (fuzz_body p1 p2 p3 p4 p5 pc n1 n2 n3 (negb (s1v =? 0)) (negb (s3v =? 0)) bs6))) st6 QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (wz a1) (wz a2) a0 b1 b2 b3 b4 b5 b6 b7
                 (wz a3) (wz a4) (wz a5) (wz ac) (wz P) (wz s3v) (wz (zlength n3)) (wz (zlength n2)) (wz (zlength n1)) (wz s1v) t3 t4 t5 t6)
            F (Z_to_bv 64 0xe1bf8) fc None m6 (seg_rom bgusegs)).
    Proof using HM HF CEIL GLO LO SPB B63 SP16 STK_MEXP STK_MEXPS BN_mod_exp_walk BN_mod_exp_simple_walk.
      intros until t6. intros HPL E1 E2 E3 E4 E5 EC FRESH ENV LS BY1 BY2 BY3 FR1 FR2 FR3 P0 PH L1 L2 L3 K1 K2 K3 S1R S3R.
      pose proof SPRf as SPR2. pose proof FBlo as FBL. pose proof FBsp as FBS. pose proof ESPf as ESP. pose proof (FROKh PL HPL) as FROK.
      pose proof LO as LO'. unfold FUZZ_STACK in LO'. pose proof GLO as GLO2. unfold GLOBALS_TOP in GLO2.
      assert (LOFB16 : lo <= FB - 16) by (clear - LO'; lia).
      assert (ZL1 : 0 <= zlength n1) by (unfold zlength; lia). assert (ZL2 : 0 <= zlength n2) by (unfold zlength; lia). assert (ZL3 : 0 <= zlength n3) by (unfold zlength; lia).
      unfold fuzz_body, MallocRep.wz.

      unfold implM. iprefix. do 3 zstep. zstep. ihere. to_implM.
      eapply (b2b_call QPOST _ PL st6 bs6 m6 OW6 RB1 a1 p1 P n1); [exact HPL | exact ENV | exact LS | exact E1 | exact BY1 | exact FR1 | exact P0 | clear - PH ZL2 ZL3; lia | exact L1 | exact K1 |].
      intros st7 bs7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7. clear ENV LS.
      replace (ret_pc (Z_to_bv 64 924680)) with (Z_to_bv 64 924680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      pose proof (lib_state_h_parts _ _ _ _ _ _ LS7) as PARTS7. pose proof PARTS7 as (_ & PWF & _).
      pose proof (pl_wf_stored PL RB1 _ PWF E1) as SR1. pose proof (pl_wf_stored PL RB2 _ PWF E2) as SR2. pose proof (pl_wf_stored PL RB3 _ PWF E3) as SR3.
      pose proof (pl_wf_stored PL RB4 _ PWF E4) as SR4. pose proof (pl_wf_stored PL RB5 _ PWF E5) as SR5.
      assert (EO1 : pl_of PL RB1 = Some (PHeap a1 p1 0)) by (rewrite pl_of_stored by exact SR1; exact E1).
      assert (EO2 : pl_of PL RB2 = Some (PHeap a2 p2 0)) by (rewrite pl_of_stored by exact SR2; exact E2).
      assert (EO3 : pl_of PL RB3 = Some (PHeap a3 p3 0)) by (rewrite pl_of_stored by exact SR3; exact E3).
      assert (EO4 : pl_of PL RB4 = Some (PHeap a4 p4 0)) by (rewrite pl_of_stored by exact SR4; exact E4).
      assert (EO5 : pl_of PL RB5 = Some (PHeap a5 p5 0)) by (rewrite pl_of_stored by exact SR5; exact E5).
      assert (HA1 : forall bs OWx, ref_at bs OWx PL RB1 a1) by (intros; apply ref_at_fixed; [exact (proj1 SR1)|]; exists (PHeap a1 p1 0); split; [exact EO1| reflexivity]).
      assert (HA2 : forall bs OWx, ref_at bs OWx PL RB2 a2) by (intros; apply ref_at_fixed; [exact (proj1 SR2)|]; exists (PHeap a2 p2 0); split; [exact EO2| reflexivity]).
      assert (HA3 : forall bs OWx, ref_at bs OWx PL RB3 a3) by (intros; apply ref_at_fixed; [exact (proj1 SR3)|]; exists (PHeap a3 p3 0); split; [exact EO3| reflexivity]).
      assert (HA4 : forall bs OWx, ref_at bs OWx PL RB4 a4) by (intros; apply ref_at_fixed; [exact (proj1 SR4)|]; exists (PHeap a4 p4 0); split; [exact EO4| reflexivity]).
      assert (HA5 : forall bs OWx, ref_at bs OWx PL RB5 a5) by (intros; apply ref_at_fixed; [exact (proj1 SR5)|]; exists (PHeap a5 p5 0); split; [exact EO5| reflexivity]).
      pose proof ENV7 as (HEAP7 & _).
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP7 PARTS7 (HA1 bs7 OW7) (hpl_heap PL RB1 a1 p1 0 EO1)) as (A10 & A1C & _).
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP7 PARTS7 (HA2 bs7 OW7) (hpl_heap PL RB2 a2 p2 0 EO2)) as (A20 & A2C & _).
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP7 PARTS7 (HA3 bs7 OW7) (hpl_heap PL RB3 a3 p3 0 EO3)) as (A30 & A3C & _).
      clear HEAP7 PARTS7 PWF.
      pose proof (set_neg_call LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO LOFB16 FBS SPB SPR2 FROK) as SNC.
      pose proof (is_zero_call LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO LOFB16 FBS SPB SPR2 FROK) as IZC.
      unfold BN_IS_ZERO in IZC.

      unfold BN_set_negative at 1. unfold bbind at 1 2. unfold bget at 1. unfold bset at 1. cbn [bind ret tree_ops tbind fst snd].
      unfold implM. iprefix.
      zstep. if_cases KE; zify_cond KE; [exfalso; apply KE; reflexivity|]. clear KE.
      do 3 zstep.
      eapply SNC; [exact ENV7 | exact LS7 | exact (HA1 bs7 OW7) | exact (wref_heap PL RB1 a1 p1 0 EO1) |].
      rewrite (unsigned_lit s1v) by (clear - S1R; lia).
      intros m8 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? bs8 ENV8 LS8. clear ENV7 LS7.
      replace (ret_pc (Z_to_bv 64 924696)) with (Z_to_bv 64 924696) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      zstep.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - P0 PH ZL1 ZL2 ZL3; lia); clear - C P0 ZL1; lia).
      do 3 zstep.
      replace (0 <? P) with true by (symmetry; apply Z.ltb_lt; exact P0).
      replace (P + zlength n1 <? 1) with false by (symmetry; apply Z.ltb_ge; clear - P0 ZL1; lia).
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      chk_lit.
      do 3 zstep. zstep. ihere. to_implM.
      eapply (b2b_call QPOST _ PL st7 bs8 m8 OW7 RB2 a2 p2 (P + zlength n1) n2); [exact HPL | exact ENV8 | exact LS8 | exact E2 | exact BY2 | exact FR2 | clear - P0 ZL1; lia | clear - PH ZL3; lia | exact L2 | exact K2 |].
      intros st9 bs9 m9 OW9 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV9 LS9. clear ENV8 LS8.
      replace (ret_pc (Z_to_bv 64 924736)) with (Z_to_bv 64 924736) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix.
      zstep. if_cases KE; zify_cond KE; [exfalso; apply KE; reflexivity|]. clear KE.
      zstep.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - P0 PH ZL1 ZL2 ZL3; lia); clear - C P0 ZL1 ZL2; lia).
      do 2 zstep.
      replace (zlength n2 + (P + zlength n1)) with (P + zlength n1 + zlength n2) by (clear; lia).
      replace (P + zlength n1 + zlength n2 <? 1) with false by (symmetry; apply Z.ltb_ge; clear - P0 ZL1 ZL2; lia).
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      chk_lit.
      do 2 zstep. zstep. ihere. to_implM.
      eapply (b2b_call QPOST _ PL st9 bs9 m9 OW9 RB3 a3 p3 (P + zlength n1 + zlength n2) n3); [exact HPL | exact ENV9 | exact LS9 | exact E3 | exact BY3 | exact FR3 | clear - P0 ZL1 ZL2; lia | exact PH | exact L3 | exact K3 |].
      intros st10 bs10 m10 OW10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV10 LS10. clear ENV9 LS9.
      replace (ret_pc (Z_to_bv 64 924772)) with (Z_to_bv 64 924772) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold BN_set_negative at 1. unfold bbind at 1 2. unfold bget at 1. unfold bset at 1. cbn [bind ret tree_ops tbind fst snd].
      unfold implM. iprefix.
      zstep. if_cases KE; zify_cond KE; [exfalso; apply KE; reflexivity|]. clear KE.
      do 3 zstep.
      eapply SNC; [exact ENV10 | exact LS10 | exact (HA3 bs10 OW10) | exact (wref_heap PL RB3 a3 p3 0 EO3) |].
      rewrite (unsigned_lit s3v) by (clear - S3R; lia).
      intros m11 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? bs11 ENV11 LS11. clear ENV10 LS10.
      replace (ret_pc (Z_to_bv 64 924788)) with (Z_to_bv 64 924788) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      do 2 zstep.
      eapply IZC; [exact ENV11 | exact LS11 | exact (HA3 bs11 OW10) | exact (proj1 (proj2 SR3)) |].
      intros m12 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV12 LS12. clear ENV11 LS11.
      replace (ret_pc (Z_to_bv 64 924796)) with (Z_to_bv 64 924796) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      ihere. to_implM.
      unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd]. fold bs11. unfold is_zero_pure.
      destruct (bn_top (getbn RB3 bs11) =? 0)%nat eqn:EZ; cbn [Z.b2z].
      {
        unfold bbind at 1. unfold bret at 1. cbn [bind ret tree_ops tbind fst snd].
        unfold implM. iprefix.
        zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ; discriminate KZ|]. clear KZ.
        ihere. to_implM.
        eapply (fuzz_done st10 bs11 m12 OW10 PL p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac); [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact ENV12 | exact LS12]. }

      unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ; [|exfalso; apply KZ; reflexivity]. clear KZ.
      do 5 zstep.
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ MEXP_STACK ENV12 LS12) as (errv12 & PRE12).
      { unfold FUZZ_CALLEE_MAX in STK_MEXP. clear - STK_MEXP LO'. lia. }
      zstep. ihere. to_implM.
      unfold bbind at 1 2. cbn [bind tree_ops]. apply BnAssoc.implM_embed_assoc.
      eapply implM_embed_bind.
      { eapply (BN_mod_exp_walk) with (rr := RB4) (ra_ := RB1) (rp := RB2) (rm := RB3) (arr := a4) (ara := a1) (arp := a2) (arm := a3) (ac := ac) (qc := pc);
          [exact PRE12 | reflexivity | rewrite ESP; replace (bv_unsigned sp + -112) with (bv_unsigned sp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SP16
          | exact (HA4 _ _) | exact (HA1 _ _) | exact (HA2 _ _) | exact (HA3 _ _) | exact (hpl_heap PL RB4 a4 p4 0 EO4)
          | exact (proj1 (proj2 SR1)) | exact (proj1 (proj2 SR2)) | exact (proj1 (proj2 SR3)) | exact EC | exact FRESH
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; discriminate Hw]. }
      cbv beta. intros [u13 bs13] st13 ms13 PO.
      apply (bn_post_cpost LB PL EA lo B (bv_unsigned sp) FB CEIL FBL FBS SPR2) in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m13 & OW13 & PL13 & -> & CP13 & (-> & ->)).
      specialize (CP13 eq_refl).
      destruct (cenv_post LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS FROK _ _ _ _ _ _ _ _ _ ENV12 CP13) as (ENV13 & LS13).
      cbn [fst snd] in *. clear ENV12 LS12 PRE12 CP13.
      replace (ret_pc (Z_to_bv 64 924940)) with (Z_to_bv 64 924940) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold MallocRep.wz. unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ; discriminate KZ|]. clear KZ.
      do 5 zstep.
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ MEXPS_STACK ENV13 LS13) as (errv13 & PRE13).
      { unfold FUZZ_CALLEE_MAX in STK_MEXPS. clear - STK_MEXPS LO'. lia. }
      zstep. ihere. to_implM.
      unfold bbind at 1. cbn [bind tree_ops]. apply BnAssoc.implM_embed_assoc.
      eapply implM_embed_bind.
      { eapply (BN_mod_exp_simple_walk) with (rr := RB5) (ra_ := RB1) (rp := RB2) (rm := RB3) (arr := a5) (ara := a1) (arp := a2) (arm := a3) (ac := ac) (qc := pc);
          [exact PRE13 | reflexivity | rewrite ESP; replace (bv_unsigned sp + -112) with (bv_unsigned sp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SP16
          | exact (HA5 _ _) | exact (HA1 _ _) | exact (HA2 _ _) | exact (HA3 _ _) | exact (hpl_heap PL RB5 a5 p5 0 EO5)
          | exact (proj1 (proj2 SR1)) | exact (proj1 (proj2 SR2)) | exact (proj1 (proj2 SR3)) | exact EC
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; discriminate Hw]. }
      cbv beta. intros [u14 bs14] st14 ms14 PO.
      apply (bn_post_cpost LB PL EA lo B (bv_unsigned sp) FB CEIL FBL FBS SPR2) in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m14 & OW14 & PL14 & -> & CP14 & (-> & ->)).
      specialize (CP14 eq_refl).
      destruct (cenv_post LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS FROK _ _ _ _ _ _ _ _ _ ENV13 CP14) as (ENV14 & LS14).
      cbn [fst snd] in *. clear ENV13 LS13 PRE13 CP14.
      replace (ret_pc (Z_to_bv 64 924968)) with (Z_to_bv 64 924968) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold bbind at 1 2. unfold bget at 1 2. cbn [bind ret tree_ops tbind fst snd].
      unfold MallocRep.wz. unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ; discriminate KZ|]. clear KZ.
      do 2 zstep.
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ BN_CMP_STACK ENV14 LS14) as (errv14 & PRE14).
      { unfold BN_CMP_STACK. clear - LO'. lia. }
      zstep.
      eapply evt_cut.
      { eapply BN_cmp_evt with (r1 := RB4) (r2 := RB5) (a := a4) (b := a5);
          [exact PRE14 | reflexivity | exact (HA4 _ _) | exact (HA5 _ _) | exact (proj1 (proj2 SR4)) | exact (proj1 (proj2 SR5)) | reflexivity | reflexivity]. }
      intros ms15 PO.
      apply (bn_post_cpost LB PL EA lo B (bv_unsigned sp) FB CEIL FBL FBS SPR2) in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m15 & OW15 & PL15 & -> & CP15 & (-> & -> & CR & _ & ->)).
      specialize (CP15 eq_refl).
      destruct (cenv_post LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS FROK _ _ _ _ _ _ _ _ _ ENV14 CP15) as (ENV15 & LS15).
      cbn [fst snd] in *. clear ENV14 LS14 PRE14 CP15.
      replace (ret_pc (Z_to_bv 64 924984)) with (Z_to_bv 64 924984) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      ihere. to_implM.
      destruct (cmp_pure (getbn RB4 bs14) (getbn RB5 bs14) =? 0) eqn:EC0.
      2:{
        unfold bunr. cbn [unreachable tree_ops tbind embed interp]. apply implM_unr. }
      apply Z.eqb_eq in EC0. rewrite EC0. unfold bret. cbn [ret tree_ops tbind fst snd].
      unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ; [|exfalso; apply KZ; reflexivity]. clear KZ.
      ihere. to_implM.
      eapply (fuzz_done st14 bs14 m15 OW14 PL p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac); [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact ENV15 | exact LS15].
    Qed.

    Lemma fuzz_split : forall (st6 : PState) (bs6 : ST) (m6 : mem) (OW6 : list block) (PL : placement)
        (p1 p2 p3 p4 p5 pc : bptr) (a1 a2 a3 a4 a5 ac : Z) (D : Z) (d : list Z)
        (x1 t0 t1 t2 a0 b1 b2 b3 b4 b5 b6 b7 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      hpl_only PL ->
      pl_bn PL RB1 = Some (PHeap a1 p1 0) -> pl_bn PL RB2 = Some (PHeap a2 p2 0) -> pl_bn PL RB3 = Some (PHeap a3 p3 0) ->
      pl_bn PL RB4 = Some (PHeap a4 p4 0) -> pl_bn PL RB5 = Some (PHeap a5 p5 0) -> pl_ctx PL = Some (ac, pc) -> W_mod_exp.pl_fresh PL ->
      CENV PL st6 bs6 m6 OW6 -> lib_state bs6 m6 OW6 PL EA ->
      payload_ok m LB D d ->
      implM bgusegs (interp (embed (fuzz_rest p1 p2 p3 p4 p5 pc d bs6))) st6 QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (wz a1) (wz a2) a0 b1 b2 b3 b4 b5 b6 b7
                 (wz a3) (wz a4) (wz a5) (wz ac) (wz D) (wz (zlength d)) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe1b68) fc None m6 (seg_rom bgusegs)).
    Proof using HM HF CEIL GLO LO SPB B63 SP16 STK_MEXP STK_MEXPS BN_mod_exp_walk BN_mod_exp_simple_walk.
      intros until t6. intros HPL E1 E2 E3 E4 E5 EC FRESH ENV LS (PLB & PLF & PLD & PLD63 & PLN & PLK).
      pose proof SPRf as SPR2. pose proof ESPf as ESP.
      pose proof LO as LO'. unfold FUZZ_STACK in LO'. pose proof GLO as GLO2. unfold GLOBALS_TOP in GLO2.
      assert (ZL0 : 0 <= zlength d) by (unfold zlength; lia).
      pose proof ENV as (_ & _ & _ & _ & MI6 & _).
      pose proof (magic255_cells m6 MI6) as MAGIC. unfold MallocRep.wz in MAGIC.
      assert (PLB6 : bytes_at bgusegs m6 D (to_bytes d)).
      { eapply (bytes_client PL); [exact HPL | exact ENV | exact PLB |]. unfold to_bytes. rewrite length_map.
        destruct PLK as [->|PLK]; [left; reflexivity| right; unfold zlength in PLK; exact PLK]. }
      unfold MallocRep.wz.
      unfold implM. iprefix.
      zstep. zstep. if_cases K3; rewrite ?unsigned_lit in K3 by (clear - ZL0 PLN; lia); zify_cond K3.
      {
        assert (ES : bg_split d = ([], [], [], false, false)).
        { unfold bg_split. replace (2 <? length d)%nat with false by (symmetry; apply Nat.ltb_ge; unfold zlength in K3; clear - K3; lia). reflexivity. }
        do 5 zstep.
        ihere. to_implM. unfold fuzz_rest. rewrite ES.
        assert (BE : forall A, 0 <= A <= 2^64 -> bytes_at bgusegs m A (to_bytes [])).
        { intros A HA. split; [lia|]. split; [cbn [to_bytes map length]; lia|]. intros i Hi. cbn in Hi. lia. }
        eapply (fuzz_main st6 bs6 m6 OW6 PL p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac D [] [] [] 0 0);
          [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact FRESH | exact ENV | exact LS
          | apply BE; clear - PLD PLD63 ZL0; lia | apply BE; unfold zlength; cbn [length]; clear - PLD PLD63 ZL0; lia | apply BE; unfold zlength; cbn [length]; clear - PLD PLD63 ZL0; lia
          | constructor | constructor | constructor | exact PLD
          | unfold zlength; cbn [length]; clear - PLD63 ZL0; lia | reflexivity | reflexivity | reflexivity
          | left; reflexivity | left; reflexivity | left; reflexivity | clear; lia | clear; lia]. }

      destruct d as [|k0 [|k1 [|k2 buf]]]; try (exfalso; unfold zlength in K3; cbn [length] in K3; clear - K3; lia).
      assert (R0 : 0 <= k0 < 256) by (inversion PLF; assumption).
      assert (R1 : 0 <= k1 < 256) by (inversion PLF as [|? ? _ H]; inversion H; assumption).
      assert (R2 : 0 <= k2 < 256) by (inversion PLF as [|? ? _ H]; inversion H as [|? ? _ H']; inversion H'; assumption).
      assert (ZLB : zlength (k0 :: k1 :: k2 :: buf) = zlength buf + 3) by (unfold zlength; cbn [length]; lia).
      assert (ZB0 : 0 <= zlength buf) by (unfold zlength; lia).
      assert (HDR : ro_cells bgusegs m6 D [C1 (Z_to_bv 8 k0); C1 (Z_to_bv 8 k1); C1 (Z_to_bv 8 k2)]).
      { change (to_bytes (k0 :: k1 :: k2 :: buf)) with ([Z_to_bv 8 k0; Z_to_bv 8 k1; Z_to_bv 8 k2] ++ to_bytes buf) in PLB6.
        apply bytes_at_app in PLB6. destruct PLB6 as [H3 _]. split; [cbn; auto| exact H3]. }
      assert (EB : forall k, 0 <= k < 256 -> bv_unsigned (Z_to_bv 8 k) = k) by (intros k Hk; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_small; lia).
      rewrite ZLB in PLN, PLD63.
      set (len := zlength buf) in *.
      set (l1 := ((len * k0) / 255) mod 512). set (q2 := ((len - l1) * k1) / 255). set (l2 := q2 mod 512). set (l3 := (len - l1 - q2) mod 512).
      assert (LEN30 : 0 <= len < 2^30) by (clear - ZB0 PLN; lia).
      assert (X40 : 0 <= len * k0 < 2^40) by (clear - LEN30 R0; change (2^40) with 1099511627776; change (2^30) with 1073741824 in LEN30; nia).
      pose proof (div255_le len k0 ZB0 R0) as Q1R.
      assert (L1R : 0 <= l1 <= len) by (unfold l1; pose proof (Z.mod_pos_bound (len * k0 / 255) 512 ltac:(lia)); pose proof (Z.mod_le (len * k0 / 255) 512 ltac:(lia) ltac:(lia)); clear - H H0 Q1R; lia).
      assert (Y30 : 0 <= len - l1 < 2^30) by (clear - L1R LEN30; lia).
      pose proof (div255_le (len - l1) k1 ltac:(clear - L1R; lia) R1) as Q2R. fold q2 in Q2R.
      assert (L2R : 0 <= l2 <= q2) by (unfold l2; pose proof (Z.mod_pos_bound q2 512 ltac:(lia)); pose proof (Z.mod_le q2 512 ltac:(clear - Q2R; lia) ltac:(lia)); clear - H H0; lia).
      assert (L3R : 0 <= l3 <= len - l1 - q2) by (unfold l3; pose proof (Z.mod_pos_bound (len - l1 - q2) 512 ltac:(lia)); pose proof (Z.mod_le (len - l1 - q2) 512 ltac:(clear - Q2R; lia) ltac:(lia)); clear - H H0; lia).
      destruct (byte_bits k2 R2) as [TB0 TB2]. destruct (byte_masks k2 R2) as [MK1 MK4].
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - PLD PLD63 ZB0; lia); clear - C PLD; lia).
      zstep.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - PLD PLD63 ZB0; lia); clear - C PLD PLD63 ZB0; lia).
      zstep.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - PLD PLD63 ZB0; lia); clear - C PLD PLD63 ZB0; lia).
      do 2 zstep.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - PLD PLD63 ZB0; lia); clear - C PLD PLD63 ZB0; lia).
      do 4 zstep. rewrite ZLB. replace (len + 3 + -3) with len by (clear; lia). rewrite (EB k0 R0).
      do 2 zstep. rewrite (EB k1 R1), (EB k2 R2).
      do 5 zstep.
      setreg 26%Z (Z_to_bv 64 l1) ltac:(f_equal; symmetry; first [apply (split_l1_m (len * k0) X40) | apply (split_l1_m' (len * k0) X40)]).
      do 10 zstep.
      replace (len + - l1) with (len - l1) by (clear; lia).
      rewrite (split_q2_m' (len - l1) k1 Y30 R1). fold q2.
      rewrite (split_l3_m (len - l1 - q2)) by (clear - L3R Y30 Q2R; change (2^31) with 2147483648; change (2^30) with 1073741824 in Y30; lia). fold l3.
      rewrite (land511_mod q2) by (clear - Q2R; lia). fold l2.

      pose proof (bg_split_cons3 k0 k1 k2 buf R0 R1 R2) as ES. cbv zeta in ES. fold len l1 q2 l2 l3 in ES.
      destruct (split_parts buf l1 l2 l3 ltac:(clear - L1R; lia) ltac:(clear - L2R; lia) ltac:(clear - L3R; lia) ltac:(fold len; clear - L1R L2R L3R; lia))
        as (ZN1 & ZN2 & ZN3 & rest & EBUF).
      set (n1 := firstn (Z.to_nat l1) buf) in *. set (n2 := firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf)) in *.
      set (n3 := firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf)) in *.
      assert (PLBs : bytes_at bgusegs m (D + 3) (to_bytes n1) /\ bytes_at bgusegs m (D + 3 + zlength n1) (to_bytes n2)
                     /\ bytes_at bgusegs m (D + 3 + zlength n1 + zlength n2) (to_bytes n3)).
      { change (to_bytes (k0 :: k1 :: k2 :: buf)) with ([Z_to_bv 8 k0; Z_to_bv 8 k1; Z_to_bv 8 k2] ++ to_bytes buf) in PLB.
        apply bytes_at_app in PLB. destruct PLB as [_ PLB]. cbn [length] in PLB. change (Z.of_nat 3) with 3 in PLB.
        rewrite EBUF in PLB. unfold to_bytes in PLB. rewrite !map_app in PLB.
        apply bytes_at_app in PLB. destruct PLB as [P1 PLB]. apply bytes_at_app in PLB. destruct PLB as [P2 PLB].
        apply bytes_at_app in PLB. destruct PLB as [P3 _]. rewrite !length_map in *. unfold zlength.
        split; [exact P1|]. split; [exact P2| exact P3]. }
      destruct PLBs as (P1 & P2 & P3).
      assert (PLFs : Forall (fun c => 0 <= c < 256) n1 /\ Forall (fun c => 0 <= c < 256) n2 /\ Forall (fun c => 0 <= c < 256) n3).
      { assert (FB0 : Forall (fun c => 0 <= c < 256) buf) by (inversion PLF as [|? ? _ H]; inversion H as [|? ? _ H']; inversion H'; assumption).
        rewrite EBUF in FB0. apply Forall_app in FB0. destruct FB0 as [F1 FB0]. apply Forall_app in FB0. destruct FB0 as [F2 FB0].
        apply Forall_app in FB0. destruct FB0 as [F3 _]. auto. }
      destruct PLFs as (F1 & F2 & F3).
      assert (PLKs : exists b, In b LB /\ blk_addr b <= D /\ D + (len + 3) <= blk_addr b + blk_size b)
        by (destruct PLK as [E|H]; [discriminate E| rewrite ZLB in H; exact H]).
      destruct PLKs as (bb & Hbb & Hbb1 & Hbb2).
      ihere. to_implM. unfold fuzz_rest. rewrite ES. fold n1 n2 n3.
      rewrite <- TB0, <- TB2. rewrite <- ZN1, <- ZN2, <- ZN3.
      eapply (fuzz_main st6 bs6 m6 OW6 PL p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac (D + 3) n1 n2 n3 (Z.land k2 1) (Z.land k2 4));
        [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact FRESH | exact ENV | exact LS
        | exact P1 | exact P2 | exact P3 | exact F1 | exact F2 | exact F3 | clear - PLD; lia
        | rewrite ZN1, ZN2, ZN3; clear - PLD63 L1R L2R L3R; lia | rewrite ZN1; clear - L1R LEN30; change (2^31) with 2147483648; change (2^30) with 1073741824 in LEN30; lia
        | rewrite ZN2; clear - L2R Q2R L1R LEN30; change (2^31) with 2147483648; change (2^30) with 1073741824 in LEN30; lia
        | rewrite ZN3; clear - L3R Q2R L1R LEN30; change (2^31) with 2147483648; change (2^30) with 1073741824 in LEN30; lia
        | right; exists bb; split; [exact Hbb|]; rewrite ZN1; clear - Hbb1 Hbb2 L1R L2R L3R; lia
        | right; exists bb; split; [exact Hbb|]; rewrite ZN1, ZN2; clear - Hbb1 Hbb2 L1R L2R L3R; lia
        | right; exists bb; split; [exact Hbb|]; rewrite ZN1, ZN2, ZN3; clear - Hbb1 Hbb2 L1R L2R L3R; lia
        | clear - MK1; change (2^64) with 18446744073709551616; lia | clear - MK4; change (2^64) with 18446744073709551616; lia].
    Qed.

    Lemma new_call : forall (Q : Z * ST -> PState -> machine_state -> Prop) (K : bptr -> BM (M := btree bptr) Z)
        (PL : placement) (st : PState) (bs : ST) (mx : mem) (OWx : list block) (r : bnref)
        (rax t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      hpl_only PL -> CENV PL st bs mx OWx -> lib_state bs mx OWx PL EA -> stored_ref r -> pl_bn PL r = None ->
      (forall (p : bptr) (a : Z) st' m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
          0 < a < 2^63 ->
          CENV (pl_set PL r (Some (PHeap a p 0))) st' (setbn r (bn_nil BN_FLG_MALLOCED) bs) m' ((p, a, 24) :: OWx) ->
          lib_state (setbn r (bn_nil BN_FLG_MALLOCED) bs) m' ((p, a, 24) :: OWx) (pl_set PL r (Some (PHeap a p 0))) EA ->
          implM bgusegs (interp (embed (K p (setbn r (bn_nil BN_FLG_MALLOCED) bs)))) st' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) y0 y1 y2 x8 x9 (wz a) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F (ret_pc rax) fc None m' (seg_rom bgusegs))) ->
      implM bgusegs (interp (embed (bbind ops (BN_new ops r) K bs))) st Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz W_new.BN_NEW) fc None mx (seg_rom bgusegs)).
    Proof using HM CEIL GLO LO SPB B63.
      intros until t6. intros HPL ENV LS SR E K1.
      pose proof SPRf as SPR2. pose proof FBlo as FBL. pose proof FBsp as FBS. pose proof (FROKh PL HPL) as FROK.
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ W_new.BN_NEW_STACK ENV LS) as (errv1 & PRE1).
      { unfold W_new.BN_NEW_STACK, W_alloc3.BN_NEW_STACK, W_crypto.CRYPTO_ZALLOC_STACK, W_crypto.CRYPTO_MALLOC_STACK, RMALLOC_STACK, FUZZ_STACK in *. lia. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (W_new.BN_new_walk HM) with (r := r); [exact PRE1 | reflexivity | exact SR | exact E]. }
      cbv beta. intros [p bs'] st' ms' PO. unfold bn_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & OW' & PL' & errv'
                      & -> & HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS' & (a & -> & -> & RA & -> & EBS)).
      cbn [fst snd] in *. subst bs'. rewrite ESPf in *.
      eapply K1; [exact RA | | exact LS'].
      eapply (cenv_call_raw LB PL (pl_set PL r (Some (PHeap a p 0)))); [exact CEIL| exact GLO| exact FBL| exact FBS| exact FROK
        | apply xw_hpl_only; [exact HPL| apply hpl_only_set_heap; exact HPL] | exact ENV | exact HEAP' | exact AUX' | exact ST' | exact ERR' | exact MI' | exact LXP' | exact FA' | exact SO'|].
      apply refs_stable_noitems. reflexivity.
    Qed.

    Lemma ctx_new_call : forall (Q : Z * ST -> PState -> machine_state -> Prop) (K : bptr -> BM (M := btree bptr) Z)
        (PL : placement) (st : PState) (bs : ST) (mx : mem) (OWx : list block)
        (rax t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      hpl_only PL -> CENV PL st bs mx OWx -> lib_state bs mx OWx PL EA -> pl_ctx PL = None ->
      (forall (p : bptr) (a : Z) st' m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
          0 < a < 2^63 ->
          CENV (pl_set_ctx PL (Some (a, p))) st' (set_ctx gx_nil bs) m' ((p, a, 72) :: OWx) ->
          lib_state (set_ctx gx_nil bs) m' ((p, a, 72) :: OWx) (pl_set_ctx PL (Some (a, p))) EA ->
          implM bgusegs (interp (embed (K p (set_ctx gx_nil bs)))) st' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) y0 y1 y2 x8 x9 (wz a) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F (ret_pc rax) fc None m' (seg_rom bgusegs))) ->
      implM bgusegs (interp (embed (bbind ops (BN_CTX_new ops) K bs))) st Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz W_new.BN_CTX_NEW) fc None mx (seg_rom bgusegs)).
    Proof using HM CEIL GLO LO SPB B63.
      intros until t6. intros HPL ENV LS E K1.
      pose proof SPRf as SPR2. pose proof FBlo as FBL. pose proof FBsp as FBS. pose proof (FROKh PL HPL) as FROK.
      destruct (cenv_pre LB PL EA lo B (bv_unsigned sp) FB s st_init OW m CEIL GLO FBL FBS SPB SPR2 FROK _ _ _ _ _ W_new.BN_CTX_NEW_STACK ENV LS) as (errv1 & PRE1).
      { unfold W_new.BN_CTX_NEW_STACK, W_ctx3.BN_CTX_NEW_STACK, W_crypto.CRYPTO_ZALLOC_STACK, W_crypto.CRYPTO_MALLOC_STACK, RMALLOC_STACK, FUZZ_STACK in *. lia. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (W_new.BN_CTX_new_walk HM); [exact PRE1 | reflexivity | exact E]. }
      cbv beta. intros [p bs'] st' ms' PO. unfold bn_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & OW' & PL' & errv'
                      & -> & HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS' & (a & -> & -> & RA & -> & EBS)).
      cbn [fst snd] in *. subst bs'. rewrite ESPf in *.
      eapply K1; [exact RA | | exact LS'].
      eapply (cenv_call_raw LB PL (pl_set_ctx PL (Some (a, p)))); [exact CEIL| exact GLO| exact FBL| exact FBS| exact FROK
        | apply xw_hpl_only; [exact HPL| apply hpl_only_set_ctx; exact HPL] | exact ENV | exact HEAP' | exact AUX' | exact ST' | exact ERR' | exact MI' | exact LXP' | exact FA' | exact SO'|].
      apply refs_stable_noitems. reflexivity.
    Qed.

    Lemma fuzz_create : forall (st0 : PState) (m0 : mem) (D : Z) (d : list Z)
        (x1 t0 t1 t2 x8 x9 a0 b1 b2 b3 b4 b5 b6 b7 x18 x19 x20 x21 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      CENV pl_empty st0 st_init m0 OW -> lib_state st_init m0 OW pl_empty EA ->
      payload_ok m LB D d ->
      implM bgusegs (interp (embed (fuzz_one_g ops d st_init))) st0 QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 b1 b2 b3 b4 b5 b6 b7
                 x18 x19 x20 x21 (wz D) (wz (zlength d)) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe1b20) fc None m0 (seg_rom bgusegs)).
    Proof using HM HF CEIL GLO LO SPB B63 SP16 STK_MEXP STK_MEXPS BN_mod_exp_walk BN_mod_exp_simple_walk.
      intros until t6. intros ENV0 LS0 PLD.
      pose proof SPRf as SPR2. pose proof ESPf as ESP.
      pose proof LO as LO'. unfold FUZZ_STACK in LO'. pose proof GLO as GLO2. unfold GLOBALS_TOP in GLO2.
      pose proof hpl_only_empty as HPL0.
      assert (SR1 : stored_ref RB1) by (unfold stored_ref; split; [unfold RB1, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR2 : stored_ref RB2) by (unfold stored_ref; split; [unfold RB2, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR3 : stored_ref RB3) by (unfold stored_ref; split; [unfold RB3, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR4 : stored_ref RB4) by (unfold stored_ref; split; [unfold RB4, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR5 : stored_ref RB5) by (unfold stored_ref; split; [unfold RB5, NFIX; lia| split; [discriminate| reflexivity]]).
      rewrite fuzz_one_g_eq. unfold MallocRep.wz.

      unfold implM. iprefix. zstep. ihere. to_implM.
      eapply (new_call QPOST _ pl_empty st0 st_init m0 OW RB1); [exact HPL0 | exact ENV0 | exact LS0 | exact SR1 | reflexivity |].
      intros p1 a1 st1 m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? RA1 ENV1 LS1. clear ENV0 LS0.
      set (PL1 := pl_set pl_empty RB1 (Some (PHeap a1 p1 0))) in *. set (bs1 := setbn RB1 (bn_nil BN_FLG_MALLOCED) st_init) in *.
      pose proof (hpl_only_set_heap pl_empty RB1 a1 p1 0 HPL0) as HPL1. fold PL1 in HPL1.
      replace (ret_pc (Z_to_bv 64 924452)) with (Z_to_bv 64 924452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (new_call QPOST _ PL1 st1 bs1 m1 _ RB2); [exact HPL1 | exact ENV1 | exact LS1 | exact SR2 | reflexivity |].
      intros p2 a2 st2 m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? RA2 ENV2 LS2. clear ENV1 LS1.
      set (PL2 := pl_set PL1 RB2 (Some (PHeap a2 p2 0))) in *. set (bs2 := setbn RB2 (bn_nil BN_FLG_MALLOCED) bs1) in *.
      pose proof (hpl_only_set_heap PL1 RB2 a2 p2 0 HPL1) as HPL2. fold PL2 in HPL2.
      replace (ret_pc (Z_to_bv 64 924460)) with (Z_to_bv 64 924460) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (new_call QPOST _ PL2 st2 bs2 m2 _ RB3); [exact HPL2 | exact ENV2 | exact LS2 | exact SR3 | reflexivity |].
      intros p3 a3 st3 m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? RA3 ENV3 LS3. clear ENV2 LS2.
      set (PL3 := pl_set PL2 RB3 (Some (PHeap a3 p3 0))) in *. set (bs3 := setbn RB3 (bn_nil BN_FLG_MALLOCED) bs2) in *.
      pose proof (hpl_only_set_heap PL2 RB3 a3 p3 0 HPL2) as HPL3. fold PL3 in HPL3.
      replace (ret_pc (Z_to_bv 64 924468)) with (Z_to_bv 64 924468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (new_call QPOST _ PL3 st3 bs3 m3 _ RB4); [exact HPL3 | exact ENV3 | exact LS3 | exact SR4 | reflexivity |].
      intros p4 a4 st4 m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? RA4 ENV4 LS4. clear ENV3 LS3.
      set (PL4 := pl_set PL3 RB4 (Some (PHeap a4 p4 0))) in *. set (bs4 := setbn RB4 (bn_nil BN_FLG_MALLOCED) bs3) in *.
      pose proof (hpl_only_set_heap PL3 RB4 a4 p4 0 HPL3) as HPL4. fold PL4 in HPL4.
      replace (ret_pc (Z_to_bv 64 924476)) with (Z_to_bv 64 924476) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (new_call QPOST _ PL4 st4 bs4 m4 _ RB5); [exact HPL4 | exact ENV4 | exact LS4 | exact SR5 | reflexivity |].
      intros p5 a5 st5 m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? RA5 ENV5 LS5. clear ENV4 LS4.
      set (PL5 := pl_set PL4 RB5 (Some (PHeap a5 p5 0))) in *. set (bs5 := setbn RB5 (bn_nil BN_FLG_MALLOCED) bs4) in *.
      pose proof (hpl_only_set_heap PL4 RB5 a5 p5 0 HPL4) as HPL5. fold PL5 in HPL5.
      replace (ret_pc (Z_to_bv 64 924484)) with (Z_to_bv 64 924484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (ctx_new_call QPOST _ PL5 st5 bs5 m5 _); [exact HPL5 | exact ENV5 | exact LS5 | reflexivity |].
      intros pc ac st6 m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? RAC ENV6 LS6. clear ENV5 LS5.
      set (PL6 := pl_set_ctx PL5 (Some (ac, pc))) in *. set (bs6 := set_ctx gx_nil bs5) in *.
      pose proof (hpl_only_set_ctx PL5 (Some (ac, pc)) HPL5) as HPL6. fold PL6 in HPL6.
      replace (ret_pc (Z_to_bv 64 924492)) with (Z_to_bv 64 924492) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. zstep.
      zstep. if_cases KN1; unfold MallocRep.wz in KN1; rewrite ?unsigned_lit in KN1 by (clear - RA1; lia); zify_cond KN1. { exfalso. clear - KN1 RA1. lia. }
      zstep. if_cases KN2; unfold MallocRep.wz in KN2; rewrite ?unsigned_lit in KN2 by (clear - RA2; lia); zify_cond KN2. { exfalso. clear - KN2 RA2. lia. }
      zstep. if_cases KN3; unfold MallocRep.wz in KN3; rewrite ?unsigned_lit in KN3 by (clear - RA3; lia); zify_cond KN3. { exfalso. clear - KN3 RA3. lia. }
      zstep. if_cases KN4; unfold MallocRep.wz in KN4; rewrite ?unsigned_lit in KN4 by (clear - RA4; lia); zify_cond KN4. { exfalso. clear - KN4 RA4. lia. }
      zstep. if_cases KN5; unfold MallocRep.wz in KN5; rewrite ?unsigned_lit in KN5 by (clear - RA5; lia); zify_cond KN5. { exfalso. clear - KN5 RA5. lia. }
      zstep. if_cases KN6; unfold MallocRep.wz in KN6; rewrite ?unsigned_lit in KN6 by (clear - RAC; lia); zify_cond KN6. { exfalso. clear - KN6 RAC. lia. }
      ihere. to_implM.
      eapply (fuzz_split st6 bs6 m6 _ PL6 p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac D d);
        [exact HPL6 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | unfold W_mod_exp.pl_fresh; repeat split; reflexivity | exact ENV6 | exact LS6 | exact PLD].
    Qed.

  End Env.

  Lemma fuzz_one_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (OW LB : list block) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (D : Z) (d : list Z),
    bn_pre s st_init m OW LB pl_empty EA sp lo B errv FUZZ_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    payload_ok m LB D d -> a0 = wz D -> a1 = wz (zlength d) ->
    implM bgusegs (interp (embed (fuzz_one_g ops d st_init))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s st_init OW LB lo B m pl_empty EA
               (fun (rc : Z) (_ : ST) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ_ENTRY) fc None m (seg_rom bgusegs)).
  Proof using HM HF STK_MEXP STK_MEXPS BN_mod_exp_walk BN_mod_exp_simple_walk.
    intros until d. intros PRE -> SP16 PLD -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof LO as LO'. unfold FUZZ_STACK in LO'.
    unfold LX_FUZZ_ENTRY, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold implM. iprefix.
    zstep.
    carve_frame 112%nat ST. do 16 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib st_init OW pl_empty lo (bv_unsigned sp)) [(bv_unsigned sp - 112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB st_init pl_empty EA (bv_unsigned sp) []) [(bv_unsigned sp - 112, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] st_init m m1 OW pl_empty EA _ HEAP LS MU WM FROK WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
      assert (ENV : cenv LB pl_empty lo B (bv_unsigned sp) (bv_unsigned sp + -112) s st_init OW m (fuzz_frame jbv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) s st_init m1 OW);
      [| set (jb := jbv) in * ]
    end.
    { unfold cenv, fuzz_frame. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL0 SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    ihere. to_implM.
    eapply (fuzz_create ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s OW LB EA lo B jb CEIL GLO' LO SPB B63 SP16 s m1 D d);
      [exact ENV | exact LS0 | exact PLD].
  Qed.
End Proofs.
End WithCeiling0.
