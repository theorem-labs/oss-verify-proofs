(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ValArr W_mod_exp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac the_mi := lazymatch goal with H : mem_inv bgusegs _ |- _ => exact H end.
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_DIV_RECP : Z := 0x151eac.
Definition BN_CTX_START : Z := 0x100c14.
Definition BN_CTX_GET : Z := 0x100e84.
Definition BN_CTX_END : Z := 0x100da4.
Definition BN_UCMP : Z := 0xfecac.
Definition BN_COPY : Z := 0xfe304.
Definition BN_RECIPROCAL : Z := 0x152170.
Definition BN_RSHIFT : Z := 0x10a4ec.
Definition BN_MUL : Z := 0x102690.
Definition BN_USUB : Z := 0x10aa0c.
Definition BN_ADD_WORD : Z := 0x10afb8.

Lemma nbits_range' : forall b : bignum bptr, limbs (bn_buf b) -> 0 <= num_bits_pure b <= 64 * Z.of_nat (bn_top b).
Proof.
  intros b HL. unfold num_bits_pure. destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
  pose proof (limbs_nth (bn_buf b) (bn_top b - 1) HL) as LN. unfold limb, BW in LN.
  pose proof (num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). lia.
Qed.

Lemma sx32_int : forall z, -2147483648 <= z < 2147483648 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (z mod 18446744073709551616) with (z mod 18446744073709551616 + 0) by lia. rewrite bn_swrap32_mod by lia. lia.
Qed.

Lemma zx32_int : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small z) by lia. apply Z.mod_small. lia. Qed.

Lemma eqb_int : forall x y, -9223372036854775808 <= x < 9223372036854775808 -> -9223372036854775808 <= y < 9223372036854775808 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. rewrite bv_eqb_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec x y) as [E|NE]; [subst; apply Z.eqb_refl|]. apply Z.eqb_neq. intros E. apply NE. clear NE.
  pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). pose proof (Z.mod_pos_bound y 18446744073709551616 ltac:(lia)).
  pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)). pose proof (Z.div_mod y 18446744073709551616 ltac:(lia)). lia.
Qed.

Section Proofs.
  Variable CS : Z.
  Hypothesis CS96 : 128 <= CS.
  Definition BN_DIV_RECP_STACK : Z := 96 + CS.

  Hypothesis BN_CTX_start_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_start (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' _ => PL' = PL /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_START) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_get_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_get (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun r bs' OW' PL' a0' => PL' = PL /\ (exists i, r = RPool i) /\ (exists a, ref_at bs' OW' PL r a /\ a0' = wz a) /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_GET) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_end_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' _ => PL' = PL /\ OW' = OW))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_END) fc None m (seg_rom bgusegs)).

  Hypothesis BN_ucmp_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL r1 a -> ref_at bs OW PL r2 b -> r1 <> ROne -> r2 <> ROne -> a0 = wz a -> a1 = wz b ->
    implM bgusegs (interp (embed (BN_ucmp (tree_ops bptr) r1 r2 bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun c bs' OW' PL' a0' => (PL' = PL /\ a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ bs' = bs /\ OW' = OW) /\ c = ucmp_pure (getbn r1 bs) (getbn r2 bs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UCMP) fc None m (seg_rom bgusegs)).

  Hypothesis BN_copy_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx ry : bnref) (ax ay : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> wref PL rx -> ry <> ROne -> a0 = wz ax -> a1 = wz ay ->
    implM bgusegs (interp (embed (BN_copy (tree_ops bptr) rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_COPY) fc None m (seg_rom bgusegs)).

  Hypothesis BN_reciprocal_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rm : bnref) (arr arm len ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL rm arm -> wref PL rr -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> 0 <= len < 2^31 ->
    a0 = wz arr -> a1 = wz arm -> a2 = wz len -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_reciprocal (tree_ops bptr) rr rm len bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun r _ _ PL' a0' => PL' = PL /\ r = len /\ a0' = wz len))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECIPROCAL) fc None m (seg_rom bgusegs)).

  Hypothesis BN_rshift_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (R X n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL rx X -> rx <> ROne -> a0 = wz R -> a1 = wz X -> a2 = wz n -> 0 <= n < 2^30 ->
    implM bgusegs (interp (embed (BN_rshift (tree_ops bptr) rr rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RSHIFT) fc None m (seg_rom bgusegs)).

  Hypothesis BN_mul_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_mul (tree_ops bptr) rr rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL) fc None m (seg_rom bgusegs)).

  Hypothesis BN_usub_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL x X -> x <> ROne -> ref_at bs OW PL y Y -> y <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y ->
    implM bgusegs (interp (embed (BN_usub (tree_ops bptr) rr x y bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_USUB) fc None m (seg_rom bgusegs)).

  Hypothesis BN_add_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
    implM bgusegs (interp (embed (BN_add_word (tree_ops bptr) rx w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_ADD_WORD) fc None m (seg_rom bgusegs)).

  Section Body.
    Variables (ra gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL : placement) (EA : BnRep.err_addrs).
    Variables (rr rm : bnref) (arr arm an ac : Z) (qc : bptr).
    Variables (FB SPv : Z).
    Variable j0 : list byte.
    Hypothesis ESPV : SPv = FB + 96.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO' : GLOBALS_TOP <= lo.
    Hypothesis FBlo : lo <= FB.
    Hypothesis FBsp : FB <= SPv.
    Hypothesis SPB : SPv <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis SPR2 : SPv < 2^64.
    Hypothesis FROK : frames_ok PL SPv B.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis HPC : pl_ctx PL = Some (ac, qc).
    Hypothesis HRC : recp_at PL an.
    Hypothesis HAr : ref_at bs OW PL rr arr.
    Hypothesis HAm : ref_at bs OW PL rm arm.
    Hypothesis HPr : hpl PL rr.
    Hypothesis NROm : rm <> ROne.
    Hypothesis ArR : 0 < arr < 2^64.
    Hypothesis AmR : 0 < arm < 2^64.
    Hypothesis AnR : 0 < an /\ an + 60 < 2^63.
    Hypothesis AN8 : an mod 8 = 0.
    Hypothesis ArA : arr mod 8 = 0.
    Hypothesis AmA : arm mod 8 = 0.

    Definition saved : list cell := [CB 8 j0; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Definition FINALQ : unit * bstate bptr -> PState -> machine_state -> Prop :=
      bn_post ra (Z_to_bv 64 SPv) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
              (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1).

    Local Ltac kit :=
      pose proof (kenv_pre LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE;
      pose proof (kenv_post LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST;
      pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B SPv FB CEIL FBlo FBsp SPR2 A) as BPK;
      pose proof (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KOPEN;
      pose proof (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KOPENU;
      pose proof (kenv_below LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW;
      pose proof (kenv_struct_store LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KSTORE;
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - FBlo FBsp SPR2 CEIL; lia);
      pose proof GLO' as GLO2; unfold GLOBALS_TOP in GLO2.

    Lemma div_exit : forall stK bsK mK OWK
        (rax t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m saved stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1520f4) fc None mK (seg_rom bgusegs)).
    Proof.
      intros. kit.
      unfold implM. iprefix. step. step.
      destruct (KPRE _ _ _ _ _ CS H H0 LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m14 & OW14 & -> & KP & (_ & EOW14)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ H KP) as (ENV14 & LS14). pose proof KP as RS14; apply kpost_refs in RS14.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x1520fc)) with (Z_to_bv 64 0x1520fc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B SPv FB s bs OW m _ _ _ _ _ ENV14) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      unfold saved in FRF.
      step. do 11 step. release_frame FRF STF SPv. step. step.
      apply evt_done. unfold FINALQ, bn_post. do 15 eexists. exists m14, OW14, PL, errvF.
      replace (FB + 96) with SPv by lia. rewrite (unsigned_lit SPv) by lia. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS14|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
    Qed.

    Definition fin_r (sx : bstate bptr) : bstate bptr :=
      setbn rr (bn_with_neg (getbn rr sx) (if is_zero_pure (getbn rr sx) then false else bn_neg (getbn rm sx))) sx.
    Definition fin_d (d : bnref) (sx : bstate bptr) : bstate bptr :=
      setbn d (bn_with_neg (getbn d sx) (xorb (bn_neg (getbn rm sx)) (bn_neg (getbn RRecpN sx)))) sx.

    Lemma div_final : forall stK bsK mK OWK (d : bnref) (ad : Z) (di : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m saved stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL d ad -> d = RPool di ->
      implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) (fin_d d (fin_r bsK))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 ad) (Z_to_bv 64 arr) x22 x23 x24 (Z_to_bv 64 (an + 24)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1520a8) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HAd Ed. kit.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAr) as HArK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      pose proof (proj1 HPr) as NROr.
      assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
      assert (NRON : RRecpN <> ROne) by (unfold RRecpN, ROne; lia).

      destruct (KOPEN _ _ _ _ _ rr arr ENVK LSK HArK NROr) as (Dr & BNr & _ & (OKr1 & OKr2 & OKr3 & OKr4) & _ & SEPr & _ & _).
      pose proof ENVK as (_ & _ & STK & _ & MIK & _).
      unfold implM. iprefix.
      step. step.
      eapply evt_cut.
      { eapply (BN_is_zero_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arr) (D := Dr) (b := getbn rr bsK);
          [exact BNr | exact (conj (proj1 ArR) ArA) | clear - OKr2 OKr3; unfold BG_DMAX in OKr3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS96; lia | exact MIK
          | rewrite ESP; clear - SEPr FBlo FBsp CS96 LOF; lia | reflexivity]. }
      clear STK MIK.
      intros ms2 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *.
      destruct (KBELOW _ _ _ _ m2 _ 16 ENVK LSK ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear ENVK LSK MUc WMc MIc STc BNr.
      replace (ret_pc (Z_to_bv 64 0x1520b0)) with (Z_to_bv 64 0x1520b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      assert (TAIL2 : forall st3 bs3 m3 OW3 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x22' x23' x24' t3' t4' t5' t6' : word),
            kenv LB PL lo B SPv FB s bs OW m saved st3 bs3 m3 OW3 -> lib_state bs3 m3 OW3 PL EA ->
            ref_at bs3 OW3 PL d ad -> ref_at bs3 OW3 PL rm arm -> bv_unsigned a0' = 1 ->
            implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) (fin_d d bs3)))) st3 FINALQ
              (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 ad) (Z_to_bv 64 arr) x22' x23' x24' (Z_to_bv 64 (an + 24)) s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x15214c) fc None m3 (seg_rom bgusegs))).
      { intros until t6'. intros ENV3 LS3 HAd3 HAm3 A0Z.
        destruct (KOPEN _ _ _ _ _ rm arm ENV3 LS3 HAm3 NROm) as (Dm & BNm & _ & _ & _ & _ & _ & _). unfold bn_cells in BNm.
        destruct (KOPEN _ _ _ _ _ RRecpN an ENV3 LS3 (recp_at_refN _ _ _ _ HRC) NRON) as (Dn & BNn & _ & _ & _ & _ & _ & _). unfold bn_cells in BNn.
        unfold implM. iprefix.
        chkw ltac:(fun C => clear - C AmR; lia).
        chkw ltac:(fun C => clear - C A0Z; lia).
        step. step. step. clear BNm BNn.
        destruct (KSTORE _ _ _ _ _ d ad ENV3 LS3 HAd3 NROd) as (Dd & BNd & OKd & Ad0 & SEPd & Ad63 & AId & CLOSEd).
        unfold bn_cells in BNd.
        pose proof ENV3 as (_ & _ & ST3 & _ & MI3 & _).
        pose proof (munch_refl [(ad, ad + 24)]%Z m3) as MU. pose proof (wmono_refl bgusegs m3) as WM.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        destruct (CLOSEd m4 (bn_with_neg (getbn d bs3) (xorb (bn_neg (getbn rm bs3)) (bn_neg (getbn RRecpN bs3)))) MU WM) as (ENV4 & LS4);
          [ destruct (bn_neg (getbn rm bs3)), (bn_neg (getbn RRecpN bs3)); exact BNd | reflexivity | reflexivity | exact OKd | exact ST3 | exact MI3 |].
        clear BNd MU WM ST3 MI3 CLOSEd.
        step. step.
        ihere. to_implM. fold (fin_d d bs3) in ENV4, LS4.
        eapply div_exit; [exact ENV4| exact LS4]. }
      pose proof (ref_at_stable _ _ _ _ PL _ _ (refs_stable_refl bsK OWK) HAd) as HAd2.
      destruct (KSTORE _ _ _ _ _ rr arr ENV2 LS2 HArK NROr) as (Dr2 & BNr2 & OKr & Ar0 & SEPr2 & Ar63 & AIr & CLOSEr).
      unfold bn_cells in BNr2.
      pose proof ENV2 as (_ & _ & ST2 & _ & MI2 & _).
      unfold fin_r at 1. unfold is_zero_pure.
      destruct (Nat.eqb_spec (bn_top (getbn rr bsK)) 0) as [TZ|TNZ]; cbn [Z.b2z].
      -
        step. if_false. step. step. step. step.
        pose proof (munch_refl [(arr, arr + 24)]%Z m2) as MU. pose proof (wmono_refl bgusegs m2) as WM.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        destruct (CLOSEr m3 (bn_with_neg (getbn rr bsK) false) MU WM) as (ENV3 & LS3);
          [ exact BNr2 | reflexivity | reflexivity | exact OKr | exact ST2 | exact MI2 |].
        clear BNr2 MU WM ST2 MI2 CLOSEr.
        ihere. to_implM.
        eapply TAIL2; [exact ENV3| exact LS3| apply ref_at_setbn; exact HAd| apply ref_at_setbn; exact HAmK|].
        rewrite ?(land7_wrap _ AmA), ?(land7_wz _ AmA). rewrite ?unsigned_lit by lia. reflexivity.
      -
        step. if_true.
        chkw ltac:(fun C => clear - C AmR; lia).
        step. rewrite ?(land7_wrap _ AmA), ?(land7_wz _ AmA).
        chkw ltac:(fun C => clear - C; lia).
        destruct (KOPEN _ _ _ _ _ rm arm ENV2 LS2 HAmK NROm) as (Dm & BNm & _ & _ & _ & _ & _ & _). unfold bn_cells in BNm.
        step. step. clear BNm.
        pose proof (munch_refl [(arr, arr + 24)]%Z m2) as MU. pose proof (wmono_refl bgusegs m2) as WM.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        destruct (CLOSEr m3 (bn_with_neg (getbn rr bsK) (bn_neg (getbn rm bsK))) MU WM) as (ENV3 & LS3);
          [ destruct (bn_neg (getbn rm bsK)); exact BNr2 | reflexivity | reflexivity | exact OKr | exact ST2 | exact MI2 |].
        clear BNr2 MU WM ST2 MI2 CLOSEr.
        ihere. to_implM.
        eapply TAIL2; [exact ENV3| exact LS3| apply ref_at_setbn; exact HAd| apply ref_at_setbn; exact HAmK|].
        rewrite ?unsigned_lit by lia. reflexivity.
    Qed.

    Lemma recp_fix_loop_S : forall f r d j (sx : bstate bptr),
      recp_fix_loop (tree_ops bptr) (S f) r d j sx =
      tbind (BN_ucmp (tree_ops bptr) r RRecpN sx)
            (fun p => (if fst p <? 0 then bret (tree_ops bptr) tt
                       else if 2 <? j then bunr (tree_ops bptr)
                       else fun s1 => tbind (BN_usub (tree_ops bptr) r r RRecpN s1)
                                        (fun p1 => tbind (BN_add_word (tree_ops bptr) d 1 (snd p1))
                                                     (fun p2 => recp_fix_loop (tree_ops bptr) f r d (j + 1) (snd p2)))) (snd p)).
    Proof. reflexivity. Qed.

    Definition LOOPQ (d : bnref) (ad : Z) (r : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 ad) (Z_to_bv 64 arr) x22 x23 x24 (Z_to_bv 64 (an + 24)) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1520a8) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m saved st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ ref_at (snd r) OWK' PL d ad.

    Lemma div_loop : forall fuel (j : Z) stK bsK mK OWK (d : bnref) (ad : Z) (di : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x24 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m saved stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL d ad -> d = RPool di -> 0 <= j <= 3 -> 4 - j <= Z.of_nat fuel ->
      implM bgusegs (interp (embed (recp_fix_loop (tree_ops bptr) fuel rr d j bsK))) stK (LOOPQ d ad)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 ad) (Z_to_bv 64 arr) (Z_to_bv 64 (4 - j)) x23 x24 (Z_to_bv 64 (an + 24)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15202c) fc None mK (seg_rom bgusegs)).
    Proof.
      induction fuel as [|f IH]; intros until t6; intros ENVK LSK HAd Ed J FU; [exfalso; clear - J FU; lia|]. kit.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAr) as HArK.
      pose proof (proj1 HPr) as NROr.
      assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
      assert (NRON : RRecpN <> ROne) by (unfold RRecpN, ROne; lia).
      rewrite recp_fix_loop_S.
      unfold implM. iprefix. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_ucmp_walk; [exact PRE3| reflexivity| exact HArK| exact (recp_at_refN _ _ _ _ HRC)| exact NROr| exact NRON| reflexivity| reflexivity]. }
      cbv beta. intros [c bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [[E _] _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & ((_ & -> & CR & Ebs & EOW) & Ec)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11).
      cbn [fst snd] in *. subst bs4 OW11. clear PRE3 KP Ec.
      replace (ret_pc (Z_to_bv 64 0x152038)) with (Z_to_bv 64 0x152038) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. rewrite lts_signed by (clear - CR; lia).
      destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
      {
        ihere. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
        unfold LOOPQ. exists m11, OWK. do 19 eexists. split; [reflexivity|]. cbn [snd]. split; [exact ENV11|]. split; [exact LS11| exact HAd]. }
      step. rewrite (swrap32_wrap64 (4 - j) (-1)) by (clear - J; lia).
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - J; lia); zify_cond KZ.
      {
        replace (2 <? j) with true by (symmetry; apply Z.ltb_lt; clear - KZ J; lia).
        ihere. to_implM. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
      replace (2 <? j) with false by (symmetry; apply Z.ltb_ge; clear - KZ J; lia).

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV11 LS11 LOF) as (errv5 & PRE5). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_usub_walk; [exact PRE5| reflexivity| exact HArK| exact HPr| exact HArK| exact NROr| exact (recp_at_refN _ _ _ _ HRC)| exact NRON| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m12 & OW12 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV11 KP) as (ENV12 & LS12). pose proof KP as RS12; apply kpost_refs in RS12.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x152054)) with (Z_to_bv 64 0x152054) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.

      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV12 LS12 LOF) as (errv7 & PRE7). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_add_word_walk; [exact PRE7| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS12 HAd)| rewrite Ed; apply wref_pool| reflexivity| reflexivity| clear; lia]. }
      cbv beta. intros [u8 bs8] st8 ms8 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m13 & OW13 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV12 KP) as (ENV13 & LS13). pose proof KP as RS13; apply kpost_refs in RS13.
      cbn [fst snd] in *. clear PRE7 KP.
      replace (ret_pc (Z_to_bv 64 0x152064)) with (Z_to_bv 64 0x152064) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false. step.
      replace (4 - j + -1) with (4 - (j + 1)) by (clear; lia).
      ihere. to_implM.
      eapply IH; [exact ENV13| exact LS13| exact (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS12 RS13) HAd)| exact Ed| clear - J KZ; lia| clear - FU; lia].
    Qed.

    Lemma div_body : forall m1
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m saved s bs m1 OW -> lib_state bs m1 OW PL EA ->
      implM bgusegs (interp (embed (BN_div_recp (tree_ops bptr) None (Some rr) rm bs))) s FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 ac) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 0) (Z_to_bv 64 arr) x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x151ef8) fc None m1 (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENV LS1. kit. unfold MallocRep.wz in *.
      pose proof (proj1 HPr) as NROr.
      assert (NRON : RRecpN <> ROne) by (unfold RRecpN, ROne; lia).
      assert (NRONr : RRecpNr <> ROne) by (unfold RRecpNr, ROne; lia).
      pose proof (recp_at_recp PL an HRC) as HRc.
      unfold BN_div_recp, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
      unfold implM. iprefix. step.

      destruct (KPRE _ _ _ _ _ CS ENV LS1 LOF) as (errv1 & PRE1).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_CTX_start_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & INCL2)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
      cbn [fst snd] in *. clear PRE1 KP ENV LS1.
      replace (ret_pc (Z_to_bv 64 0x151efc)) with (Z_to_bv 64 0x151efc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. if_true. step.
      step.
      destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv2 & PRE2).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [d bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & (di & Ed) & (ad & HAd & ->) & INCL3)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
      cbn [fst snd] in *. clear PRE2 KP ENV2 LS2.
      replace (ret_pc (Z_to_bv 64 0x152074)) with (Z_to_bv 64 0x152074) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step.
      step. if_cases KR; rewrite ?unsigned_lit in KR by (clear - ArR; lia); zify_cond KR; [|exfalso; clear - KR ArR; lia]. clear KR.

      step. step.
      destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_CTX_get_walk; [exact PRE3| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [a bs3] st3 ms3 PO. apply BPK in PO; [|intros v b o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & (ai & Ea) & (aa & HAa & ->) & INCL4)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
      cbn [fst snd] in *. clear PRE3 KP ENV3 LS3.
      replace (ret_pc (Z_to_bv 64 0x151f0c)) with (Z_to_bv 64 0x151f0c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv4 & PRE4).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_CTX_get_walk; [exact PRE4| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [b bs4] st4 ms4 PO. apply BPK in PO; [|intros v b' o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & (bi & Eb) & (ab & HAb & ->) & INCL5)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE4 KP ENV4 LS4.
      replace (ret_pc (Z_to_bv 64 0x151f18)) with (Z_to_bv 64 0x151f18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      pose proof (refs_stable_trans _ _ _ _ _ _ RS2 (refs_stable_trans _ _ _ _ _ _ RS3 (refs_stable_trans _ _ _ _ _ _ RS4 RS5))) as RS05.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS05 HAr) as HAr5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS05 HAm) as HAm5.
      pose proof (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS4 RS5) HAd) as HAd5.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAa) as HAa5.
      pose proof ENV5 as (HEAP5 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS5) as PARTS5.
      assert (FROK5 : frames_ok PL FB B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
      assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
      assert (NROa : a <> ROne) by (rewrite Ea; unfold RPool, ROne, NFIX; lia).
      assert (NROb : b <> ROne) by (rewrite Eb; unfold RPool, ROne, NFIX; lia).
      assert (AbR : 0 < ab < 2^64).
      { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP5 PARTS5 FROK5 HAb NROb) as (X & Y & _). clear - X Y SPR2 SPB B63 ESPV. lia. }
      assert (AdR : 0 < ad < 2^64).
      { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP5 PARTS5 FROK5 HAd5 NROd) as (X & Y & _). clear - X Y SPR2 SPB B63 ESPV. lia. }
      pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP5 PARTS5 HAd5 NROd) as (_ & AD8).
      clear HEAP5 PARTS5.
      unfold implM. iprefix.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AbR; lia); zify_cond KZ; [exfalso; clear - KZ AbR; lia| clear KZ].

      chkw ltac:(fun C => clear - C AnR; lia).
      step. step. rewrite ?(land7_wrap _ AN8), ?(land7_wz _ AN8).
      chkw ltac:(fun C => clear - C; lia).
      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_ucmp_walk; [exact PRE6| reflexivity| exact HAm5| exact (recp_at_refN _ _ _ _ HRC)| exact NROm| exact NRON| reflexivity| reflexivity]. }
      cbv beta. intros [c bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b' o p a' [[E _] _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & ((_ & -> & CR & Ebs & EOW) & Ec)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6).
      cbn [fst snd] in *. subst bs6 OW6. clear PRE6 KP Ec ENV5 LS5.
      replace (ret_pc (Z_to_bv 64 0x151f38)) with (Z_to_bv 64 0x151f38) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. rewrite lts_signed by (clear - CR; lia).
      destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
      {
        unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
        step. step.
        eapply (zero_call LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) with (r := d) (ar := ad);
          [clear - LOF CS96; lia | reflexivity | exact ENV6 | exact LS6 | exact HAd5 | rewrite Ed; apply wref_pool |].
        intros m7 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV7 LS7.
        replace (ret_pc (Z_to_bv 64 0x152094)) with (Z_to_bv 64 0x152094) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV7 LS7 LOF) as (errv8 & PRE8). ihere. to_implM.
        eapply implM_embed_bind.
        { eapply BN_copy_walk; [exact PRE8| reflexivity| apply ref_at_setbn; exact HAr5| apply ref_at_setbn; exact HAm5| exact (hpl_wref _ _ HPr)| exact NROm| reflexivity| reflexivity]. }
        cbv beta. intros [u9 bs9] st9 ms9 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW9 & -> & KP & (_ & -> & _)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV7 KP) as (ENV9 & LS9).
        cbn [fst snd] in *. clear PRE8 KP.
        replace (ret_pc (Z_to_bv 64 0x1520a0)) with (Z_to_bv 64 0x1520a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix. step. step.
        assert (ESL : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 arr) = Z_to_bv 64 1).
        { rewrite v_sltu_b2z. rewrite (unsigned_lit arr) by (clear - ArR; lia). rewrite (unsigned_lit 0) by (clear; lia).
          replace (0 <? arr) with true by (symmetry; apply Z.ltb_lt; clear - ArR; lia). reflexivity. }
        rewrite ESL. clear ESL.
        ihere. to_implM. eapply div_exit; [exact ENV9| exact LS9]. }

      unfold BN_num_bits, bgetst, bget, bset, bsetrecp, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
      destruct (KOPENU _ _ _ _ _ rm arm ENV6 LS6 HAm5 NROm) as (Dm & BNm & Um & (OKm1 & OKm2 & OKm3 & OKm4) & _ & SEPm & SEPDm & _ & ALm & UPm).
      set (bm := getbn rm bs4) in *.
      assert (FLm : 0 <= bn_flags bm <= 1) by (destruct OKm4 as [E|E]; rewrite E; lia).
      assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
      pose proof ENV6 as (_ & _ & ST6 & _ & MI6 & _). unfold BG_DMAX in OKm3.
      step. step.
      eapply evt_cut.
      { eapply (BN_num_bits_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arm) (D := Dm) (b := bm);
          [exact BNm | exact ALm | exact UPm | exact Um | exact OKm1 | exact OKm2 | clear - OKm3; lia | clear - FLm; lia | exact CTm
          | rewrite ESP; exact ST6 | rewrite ESP; clear - LOF CS96; lia | exact MI6
          | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDm FBlo FBsp CS96 LOF; lia | reflexivity]. }
      clear ST6 MI6.
      intros ms7 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *.
      destruct (KBELOW _ _ _ _ m7 _ 128 ENV6 LS6 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV7 & LS7). clear ENV6 LS6 MUc WMc MIc STc BNm Um.
      replace (ret_pc (Z_to_bv 64 0x151f44)) with (Z_to_bv 64 0x151f44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (nbits_range' bm OKm1) as BITS.
      unfold has_flag, BN_FLG_CONSTTIME. fold bm. rewrite CTm. cbn [Z.eqb negb tbind]. cbv beta.
      set (i0 := num_bits_pure bm) in *.
      assert (I0R : 0 <= i0 <= 32768) by (clear - BITS OKm2 OKm3; lia).

      cbn [fst snd].
      destruct (recp_rng bs4) eqn:RNG1; cbn [negb]; [| ihere; to_implM; unfold bunr; cbn [unreachable tree_ops embed interp fst snd]; apply implM_interp_unr].
      unfold recp_rng in RNG1. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in RNG1. destruct RNG1 as (((R1 & R2) & R3) & R4).
      pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS7 HRc) as RC. unfold recp_cells in RC.
      remember (if i0 <? 2 * st_rbits bs4 then 2 * st_rbits bs4 else i0) as i eqn:Ei.
      assert (IR : 0 <= i < 33554432) by (rewrite Ei; destruct (i0 <? 2 * st_rbits bs4); clear - I0R R1 R2; lia).
      lazymatch goal with |- evt _ ?POSTX _ =>
        assert (CONT : forall (rax' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          evt bgusegs POSTX
            (MS (mkR rax' (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' (Z_to_bv 64 (st_rbits bs4)) a3' a4' a5' a6' a7'
                      (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 ad) (Z_to_bv 64 arr) (Z_to_bv 64 ab) (Z_to_bv 64 aa) (Z_to_bv 64 i) s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x151f5c) fc None m7 (seg_rom bgusegs)))
      end.
      2: { step. rewrite (zx32_int (st_rbits bs4)) by (clear - R1 R2; lia).
           step. rewrite (unsigned_lit (st_rbits bs4)) by (clear - R1 R2; lia). rewrite Z.shiftr_div_pow2 by (clear; lia). rewrite (Z.div_small (st_rbits bs4) (2 ^ 30)) by (clear - R1 R2; lia).
           chkw ltac:(fun C => clear - C; lia).
           step. rewrite (unsigned_lit (st_rbits bs4)) by (clear - R1 R2; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 1) with 2.
           rewrite (bn_swrap32_small (st_rbits bs4 * 2)) by (clear - R1 R2; lia). replace (st_rbits bs4 * 2) with (2 * st_rbits bs4) by (clear; lia).
           step. rewrite lts_signed by (clear - I0R R1 R2; lia).
           destruct (Z.ltb_spec i0 (2 * st_rbits bs4)) as [LT|GE]; cbn [negb].
           - rewrite <- Ei. eapply CONT.
           - step. rewrite <- Ei. eapply CONT. }
      intros until t6'. clear RC.

      pose (RCPQ := fun (r : unit * bstate bptr) (st' : PState) (ms' : machine_state) =>
        exists mJ OWJ (rax2 t02 t12 t22 a02 a12 a32 a42 a52 a62 a72 t32 t42 t52 t62 : word),
          ms' = MS (mkR rax2 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t02 t12 t22 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a02 a12 (sx32 (Z_to_bv 64 (st_rbits (snd r)))) a32 a42 a52 a62 a72
                        (Z_to_bv 64 arm) (Z_to_bv 64 an) (Z_to_bv 64 ad) (Z_to_bv 64 arr) (Z_to_bv 64 ab) (Z_to_bv 64 aa) (Z_to_bv 64 i) (Z_to_bv 64 (an + 24)) s10 s11 t32 t42 t52 t62)
                   F (Z_to_bv 64 0x151f8c) fc None mJ (seg_rom bgusegs)
          /\ kenv LB PL lo B SPv FB s bs OW m saved st' (snd r) mJ OWJ /\ lib_state (snd r) mJ OWJ PL EA /\ refs_stable bs4 OW5 (snd r) OWJ /\ st_rshift (snd r) = i).
      ihere. to_implM.
      eapply implM_embed_bind with (Q1 := RCPQ).
      { pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS7 HRc) as RC. unfold recp_cells in RC.
        unfold implM. iprefix.
        step. rewrite (sx32_int (st_rshift bs4)) by (clear - R3 R4; lia).
        step.
        step. rewrite eqb_int by (clear - IR R3 R4; lia).
        destruct (Z.eqb_spec i (st_rshift bs4)) as [ESH|NSH].
        -
          ihere. cbn [embed interp]. apply implM_interp_ret. apply evt_done.
          unfold RCPQ. exists m7, OW5. do 15 eexists. cbn [snd].
          split; [rewrite (sx32_int (st_rbits bs4)) by (clear - R1 R2; lia); reflexivity|].
          split; [exact ENV7|]. split; [exact LS7|]. split; [apply refs_stable_refl| symmetry; exact ESH].
        - clear RC.
          step. step. step. step. step.
          destruct (KPRE _ _ _ _ _ CS ENV7 LS7 LOF) as (errv8 & PRE8). ihere. to_implM.
          eapply implM_embed_bind.
          { eapply BN_reciprocal_walk; [exact PRE8| reflexivity| exact (recp_at_refNr _ _ _ _ HRC)| exact (recp_at_refN _ _ _ _ HRC)| exact (recp_at_wrefNr _ _ HRC)| exact NRON| exact HPC
              | clear - IR; lia| reflexivity| reflexivity| reflexivity| reflexivity]. }
          cbv beta. intros [sh bs8] st8 ms8 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & Esh & ->)).
          destruct (KPOST _ _ _ _ _ _ _ _ _ ENV7 KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
          cbn [fst snd] in *. subst sh. clear PRE8 KP. unfold MallocRep.wz in *.
          replace (ret_pc (Z_to_bv 64 0x151f7c)) with (Z_to_bv 64 0x151f7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          cbn [embed interp]. apply implM_interp_ret.
          pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS8 HRc) as RC8. unfold recp_cells in RC8.
          pose proof ENV8 as (HEAP8 & _ & ST8 & (errv8' & ERR8) & MI8 & _ & _ & _ & _ & FR8 & _).
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8.
          pose proof (recp_facts _ _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 FROK HRc) as (RC0 & RCS & RCB & _ & _ & _). unfold RECP_SC_SZ in RCB.
          unfold LX_ERRNO, RATP in ERR8. change (3346328 - 164) with 3346164 in ERR8. unfold saved in FR8.
          pose proof (munch_refl [(an + 48, an + 48 + RECP_SC_SZ)]%Z m8) as MU. pose proof (wmono_refl bgusegs m8) as WM. unfold RECP_SC_SZ in MU.
          step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
          assert (LS9 : lib_state (set_recp (st_rbits bs8) i bs8) m9 OW8 PL EA).
          { eapply (lib_state_set_recp _ LB SPv B false [] bs8 m8 m9 OW8 PL EA (an + 48) (st_rbits bs8) i);
              [exact HEAP8| exact LS8| exact FROK| exact HRc| exact MU| exact WM| exact RC8]. }
          assert (ENV9 : kenv LB PL lo B SPv FB s bs OW m saved st8 (set_recp (st_rbits bs8) i bs8) m9 OW8).
          { apply kenv_set_recp.
            eapply kenv_xw with (m := m8) (W := [(an + 48, an + 48 + 12)]) (errv' := errv8');
              [exact CEIL| exact GLO'| exact FBlo| exact FBsp| exact SPB| exact FROK| exact ENV8| exact MU| exact WM| | exact ST8| unfold LX_ERRNO, RATP; exact ERR8| exact MI8| exact FR8].
            constructor; [|constructor]. exists (an + 48, an + 48 + RECP_SC_SZ). split; [apply pl_frames_recp; exact HRc|]. unfold RECP_SC_SZ. cbn [fst snd]. clear. lia. }
          clear RC8 MU WM ST8 FR8 ERR8 MI8 HEAP8 PARTS8.
          step. if_cases KM; rewrite ?unsigned_lit in KM by (clear - IR; lia); zify_cond KM; [exfalso; clear - KM IR; lia|]. clear KM.
          pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS9 HRc) as RC9. unfold recp_cells in RC9.
          step. clear RC9.
          apply evt_done.
          unfold RCPQ. exists m9, OW8. do 15 eexists. split; [reflexivity|]. cbn [snd].
          split; [exact ENV9|]. split; [exact LS9|]. split; [| reflexivity].
          eapply refs_stable_trans; [exact RS8|]. intros PL' k a' H. apply ref_at_set_recp. exact H. }
      cbv beta. intros [uJ bsJ] stJ msJ (mJ & OWJ & R).
      destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVJ & LSJ & RSJ & HSH). cbn [fst snd] in *.
      clear RCPQ ENV7 LS7.

      cbn [tbind fst snd].
      destruct (recp_rng bsJ) eqn:RNG2; cbn [negb]; [| unfold bunr; cbn [unreachable tree_ops embed interp fst snd]; apply implM_interp_unr].
      unfold recp_rng in RNG2. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in RNG2. destruct RNG2 as (((RJ1 & RJ2) & _) & _).
      rewrite HSH. replace (i =? -1) with false by (symmetry; apply Z.eqb_neq; clear - IR; lia).
      unfold implM. iprefix.
      step. rewrite !(sx32_int (st_rbits bsJ)) by (clear - RJ1 RJ2; lia). rewrite (unsigned_lit (st_rbits bsJ)) by (clear - RJ1 RJ2; lia).
      rewrite Z.add_0_r, (bn_swrap32_small (st_rbits bsJ)) by (clear - RJ1 RJ2; lia).
      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVJ LSJ LOF) as (errv10 & PRE10). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_rshift_walk; [exact PRE10| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RSJ HAa5)| rewrite Ea; apply hpl_pool| exact (ref_at_stable _ _ _ _ PL _ _ RSJ HAm5)| exact NROm
          | reflexivity| reflexivity| reflexivity| clear - RJ1 RJ2; lia]. }
      cbv beta. intros [u10 bs10] st10 ms10 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m10 & OW10 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVJ KP) as (ENV10 & LS10). pose proof KP as RS10; apply kpost_refs in RS10.
      cbn [fst snd] in *. clear PRE10 KP ENVJ LSJ.
      replace (ret_pc (Z_to_bv 64 0x151f9c)) with (Z_to_bv 64 0x151f9c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RSJ RS10) as RSc10.
      unfold implM. iprefix. step. if_false.

      step. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV10 LS10 LOF) as (errv11 & PRE11). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_mul_walk; [exact PRE11| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RSc10 HAb)| exact (ref_at_stable _ _ _ _ PL _ _ RSc10 HAa5)| exact (recp_at_refNr _ _ _ _ HRC)
          | rewrite Eb; apply hpl_pool| exact NROa| exact NRONr| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u11 bs11] st11 ms11 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV10 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE11 KP ENV10 LS10.
      replace (ret_pc (Z_to_bv 64 0x151fb4)) with (Z_to_bv 64 0x151fb4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RSc10 RS11) as RSc11.

      cbn [tbind fst snd].
      destruct (recp_rng bs11) eqn:RNG3; cbn [negb]; [| unfold bunr; cbn [unreachable tree_ops embed interp fst snd]; apply implM_interp_unr].
      unfold recp_rng in RNG3. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in RNG3. destruct RNG3 as (((RK1 & RK2) & _) & _).
      unfold implM. iprefix. step. if_false.
      pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS11 HRc) as RC. unfold recp_cells in RC.
      step. rewrite (sx32_int (st_rbits bs11)) by (clear - RK1 RK2; lia). clear RC.
      step. rewrite (unsigned_lit (st_rbits bs11)) by (clear - IR RK1 RK2; lia). replace (i + - st_rbits bs11) with (i - st_rbits bs11) by (clear; lia).
      step. rewrite ?(unsigned_lit i), ?(unsigned_lit (st_rbits bs11)) by (clear - IR RK1 RK2; lia).
      try replace (i + - st_rbits bs11) with (i - st_rbits bs11) by (clear; lia).
      rewrite (bn_swrap32_small (i - st_rbits bs11)) by (clear - IR RK1 RK2; lia).
      chkw ltac:(fun C => clear - C; lia).
      destruct (Z.ltb_spec (i - st_rbits bs11) 0) as [NEG|NNEG].
      {
        ihere. to_implM. unfold BN_rshift at 1. replace (i - st_rbits bs11 <? 0) with true by (symmetry; apply Z.ltb_lt; exact NEG).
        unfold bunr. cbn [unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
      step. rewrite (unsigned_lit (i - st_rbits bs11)) by (clear - IR RK1 RK2 NNEG; lia).
      rewrite Z.add_0_r, (bn_swrap32_small (i - st_rbits bs11)) by (clear - IR RK1 RK2; lia).
      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV11 LS11 LOF) as (errv12 & PRE12). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_rshift_walk; [exact PRE12| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RSc11 HAd5)| rewrite Ed; apply hpl_pool| exact (ref_at_stable _ _ _ _ PL _ _ RSc11 HAb)| exact NROb
          | reflexivity| reflexivity| reflexivity| clear - IR RK1 NNEG; lia]. }
      cbv beta. intros [u12 bs12] st12 ms12 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m12 & OW12 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV11 KP) as (ENV12 & LS12). pose proof KP as RS12; apply kpost_refs in RS12.
      cbn [fst snd] in *. clear PRE12 KP ENV11 LS11.
      replace (ret_pc (Z_to_bv 64 0x151fd8)) with (Z_to_bv 64 0x151fd8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RSc11 RS12) as RSc12.
      unfold implM. iprefix. step. if_false.

      cbn [tbind fst snd].
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSc12 HAd5) as HAd12.
      destruct (KSTORE _ _ _ _ _ d ad ENV12 LS12 HAd12 NROd) as (Dd & BNd & OKd & Ad0 & SEPd & Ad63 & AId & CLOSEd).
      unfold bn_cells in BNd.
      pose proof ENV12 as (_ & _ & ST12 & _ & MI12 & _).
      pose proof (munch_refl [(ad, ad + 24)]%Z m12) as MU. pose proof (wmono_refl bgusegs m12) as WM.
      chkw ltac:(fun C => clear - C AdR; lia).
      step. rewrite ?(land7_wrap _ AD8), ?(land7_wz _ AD8).
      chkw ltac:(fun C => clear - C; lia).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m13 end.
      destruct (CLOSEd m13 (bn_with_neg (getbn d bs12) false) MU WM) as (ENV13 & LS13);
        [ exact BNd | reflexivity | reflexivity | exact OKd | exact ST12 | exact MI12 |].
      clear BNd MU WM ST12 MI12 CLOSEd ENV12 LS12.
      set (bs13 := setbn d (bn_with_neg (getbn d bs12) false) bs12) in *.
      assert (RSc13 : refs_stable bs4 OW5 bs13 OW12) by (eapply refs_stable_trans; [exact RSc12| apply refs_stable_setbn]).

      step. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV13 LS13 LOF) as (errv14 & PRE14). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_mul_walk; [exact PRE14| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RSc13 HAb)| exact (recp_at_refN _ _ _ _ HRC)| exact (ref_at_stable _ _ _ _ PL _ _ RSc13 HAd5)
          | rewrite Eb; apply hpl_pool| exact NRON| exact NROd| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u14 bs14] st14 ms14 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m14 & OW14 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV13 KP) as (ENV14 & LS14). pose proof KP as RS14; apply kpost_refs in RS14.
      cbn [fst snd] in *. clear PRE14 KP ENV13 LS13.
      replace (ret_pc (Z_to_bv 64 0x152000)) with (Z_to_bv 64 0x152000) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RSc13 RS14) as RSc14.
      unfold implM. iprefix. step. if_false.

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV14 LS14 LOF) as (errv15 & PRE15). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_usub_walk; [exact PRE15| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RSc14 HAr5)| exact HPr| exact (ref_at_stable _ _ _ _ PL _ _ RSc14 HAm5)| exact NROm
          | exact (ref_at_stable _ _ _ _ PL _ _ RSc14 HAb)| exact NROb| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u15 bs15] st15 ms15 PO. apply BPK in PO; [|intros vv b' o p a' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m15 & OW15 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV14 KP) as (ENV15 & LS15). pose proof KP as RS15; apply kpost_refs in RS15.
      cbn [fst snd] in *. clear PRE15 KP ENV14 LS14.
      replace (ret_pc (Z_to_bv 64 0x152014)) with (Z_to_bv 64 0x152014) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RSc14 RS15) as RSc15.
      unfold implM. iprefix. step. if_false.

      cbn [tbind fst snd].
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSc15 HAr5) as HAr15.
      destruct (KSTORE _ _ _ _ _ rr arr ENV15 LS15 HAr15 NROr) as (Dr & BNr & OKr & Ar0 & SEPr & Ar63 & AIr & CLOSEr).
      unfold bn_cells in BNr.
      pose proof ENV15 as (_ & _ & ST15 & _ & MI15 & _).
      pose proof (munch_refl [(arr, arr + 24)]%Z m15) as MU. pose proof (wmono_refl bgusegs m15) as WM.
      chkw ltac:(fun C => clear - C ArR; lia).
      step. rewrite ?(land7_wrap _ ArA), ?(land7_wz _ ArA).
      chkw ltac:(fun C => clear - C; lia).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m16 end.
      destruct (CLOSEr m16 (bn_with_neg (getbn rr bs15) false) MU WM) as (ENV16 & LS16);
        [ exact BNr | reflexivity | reflexivity | exact OKr | exact ST15 | exact MI15 |].
      clear BNr MU WM ST15 MI15 CLOSEr ENV15 LS15.
      set (bs16 := setbn rr (bn_with_neg (getbn rr bs15) false) bs15) in *.
      assert (RSc16 : refs_stable bs4 OW5 bs16 OW15) by (eapply refs_stable_trans; [exact RSc15| apply refs_stable_setbn]).

      step.
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply (div_loop 5 0 st15 bs16 m16 OW15 d ad di); [exact ENV16| exact LS16| exact (ref_at_stable _ _ _ _ PL _ _ RSc16 HAd5)| exact Ed| clear; lia| clear; lia]. }
      cbv beta. intros [uL bsL] stL msL (mL & OWL & R).
      destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVL & LSL & HAdL). cbn [fst snd] in *.
      eapply div_final; [exact ENVL| exact LSL| exact HAdL| exact Ed].
    Qed.
  End Body.

  Lemma BN_div_recp_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rm : bnref) (ar am an ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_DIV_RECP_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rm am -> hpl PL rr -> rm <> ROne -> recp_at PL an -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz am -> a3 = wz an -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_div_recp (tree_ops bptr) None (Some rr) rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV_RECP) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAr HAm HPr NROm HRC HPC -> -> -> -> ->.
    pose proof (proj1 HPr) as NROr.
    unfold BN_DIV_RECP_STACK, BN_DIV_RECP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (recp_at_recp PL an HRC) as HRc.
    assert (ArR : 0 < ar < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAr NROr) as (X & Y & _); clear - X Y SPR; lia).
    assert (AmR : 0 < am < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAm NROm) as (X & Y & _); clear - X Y SPR; lia).
    assert (AnR : 0 < an /\ an + 60 < 2^63).
    { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK (recp_at_refN bs OW PL an HRC) (proj1 (recp_at_wrefN PL an HRC))) as (X & _ & _).
      pose proof (recp_facts _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HRc) as (_ & _ & Y & Z_ & _). unfold RECP_SC_SZ in Y. clear - X Y Z_. lia. }
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS (recp_at_refN bs OW PL an HRC) (proj1 (recp_at_wrefN PL an HRC))) as (_ & AN8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAr NROr) as (_ & ArA).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAm NROm) as (_ & AmA).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold implM. iprefix.

    carve_frame 96%nat ST. do 19 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -96) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -96) by lia.
    assert (FBsp : bv_unsigned sp + -96 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -96) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -96) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -96) CEIL FBlo FBsp SPR2 A) as BPK.
    assert (LOF : lo <= bv_unsigned sp + -96 - CS) by lia.
    lazymatch type of FR with rw_cells _ _ _ (CB _ ?j :: _) => set (j0 := j) in * end.
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR LS.
    ihere. to_implM.
    pose proof (div_body ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA rr rm ar am an ac qc (bv_unsigned sp + -96) (bv_unsigned sp) j0
                  ltac:(clear; lia) CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK LOF HPC HRC HAr HAm HPr NROm ArR AmR AnR AN8 ArA AmA m1) as LN.
    unfold FINALQ in LN. rewrite (Z_to_bv_bv_unsigned sp) in LN.
    eapply LN; [exact ENV| exact LS1].
  Qed.
End Proofs.
End WithCeiling0.
