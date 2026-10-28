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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ValArr W_mod_exp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
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

Definition BN_MOD_EXP_SIMPLE : Z := 0x151770.

Definition BN_MOD_MUL : Z := 0x109378.
Definition BN_NNMOD : Z := 0x108af0.
Definition BN_SET_WORD : Z := 0xfe4e4.
Definition BN_CTX_START : Z := 0x100c14.
Definition BN_CTX_GET : Z := 0x100e84.
Definition BN_CTX_END : Z := 0x100da4.

Lemma num_bits_pure_range : forall b : bignum bptr, limbs (bn_buf b) -> 0 <= num_bits_pure b <= 64 * Z.of_nat (bn_top b).
Proof.
  intros b HL. unfold num_bits_pure. destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
  pose proof (limbs_nth (bn_buf b) (bn_top b - 1) HL) as LN. unfold limb, BW in LN.
  pose proof (num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). lia.
Qed.

Lemma last_nth : forall {A} (l : list A) (d : A), last l d = nth (length l - 1) l d.
Proof.
  intros A l d. induction l as [|x l IH]; [reflexivity|]. destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH.
  cbn [length]. destruct (length l'); reflexivity.
Qed.

Lemma exp_table_loop_S : forall (mulop : bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit) c vals d (s : bstate bptr),
  exp_table_loop (tree_ops bptr) mulop (S c) vals d s =
  tbind (BN_CTX_get (tree_ops bptr) s)
        (fun p => tbind (mulop (fst p) (last vals 0%nat) d (snd p)) (fun p0 => exp_table_loop (tree_ops bptr) mulop c (vals ++ [fst p]) d (snd p0))).
Proof. reflexivity. Qed.
Lemma exp_table_loop_O : forall (mulop : bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit) vals d (s : bstate bptr),
  exp_table_loop (tree_ops bptr) mulop 0 vals d s = TRet (vals, s).
Proof. reflexivity. Qed.

Section LoopEqs.
  Context (mulop : bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit).
  Lemma exp_sqr_loop_S : forall c r (s : bstate bptr),
    exp_sqr_loop (tree_ops bptr) mulop (S c) r s = tbind (mulop r r r s) (fun p => exp_sqr_loop (tree_ops bptr) mulop c r (snd p)).
  Proof. reflexivity. Qed.
  Lemma exp_sqr_loop_O : forall r (s : bstate bptr), exp_sqr_loop (tree_ops bptr) mulop 0 r s = TRet (tt, s).
  Proof. reflexivity. Qed.
  Lemma tbind_bret : forall {A B} (a : A) (s : bstate bptr) (k : A * bstate bptr -> btree bptr B),
    tbind (bret (tree_ops bptr) a s) k = k (a, s).
  Proof. reflexivity. Qed.
  Lemma ewl_clear : forall f rp rr vals window wstart start (s : bstate bptr),
    is_bit_set_pure (getbn rp s) wstart = false ->
    exp_window_loop (tree_ops bptr) mulop (S f) rp rr vals window wstart start s =
    tbind ((if start then bret (tree_ops bptr) tt else mulop rr rr rr) s)
          (fun p => (if wstart =? 0 then bret (tree_ops bptr) tt else exp_window_loop (tree_ops bptr) mulop f rp rr vals window (wstart - 1) start) (snd p)).
  Proof. intros. cbn [exp_window_loop bbind bget bret bind ret tree_ops tbind]. rewrite H. cbn [negb]. destruct start; reflexivity. Qed.
  Lemma ewl_set : forall f rp rr vals window wstart start (s : bstate bptr) wv we,
    is_bit_set_pure (getbn rp s) wstart = true ->
    window_scan (is_bit_set_pure (getbn rp s)) wstart (Z.to_nat (window - 1)) 1 1 0 = (wv, we) ->
    exp_window_loop (tree_ops bptr) mulop (S f) rp rr vals window wstart start s =
    tbind ((if start then bret (tree_ops bptr) tt else exp_sqr_loop (tree_ops bptr) mulop (Z.to_nat (we + 1)) rr) s)
          (fun p2 => tbind (mulop rr rr (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) (snd p2))
             (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt else exp_window_loop (tree_ops bptr) mulop f rp rr vals window (wstart - (we + 1)) false) (snd p))).
  Proof. intros. cbn [exp_window_loop bbind bget bret bind ret tree_ops tbind]. rewrite H. cbn [negb]. rewrite H0. destruct start; reflexivity. Qed.
End LoopEqs.

Lemma lor_shiftl_1 : forall wv k, 0 <= wv -> 1 <= k -> Z.lor (Z.shiftl wv k) 1 = wv * 2 ^ k + 1.
Proof.
  intros wv k Hw Hk. rewrite Z.shiftl_mul_pow2 by lia.
  assert (L0 : Z.land (wv * 2 ^ k) 1 = 0).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    replace (2 ^ k) with (2 * 2 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    replace (wv * (2 * 2 ^ (k - 1))) with ((wv * 2 ^ (k - 1)) * 2) by lia. apply Z.mod_mul. lia. }
  rewrite <- Z.lxor_lor by exact L0. symmetry. apply Z.add_nocarry_lxor. exact L0.
Qed.

Lemma swrap32_plus_2_64 : forall x, bv_swrap 32 (x + 18446744073709551616) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
  replace (x + 18446744073709551616 + 2147483648) with (x + 2147483648 + 4294967296 * 4294967296) by lia.
  rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma window_scan_bnd : forall (bit : Z -> bool) wstart c i wv we,
  1 <= i -> 0 <= we < i -> we <= wstart -> 1 <= wv < 2 ^ (we + 1) ->
  let '(wv', we') := window_scan bit wstart c i wv we in
  0 <= we' < i + Z.of_nat c /\ we' <= wstart /\ 1 <= wv' < 2 ^ (we' + 1).
Proof.
  intros bit wstart c. induction c as [|c IH]; intros i wv we Hi Hwe Hws Hwv; cbn [window_scan].
  - lia.
  - destruct (Z.ltb_spec (wstart - i) 0) as [Hl|Hge]; [lia|].
    destruct (bit (wstart - i)).
    + assert (HB : 1 <= Z.lor (Z.shiftl wv (i - we)) 1 < 2 ^ (i + 1)).
      { rewrite lor_shiftl_1 by lia.
        assert (2 ^ (we + 1) * 2 ^ (i - we) = 2 ^ (i + 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (2 <= 2 ^ (i - we)) by (replace (2 ^ (i - we)) with (2 * 2 ^ (i - we - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia);
                                       assert (0 < 2 ^ (i - we - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
        assert (0 <= wv * 2 ^ (i - we)) by (apply Z.mul_nonneg_nonneg; lia).
        split; [lia|]. assert (wv * 2 ^ (i - we) <= (2 ^ (we + 1) - 1) * 2 ^ (i - we)) by (apply Z.mul_le_mono_nonneg_r; lia).
        assert ((2 ^ (we + 1) - 1) * 2 ^ (i - we) = 2 ^ (we + 1) * 2 ^ (i - we) - 2 ^ (i - we)) by lia. lia. }
      specialize (IH (i + 1) (Z.lor (Z.shiftl wv (i - we)) 1) i ltac:(lia) ltac:(lia) ltac:(lia) HB).
      destruct (window_scan bit wstart c (i + 1) (Z.lor (Z.shiftl wv (i - we)) 1) i) as [wv' we']. lia.
    + specialize (IH (i + 1) wv we ltac:(lia) ltac:(lia) ltac:(lia) Hwv). destruct (window_scan bit wstart c (i + 1) wv we) as [wv' we']. lia.
Qed.

Section Proofs.
  Variable CS : Z.
  Hypothesis CS96 : 128 <= CS.
  Definition BN_MOD_EXP_SIMPLE_STACK : Z := 368 + CS.

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

  Hypothesis BN_nnmod_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod (tree_ops bptr) rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NNMOD) fc None m (seg_rom bgusegs)).

  Hypothesis BN_mod_mul_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rb rm : bnref) (arr ara arb arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL ra_ ara -> ref_at bs OW PL rb arb -> ref_at bs OW PL rm arm ->
    hpl PL rr -> ra_ <> ROne -> rb <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz arr -> a1 = wz ara -> a2 = wz arb -> a3 = wz arm -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_mod_mul (tree_ops bptr) rr ra_ rb rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_MUL) fc None m (seg_rom bgusegs)).

  Hypothesis BN_set_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr : bnref) (ar w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> wref PL rr -> 0 <= w < BW -> a0 = wz ar -> a1 = wz w ->
    implM bgusegs (interp (embed (BN_set_word (tree_ops bptr) rr w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SET_WORD) fc None m (seg_rom bgusegs)).

  Section Body.
    Variables (ra gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL : placement) (EA : BnRep.err_addrs).
    Variables (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr).
    Variables (FB SPv : Z).
    Hypothesis ESPV : SPv = FB + 368.
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
    Hypothesis HAr : ref_at bs OW PL rr arr.
    Hypothesis HAp : ref_at bs OW PL rp arp.
    Hypothesis HAm : ref_at bs OW PL rm arm.
    Hypothesis WRr : hpl PL rr.
    Hypothesis NROp : rp <> ROne.
    Hypothesis NROm : rm <> ROne.
    Hypothesis ArR : 0 < arr < 2^64.
    Hypothesis ApR : 0 < arp < 2^64.
    Hypothesis FB16 : FB mod 16 = 0.

    Definition saved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Definition efr (j0 : list byte) (ws : list word) : list cell := CB 8 j0 :: CB 256 (u64s ws) :: saved.
    Definition FINALQ : unit * bstate bptr -> PState -> machine_state -> Prop :=
      bn_post ra (Z_to_bv 64 SPv) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
              (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1).

    Local Ltac kit :=
      pose proof (kenv_pre LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE;
      pose proof (kenv_post LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST;
      pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B SPv FB CEIL FBlo FBsp SPR2 A) as BPK;
      pose proof (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KOPEN;
      pose proof (kenv_below LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW;
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - FBlo FBsp SPR2 CEIL; lia);
      pose proof GLO' as GLO2; unfold GLOBALS_TOP in GLO2.

    Lemma simple_exit : forall j0 ws stK bsK mK OWK
        (rax t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 1) x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x151b98) fc None mK (seg_rom bgusegs)).
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
      replace (ret_pc (Z_to_bv 64 1383328)) with (Z_to_bv 64 1383328) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B SPv FB s bs OW m _ _ _ _ _ ENV14) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      unfold efr, saved in FRF.
      step. step. do 13 step. release_frame FRF STF SPv. step. step.
      apply evt_done. unfold FINALQ, bn_post. do 15 eexists. exists m14, OW14, PL, errvF.
      replace (FB + 368) with SPv by lia. rewrite (unsigned_lit SPv) by lia. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS14|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [first [eapply refs_stable_trans; [exact F9| exact RS14] | exact F9]|]. split; reflexivity.
    Qed.

    Definition vtab (bsK : bstate bptr) (OWK : list block) (ws : list word) (vals : list bnref) (addrs : list Z) : Prop :=
      length addrs = length vals /\
      forall i, (i < length vals)%nat ->
        nth_error ws i = Some (Z_to_bv 64 (nth i addrs 0)) /\ ref_at bsK OWK PL (nth i vals 0%nat) (nth i addrs 0)
        /\ (exists j, nth i vals 0%nat = RPool j) /\ 0 < nth i addrs 0 < 2^64.

    Lemma vtab_stable : forall bsK OWK bs' OW' ws vals addrs, vtab bsK OWK ws vals addrs -> refs_stable bsK OWK bs' OW' -> vtab bs' OW' ws vals addrs.
    Proof.
      intros bsK OWK bs' OW' ws vals addrs [L H] RS. split; [exact L|]. intros i Hi. destruct (H i Hi) as (H1 & H2 & H3 & H4).
      split; [exact H1|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS H2)|]. split; [exact H3| exact H4].
    Qed.

    Lemma vtab_snoc : forall bsK OWK ws vals addrs v a j, vtab bsK OWK ws vals addrs -> (length vals < length ws)%nat ->
      ref_at bsK OWK PL v a -> v = RPool j -> 0 < a < 2^64 ->
      vtab bsK OWK (Arr.upd ws (length vals) (Z_to_bv 64 a)) (vals ++ [v]) (addrs ++ [a]).
    Proof.
      intros bsK OWK ws vals addrs v a j [L H] Hl HA Ev Ha. split; [rewrite !length_app; cbn; lia|].
      intros i Hi. rewrite length_app in Hi. cbn in Hi.
      destruct (Nat.lt_ge_cases i (length vals)) as [Hlt|Hge].
      - destruct (H i Hlt) as (H1 & H2 & H3 & H4). rewrite !app_nth1 by lia.
        split; [rewrite nth_error_upd_other by lia; exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
      - assert (Ei : i = length vals) by lia. subst i.
        rewrite app_nth2 by lia. rewrite (app_nth2 vals [v] 0%nat) by lia. rewrite L, Nat.sub_diag. cbn [nth].
        split; [apply nth_error_upd_same; exact Hl|]. split; [exact HA|]. split; [exists j; exact Ev| exact Ha].
    Qed.

    Definition TABLEQ (j0 : list byte) (bits window : Z) (r : list bnref * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists ws' addrs' mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x24 x25 x26 x27 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) x21 (Z_to_bv 64 bits) (Z_to_bv 64 window) x24 x25 x26 x27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x151a0c) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efr j0 ws') st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ length ws' = 32%nat
        /\ vtab (snd r) OWK' ws' (fst r) addrs' /\ Z.of_nat (length (fst r)) = (if 1 <? window then 2 ^ (window - 1) else 1).

    Lemma table_body : forall vals addrs stK bsK mK OWK j0 ws (bits window cnt : Z) (d : bnref) (ad : Z)
        (K : bnref -> bstate bptr -> btree bptr (list bnref * bstate bptr)) (Q : list bnref * bstate bptr -> PState -> machine_state -> Prop)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> (1 <= length vals)%nat -> (length vals < 32)%nat -> 1 < window <= 6 ->
      ref_at bsK OWK PL d ad -> d <> ROne -> ref_at bsK OWK PL rm arm -> 0 < cnt < 2 ^ 64 ->
      (forall v av bs2 st2 m2 OW2 ws2 (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
          kenv LB PL lo B SPv FB s bs OW m (efr j0 ws2) st2 bs2 m2 OW2 -> lib_state bs2 m2 OW2 PL EA -> length ws2 = 32%nat ->
          vtab bs2 OW2 ws2 (vals ++ [v]) (addrs ++ [av]) -> ref_at bs2 OW2 PL d ad -> ref_at bs2 OW2 PL rm arm -> refs_stable bsK OWK bs2 OW2 ->
          implM bgusegs (interp (embed (K v bs2))) st2 Q
            (MS (mkR (Z_to_bv 64 0x1519ec) (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 window)
                      (Z_to_bv 64 (window - 1)) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 (FB + 8 + 8 * Z.of_nat (length vals))) t3 t4 t5 t6)
                F (Z_to_bv 64 0x1519f0) fc None m2 (seg_rom bgusegs))) ->
      implM bgusegs (interp (embed (tbind (BN_CTX_get (tree_ops bptr) bsK)
                                           (fun p => tbind (BN_mod_mul (tree_ops bptr) (fst p) (last vals 0%nat) d rm (snd p)) (fun p0 => K (fst p) (snd p0)))))) stK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 window)
                  (Z_to_bv 64 (window - 1)) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 (FB + 8 + 8 * Z.of_nat (length vals))) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1519c4) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN VT K1 K32 WB HAd NROd HAmK CNT CONT; kit. unfold MallocRep.wz in *.
      unfold implM. iprefix. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv2 & PRE2).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [v bs2] st2 ms2 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & (vi & Ev) & (av & HAv & ->) & INCL8)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
      cbn [fst snd] in *. clear PRE2 KP.
      replace (ret_pc (Z_to_bv 64 1382860)) with (Z_to_bv 64 1382860) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof ENV8 as (HEAP8 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8.
      assert (FROK8 : frames_ok PL FB B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
      assert (NROv : v <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; lia).
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 FROK8 HAv NROv) as (Av0 & AvC & _).
      assert (AvR : 0 < av < 2^64) by (clear - Av0 AvC SPR2 SPB B63 ESPV; lia). clear AvC.

      pose proof ENV8 as (_ & _ & ST8 & (errv8 & ERR8) & MI8 & _ & _ & _ & _ & FR8 & _).
      unfold efr in FR8. destruct (val_frame_split bgusegs m8 FB j0 ws saved LEN FR8) as (F0 & VA & FS). clear FR8.
      assert (IDX : 0 <= Z.of_nat (length vals) < Z.of_nat (length ws)) by (rewrite LEN; lia).
      pose proof (u64arr_store_ok bgusegs m8 (FB + 8) ws (Z.of_nat (length vals)) (wa (FB + 8 + 8 * Z.of_nat (length vals))) VA IDX eq_refl) as SOKW.
      pose proof (u64arr_write bgusegs m8 (FB + 8) ws (Z.of_nat (length vals)) (Z_to_bv 64 av) VA IDX) as U2.
      pose proof (munch_refl [(FB + 8 + 8 * Z.of_nat (length vals), FB + 8 + 8 * Z.of_nat (length vals) + 8)]%Z m8) as MU. pose proof (wmono_refl bgusegs m8) as WM.
      apply hide_intro in ERR8.
      unfold implM. iprefix. ub_chk. step. store_done. apply hide_elim in ERR8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      eapply (rw_cells_transport bgusegs _ m8 m9) in ERR8; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]].
      rewrite Nat2Z.id in U2.
      pose proof (val_frame_join bgusegs m9 FB j0 _ saved ltac:(etransitivity; [apply Arr.upd_length| exact LEN]) F0 U2 FS) as FR9. fold (efr j0 (Arr.upd ws (length vals) (Z_to_bv 64 av))) in FR9.
      assert (HWL : Forall (w_lib bs2 OW8 PL lo SPv) [(FB + 8 + 8 * Z.of_nat (length vals), FB + 8 + 8 * Z.of_nat (length vals) + 8)]) by (constructor; [left; cbn; lia| constructor]).
      pose proof (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ st2 bs2 m8 m9 OW8 _ errv8
                    ENV8 PARTS8 MU WM HWL ST8 ERR8 ltac:(the_mi) FR9 ltac:(cbn; lia)) as ENV9.
      assert (LS9 : lib_state bs2 m9 OW8 PL EA).
      { assert (WOK : Forall (w_ok OW8 LB bs2 PL EA SPv []) [(FB + 8 + 8 * Z.of_nat (length vals), FB + 8 + 8 * Z.of_nat (length vals) + 8)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
        exact (lib_state_frame st2 LB _ _ [] bs2 m8 m9 OW8 PL EA _ HEAP8 LS8 MU WM FROK WOK). }
      clear ST8 F0 FS MU WM HWL ERR8 FR9.

      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].
      pose proof VT as [VL VT']. pose proof (VT' (length vals - 1)%nat ltac:(lia)) as (Wp & HAprev & (jp & Eprev) & AprevR). clear VT'.
      assert (Wp' : nth_error (Arr.upd ws (length vals) (Z_to_bv 64 av)) (Z.to_nat (Z.of_nat (length vals) - 1)) = Some (Z_to_bv 64 (nth (length vals - 1) addrs 0))).
      { rewrite nth_error_upd_other by lia. replace (Z.to_nat (Z.of_nat (length vals) - 1)) with (length vals - 1)%nat by lia. exact Wp. }
      let a := cur_mem_addr in pose proof (u64arr_read bgusegs m9 (FB + 8) _ (Z.of_nat (length vals) - 1) _ a U2 Wp' ltac:(lia) ltac:(addr_tac)) as RD.
      step. clear RD.

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV9 LS9 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { rewrite last_nth. eapply BN_mod_mul_walk; [exact PRE3| reflexivity| first [rewrite ESP; exact FB16 | rewrite unsigned_lit by lia; exact FB16]| exact HAv| exact (ref_at_stable _ _ _ _ PL _ _ RS8 HAprev)| exact (ref_at_stable _ _ _ _ PL _ _ RS8 HAd)
          | exact (ref_at_stable _ _ _ _ PL _ _ RS8 HAmK)| rewrite Ev; apply hpl_pool| rewrite Eprev; unfold RPool, ROne, NFIX; lia| exact NROd| exact NROm| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV9 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 1382892)) with (Z_to_bv 64 1382892) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS8 RS11) as RS811.
      unfold implM. iprefix. step. if_false.
      ihere. to_implM. eapply CONT; [exact ENV11| exact LS11| etransitivity; [apply Arr.upd_length| exact LEN]| | exact (ref_at_stable _ _ _ _ PL _ _ RS811 HAd)
        | exact (ref_at_stable _ _ _ _ PL _ _ RS811 HAmK)| exact RS811].
      apply (vtab_stable bs2 OW8); [|exact RS11]. eapply vtab_snoc; [eapply vtab_stable; [exact VT| exact RS8]| rewrite LEN; exact K32| exact HAv| exact Ev| exact AvR].
    Qed.

    Lemma table_loop : forall c vals addrs stK bsK mK OWK j0 ws (bits window cnt : Z) (d : bnref) (ad : Z)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> (1 <= length vals)%nat -> Z.of_nat (length vals) + Z.of_nat (S c) = 2 ^ (window - 1) -> 1 < window <= 6 ->
      ref_at bsK OWK PL d ad -> d <> ROne -> ref_at bsK OWK PL rm arm -> cnt = 32 - Z.of_nat (length vals) ->
      implM bgusegs (interp (embed (exp_table_loop (tree_ops bptr) (fun r a b => BN_mod_mul (tree_ops bptr) r a b rm) (S c) vals d bsK))) stK
        (TABLEQ j0 bits window)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 window)
                  (Z_to_bv 64 (window - 1)) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 (FB + 8 + 8 * Z.of_nat (length vals))) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1519c4) fc None mK (seg_rom bgusegs)).
    Proof.
      induction c as [|c IH]; intros until t6; intros ENVK LSK LEN VT K1 KC WB HAd NROd HAmK CNT.
      -
        rewrite exp_table_loop_S.
        assert (TS : 2 ^ (window - 1) <= 32) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
        eapply (table_body vals addrs stK bsK mK OWK j0 ws bits window cnt d ad
                  (fun v bs' => exp_table_loop (tree_ops bptr) (fun r a b => BN_mod_mul (tree_ops bptr) r a b rm) 0 (vals ++ [v]) d bs'));
          [exact ENVK| exact LSK| exact LEN| exact VT| exact K1| clear - KC TS; lia| exact WB| exact HAd| exact NROd| exact HAmK| clear - CNT KC TS; lia|].
        intros v av bs2 st2 m2 OW2 ws2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV2 LS2 LEN2 VT2 HAd2 HAm2 RS2.
        cbv beta. rewrite exp_table_loop_O. cbn [embed interp]. apply implM_interp_ret. unfold MallocRep.wz.
        assert (TS1 : 1 <= 2 ^ (window - 1)) by (clear - WB; assert (0 < 2 ^ (window - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
        step. rewrite !unsigned_lit by (clear - KC TS WB; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - KC TS; lia).
        rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia). rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
        replace ((Z.of_nat (length vals) + 1) / 2 ^ (window - 1)) with 1 by (symmetry; replace (Z.of_nat (length vals) + 1) with (2 ^ (window - 1)) by (clear - KC; lia); apply Z.div_same; clear - TS1; lia).
        rewrite (bn_swrap32_small 1) by lia.
        step. step. step. step. if_true.
        apply evt_done. unfold TABLEQ. exists ws2. exists (addrs ++ [av]). exists m2, OW2. do 21 eexists.
        split; [reflexivity|]. cbn [fst snd]. split; [exact ENV2|]. split; [exact LS2|]. split; [exact LEN2|]. split; [exact VT2|].
        rewrite length_app. cbn [length]. replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia). clear - KC; lia.
      -
        rewrite exp_table_loop_S.
        assert (TS : 2 ^ (window - 1) <= 32) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
        eapply (table_body vals addrs stK bsK mK OWK j0 ws bits window cnt d ad
                  (fun v bs' => exp_table_loop (tree_ops bptr) (fun r a b => BN_mod_mul (tree_ops bptr) r a b rm) (S c) (vals ++ [v]) d bs'));
          [exact ENVK| exact LSK| exact LEN| exact VT| exact K1| clear - KC TS; lia| exact WB| exact HAd| exact NROd| exact HAmK| clear - CNT KC TS; lia|].
        intros v av bs2 st2 m2 OW2 ws2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV2 LS2 LEN2 VT2 HAd2 HAm2 RS2.

        cbv beta.
        unfold implM. iprefix.
        step. rewrite !unsigned_lit by (clear - KC TS WB; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - KC TS; lia).
        rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia). rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
        rewrite (Z.div_small (Z.of_nat (length vals) + 1) (2 ^ (window - 1))) by (clear - KC; lia).
        rewrite (bn_swrap32_small 0) by lia.
        step. step. step. step. if_false. step.
        replace (Z.of_nat (length vals) + 2) with (Z.of_nat (length (vals ++ [v])) + 1) by (rewrite length_app; cbn [length]; lia).
        replace (FB + 8 + 8 * Z.of_nat (length vals) + 8) with (FB + 8 + 8 * Z.of_nat (length (vals ++ [v]))) by (rewrite length_app; cbn [length]; lia).
        ihere. to_implM.
        eapply (IH (vals ++ [v]) (addrs ++ [av])); [exact ENV2| exact LS2| exact LEN2| exact VT2| rewrite length_app; cbn [length]; lia
          | rewrite length_app; cbn [length]; clear - KC; lia| exact WB| exact HAd2| exact NROd| exact HAm2| rewrite length_app; cbn [length]; clear - CNT; lia].
    Qed.

    Definition SQRQ (j0 : list byte) (ws : list word) (bsK : bstate bptr) (OWK : list block) (x20 x21 x23 x24 x25 x26 x27 : word)
        (r : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 arr) (Z_to_bv 64 arm) x20 x21 (Z_to_bv 64 0) x23 x24 x25 x26 x27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x151b24) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable bsK OWK (snd r) OWK'.

    Lemma sqr_loop : forall c stK bsK mK OWK j0 ws (x20 x21 x23 x24 x25 x26 x27 : word)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL rr arr -> ref_at bsK OWK PL rm arm -> Z.of_nat (S c) < 2 ^ 31 ->
      implM bgusegs (interp (embed (exp_sqr_loop (tree_ops bptr) (fun r a b => BN_mod_mul (tree_ops bptr) r a b rm) (S c) rr bsK))) stK
        (SQRQ j0 ws bsK OWK x20 x21 x23 x24 x25 x26 x27)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) x20 x21 (Z_to_bv 64 (Z.of_nat (S c))) x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x151b00) fc None mK (seg_rom bgusegs)).
    Proof.
      induction c as [|c IH]; intros until t6; intros ENVK LSK HArK HAmK CB; kit;
        rewrite exp_sqr_loop_S; unfold implM; iprefix; do 5 step; step;
        destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3); ihere; to_implM;
        (eapply implM_embed_bind;
        [eapply BN_mod_mul_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16
            | exact HArK| exact HArK| exact HArK| exact HAmK| exact WRr| exact (proj1 WRr)| exact (proj1 WRr)| exact NROm| exact HPC
            | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]|]);
        cbv beta; intros [u4 bs4] st4 ms4 PO; (apply BPK in PO; [|intros vv b o p a [E _]; exact E]);
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->));
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11); pose proof KP as RS11; apply kpost_refs in RS11;
        cbn [fst snd] in *; clear PRE3 KP;
        (replace (ret_pc (Z_to_bv 64 1383192)) with (Z_to_bv 64 1383192) by (symmetry; apply ret_pc_even; [lia| reflexivity]));
        unfold implM; iprefix; step; if_false;
        step; rewrite unsigned_lit by (clear - CB; lia); rewrite (bn_swrap32_small _) by (clear - CB; lia).
      -
        rewrite exp_sqr_loop_O. change (Z.of_nat 1 + -1) with 0.
        step. if_false.
        ihere. cbn [embed interp]. apply implM_interp_ret. apply evt_done.
        unfold SQRQ. exists m11, OW11. do 16 eexists. split; [reflexivity|]. cbn [fst snd].
        split; [exact ENV11|]. split; [exact LS11| exact RS11].
      - replace (Z.of_nat (S (S c)) + -1) with (Z.of_nat (S c)) by lia.
        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - CB; lia); zify_cond KZ; try (exfalso; clear - KZ; lia).
        ihere. to_implM.
        eapply implM_mono; [eapply IH; [exact ENV11| exact LS11| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAmK)| clear - CB; lia]|].
        cbv beta. intros r st' ms' (mK' & OWK' & R); unfold SQRQ. exists mK', OWK'.
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3).
        do 16 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2| eapply refs_stable_trans; [exact RS11| exact K3]].
    Qed.

    Lemma lxor_shamt : forall t, 0 <= t < 8 ->
      bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 t)) 18446744073709551615)) mod 32 = 31 - t.
    Proof.
      intros t T. assert (E : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7) by lia.
      destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
    Qed.

    Lemma scan_loop : forall c (i wvalue wend : Z) stK bsK mK OWK fr (wstart window : Z) (POST : machine_state -> Prop)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m fr stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> ref_at bsK OWK PL rp arp ->
      1 <= i -> i + Z.of_nat c = window -> (0 < c)%nat -> window <= 6 -> 0 <= wstart < 2 ^ 31 -> 0 <= wend < i -> wend <= wstart -> 1 <= wvalue < 2 ^ (wend + 1) ->
      (forall mK' (wv' we' : Z) (rax' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word),
          kenv LB PL lo B SPv FB s bs OW m fr stK bsK mK' OWK -> lib_state bsK mK' OWK PL EA ->
          window_scan (is_bit_set_pure (getbn rp bsK)) wstart c i wvalue wend = (wv', we') ->
          evt bgusegs POST
            (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) x22 (Z_to_bv 64 window) (Z_to_bv 64 wv') x25 (Z_to_bv 64 we') (Z_to_bv 64 31) t3 t4 t5 t6)
                F (Z_to_bv 64 0x151adc) fc None mK' (seg_rom bgusegs))) ->
      evt bgusegs POST
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) x22 (Z_to_bv 64 window) (Z_to_bv 64 wvalue) (Z_to_bv 64 i) (Z_to_bv 64 wend) (Z_to_bv 64 31) t3 t4 t5 t6)
            F (Z_to_bv 64 0x151a98) fc None mK (seg_rom bgusegs)).
    Proof.
      induction c as [|c IH]; intros until t6; intros ENVK LSK HApK I1 IC C0 W6 WS WE WES WV K; [lia|]. kit.
      assert (P2 : 2 ^ (wend + 1) <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
      assert (P6 : 2 ^ i <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia).
      step. step. rewrite (unsigned_lit wstart), (unsigned_lit i) by (clear - WS I1 IC W6; lia). rewrite (bn_swrap32_small (wstart - i)) by (clear - WS I1 IC W6; lia).
      ub_chk.
      step. rewrite lts_signed by (clear - WS I1 IC W6; lia).
      destruct (Z.ltb_spec (wstart - i) 0) as [LT|GE].
      -
        cbn [negb]. eapply K; [exact ENVK| exact LSK|]. cbn [window_scan]. replace (wstart - i <? 0) with true by (symmetry; apply Z.ltb_lt; exact LT). reflexivity.
      - cbn [negb].

        destruct (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rp arp ENVK LSK HApK NROp)
          as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
        pose proof ENVK as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OKp3.
        step. step.
        eapply evt_cut.
        { eapply (BN_is_bit_set_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arp) (D := Dp) (b := getbn rp bsK) (n := wstart - i);
            [exact BNp | exact ALp | exact UPp | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS96; lia | exact MIK
            | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp FBlo FBsp CS96 LOF; lia | reflexivity | reflexivity | clear - GE WS I1; lia]. }
        clear STK MIK.
        intros ms2 PO. unfold bn_small_post in PO.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
        rewrite ESP in *.
        destruct (KBELOW _ _ _ _ m2 _ 16 ENVK LSK ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear MUc WMc MIc STc BNp Up.
        replace (ret_pc (Z_to_bv 64 1383088)) with (Z_to_bv 64 1383088) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        destruct (is_bit_set_pure (getbn rp bsK) (wstart - i)) eqn:EB; cbn [Z.b2z].
        +
          step. if_false.
          step. rewrite (unsigned_lit i), (unsigned_lit wend) by (clear - I1 WE IC W6; lia). rewrite (bn_swrap32_small (i - wend)) by (clear - I1 WE IC W6; lia).
          pose proof (lor_shiftl_1 wvalue (i - wend) ltac:(clear - WV P2; lia) ltac:(clear - WE; lia)) as LOR.
          assert (WB2 : 1 <= Z.lor (Z.shiftl wvalue (i - wend)) 1 < 2 ^ (i + 1)).
          { rewrite LOR.
            assert (2 <= 2 ^ (i - wend)) by (replace (2 ^ (i - wend)) with (2 * 2 ^ (i - wend - 1)) by (rewrite <- Z.pow_succ_r by (clear - WE; lia); f_equal; clear - WE; lia);
                                           assert (0 < 2 ^ (i - wend - 1)) by (apply Z.pow_pos_nonneg; clear - WE; lia); lia).
            assert (wvalue * 2 ^ (i - wend) <= (2 ^ (wend + 1) - 1) * 2 ^ (i - wend)) by (apply Z.mul_le_mono_nonneg_r; clear - WV WE H; lia).
            assert (2 ^ (wend + 1) * 2 ^ (i - wend) = 2 ^ (i + 1)) by (rewrite <- Z.pow_add_r by (clear - WE; lia); f_equal; clear - WE; lia).
            assert (0 <= wvalue * 2 ^ (i - wend)) by (apply Z.mul_nonneg_nonneg; clear - WV H; lia).
            assert ((2 ^ (wend + 1) - 1) * 2 ^ (i - wend) = 2 ^ (wend + 1) * 2 ^ (i - wend) - 2 ^ (i - wend)) by (clear; lia).
            clear - H H0 H1 H2 H3 WV. lia. }
          assert (P7 : 2 ^ (i + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - IC C0 W6; lia).
          assert (SH : 0 <= Z.shiftl wvalue (i - wend) < 2 ^ 7) by (rewrite LOR in WB2; rewrite Z.shiftl_mul_pow2 by (clear - WE; lia); clear - WB2 P7; lia).
          ub_chk. step. step.
          step. rewrite (lxor_shamt (i - wend)) by (clear - I1 WE IC W6; lia).
          rewrite (unsigned_lit wvalue) by (clear - WV P2 P6; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - WV P2 P6; lia).
          rewrite Z.shiftr_div_pow2 by (clear - I1 WE IC W6; lia).
          rewrite (Z.div_small wvalue (2 ^ (31 - (i - wend))))
            by (assert (2 ^ (wend + 1) <= 2 ^ (31 - (i - wend))) by (apply Z.pow_le_mono_r; clear - I1 WE IC W6; lia); clear - WV H; lia).
          rewrite (bn_swrap32_small 0) by lia.
          if_cases KS; zify_cond KS; [exfalso; clear - KS; lia| clear KS].
          step. rewrite (unsigned_lit (i - wend)) by (clear - I1 WE IC W6; lia). rewrite (Z.mod_small (i - wend) 32) by (clear - I1 WE IC W6; lia).
          rewrite (unsigned_lit wvalue) by (clear - WV P2 P6; lia). rewrite (bn_swrap32_small (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
          step. rewrite (unsigned_lit (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
          step.

          step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
          step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
          *
            eapply (IH (i + 1) (Z.lor (Z.shiftl wvalue (i - wend)) 1) i);
              [exact ENV2| exact LS2| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - I1; lia| clear - GE; lia
              | replace (i + 1) with (i + 1) by reflexivity; exact WB2 |].
            intros mK' wv' we' rax'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x25' t3' t4' t5' t6' ENV' LS' SC.
            eapply K; [exact ENV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
          *
            eapply K; [exact ENV2| exact LS2|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
            replace c with 0%nat by (clear - IC KW; lia). reflexivity.
        +
          step. if_true.
          step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
          step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
          * eapply (IH (i + 1) wvalue wend);
              [exact ENV2| exact LS2| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - WE; lia| exact WES| exact WV|].
            intros mK' wv' we' rax'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x25' t3' t4' t5' t6' ENV' LS' SC.
            eapply K; [exact ENV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
          * eapply K; [exact ENV2| exact LS2|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
            replace c with 0%nat by (clear - IC KW; lia). reflexivity.
    Qed.

    Definition WINQ (j0 : list byte) (ws : list word) (r : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) x21 (Z_to_bv 64 1) x23 x24 x25 x26 x27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x151b98) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA.

    Local Notation MUL := (fun r a b : bnref => BN_mod_mul (tree_ops bptr) r a b rm).

    Definition WLOOP (f : nat) : Prop := forall (wstart : Z) (start : bool) stK bsK mK OWK j0 ws vals addrs (window : Z)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 <= wstart < Z.of_nat f -> wstart < 2 ^ 24 -> j0 = le8 (Z_to_bv 64 (Z.lxor (SPv + -360) 18446744073709551615)) ->
      ref_at bsK OWK PL rr arr -> ref_at bsK OWK PL rp arp -> ref_at bsK OWK PL rm arm ->
      implM bgusegs (interp (embed (exp_window_loop (tree_ops bptr) MUL f rp rr vals window wstart start bsK))) stK (WINQ j0 ws)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 window)
                  (Z_to_bv 64 (Z.b2z (negb start))) x25 x26 (Z_to_bv 64 31) t3 t4 t5 t6)
            F (Z_to_bv 64 0x151a40) fc None mK (seg_rom bgusegs)).

    Lemma after_scan : forall f, WLOOP f -> forall (wstart wv we : Z) (start : bool) stK bsK mK OWK j0 ws vals addrs (window : Z)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 <= wstart < 2 ^ 24 -> 0 <= we < window -> we <= wstart -> 1 <= wv < 2 ^ (we + 1) -> wstart - (we + 1) < Z.of_nat f ->
      j0 = le8 (Z_to_bv 64 (Z.lxor (SPv + -360) 18446744073709551615)) ->
      ref_at bsK OWK PL rr arr -> ref_at bsK OWK PL rp arp -> ref_at bsK OWK PL rm arm ->
      implM bgusegs (interp (embed (tbind ((if start then bret (tree_ops bptr) tt else exp_sqr_loop (tree_ops bptr) MUL (Z.to_nat (we + 1)) rr) bsK)
                                           (fun p2 => tbind (BN_mod_mul (tree_ops bptr) rr rr (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) rm (snd p2))
                                             (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt
                                                        else exp_window_loop (tree_ops bptr) MUL f rp rr vals window (wstart - (we + 1)) false) (snd p)))))) stK (WINQ j0 ws)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 window)
                  x24 (Z_to_bv 64 (Z.shiftr wv 1)) (Z_to_bv 64 we) (Z_to_bv 64 31) t3 t4 t5 t6)
            F (Z_to_bv 64 0x151ae8) fc None mK (seg_rom bgusegs)).
    Proof.
      intros f REC. intros until t6; intros ENVK LSK LEN VT VL WB WS WE WES WV WF HJ0 HArK HApK HAmK. kit.
      assert (L32 : Z.of_nat (length vals) <= 32).
      { rewrite VL. destruct (1 <? window); [|lia]. change 32 with (2 ^ 5). apply Z.pow_le_mono_r; lia. }
      assert (WV2 : 0 <= Z.shiftr wv 1 < Z.of_nat (length vals)).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite VL.
        assert (2 ^ (we + 1) <= 2 ^ window) by (apply Z.pow_le_mono_r; lia).
        destruct (Z.ltb_spec 1 window) as [Hw|Hw].
        - assert (2 ^ window = 2 * 2 ^ (window - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
        - assert (we = 0) by lia. subst we. change (2 ^ (0 + 1)) with 2 in WV. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }

      assert (TAIL : forall st1 bs1 m1 OW1 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x22 : word),
            kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) st1 bs1 m1 OW1 -> lib_state bs1 m1 OW1 PL EA -> refs_stable bsK OWK bs1 OW1 ->
            implM bgusegs (interp (embed (tbind (BN_mod_mul (tree_ops bptr) rr rr (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) rm bs1)
                                             (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt
                                                        else exp_window_loop (tree_ops bptr) MUL f rp rr vals window (wstart - (we + 1)) false) (snd p))))) st1 (WINQ j0 ws)
              (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) x22 (Z_to_bv 64 window)
                        (Z_to_bv 64 (we + 1)) (Z_to_bv 64 (Z.shiftr wv 1)) (Z_to_bv 64 we) (Z_to_bv 64 31) t3' t4' t5' t6')
                  F (Z_to_bv 64 0x151b24) fc None m1 (seg_rom bgusegs))).
      { intros until x22. intros ENV1 LS1 RS1.
        pose proof VT as [VTL VT']. destruct (VT' (Z.to_nat (Z.shiftr wv 1)) ltac:(lia)) as (Wi & HAi & (ji & Ei) & AiR). clear VT'.
        pose proof ENV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _). unfold efr in FR1.
        destruct (val_frame_split bgusegs m1 FB j0 ws saved LEN FR1) as (J1 & VA & _). clear FR1.
        rewrite HJ0 in J1.
        assert (J8 : rw_cells bgusegs m1 FB [C8 (Z_to_bv 64 (Z.lxor (SPv + -360) 18446744073709551615))])
          by (eapply bk_rw_cells_recast; [exact J1| cbn; tauto| reflexivity| reflexivity]). clear J1.
        assert (LXS : Z.lxor (SPv + -360) 18446744073709551615 = 18446744073709551615 - (SPv + -360))
          by (apply zb_lxor_ones; clear - ESPV FBlo SPR2 CEIL; lia).
        unfold implM. iprefix.
        ub_chk.
        step. rewrite (unsigned_lit (Z.shiftr wv 1)) by (clear - WV2 L32; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
        replace (Z_to_bv 64 SPv) with (Z_to_bv 64 (FB + 368)) by (f_equal; clear - ESPV; lia).
        step.
        replace (Z_to_bv 64 (FB + 368)) with (Z_to_bv 64 SPv) by (f_equal; clear - ESPV; lia).
        clear J8.
        zstep. let C := fresh "C" in if_cases C;
          [ exfalso; rewrite ?LXS in C; zify_cond C; rewrite ?LXS in C; clear - C ESPV FBlo SPR2 CEIL WV2 L32; lia
          | clear C ].
        step. step.
        assert (Wi' : nth_error ws (Z.to_nat (Z.shiftr wv 1)) = Some (Z_to_bv 64 (nth (Z.to_nat (Z.shiftr wv 1)) addrs 0))) by exact Wi.
        let a := cur_mem_addr in pose proof (u64arr_read bgusegs m1 (FB + 8) _ (Z.shiftr wv 1) _ a VA Wi' ltac:(lia)
                                               ltac:(first [addr_tac | unfold wa; f_equal; clear - ESPV; lia])) as RD.
        step. clear RD VA Wi'.

        step. step. step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV1 LS1 LOF) as (errv3 & PRE3).
        ihere. to_implM.
        eapply implM_embed_bind.
        { eapply BN_mod_mul_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)
            | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAi)| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAmK)| exact WRr| exact (proj1 WRr)
            | rewrite Ei; unfold RPool, ROne, NFIX; lia| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV1 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
        cbn [fst snd] in *. clear PRE3 KP.
        replace (ret_pc (Z_to_bv 64 0x151b54)) with (Z_to_bv 64 0x151b54) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RS11) as RS011.
        unfold implM. iprefix. step. if_false.
        step. step.
        rewrite ?(unsigned_lit wstart), ?(unsigned_lit (we + 1)) by (clear - WS WE WB; lia).
        try replace (wstart + - (we + 1)) with (wstart - (we + 1)) by (clear; lia).
        rewrite ?(bn_swrap32_small (wstart - (we + 1))) by (clear - WS WE WB; lia).
        ub_chk.
        step. try replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (wstart - (we + 1))) + 0)) with (wstart - (we + 1))
          by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616;
              rewrite bn_swrap32_mod by (clear - WS WE WB; lia); clear; lia).
        step. step. rewrite lts_signed by (clear - WS WE WB; lia).
        destruct (Z.ltb_spec (wstart - (we + 1)) 0) as [WLT|WGE]; cbn [negb].
        -
          step. ihere. to_implM. cbv beta iota. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
          unfold WINQ. exists m11, OW11. do 22 eexists. split; [reflexivity|]. cbn [snd]. split; [exact ENV11| exact LS11].
        -
          step. change (Z.land 1 1) with (Z.b2z (negb false)) || idtac.
          change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.b2z (negb false))).
          ihere. to_implM. cbv beta iota.
          eapply REC; [exact ENV11| exact LS11| exact LEN| eapply vtab_stable; [exact VT| exact RS011]| exact VL| exact WB| clear - WGE WF; lia| clear - WS WE; lia
            | exact HJ0| exact (ref_at_stable _ _ _ _ PL _ _ RS011 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS011 HApK)| exact (ref_at_stable _ _ _ _ PL _ _ RS011 HAmK)]. }

      unfold implM. iprefix.
      step. ub_chk.
      step. step. step.
      destruct start; cbn [negb Z.b2z].
      -
        rewrite tbind_bret. cbv beta.
        rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
        step. if_true.
        ihere. to_implM. eapply TAIL; [exact ENVK| exact LSK| apply refs_stable_refl].
      -
        unfold v_slt, c_lts. rewrite (lts_signed 0 (we + 1)) by (clear - WE WB; lia). rewrite (proj2 (Z.ltb_lt 0 (we + 1))) by (clear - WE; lia).
        rewrite (unsigned_lit 1) by lia. change (Z.land 1 1) with 1.
        step. if_false.
        replace (Z.to_nat (we + 1)) with (S (Z.to_nat we)) by (clear - WE; lia).
        replace (Z_to_bv 64 (we + 1)) with (Z_to_bv 64 (Z.of_nat (S (Z.to_nat we)))) by (f_equal; clear - WE; lia).
        ihere. to_implM. eapply implM_embed_bind.
        { eapply sqr_loop; [exact ENVK| exact LSK| exact HArK| exact HAmK| clear - WE WB; lia]. }
        cbv beta. intros [u1 bs1] st1 ms1 (m1 & OW1 & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV1 & LS1 & RS1). cbn [snd] in *.
        replace (Z.of_nat (S (Z.to_nat we))) with (we + 1) by (clear - WE; lia).
        eapply TAIL; [exact ENV1| exact LS1| exact RS1].
    Qed.

    Lemma wl_set : forall f, WLOOP f -> forall (wstart : Z) (start : bool) stK bsK mK OWK j0 ws vals addrs (window : Z)
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 <= wstart < Z.of_nat (S f) -> wstart < 2 ^ 24 -> j0 = le8 (Z_to_bv 64 (Z.lxor (SPv + -360) 18446744073709551615)) ->
      ref_at bsK OWK PL rr arr -> ref_at bsK OWK PL rp arp -> ref_at bsK OWK PL rm arm ->
      is_bit_set_pure (getbn rp bsK) wstart = true ->
      implM bgusegs (interp (embed (exp_window_loop (tree_ops bptr) MUL (S f) rp rr vals window wstart start bsK))) stK (WINQ j0 ws)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 window)
                  (Z_to_bv 64 (Z.b2z (negb start))) x25 x26 (Z_to_bv 64 31) t3 t4 t5 t6)
            F (Z_to_bv 64 0x151a4c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros f IH. intros until t6; intros ENV2 LS2 LEN VT VL WB WS WS24 HJ0 HArK HApK HAmK EB. kit.
      unfold implM. iprefix.
      destruct (window_scan (is_bit_set_pure (getbn rp bsK)) wstart (Z.to_nat (window - 1)) 1 1 0) as [wv we] eqn:SC.
      rewrite (ewl_set MUL f rp rr vals window wstart start bsK wv we EB SC). cbv beta.
      pose proof (window_scan_bnd (is_bit_set_pure (getbn rp bsK)) wstart (Z.to_nat (window - 1)) 1 1 0
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - WS; lia) ltac:(clear; cbn; lia)) as BND.
      rewrite SC in BND. destruct BND as (WE & WES & WV).
      replace (1 + Z.of_nat (Z.to_nat (window - 1))) with window in WE by (clear - WB; lia).
      step. if_true. step. step.
      step. rewrite (lts_signed window 2) by (clear - WB; lia). destruct (Z.ltb_spec window 2) as [KW|KW]; cbn [negb].
      -
        assert (W1 : window = 1) by (clear - KW WB; lia). subst window.
        change (Z.to_nat (1 - 1)) with 0%nat in SC. cbn [window_scan] in SC. injection SC as <- <-.
        step.
        ihere. to_implM.
        eapply (after_scan f IH wstart 1 0 start stK bsK mK OWK j0 ws vals addrs 1);
          [exact ENV2| exact LS2| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| clear; lia| clear - WS; lia| clear; cbn; lia| clear - WS; lia
          | exact HJ0| exact HArK| exact HApK| exact HAmK].
      -
        step. step.
        eapply (scan_loop (Z.to_nat (window - 1)) 1 1 0 stK bsK mK OWK (efr j0 ws) wstart window);
          [exact ENV2| exact LS2| exact HApK| clear; lia| clear - WB; lia| clear - KW WB; lia| clear - WB; lia| clear - WS WS24; lia| clear; lia| clear - WS; lia
          | clear; cbn; lia|].
        intros mK' wv' we' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x25' t3' t4' t5' t6' ENV' LS' SC'.
        rewrite SC in SC'. injection SC' as <- <-.
        assert (P7 : 2 ^ (we + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - WE WB; lia).
        assert (SHR : 0 <= Z.shiftr wv 1 < 2 ^ 7) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 1) with 2; clear - WV P7; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
        step. rewrite (unsigned_lit wv) by (clear - WV P7; lia). rewrite (bn_swrap32_small wv) by (clear - WV P7; lia).
        rewrite (bn_swrap32_small (Z.shiftr wv 1)) by (clear - SHR; lia).
        step.
        ihere. to_implM.
        eapply (after_scan f IH wstart wv we start stK bsK mK' OWK j0 ws vals addrs window);
          [exact ENV'| exact LS'| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| exact WE| exact WES| exact WV| clear - WS WE; lia
          | exact HJ0| exact HArK| exact HApK| exact HAmK].
    Qed.

    Lemma window_loop : forall f, WLOOP f.
    Proof.
      induction f as [|f IH]; unfold WLOOP; intros until t6; intros ENVK LSK LEN VT VL WB WS WS24 HJ0 HArK HApK HAmK; [exfalso; clear - WS; lia|]. kit.

      destruct (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rp arp ENVK LSK HApK NROp)
        as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
      pose proof ENVK as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OKp3.
      unfold implM. iprefix.
      step. step. step.
      eapply evt_cut.
      { eapply (BN_is_bit_set_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arp) (D := Dp) (b := getbn rp bsK) (n := wstart);
          [exact BNp | exact ALp | exact UPp | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS96; lia | exact MIK
          | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp FBlo FBsp CS96 LOF; lia | reflexivity | reflexivity | clear - WS WS24; lia]. }
      clear STK MIK.
      intros ms2 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *.
      destruct (KBELOW _ _ _ _ m2 _ 16 ENVK LSK ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear MUc WMc MIc STc BNp Up.
      replace (ret_pc (Z_to_bv 64 1382988)) with (Z_to_bv 64 1382988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (is_bit_set_pure (getbn rp bsK) wstart) eqn:EB; cbn [Z.b2z].
      -
        ihere. to_implM.
        eapply (wl_set f IH wstart start stK bsK m2 OWK j0 ws vals addrs window);
          [exact ENV2| exact LS2| exact LEN| exact VT| exact VL| exact WB| exact WS| exact WS24| exact HJ0| exact HArK| exact HApK| exact HAmK| exact EB].
      -
        rewrite (ewl_clear MUL f rp rr vals window wstart start bsK EB). cbv beta.
        step. if_false.
        assert (NEXT : forall st1 bs1 m1 OW1 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x25' x26' t3' t4' t5' t6' : word),
              kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) st1 bs1 m1 OW1 -> lib_state bs1 m1 OW1 PL EA -> refs_stable bsK OWK bs1 OW1 ->
              implM bgusegs (interp (embed ((if wstart =? 0 then bret (tree_ops bptr) tt
                                             else exp_window_loop (tree_ops bptr) MUL f rp rr vals window (wstart - 1) start) bs1))) st1 (WINQ j0 ws)
                (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                          (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 wstart) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 window)
                          (Z_to_bv 64 (Z.b2z (negb start))) x25' x26' (Z_to_bv 64 31) t3' t4' t5' t6')
                    F (Z_to_bv 64 0x151a70) fc None m1 (seg_rom bgusegs))).
        { intros until t6'. intros ENV1 LS1 RS1.
          unfold implM. iprefix.
          destruct (Z.eqb_spec wstart 0) as [W0|WN0].
          -
            subst wstart.
            step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear; lia); zify_cond KZ; try (exfalso; clear - KZ; lia). step. step.
            ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
            unfold WINQ. exists m1, OW1. do 22 eexists. split; [reflexivity|]. cbn [snd]. split; [exact ENV1| exact LS1].
          - step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - WS WS24; lia); zify_cond KZ; try (exfalso; clear - KZ WN0 WS WS24; lia).
            step. rewrite (swrap32_wrap64 wstart (-1)) by (clear - WS WS24; lia). replace (wstart + -1) with (wstart - 1) by (clear; lia).
            ub_chk. step. step.
            ihere. to_implM. change (if start then false else true) with (negb start).
            eapply IH; [exact ENV1| exact LS1| exact LEN| eapply vtab_stable; [exact VT| exact RS1]| exact VL| exact WB| clear - WS WN0; lia| clear - WS24; lia| exact HJ0
              | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HApK)| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAmK)]. }
        destruct start; cbn [negb Z.b2z].
        +
          rewrite tbind_bret. cbv beta.
          step. if_true.
          ihere. to_implM. eapply NEXT; [exact ENV2| exact LS2| apply refs_stable_refl].
        +
          step. if_false.
          do 5 step. step.
          destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv3 & PRE3). ihere. to_implM.
          eapply implM_embed_bind.
          { eapply BN_mod_mul_walk; [exact PRE3| reflexivity| first [rewrite ESP; exact FB16 | rewrite unsigned_lit by lia; exact FB16]| exact HArK| exact HArK| exact HArK| exact HAmK| exact WRr| exact (proj1 WRr)| exact (proj1 WRr)| exact NROm| exact HPC
              | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
          cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
          destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
          cbn [fst snd] in *. clear PRE3 KP.
          replace (ret_pc (Z_to_bv 64 1383020)) with (Z_to_bv 64 1383020) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          unfold implM. iprefix. step. if_false.
          ihere. to_implM. eapply NEXT; [exact ENV11| exact LS11| exact RS11].
    Qed.

    Lemma L_rest : forall stK bsK mK OWK j0 ws vals addrs (bits window : Z)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 < bits < 2 ^ 24 ->
      implM bgusegs (interp (embed ((if (rr =? rp)%nat then (fun _ : bstate bptr => TUnr)
                                     else fun s12 : bstate bptr => tbind (BN_one (tree_ops bptr) rr s12)
                                            (fun p0 : unit * bstate bptr => exp_window_loop (tree_ops bptr) MUL (Z.to_nat bits) rp rr vals window (bits - 1) true (snd p0))) bsK)))
        stK (WINQ (le8 (Z_to_bv 64 (Z.lxor (SPv + -360) 18446744073709551615))) ws)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) x21 (Z_to_bv 64 bits) (Z_to_bv 64 window) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x151a0c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN VT VL WB BITS. kit.
      pose proof ENVK as (HEAPK & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (RH_nodup_l _ _ _ _ HEAPK) as NDK. pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as PARTSK.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAr) as HArK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      unfold implM. iprefix.
      step. replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 bits) + -1)) with (bits - 1)
        by (rewrite (unsigned_lit bits) by (clear - BITS; lia); rewrite bn_swrap32_small by (clear - BITS; lia); clear; lia).
      ub_chk.
      step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - ArR ApR; lia); zify_cond KE.
      {
        assert (Erp : rr = rp).
        { destruct (Nat.eq_dec rr rp) as [E|NE]; [exact E| exfalso].
          pose proof (struct_disj stK OWK LB mK HEAPK bsK PL EA _ _ PARTSK FROK rr rp arr arp NE HArK HApK) as D. clear - D KE. lia. }
        replace ((rr =? rp)%nat) with true by (symmetry; apply Nat.eqb_eq; exact Erp).
        ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      assert (NErp : rr <> rp) by (intros E; rewrite <- E in HApK; pose proof (ref_at_fun _ _ _ _ _ _ NDK HArK HApK) as EA_; clear - EA_ KE; lia).
      replace ((rr =? rp)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NErp).

      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { unfold BN_one. eapply BN_set_word_walk; [exact PRE3| reflexivity| exact HArK| exact (hpl_wref _ _ WRr)| unfold BW; clear; lia| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x151a24)) with (Z_to_bv 64 0x151a24) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.

      step. step. step.
      pose proof ENV11 as (HEAP11 & _ & ST11 & (errv11 & ERR11) & MI11 & _ & _ & _ & _ & FR11 & _).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS11) as PARTS11.
      unfold efr in FR11.
      assert (FRx : rw_cells bgusegs m11 (SPv + -368) (CB 8 j0 :: CB 256 (u64s ws) :: saved)) by (replace (SPv + -368) with FB by (clear - ESPV; lia); exact FR11).
      clear FR11.
      pose proof (munch_refl [(FB, FB + 8)]%Z m11) as MU. pose proof (wmono_refl bgusegs m11) as WM.
      apply hide_intro in ERR11.
      step. apply hide_elim in ERR11.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m12 end.
      eapply (rw_cells_transport bgusegs _ m11 m12) in ERR11; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]].
      rewrite (unsigned_lit (SPv + -360)) in FRx by lia.
      assert (FRn : rw_cells bgusegs m12 FB (efr (le8 (Z_to_bv 64 (Z.lxor (SPv + -360) 18446744073709551615))) ws)).
      { unfold efr. replace FB with (SPv + -368) by (clear - ESPV; lia).
        destruct FRx as [[W0 Bd] Wr]. split; [split|].
        - cbn [cells_wf cell_wf] in *. split; [apply length_le8| exact (proj2 W0)].
        - exact Bd.
        - exact Wr. }
      clear FRx.
      assert (HWL : Forall (w_lib bs4 OW11 PL lo SPv) [(FB, FB + 8)]) by (constructor; [left; cbn; lia| constructor]).
      pose proof (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ st4 bs4 m11 m12 OW11 _ errv11
                    ENV11 PARTS11 MU WM HWL ST11 ERR11 ltac:(the_mi) FRn ltac:(cbn; lia)) as ENV12.
      assert (LS12 : lib_state bs4 m12 OW11 PL EA).
      { assert (WOK : Forall (w_ok OW11 LB bs4 PL EA SPv []) [(FB, FB + 8)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
        exact (lib_state_frame st4 LB _ _ [] bs4 m11 m12 OW11 PL EA _ HEAP11 LS11 MU WM FROK WOK). }
      clear ST11 MU WM HWL ERR11 FRn.
      step. step.
      ihere. to_implM.
      eapply (window_loop (Z.to_nat bits) (bits - 1) true st4 bs4 m12 OW11 _ ws vals addrs window);
        [exact ENV12| exact LS12| exact LEN| eapply vtab_stable; [exact VT| exact RS11]| exact VL| exact WB| clear - BITS; lia| clear - BITS; lia
        | reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HApK)| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAmK)].
    Qed.

    Lemma vtab_one : forall bsK OWK ws v0 av0 vi, nth_error ws 0 = Some (Z_to_bv 64 av0) -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
      vtab bsK OWK ws [v0] [av0].
    Proof.
      intros bsK OWK ws v0 av0 vi W0 HAv Ev AvR. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by (clear - Hi; lia). subst i. cbn [nth].
      split; [exact W0|]. split; [exact HAv|]. split; [exists vi; exact Ev| exact AvR].
    Qed.

    Lemma L_table : forall stK bsK mK OWK j0 ws (bits window : Z) (d v0 : bnref) (ad av0 : Z) (di vi : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 1 < window <= 6 ->
      implM bgusegs (interp (embed (exp_table (tree_ops bptr) MUL window v0 d bsK))) stK (TABLEQ j0 bits window)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 window) (Z_to_bv 64 av0) x23 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x151998) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR WB. kit.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
      assert (NROv : v0 <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; lia).
      assert (P2 : 2 <= 2 ^ (window - 1) <= 32).
      { split; [change 2 with (2 ^ 1) at 1| change 32 with (2 ^ 5)]; apply Z.pow_le_mono_r; clear - WB; lia. }
      unfold exp_table. replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia).
      unfold bbind. cbn [bind tree_ops].
      replace (Z.to_nat (2 ^ (window - 1)) - 1)%nat with (S (Z.to_nat (2 ^ (window - 1)) - 2)) by (clear - P2; lia).
      unfold implM. iprefix.
      do 5 step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_mod_mul_walk; [exact PRE3| reflexivity| first [rewrite ESP; exact FB16 | rewrite unsigned_lit by lia; exact FB16]| exact HAd| exact HAv| exact HAv| exact HAmK| rewrite Ed; apply hpl_pool| exact NROv| exact NROv| exact NROm| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x1519b0)) with (Z_to_bv 64 0x1519b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.
      step. step. step. step.
      replace (window + -1) with (window - 1) by (clear; lia).
      replace (SPv + -352) with (FB + 8 + 8 * Z.of_nat (length [v0])) by (cbn [length]; clear - ESPV; lia).
      replace (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length [v0]) + 1)) by reflexivity.
      ihere. to_implM.
      eapply (table_loop (Z.to_nat (2 ^ (window - 1)) - 2) [v0] [av0] st4 bs4 m11 OW11 j0 ws bits window 31 d ad);
        [exact ENV11| exact LS11| exact LEN| | cbn [length]; clear; lia| cbn [length]; clear - P2; lia| exact WB| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAd)| exact NROd
        | exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAmK)| cbn [length]; clear; lia].
      exact (vtab_one bs4 OW11 ws v0 av0 vi W0 (ref_at_stable _ _ _ _ PL _ _ RS11 HAv) Ev AvR).
    Qed.

    Definition WINQX (j0 : list byte) (r : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop := exists j0' ws', WINQ j0' ws' r st' ms'.

    Lemma L_nonzero : forall stK bsK mK OWK j0 ws (bits : Z) (d v0 : bnref) (ad av0 : Z) (di vi : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x25 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efr j0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 0 < bits < 2 ^ 24 ->
      implM bgusegs (interp (embed (tbind (tbind (exp_table (tree_ops bptr) MUL (window_bits bits) v0 d bsK)
                                             (fun p : list bnref * bstate bptr =>
                                                (if (rr =? rp)%nat then (fun _ : bstate bptr => TUnr)
                                                 else fun s12 : bstate bptr => tbind (BN_one (tree_ops bptr) rr s12)
                                                        (fun p0 : unit * bstate bptr => exp_window_loop (tree_ops bptr) MUL (Z.to_nat bits) rp rr (fst p) (window_bits bits) (bits - 1) true (snd p0)))
                                                  (snd p)))
                                      (fun p : unit * bstate bptr => BN_CTX_end (tree_ops bptr) (snd p))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 ad) (Z_to_bv 64 bits) x23 (Z_to_bv 64 av0) x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15195c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR BITS.
      eapply implM_embed_bind with (Q1 := WINQX j0).
      2: { cbv beta. intros [u bsW] stW msW (jW & wsW & mW & OWW & R).
           destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVW & LSW). cbn [snd] in *.
           eapply simple_exit; [exact ENVW| exact LSW]. }
      remember (window_bits bits) as window eqn:EW.
      assert (REST : forall (r : list bnref * bstate bptr) stT msT, 1 <= window <= 6 -> TABLEQ j0 bits window r stT msT ->
                implM bgusegs (interp (embed ((if (rr =? rp)%nat then (fun _ : bstate bptr => TUnr)
                                               else fun s12 : bstate bptr => tbind (BN_one (tree_ops bptr) rr s12)
                                                      (fun p0 : unit * bstate bptr => exp_window_loop (tree_ops bptr) MUL (Z.to_nat bits) rp rr (fst r) window (bits - 1) true (snd p0)))
                                                (snd r)))) stT (WINQX j0) msT).
      { intros [vals bsT] stT msT WB (wsT & addrsT & mT & OWT & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVT & LST & LENT & VTT & VLT). cbn [fst snd] in *.
        eapply implM_mono; [eapply (L_rest stT bsT mT OWT j0 wsT vals addrsT bits window); [exact ENVT| exact LST| exact LENT| exact VTT| exact VLT| exact WB| exact BITS]|].
        cbv beta. intros r st' ms' PO. unfold WINQX. eexists. exists wsT. exact PO. }
      assert (TBL : forall (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x23' x26' x27' t3' t4' t5' t6' : word), 1 < window <= 6 ->
                implM bgusegs (interp (embed (tbind (exp_table (tree_ops bptr) MUL window v0 d bsK)
                                             (fun p : list bnref * bstate bptr =>
                                                (if (rr =? rp)%nat then (fun _ : bstate bptr => TUnr)
                                                 else fun s12 : bstate bptr => tbind (BN_one (tree_ops bptr) rr s12)
                                                        (fun p0 : unit * bstate bptr => exp_window_loop (tree_ops bptr) MUL (Z.to_nat bits) rp rr (fst p) window (bits - 1) true (snd p0)))
                                                  (snd p))))) stK (WINQX j0)
                  (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 arp) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 window) (Z_to_bv 64 av0) x23' x26' x27' t3' t4' t5' t6')
                      F (Z_to_bv 64 0x151998) fc None mK (seg_rom bgusegs))).
      { intros until t6'. intros WB.
        eapply implM_embed_bind; [eapply (L_table stK bsK mK OWK j0 ws bits window d v0 ad av0 di vi); [exact ENVK| exact LSK| exact LEN| exact W0| exact HAd| exact Ed| exact HAv| exact Ev| exact AvR| exact WB]|].
        cbv beta. intros r stT msT PO. eapply REST; [clear - WB; lia| exact PO]. }
      unfold window_bits in EW.
      unfold implM. iprefix.
      step. step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 671 bits) as [B1|B1]; cbn [negb].
      { step. step. subst window. ihere. to_implM. eapply TBL. clear; lia. }
      step. step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 239 bits) as [B2|B2]; cbn [negb].
      { step. step. subst window. ihere. to_implM. eapply TBL. clear; lia. }
      step. step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 79 bits) as [B3|B3]; cbn [negb].
      { step. step. subst window. ihere. to_implM. eapply TBL. clear; lia. }
      step. step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 23 bits) as [B4|B4]; [if_false| if_true].
      { step. subst window. ihere. to_implM. eapply TBL. clear; lia. }

      step. subst window.
      replace (exp_table (tree_ops bptr) MUL 1 v0 d bsK) with (bret (tree_ops bptr) [v0] bsK) by reflexivity.
      rewrite tbind_bret. cbv beta. cbn [fst snd].
      ihere. to_implM.
      eapply implM_mono; [eapply (L_rest stK bsK mK OWK j0 ws [v0] [av0] bits 1);
                           [exact ENVK| exact LSK| exact LEN| exact (vtab_one bsK OWK ws v0 av0 vi W0 HAv Ev AvR)| reflexivity| clear; lia| exact BITS]|].
      cbv beta. intros r st' ms' PO. unfold WINQX. eexists. exists ws. exact PO.
    Qed.
  End Body.

  Lemma BN_mod_exp_simple_walk : exp_stmt BN_MOD_EXP_SIMPLE BN_MOD_EXP_SIMPLE_STACK (BN_mod_exp_simple (tree_ops bptr)) None.
  Proof.
    unfold exp_stmt. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa HAp HAm WRr NROa NROp NROm HPC -> -> -> -> -> _.
    unfold BN_MOD_EXP_SIMPLE_STACK, BN_MOD_EXP_SIMPLE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    assert (ArR : 0 < arr < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAr (proj1 WRr)) as (X & Y & _); clear - X Y SPR; lia).
    assert (AmR : 0 < arm < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAm NROm) as (X & Y & _); clear - X Y SPR; lia).
    assert (ApR : 0 < arp < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAp NROp) as (X & Y & _); clear - X Y SPR; lia).
    pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_mod_exp_simple, any_consttime, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
    unfold implM. iprefix.

    carve_frame 368%nat ST. do 22 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -368, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -368, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -368) by lia.
    assert (FBsp : bv_unsigned sp + -368 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (kenv_open LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL FROK) as KOPEN.
    pose proof (kenv_open_u LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL FROK) as KOPENU.
    pose proof (kenv_below LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW.
    assert (LOF : lo <= bv_unsigned sp + -368 - CS) by lia.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368)) = bv_unsigned sp + -368) by (apply unsigned_lit; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR LS.

    destruct (KOPENU _ _ _ _ _ rp arp ENV LS1 HAp NROp) as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & _).
    set (bp := getbn rp bs) in *.
    assert (FLp : 0 <= bn_flags bp <= 1) by (destruct OKp4 as [E|E]; rewrite E; lia).
    assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV as (_ & _ & ST1 & _ & MI1 & _).
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -368))) with (lo := lo) (A := arp) (D := Dp) (b := bp);
        [exact BNp | exact ALp | clear - FLp; lia | rewrite ESP; exact ST1 | rewrite ESP; clear - LOF CS96; lia | exact MI1 | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST1 MI1.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTp.
    replace (bv_unsigned sp + -368 - 16) with (bv_unsigned sp + -368 - 16) in MUc by reflexivity.
    destruct (KBELOW _ _ _ _ m2 _ 16 ENV LS1 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear ENV LS1 MUc WMc MIc STc BNp Up.
    replace (ret_pc (Z_to_bv 64 1382348)) with (Z_to_bv 64 1382348) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_false.

    destruct (KOPENU _ _ _ _ _ ra_ ara ENV2 LS2 HAa NROa) as (Da & BNa & Ua & (OKa1 & OKa2 & OKa3 & OKa4) & _ & SEPa & SEPDa & _ & ALa & _).
    set (ba := getbn ra_ bs) in *.
    assert (FLa : 0 <= bn_flags ba <= 1) by (destruct OKa4 as [E|E]; rewrite E; lia).
    assert (CTa : Z.land (bn_flags ba) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV2 as (_ & _ & ST2 & _ & MI2 & _).
    step. step. step.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -368))) with (lo := lo) (A := ara) (D := Da) (b := ba);
        [exact BNa | exact ALa | clear - FLa; lia | rewrite ESP; exact ST2 | rewrite ESP; clear - LOF CS96; lia | exact MI2 | rewrite ESP; clear - SEPa FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST2 MI2.
    intros ms3 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTa.
    destruct (KBELOW _ _ _ _ m3 _ 16 ENV2 LS2 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV3 & LS3). clear ENV2 LS2 MUc WMc MIc STc BNa Ua.
    replace (ret_pc (Z_to_bv 64 1382364)) with (Z_to_bv 64 1382364) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_false.

    destruct (KOPENU _ _ _ _ _ rm arm ENV3 LS3 HAm NROm) as (Dm & BNm & Um & (OKm1 & OKm2 & OKm3 & OKm4) & _ & SEPm & SEPDm & _ & ALm & _).
    set (bm := getbn rm bs) in *.
    assert (FLm : 0 <= bn_flags bm <= 1) by (destruct OKm4 as [E|E]; rewrite E; lia).
    assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV3 as (_ & _ & ST3 & _ & MI3 & _).
    step. step. step.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -368))) with (lo := lo) (A := arm) (D := Dm) (b := bm);
        [exact BNm | exact ALm | clear - FLm; lia | rewrite ESP; exact ST3 | rewrite ESP; clear - LOF CS96; lia | exact MI3 | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST3 MI3.
    intros ms4 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTm.
    destruct (KBELOW _ _ _ _ m4 _ 16 ENV3 LS3 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV4 & LS4). clear ENV3 LS3 MUc WMc MIc STc BNm Um.
    replace (ret_pc (Z_to_bv 64 1382380)) with (Z_to_bv 64 1382380) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_true.
    unfold has_flag, BN_FLG_CONSTTIME. fold bp ba bm. rewrite CTa, CTp, CTm. cbn [Z.eqb negb orb andb].

    step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - ArR AmR; lia); zify_cond KE.
    {
      assert (Erm : rr = rm).
      { destruct (Nat.eq_dec rr rm) as [E|NE]; [exact E| exfalso].
        pose proof ENV4 as (HEAP4 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4.
        pose proof (struct_disj s OW LB m4 HEAP4 bs PL EA _ _ PARTS4 FROK rr rm arr arm NE HAr HAm) as D. clear - D KE. lia. }
      subst rm. rewrite Nat.eqb_refl. ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    assert (NErm : rr <> rm) by (intros E; subst rm; pose proof (ref_at_fun _ _ _ _ _ _ ND HAr HAm) as EA_; clear - EA_ KE; lia).
    replace ((rr =? rm)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NErm).

    destruct (KOPENU _ _ _ _ _ rp arp ENV4 LS4 HAp NROp) as (Dp' & BNp & Up & _ & _ & _ & SEPDp' & _ & ALp' & UPp'). fold bp in BNp, Up, SEPDp', UPp'.
    pose proof ENV4 as (_ & _ & ST4 & _ & MI4 & _).
    step. step.
    eapply evt_cut.
    { eapply (BN_num_bits_spec _ (Z_to_bv 64 (bv_unsigned sp + -368))) with (lo := lo) (A := arp) (D := Dp') (b := bp);
        [exact BNp | exact ALp' | exact UPp' | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; unfold BG_DMAX in OKp3; lia | clear - FLp; lia | exact CTp
        | rewrite ESP; exact ST4 | rewrite ESP; clear - LOF CS96; lia | exact MI4
        | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp' FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST4 MI4.
    intros ms5 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m5 _ 128 ENV4 LS4 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV5 & LS5). clear ENV4 LS4 MUc WMc MIc STc BNp Up.
    replace (ret_pc (Z_to_bv 64 1382512)) with (Z_to_bv 64 1382512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (num_bits_pure_range bp OKp1) as BITS. unfold BG_DMAX in OKp3.
    replace (getbn rp bs) with bp by reflexivity. rewrite CTp. cbn [Z.eqb negb tbind]. cbv beta.
    set (bits := num_bits_pure bp) in *.
    step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - BITS; lia); zify_cond KB.
    {
      cbn [fst snd]. rewrite KB. cbn [Z.eqb]. unfold exp_bits0, bbind, bget. cbn [bind ret tree_ops tbind fst snd].
      replace (getbn rm bs) with bm by reflexivity.
      destruct (KOPENU _ _ _ _ _ rm arm ENV5 LS5 HAm NROm) as (Dm' & BNm & Um & _ & _ & _ & SEPDm' & _ & ALm' & UPm'). fold bm in BNm, Um, SEPDm', UPm'.
      pose proof ENV5 as (_ & _ & ST5 & _ & MI5 & _).
      step. step. step. step.
      eapply evt_cut.
      { eapply (BN_abs_is_word_spec _ (Z_to_bv 64 (bv_unsigned sp + -368))) with (lo := lo) (A := arm) (D := Dm') (b := bm);
          [exact BNm | exact ALm' | exact UPm' | exact Um | exact OKm1 | exact OKm2 | clear - OKm3; unfold BG_DMAX in OKm3; lia
          | rewrite ESP; exact ST5 | rewrite ESP; clear - LOF CS96; lia | exact MI5
          | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDm' FBlo FBsp CS96 LOF; lia | reflexivity]. }
      clear ST5 MI5.
      intros ms6 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *. rewrite (unsigned_lit 1) by lia.
      destruct (KBELOW _ _ _ _ m6 _ 16 ENV5 LS5 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV6 & LS6). clear ENV5 LS5 MUc WMc MIc STc BNm Um.
      replace (ret_pc (Z_to_bv 64 1382664)) with (Z_to_bv 64 1382664) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (abs_is_word_pure bm 1); cbn [Z.b2z].
      -
        step. if_false. step. step.
        eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
          [clear - LOF CS96; lia | reflexivity | exact ENV6 | exact LS6 | exact HAr | exact (hpl_wref _ _ WRr) |].
        intros m7 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV7 LS7.
        replace (ret_pc (Z_to_bv 64 1382676)) with (Z_to_bv 64 1382676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        ihere. to_implM. unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
        pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m _ _ _ _ _ ENV7) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
        step. step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
        apply evt_done. unfold bn_post. do 15 eexists. exists m7, OW, PL, errvF. split; [reflexivity|]. cbn [fst snd].
        split; [exact F1|]. split; [exact LS7|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
        split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
      -
        step. if_true. step. step.
        pose proof ENV6 as (_ & _ & ST6 & _ & _ & _ & _ & _ & _ & FR6 & _).
        do 13 step. release_frame FR6 ST6 (bv_unsigned sp). step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
        ihere. to_implM. unfold BN_one.
        destruct (kenv_tail LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK
                    _ _ _ mX OW CS errv ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1)
                    ENV6 LS6 ST6 ltac:(clear - LO; lia)) as [[errvX PREX] POSTX].
        rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
        eapply implM_mono; [eapply BN_set_word_walk; [exact PREX| reflexivity| exact HAr| exact (hpl_wref _ _ WRr)| unfold BW; lia| reflexivity| reflexivity]|].
        cbv beta. intros r st' ms' PO. apply POSTX. revert PO. unfold bn_post.
        intros (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m9 & OW9 & PL9 & errv9 & -> & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (E1 & E2 & _)).
        do 15 eexists. exists m9, OW9, PL9, errv9. split; [reflexivity|].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
        split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact E1| exact E2]. }

    cbn [fst snd]. replace (bits =? 0) with false by (symmetry; apply Z.eqb_neq; exact KB).
    step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_start_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & OW7 & -> & KP & (_ & INCL7)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV7 & LS7). pose proof KP as RS7; apply kpost_refs in RS7.
    cbn [fst snd] in *. clear PRE1 KP ENV5 LS5.
    replace (ret_pc (Z_to_bv 64 1382528)) with (Z_to_bv 64 1382528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV7 LS7 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [d bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & (di & Ed) & (ad & HAd & ->) & INCL8)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV7 KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
    cbn [fst snd] in *. clear PRE2 KP ENV7 LS7.
    replace (ret_pc (Z_to_bv 64 1382536)) with (Z_to_bv 64 1382536) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV8 LS8 LOF) as (errv3 & PRE3).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE3| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [v0 bs3] st3 ms3 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW9 & -> & KP & (_ & (vi & Ev0) & (av0 & HAv0 & ->) & INCL9)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV8 KP) as (ENV9 & LS9). pose proof KP as RS9; apply kpost_refs in RS9.
    cbn [fst snd] in *. clear PRE3 KP ENV8 LS8.
    replace (ret_pc (Z_to_bv 64 1382548)) with (Z_to_bv 64 1382548) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (refs_stable_trans _ _ _ _ _ _ RS7 (refs_stable_trans _ _ _ _ _ _ RS8 RS9)) as RS09.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS09 HAr) as HAr9. pose proof (ref_at_stable _ _ _ _ PL _ _ RS09 HAa) as HAa9.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS09 HAp) as HAp9. pose proof (ref_at_stable _ _ _ _ PL _ _ RS09 HAm) as HAm9.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS9 HAd) as HAd9.
    pose proof ENV9 as (HEAP9 & _). pose proof (RH_nodup_l _ _ _ _ HEAP9) as ND9. pose proof (lib_state_h_parts _ _ _ _ _ _ LS9) as PARTS9.
    assert (FROK9 : frames_ok PL (bv_unsigned sp + -368) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
    assert (NROv0 : v0 <> ROne) by (rewrite Ev0; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP9 PARTS9 FROK9 HAv0 NROv0) as (Av0 & AvC & _).
    assert (AvR : 0 < av0 < 2^64) by (clear - Av0 AvC SPR; lia). clear AvC.

    pose proof ENV9 as (_ & _ & ST9 & _ & MI9 & _ & _ & _ & _ & FR9 & _).
    pose proof (munch_refl [(bv_unsigned sp + -368 + 8, bv_unsigned sp + -368 + 16)]%Z m9) as MU. pose proof (wmono_refl bgusegs m9) as WM.
    unfold implM. iprefix. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
    destruct (val_frame_init bgusegs m10 _ _ _ _ _ FR9) as (ws0 & LEN0 & WS0 & FR10).
    assert (HWL : Forall (w_lib bs3 OW9 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -368 + 8, bv_unsigned sp + -368 + 16)]) by (constructor; [left; cbn; lia| constructor]).
    pose proof ENV9 as (_ & _ & _ & (errv9 & ERR9) & _).
    eapply (rw_cells_transport bgusegs _ m9 m10) in ERR9; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]].
    pose proof (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ st3 bs3 m9 m10 OW9 _ errv9
                  ENV9 PARTS9 MU WM HWL ST9 ERR9 ltac:(the_mi) FR10 ltac:(cbn; lia)) as ENV10.
    assert (LS10 : lib_state bs3 m10 OW9 PL EA).
    { assert (WOK : Forall (w_ok OW9 LB bs3 PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -368 + 8, bv_unsigned sp + -368 + 16)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
      exact (lib_state_frame st3 LB _ _ [] bs3 m9 m10 OW9 PL EA _ HEAP9 LS9 MU WM FROK WOK). }
    clear ST9 MI9 FR9 MU WM HWL ERR9 ENV9 LS9 FR10 HEAP9 ND9 PARTS9.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].

    step. step. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV10 LS10 LOF) as (errv4 & PRE4).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_nnmod_walk; [exact PRE4| reflexivity| exact HAv0| exact HAa9| exact HAm9| rewrite Ev0; apply hpl_pool| exact NROa| exact NROm| exact HPC
        | reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV10 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
    cbn [fst snd] in *. clear PRE4 KP ENV10 LS10.
    replace (ret_pc (Z_to_bv 64 1382576)) with (Z_to_bv 64 1382576) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS09 RS11) as RS011.

    unfold implM. iprefix. step. if_false. step. step.
    destruct (KOPEN _ _ _ _ _ v0 av0 ENV11 LS11 (ref_at_stable _ _ _ _ PL _ _ RS11 HAv0) NROv0) as (Dv & BNv & Uv & (OKv1 & OKv2 & OKv3 & OKv4) & _ & SEPv & SEPDv & _).
    pose proof ENV11 as (_ & _ & ST11 & _ & MI11 & _).
    eapply evt_cut.
    { eapply (BN_is_zero_spec _ (Z_to_bv 64 (bv_unsigned sp + -368))) with (lo := lo) (A := av0) (D := Dv) (b := getbn v0 bs4);
        [exact BNv | exact (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENV11) (lib_state_h_parts _ _ _ _ _ _ LS11) (ref_at_stable _ _ _ _ PL _ _ RS11 HAv0) NROv0)
        | clear - OKv2 OKv3; unfold BG_DMAX in OKv3; lia | rewrite ESP; exact ST11 | rewrite ESP; clear - LOF CS96; lia | exact MI11
        | rewrite ESP; clear - SEPv FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST11 MI11.
    intros ms12 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m12 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m12 _ 16 ENV11 LS11 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV12 & LS12). clear ENV11 LS11 MUc WMc MIc STc BNv Uv.
    replace (ret_pc (Z_to_bv 64 1382588)) with (Z_to_bv 64 1382588) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top (getbn v0 bs4)) 0) as [TZ|TNZ]; cbn [Z.b2z].
    {
      step. if_false. step. step.
      unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
      eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
        [clear - LOF CS96; lia | reflexivity | exact ENV12 | exact LS12 | exact (ref_at_stable _ _ _ _ PL _ _ RS011 HAr) | exact (hpl_wref _ _ WRr) |].
      intros m13 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV13 LS13.
      replace (ret_pc (Z_to_bv 64 1382600)) with (Z_to_bv 64 1382600) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV13 LS13 LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE5| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m14 & OW14 & -> & KP & (_ & EOW14)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV13 KP) as (ENV14 & LS14). pose proof KP as RS14; apply kpost_refs in RS14.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 1383328)) with (Z_to_bv 64 1383328) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -368) s bs OW m _ _ _ _ _ ENV14) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      step. step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m14, OW14, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS14|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [first [eapply refs_stable_trans; [exact F9| exact RS14] | exact F9]|]. split; reflexivity. }

    step. if_true.
    ihere. to_implM.
    lazymatch type of ENV12 with kenv _ _ _ _ _ _ _ _ _ _ (CB 8 ?j0 :: _) _ _ _ _ =>
      pose proof (L_nonzero ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA rr rp rm arr arp arm ac qc (bv_unsigned sp + -368) (bv_unsigned sp)
                    ltac:(clear; lia) CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK LOF HPC HAr HAp HAm WRr NROp NROm ArR ApR ltac:(clear - SP16; Z.div_mod_to_equations; lia)
                    st4 bs4 m12 OW11 j0 ws0 bits d v0 ad av0 di vi) as LN
    end.
    unfold FINALQ in LN. rewrite (Z_to_bv_bv_unsigned sp) in LN.
    eapply LN; [exact ENV12| exact LS12| exact LEN0| exact WS0| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAd9)| exact Ed
               | exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAv0)| exact Ev0| exact AvR| clear - KB BITS OKp2 OKp3; lia].
  Qed.
End Proofs.
End WithCeiling0.
