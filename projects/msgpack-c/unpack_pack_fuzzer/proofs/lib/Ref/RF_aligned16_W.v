(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_MallocKit_AB A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Inv MI_Read MI_Geom MI_Pres2 MI_WFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_get_meta RF_malloc_top RMemEq.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv A_MallocFacts_inv2.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma impl_post_evt {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) t Q ms -> (forall r ms', Q r ms' -> evt rsegs (Q' r) ms') -> impl rsegs (at_node rsegs) t Q' ms.
Proof.
  revert Q Q' ms. induction t as [r|nd k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. exact (HQ _ _ H').
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implM_post_evt {A} (c : @M PState A) s (Q Q' : A -> PState -> machine_state -> Prop) ms :
  implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof.
  intros H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I| intros H'; exact (HQ _ _ _ H')].
Qed.

Lemma memeq_store_same m a bs :
  bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ 0x88000 <= a) -> memeq m (write_to_mem m (wa a) bs).
Proof.
  intros (H0 & H1 & HB) OUT. apply memeq_write_same; [exact H0| exact H1|].
  intros i Hi. rewrite <- (HB i Hi). symmetry. apply ref_mrd_overlay. rewrite wa_unsigned by lia. lia.
Qed.

Lemma store_ok_memeq m m' : memeq m m' -> forall n a, store_ok rsegs m' a n = store_ok rsegs m a n.
Proof.
  intros H. induction n as [|n IH]; intros a; [reflexivity|]. cbn [store_ok].
  rewrite (wview_memeq rsegs m m' a H). destruct (wview rsegs m a); [apply IH| reflexivity].
Qed.

Lemma wr_at_store_ok1 m a n x (j : nat) :
  wr_at rsegs m a n -> a <= x -> x + Z.of_nat j <= a + n -> store_ok rsegs m (wa x) j = true.
Proof. intros W H1 H2. replace x with (a + (x - a)) by lia. eapply wr_at_store_ok; [exact W| lia| lia]. Qed.

Lemma land_idx_code i k : 0 <= i < 32 -> 0 <= k -> Z.land (i + 32 * k) 31 = i.
Proof.
  intros Hi Hk. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
  replace (i + 32 * k) with (i + k * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma land_hi_lo i k : 0 <= i < 32 -> 0 <= k -> Z.land (k * 32) i = 0.
Proof.
  intros Hi Hk. apply Z.bits_inj'; intros j Hj. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec j 5) as [L|L].
  - change 32 with (2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 i j); [apply Bool.andb_false_r| lia|].
    destruct (Z.eq_dec i 0) as [->|NZ]; [cbn; lia|].
    apply (Z.lt_le_trans _ 5); [| lia]. apply Z.log2_lt_pow2; [lia|]. change (2^5) with 32. lia.
Qed.

Lemma lor_idx_code i k : 0 <= i < 32 -> 0 <= k -> Z.lor (k * 32) i = i + 32 * k.
Proof.
  intros Hi Hk. rewrite <- Z.lxor_lor by (apply land_hi_lo; lia). rewrite <- Z.add_nocarry_lxor by (apply land_hi_lo; lia). lia.
Qed.

Lemma swrap32_small z : -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros Hz. rewrite swrap32_eq'. rewrite Z.mod_small by lia. lia. Qed.

Lemma le1_b8 z : 0 <= z < 2^64 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof. intros Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma signed_lit_small z : 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite zb_signed, unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.

Ltac memeq_transport m m2 EQ :=
  repeat match goal with
  | H : ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs /\ ov_read_bytes rsegs m ?x2 ?n2 = Some ?bs2 |- _ =>
      rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ), <- (ov_read_bytes_memeq rsegs m m2 x2 n2 EQ) in H
  | H : rw_cells rsegs m ?A ?cs |- _ => apply (rw_cells_memeq rsegs m m2 A cs EQ) in H
  | H : bytes_at rsegs m ?A ?bs |- _ => apply (bytes_at_memeq rsegs m m2 A bs EQ) in H
  | H : _ -> bytes_at rsegs m ?A ?bs |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs) by (intros XX; apply (bytes_at_memeq rsegs m m2 A bs EQ), H, XX); clear H; rename H' into H
  | H : _ -> bytes_at rsegs m ?A ?bs /\ bytes_at rsegs m ?A2 ?bs2 |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs /\ bytes_at rsegs m2 A2 bs2)
        by (intros XX; destruct (H XX) as [X1 X2]; split; [apply (bytes_at_memeq rsegs m m2 A bs EQ), X1| apply (bytes_at_memeq rsegs m m2 A2 bs2 EQ), X2]); clear H; rename H' into H
  | H : wr_at rsegs m ?A ?n |- _ => apply (wr_at_memeq rsegs m m2 A n EQ) in H
  | H : _ -> wr_at rsegs m ?A ?n |- _ =>
      let H' := fresh H in assert (H' : _ -> wr_at rsegs m2 A n) by (intros XX; apply (wr_at_memeq rsegs m m2 A n EQ), H, XX); clear H; rename H' into H
  | H : stk rsegs m ?lo ?hi |- _ => apply (stk_memeq rsegs m m2 lo hi EQ) in H
  | H : mem_inv rsegs m |- _ => apply (mem_inv_memeq rsegs m m2 EQ) in H
  | H : memeq ?m0 m |- _ => lazymatch m0 with m => clear H | _ => apply (fun X => memeq_trans m0 m m2 X EQ) in H end
  end.

Ltac store_same BY :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let m2 := fresh "m" in let EQ := fresh "EQ" in
      assert (EQ : memeq m (write_to_mem m a bs)) by BY;
      set (m2 := write_to_mem m a bs) in *; clearbody m2;
      first [ match goal with H : memeq ?m0 m |- _ => lazymatch m0 with m => fail | _ => memeq_transport m m2 EQ; clear EQ end end
            | memeq_transport m m2 EQ; let nm := fresh "MEQ" in rename EQ into nm ];
      try clear m
  end.

Definition raligned_tail_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v a0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 a1 a2 a3 a4 a5 a6 a7 x28 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp x5 x6 x7 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ memeq m m'.

Section TAIL.
Variables (ra1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rav s0v s1v : word) (junk : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n G B AREA stride : Z) (i res off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word).
Let b3 := i + 32 * Z.min res 5.
Let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen.
Let E := B + 16 + stride * (i + 1) - 4.
Let POST := raligned_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v (Z_to_bv 64 P) F fc m.

Hypotheses (HN : 0 <= n < 2^48) (SPH : bv_unsigned sp + 32 <= 2^64)
    (FR : rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 s0v; C8 rav]).

Hypotheses (P0 : 0 < P) (AL : P mod 16 = 0) (PLO : 16 * off16 + 16 <= P) (PHI : P + 16 <= 2^64)
    (HB : B = P - 16 * off16 - 16) (HAREA : AREA = G - G mod 4096) (GLO : 0 <= G) (GHI : G + 40 <= 2^64)
    (R4 : ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0])
    (R3 : ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3])
    (R2 : ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)))
    (RG : ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)))
    (MM : rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)])
    (RA : ov_read_bytes rsegs m (wa AREA) 8 = Some (le8 (wz secret)))
    (RC : ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)))
    (RS : sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))))
    (IR : 0 <= i < 32) (O16 : 0 <= off16 < 65536) (AV : 0 <= avail < 2^32) (FRD : 0 <= freed < 2^32) (SE : 0 <= secret < 2^64)
    (LI : 0 <= last_idx < 32) (FB : 0 <= freeable < 2) (SC : 0 <= sc < 64) (ML : 0 <= maplen < 2^40)
    (Hidx : i <= last_idx) (Hav : Z.testbit avail i = false) (Hfr : Z.testbit freed i = false)
    (Hsc : sc < 48 -> size_class sc * i <= off16 < size_class sc * (i + 1))
    (Hsc63 : 48 <= sc -> sc = 63)
    (Hml : maplen <> 0 -> off16 <= maplen * 256 - 1).

Hypotheses (STR1 : maplen = 0 \/ last_idx <> 0 -> sc < 48 /\ stride = 16 * size_class sc)
    (STR2 : last_idx = 0 /\ maplen <> 0 -> stride = maplen * 4096 - 16).

Hypotheses (RES : 0 <= res < 2^31) (RESE : res = E - P - n) (HEAPR : E + 1 <= 0x10000 \/ 0x88000 <= P - 4) (EHI : E + 1 <= 2^64)
    (B3AT : bytes_at rsegs m (P - 3) [b8 b3]) (W3 : wr_at rsegs m (P - 3) 1)
    (RB0 : 0 < res -> bytes_at rsegs m (E - res) [b8 0]) (W0 : 0 < res -> wr_at rsegs m (E - res) 1)
    (RB5 : 5 <= res -> bytes_at rsegs m (E - 5) [b8 0] /\ bytes_at rsegs m (E - 4) (le4 (wz res))) (W5 : 5 <= res -> wr_at rsegs m (E - 5) 5).

Lemma tail_c48 : forall (x5 x6 x7 a1v a5v a6v a7v x28 : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp x5 x6 x7 (Z_to_bv 64 15) (Z_to_bv 64 n) (Z_to_bv 64 P) a1v (Z_to_bv 64 n) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x48110) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  assert (ELO : P + n <= E) by lia.

  assert (K44 : forall (m' : mem) (y5 y6 y7 a2v a4v b5v b6v b7v y28 : word) (code : Z),
    memeq m m' -> code = Z.min res 5 ->
    evt rsegs POST
      (MS (mkR ra1 sp gp tp y5 y6 y7 (Z_to_bv 64 15) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 code) a2v (Z_to_bv 64 (E + 4)) a4v b5v b6v b7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x4818c) fc None m' (seg_rom rsegs))).
  { intros m' y5 y6 y7 a2v a4v b5v b6v b7v y28 code MEQ' HC.
    memeq_transport m m' MEQ'.

    st1. st1. rewrite (land_idx_code i (Z.min res 5)) by lia. st1. st1.
    rewrite Z.shiftl_mul_pow2, !unsigned_lit, lor_idx_code by lia. change (2^5) with 32.
    replace (i + 32 * code) with b3 by (subst b3 code; lia).

    pose proof (wr_at_store_ok1 m' (P - 3) 1 (P - 3) 1 W3 ltac:(lia) ltac:(cbn; lia)) as SOK.
    st1. rewrite (le1_b8 b3) by lia. clear SOK.
    store_same ltac:(apply memeq_store_same; [exact B3AT| cbn; lia]).

    st1. st1. st1. st1. st1. st1. finish. }

  st1. st1. rewrite (swrap32_small (E - (n + P))) by lia. st1. if_cases K0; zify_cond K0.
  -
    replace (Z_to_bv 64 (E - (n + P))) with (Z_to_bv 64 (Z.min res 5)) by (f_equal; lia).
    eapply K44; [apply memeq_refl| reflexivity].
  -
    st1. rewrite (swrap32_small (E - (n + P))) by lia. st1. rewrite (swrap32_small (0 - (E - (n + P)))) by lia. st1. st1.
    pose proof (wr_at_store_ok1 m (E - res) 1 (E - res) 1 (W0 ltac:(lia)) ltac:(lia) ltac:(cbn; lia)) as SOK.
    st1. clear SOK. change (le1 (Z_to_bv 64 0)) with [b8 0].
    store_same ltac:(apply memeq_store_same; [replace (E + (0 - (E - (n + P)))) with (E - res) by lia; apply RB0; lia| cbn; lia]).

    st1. if_cases K1; zify_cond K1; rewrite signed_lit_small in K1 by lia.
    +
      st1. replace (Z_to_bv 64 (E - (n + P))) with (Z_to_bv 64 (Z.min res 5)) by (f_equal; lia).
      eapply K44; [exact MEQ| reflexivity].
    +
      destruct (RB5 ltac:(lia)) as [RB5a RB5b].
      pose proof (wr_at_store_ok1 _ (E - 5) 5 (E - 5) 1 (W5 ltac:(lia)) ltac:(lia) ltac:(cbn; lia)) as SOK.
      st1. clear SOK. change (le1 (Z_to_bv 64 0)) with [b8 0].
      store_same ltac:(apply memeq_store_same; [replace (E + 4 + -9) with (E - 5) by lia; exact RB5a| cbn; lia]).
      pose proof (wr_at_store_ok1 _ (E - 5) 5 (E - 4) 4 (W5 ltac:(lia)) ltac:(lia) ltac:(cbn; lia)) as SOK.
      st1. clear SOK. replace (Z_to_bv 64 (E - (n + P))) with (wz res) by (unfold wz; f_equal; lia).
      store_same ltac:(apply memeq_store_same; [replace (E + 4 + -8) with (E - 4) by lia; exact RB5b| rewrite length_le4; cbn; lia]).

      st1. eapply K44; [exact MEQ| lia].
Qed.

Lemma tail_b98 : forall (x7 x28 : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 87200) (Z_to_bv 64 (sc * 2)) x7 (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 n)
              (wz off16) (wz B) (wz mword) (Z_to_bv 64 last_idx) (Z_to_bv 64 (i + 1))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x48060) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }

  assert (KC4 : forall a3v t0v t3v,
    evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 (0 + - P)) (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 n)
              a3v (wz B) (wz mword) (Z_to_bv 64 stride) (Z_to_bv 64 (i + 1))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x4808c) fc None m (seg_rom rsegs))).
  { intros.

    st1. st1. st1. st1. st1. st1. st1.
    assert (ADJ : Z.land 15 (bv_unsigned (Z_to_bv 64 (0 + - P))) = 0).
    { rewrite unsigned_lit_wrap, Z.land_comm. change 15 with (2^4 - 1). rewrite zb_land_mask by lia. change (2^4) with 16.
      change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
    rewrite ADJ. if_true.
    replace (Z_to_bv 64 (B + 16 + stride * (i + 1))) with (Z_to_bv 64 (E + 4)) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + 16 + stride * (i + 1) + -4)) with (Z_to_bv 64 E) by (f_equal; subst E; lia).
    pose proof tail_c48 as TC. cbv delta [mkR] in TC. apply TC. }
  cbv delta [mkR] in KC4.

  st1. rewrite ?wz_unsigned, MW4 by lia. st1. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  -
    destruct (STR1 ltac:(lia)) as [SC48 STR].
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87200 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87200 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
    apply KC4.
  -
    specialize (Hml ltac:(lia)).
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in K2 by lia. rewrite Z.mod_small in K2 by lia. lia. }

    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    +
      pose proof (STR2 ltac:(lia)) as STR.
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite ?wz_unsigned, land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply KC4.
    +
      destruct (STR1 ltac:(lia)) as [SC48 STR].
      st1.
      assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87200 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (87200 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply KC4.
Qed.

Lemma tail_a9c : forall (x5 x6 x7 a1v a2v a3v a4v a5v a6v a7v x28 : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp x5 x6 x7 (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 P) a1v a2v a3v a4v a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x47f64) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  assert (IDX : Z.land b3 31 = i) by (subst b3; apply land_idx_code; lia).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof tail_b98 as KB. cbv delta [mkR] in KB.

  st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. change 15 with (2^4 - 1) in K1. rewrite zb_land_mask in K1 by lia. rewrite ?unsigned_lit in K1 by lia. lia. }

  st1. st1. st1. st1. rewrite IDX. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite ?unsigned_lit by lia. rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ i < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ i)) as SXI.
  assert (LA : Z.land avail (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit avail i ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit freed i ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HAREA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  clear K K1 K2 K3 K4 K5 K6 K7.

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8; rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia.
  -
    specialize (Hsc63 ltac:(lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    apply KB.
  -
    specialize (RS ltac:(lia)). specialize (Hsc ltac:(lia)).
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87200 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87200 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply KB.
Qed.
End TAIL.

End CEIL.

Ltac memeq_transport m m2 EQ :=
  repeat match goal with
  | H : ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs /\ ov_read_bytes rsegs m ?x2 ?n2 = Some ?bs2 |- _ =>
      rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ), <- (ov_read_bytes_memeq rsegs m m2 x2 n2 EQ) in H
  | H : rw_cells rsegs m ?A ?cs |- _ => apply (rw_cells_memeq rsegs m m2 A cs EQ) in H
  | H : bytes_at rsegs m ?A ?bs |- _ => apply (bytes_at_memeq rsegs m m2 A bs EQ) in H
  | H : _ -> bytes_at rsegs m ?A ?bs |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs) by (intros XX; apply (bytes_at_memeq rsegs m m2 A bs EQ), H, XX); clear H; rename H' into H
  | H : _ -> bytes_at rsegs m ?A ?bs /\ bytes_at rsegs m ?A2 ?bs2 |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs /\ bytes_at rsegs m2 A2 bs2)
        by (intros XX; destruct (H XX) as [X1 X2]; split; [apply (bytes_at_memeq rsegs m m2 A bs EQ), X1| apply (bytes_at_memeq rsegs m m2 A2 bs2 EQ), X2]); clear H; rename H' into H
  | H : wr_at rsegs m ?A ?n |- _ => apply (wr_at_memeq rsegs m m2 A n EQ) in H
  | H : _ -> wr_at rsegs m ?A ?n |- _ =>
      let H' := fresh H in assert (H' : _ -> wr_at rsegs m2 A n) by (intros XX; apply (wr_at_memeq rsegs m m2 A n EQ), H, XX); clear H; rename H' into H
  | H : stk rsegs m ?lo ?hi |- _ => apply (stk_memeq rsegs m m2 lo hi EQ) in H
  | H : mem_inv rsegs m |- _ => apply (mem_inv_memeq rsegs m m2 EQ) in H
  | H : memeq ?m0 m |- _ => lazymatch m0 with m => clear H | _ => apply (fun X => memeq_trans m0 m m2 X EQ) in H end
  end.
Ltac store_same BY :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let m2 := fresh "m" in let EQ := fresh "EQ" in
      assert (EQ : memeq m (write_to_mem m a bs)) by BY;
      set (m2 := write_to_mem m a bs) in *; clearbody m2;
      first [ match goal with H : memeq ?m0 m |- _ => lazymatch m0 with m => fail | _ => memeq_transport m m2 EQ; clear EQ end end
            | memeq_transport m m2 EQ; let nm := fresh "MEQ" in rename EQ into nm ];
      try clear m
  end.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_get_meta.TwinB RF_malloc_top.TwinB RMemEq.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma impl_post_evt {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) t Q ms -> (forall r ms', Q r ms' -> evt rsegs (Q' r) ms') -> impl rsegs (at_node rsegs) t Q' ms.
Proof.
  revert Q Q' ms. induction t as [r|nd k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. exact (HQ _ _ H').
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implM_post_evt {A} (c : @M PState A) s (Q Q' : A -> PState -> machine_state -> Prop) ms :
  implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof.
  intros H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I| intros H'; exact (HQ _ _ _ H')].
Qed.

Lemma memeq_store_same m a bs :
  bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ 0x8a000 <= a) -> memeq m (write_to_mem m (wa a) bs).
Proof.
  intros (H0 & H1 & HB) OUT. apply memeq_write_same; [exact H0| exact H1|].
  intros i Hi. rewrite <- (HB i Hi). symmetry. apply ref_mrd_overlay. rewrite wa_unsigned by lia. lia.
Qed.

Lemma store_ok_memeq m m' : memeq m m' -> forall n a, store_ok rsegs m' a n = store_ok rsegs m a n.
Proof.
  intros H. induction n as [|n IH]; intros a; [reflexivity|]. cbn [store_ok].
  rewrite (wview_memeq rsegs m m' a H). destruct (wview rsegs m a); [apply IH| reflexivity].
Qed.

Lemma wr_at_store_ok1 m a n x (j : nat) :
  wr_at rsegs m a n -> a <= x -> x + Z.of_nat j <= a + n -> store_ok rsegs m (wa x) j = true.
Proof. intros W H1 H2. replace x with (a + (x - a)) by lia. eapply wr_at_store_ok; [exact W| lia| lia]. Qed.

Lemma land_idx_code i k : 0 <= i < 32 -> 0 <= k -> Z.land (i + 32 * k) 31 = i.
Proof.
  intros Hi Hk. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
  replace (i + 32 * k) with (i + k * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma land_hi_lo i k : 0 <= i < 32 -> 0 <= k -> Z.land (k * 32) i = 0.
Proof.
  intros Hi Hk. apply Z.bits_inj'; intros j Hj. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec j 5) as [L|L].
  - change 32 with (2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 i j); [apply Bool.andb_false_r| lia|].
    destruct (Z.eq_dec i 0) as [->|NZ]; [cbn; lia|].
    apply (Z.lt_le_trans _ 5); [| lia]. apply Z.log2_lt_pow2; [lia|]. change (2^5) with 32. lia.
Qed.

Lemma lor_idx_code i k : 0 <= i < 32 -> 0 <= k -> Z.lor (k * 32) i = i + 32 * k.
Proof.
  intros Hi Hk. rewrite <- Z.lxor_lor by (apply land_hi_lo; lia). rewrite <- Z.add_nocarry_lxor by (apply land_hi_lo; lia). lia.
Qed.

Lemma swrap32_small z : -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros Hz. rewrite swrap32_eq'. rewrite Z.mod_small by lia. lia. Qed.

Lemma le1_b8 z : 0 <= z < 2^64 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof. intros Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma signed_lit_small z : 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite zb_signed, unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.

Ltac memeq_transport m m2 EQ :=
  repeat match goal with
  | H : ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs /\ ov_read_bytes rsegs m ?x2 ?n2 = Some ?bs2 |- _ =>
      rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ), <- (ov_read_bytes_memeq rsegs m m2 x2 n2 EQ) in H
  | H : rw_cells rsegs m ?A ?cs |- _ => apply (rw_cells_memeq rsegs m m2 A cs EQ) in H
  | H : bytes_at rsegs m ?A ?bs |- _ => apply (bytes_at_memeq rsegs m m2 A bs EQ) in H
  | H : _ -> bytes_at rsegs m ?A ?bs |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs) by (intros XX; apply (bytes_at_memeq rsegs m m2 A bs EQ), H, XX); clear H; rename H' into H
  | H : _ -> bytes_at rsegs m ?A ?bs /\ bytes_at rsegs m ?A2 ?bs2 |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs /\ bytes_at rsegs m2 A2 bs2)
        by (intros XX; destruct (H XX) as [X1 X2]; split; [apply (bytes_at_memeq rsegs m m2 A bs EQ), X1| apply (bytes_at_memeq rsegs m m2 A2 bs2 EQ), X2]); clear H; rename H' into H
  | H : wr_at rsegs m ?A ?n |- _ => apply (wr_at_memeq rsegs m m2 A n EQ) in H
  | H : _ -> wr_at rsegs m ?A ?n |- _ =>
      let H' := fresh H in assert (H' : _ -> wr_at rsegs m2 A n) by (intros XX; apply (wr_at_memeq rsegs m m2 A n EQ), H, XX); clear H; rename H' into H
  | H : stk rsegs m ?lo ?hi |- _ => apply (stk_memeq rsegs m m2 lo hi EQ) in H
  | H : mem_inv rsegs m |- _ => apply (mem_inv_memeq rsegs m m2 EQ) in H
  | H : memeq ?m0 m |- _ => lazymatch m0 with m => clear H | _ => apply (fun X => memeq_trans m0 m m2 X EQ) in H end
  end.

Ltac store_same BY :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let m2 := fresh "m" in let EQ := fresh "EQ" in
      assert (EQ : memeq m (write_to_mem m a bs)) by BY;
      set (m2 := write_to_mem m a bs) in *; clearbody m2;
      first [ match goal with H : memeq ?m0 m |- _ => lazymatch m0 with m => fail | _ => memeq_transport m m2 EQ; clear EQ end end
            | memeq_transport m m2 EQ; let nm := fresh "MEQ" in rename EQ into nm ];
      try clear m
  end.

Definition raligned_tail_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v a0 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 a1 a2 a3 a4 a5 a6 a7 x28 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp x5 x6 x7 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ memeq m m'.

Section TAIL.
Variables (ra1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rav s0v s1v : word) (junk : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n G B AREA stride : Z) (i res off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word).
Let b3 := i + 32 * Z.min res 5.
Let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen.
Let E := B + 16 + stride * (i + 1) - 4.
Let POST := raligned_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v (Z_to_bv 64 P) F fc m.

Hypotheses (HN : 0 <= n < 2^48) (SPH : bv_unsigned sp + 32 <= 2^64)
    (FR : rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 s0v; C8 rav]).

Hypotheses (P0 : 0 < P) (AL : P mod 16 = 0) (PLO : 16 * off16 + 16 <= P) (PHI : P + 16 <= 2^64)
    (HB : B = P - 16 * off16 - 16) (HAREA : AREA = G - G mod 4096) (GLO : 0 <= G) (GHI : G + 40 <= 2^64)
    (R4 : ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0])
    (R3 : ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3])
    (R2 : ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)))
    (RG : ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)))
    (MM : rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)])
    (RA : ov_read_bytes rsegs m (wa AREA) 8 = Some (le8 (wz secret)))
    (RC : ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)))
    (RS : sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))))
    (IR : 0 <= i < 32) (O16 : 0 <= off16 < 65536) (AV : 0 <= avail < 2^32) (FRD : 0 <= freed < 2^32) (SE : 0 <= secret < 2^64)
    (LI : 0 <= last_idx < 32) (FB : 0 <= freeable < 2) (SC : 0 <= sc < 64) (ML : 0 <= maplen < 2^40)
    (Hidx : i <= last_idx) (Hav : Z.testbit avail i = false) (Hfr : Z.testbit freed i = false)
    (Hsc : sc < 48 -> size_class sc * i <= off16 < size_class sc * (i + 1))
    (Hsc63 : 48 <= sc -> sc = 63)
    (Hml : maplen <> 0 -> off16 <= maplen * 256 - 1).

Hypotheses (STR1 : maplen = 0 \/ last_idx <> 0 -> sc < 48 /\ stride = 16 * size_class sc)
    (STR2 : last_idx = 0 /\ maplen <> 0 -> stride = maplen * 4096 - 16).

Hypotheses (RES : 0 <= res < 2^31) (RESE : res = E - P - n) (HEAPR : E + 1 <= 0x10000 \/ 0x8a000 <= P - 4) (EHI : E + 1 <= 2^64)
    (B3AT : bytes_at rsegs m (P - 3) [b8 b3]) (W3 : wr_at rsegs m (P - 3) 1)
    (RB0 : 0 < res -> bytes_at rsegs m (E - res) [b8 0]) (W0 : 0 < res -> wr_at rsegs m (E - res) 1)
    (RB5 : 5 <= res -> bytes_at rsegs m (E - 5) [b8 0] /\ bytes_at rsegs m (E - 4) (le4 (wz res))) (W5 : 5 <= res -> wr_at rsegs m (E - 5) 5).

Lemma tail_c48 : forall (x5 x6 x7 a1v a5v a6v a7v x28 : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp x5 x6 x7 (Z_to_bv 64 15) (Z_to_bv 64 n) (Z_to_bv 64 P) a1v (Z_to_bv 64 n) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x49914) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  assert (ELO : P + n <= E) by lia.

  assert (K44 : forall (m' : mem) (y5 y6 y7 a2v a4v b5v b6v b7v y28 : word) (code : Z),
    memeq m m' -> code = Z.min res 5 ->
    evt rsegs POST
      (MS (mkR ra1 sp gp tp y5 y6 y7 (Z_to_bv 64 15) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 code) a2v (Z_to_bv 64 (E + 4)) a4v b5v b6v b7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x49990) fc None m' (seg_rom rsegs))).
  { intros m' y5 y6 y7 a2v a4v b5v b6v b7v y28 code MEQ' HC.
    memeq_transport m m' MEQ'.

    st1. st1. rewrite (land_idx_code i (Z.min res 5)) by lia. st1. st1.
    rewrite Z.shiftl_mul_pow2, !unsigned_lit, lor_idx_code by lia. change (2^5) with 32.
    replace (i + 32 * code) with b3 by (subst b3 code; lia).

    pose proof (wr_at_store_ok1 m' (P - 3) 1 (P - 3) 1 W3 ltac:(lia) ltac:(cbn; lia)) as SOK.
    st1. rewrite (le1_b8 b3) by lia. clear SOK.
    store_same ltac:(apply memeq_store_same; [exact B3AT| cbn; lia]).

    st1. st1. st1. st1. st1. st1. finish. }

  st1. st1. rewrite (swrap32_small (E - (n + P))) by lia. st1. if_cases K0; zify_cond K0.
  -
    replace (Z_to_bv 64 (E - (n + P))) with (Z_to_bv 64 (Z.min res 5)) by (f_equal; lia).
    eapply K44; [apply memeq_refl| reflexivity].
  -
    st1. rewrite (swrap32_small (E - (n + P))) by lia. st1. rewrite (swrap32_small (0 - (E - (n + P)))) by lia. st1. st1.
    pose proof (wr_at_store_ok1 m (E - res) 1 (E - res) 1 (W0 ltac:(lia)) ltac:(lia) ltac:(cbn; lia)) as SOK.
    st1. clear SOK. change (le1 (Z_to_bv 64 0)) with [b8 0].
    store_same ltac:(apply memeq_store_same; [replace (E + (0 - (E - (n + P)))) with (E - res) by lia; apply RB0; lia| cbn; lia]).

    st1. if_cases K1; zify_cond K1; rewrite signed_lit_small in K1 by lia.
    +
      st1. replace (Z_to_bv 64 (E - (n + P))) with (Z_to_bv 64 (Z.min res 5)) by (f_equal; lia).
      eapply K44; [exact MEQ| reflexivity].
    +
      destruct (RB5 ltac:(lia)) as [RB5a RB5b].
      pose proof (wr_at_store_ok1 _ (E - 5) 5 (E - 5) 1 (W5 ltac:(lia)) ltac:(lia) ltac:(cbn; lia)) as SOK.
      st1. clear SOK. change (le1 (Z_to_bv 64 0)) with [b8 0].
      store_same ltac:(apply memeq_store_same; [replace (E + 4 + -9) with (E - 5) by lia; exact RB5a| cbn; lia]).
      pose proof (wr_at_store_ok1 _ (E - 5) 5 (E - 4) 4 (W5 ltac:(lia)) ltac:(lia) ltac:(cbn; lia)) as SOK.
      st1. clear SOK. replace (Z_to_bv 64 (E - (n + P))) with (wz res) by (unfold wz; f_equal; lia).
      store_same ltac:(apply memeq_store_same; [replace (E + 4 + -8) with (E - 4) by lia; exact RB5b| rewrite length_le4; cbn; lia]).

      st1. eapply K44; [exact MEQ| lia].
Qed.

Lemma tail_b98 : forall (x7 x28 : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 87344) (Z_to_bv 64 (sc * 2)) x7 (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 n)
              (wz off16) (wz B) (wz mword) (Z_to_bv 64 last_idx) (Z_to_bv 64 (i + 1))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x49864) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }

  assert (KC4 : forall a3v t0v t3v,
    evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 (0 + - P)) (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 n)
              a3v (wz B) (wz mword) (Z_to_bv 64 stride) (Z_to_bv 64 (i + 1))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x49890) fc None m (seg_rom rsegs))).
  { intros.

    st1. st1. st1. st1. st1. st1. st1.
    assert (ADJ : Z.land 15 (bv_unsigned (Z_to_bv 64 (0 + - P))) = 0).
    { rewrite unsigned_lit_wrap, Z.land_comm. change 15 with (2^4 - 1). rewrite zb_land_mask by lia. change (2^4) with 16.
      change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
    rewrite ADJ. if_true.
    replace (Z_to_bv 64 (B + 16 + stride * (i + 1))) with (Z_to_bv 64 (E + 4)) by (f_equal; subst E; lia).
    replace (Z_to_bv 64 (B + 16 + stride * (i + 1) + -4)) with (Z_to_bv 64 E) by (f_equal; subst E; lia).
    pose proof tail_c48 as TC. cbv delta [mkR] in TC. apply TC. }
  cbv delta [mkR] in KC4.

  st1. rewrite ?wz_unsigned, MW4 by lia. st1. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  -
    destruct (STR1 ltac:(lia)) as [SC48 STR].
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87344 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87344 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
    apply KC4.
  -
    specialize (Hml ltac:(lia)).
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in K2 by lia. rewrite Z.mod_small in K2 by lia. lia. }

    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    +
      pose proof (STR2 ltac:(lia)) as STR.
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite ?wz_unsigned, land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply KC4.
    +
      destruct (STR1 ltac:(lia)) as [SC48 STR].
      st1.
      assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87344 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
      { replace (Z_to_bv 64 (87344 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). apply RS. lia. }
      pose proof (size_class_range sc ltac:(lia)) as SZ.
      st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (f_equal; lia).
      apply KC4.
Qed.

Lemma tail_a9c : forall (x5 x6 x7 a1v a2v a3v a4v a5v a6v a7v x28 : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp x5 x6 x7 (Z_to_bv 64 16) (Z_to_bv 64 n) (Z_to_bv 64 P) a1v a2v a3v a4v a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x49768) fc None m (seg_rom rsegs)).
Proof.
  intros.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  assert (IDX : Z.land b3 31 = i) by (subst b3; apply land_idx_code; lia).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof tail_b98 as KB. cbv delta [mkR] in KB.

  st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. change 15 with (2^4 - 1) in K1. rewrite zb_land_mask in K1 by lia. rewrite ?unsigned_lit in K1 by lia. lia. }

  st1. st1. st1. st1. rewrite IDX. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite ?unsigned_lit by lia. rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ i < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ i)) as SXI.
  assert (LA : Z.land avail (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit avail i ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit freed i ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HAREA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  clear K K1 K2 K3 K4 K5 K6 K7.

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1.
  if_cases K8; zify_cond K8; rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia.
  -
    specialize (Hsc63 ltac:(lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    apply KB.
  -
    specialize (RS ltac:(lia)). specialize (Hsc ltac:(lia)).
    st1.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (87344 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (87344 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply KB.
Qed.
End TAIL.

End CEIL.

Ltac memeq_transport m m2 EQ :=
  repeat match goal with
  | H : ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs |- _ => rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ) in H
  | H : _ -> ov_read_bytes rsegs m ?x ?n = Some ?bs /\ ov_read_bytes rsegs m ?x2 ?n2 = Some ?bs2 |- _ =>
      rewrite <- (ov_read_bytes_memeq rsegs m m2 x n EQ), <- (ov_read_bytes_memeq rsegs m m2 x2 n2 EQ) in H
  | H : rw_cells rsegs m ?A ?cs |- _ => apply (rw_cells_memeq rsegs m m2 A cs EQ) in H
  | H : bytes_at rsegs m ?A ?bs |- _ => apply (bytes_at_memeq rsegs m m2 A bs EQ) in H
  | H : _ -> bytes_at rsegs m ?A ?bs |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs) by (intros XX; apply (bytes_at_memeq rsegs m m2 A bs EQ), H, XX); clear H; rename H' into H
  | H : _ -> bytes_at rsegs m ?A ?bs /\ bytes_at rsegs m ?A2 ?bs2 |- _ =>
      let H' := fresh H in assert (H' : _ -> bytes_at rsegs m2 A bs /\ bytes_at rsegs m2 A2 bs2)
        by (intros XX; destruct (H XX) as [X1 X2]; split; [apply (bytes_at_memeq rsegs m m2 A bs EQ), X1| apply (bytes_at_memeq rsegs m m2 A2 bs2 EQ), X2]); clear H; rename H' into H
  | H : wr_at rsegs m ?A ?n |- _ => apply (wr_at_memeq rsegs m m2 A n EQ) in H
  | H : _ -> wr_at rsegs m ?A ?n |- _ =>
      let H' := fresh H in assert (H' : _ -> wr_at rsegs m2 A n) by (intros XX; apply (wr_at_memeq rsegs m m2 A n EQ), H, XX); clear H; rename H' into H
  | H : stk rsegs m ?lo ?hi |- _ => apply (stk_memeq rsegs m m2 lo hi EQ) in H
  | H : mem_inv rsegs m |- _ => apply (mem_inv_memeq rsegs m m2 EQ) in H
  | H : memeq ?m0 m |- _ => lazymatch m0 with m => clear H | _ => apply (fun X => memeq_trans m0 m m2 X EQ) in H end
  end.
Ltac store_same BY :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let m2 := fresh "m" in let EQ := fresh "EQ" in
      assert (EQ : memeq m (write_to_mem m a bs)) by BY;
      set (m2 := write_to_mem m a bs) in *; clearbody m2;
      first [ match goal with H : memeq ?m0 m |- _ => lazymatch m0 with m => fail | _ => memeq_transport m m2 EQ; clear EQ end end
            | memeq_transport m m2 EQ; let nm := fresh "MEQ" in rename EQ into nm ];
      try clear m
  end.
End TwinB.
