(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF W_small3A W_small4A W_calls4AF AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_set_wordAF ShiftKitAF W_shiftAF W_div_padAF W_div_tailAF W_divAF W_set_bitAF W_bndivAF PlaceTmodA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require W_sub_wordAF InvClosedAF W_mod_inverseAF W_int_invAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import RecpKitAF ExpBodyKitF InvKitAF MontSetSimF MontSetKitAF Fr_mont_set.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Definition BN_MONT_CTX_SET : Z := 0x2267e8.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2255160 => 2
  | 2255168 => 1
  | 2255172 => 2
  | 2255360 => 2
  | 2255436 => 2
  | 2255440 => 1
  | 2255444 => 2
  | 2255468 => 2
  | 2255472 => 1
  | 2255476 => 2
  | 2255508 => 2
  | 2255668 => 1
  | 2255672 => 2
  | 2255724 => 2
  | 2255728 => 1
  | 2255732 => 2
  | 2255824 => 2
  | 2255908 => 1
  | 2255912 => 1
  | 2255916 => 2
  | 2256044 => 1
  | 2256048 => 1
  | 2256056 => 1
  | 2256064 => 1
  | 2256068 => 2
  | 2256072 => 1
  | 2256076 => 1
  | 2256080 => 1
  | 2256084 => 1
  | 2256088 => 2
  | 2256092 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Section Stmt.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Definition mont_set_stmtA (STACK COST : Z) (d : nat) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room d ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MONT_CTX_SET (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
  a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
  implA (BN_MONT_CTX_set (tree_ops bptr) rd ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MONT_CTX_SET) fc None m (seg_rom bgbsegs)).
End Stmt.

Lemma bbind_get : forall {B} r (f : bignum bptr -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind ops (bget ops r) f bs = f (getbn r bs) bs.
Proof. reflexivity. Qed.
Lemma bbind_set : forall {B} r b (f : unit -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind ops (bset ops r b) f bs = f tt (setbn r b bs).
Proof. reflexivity. Qed.
Lemma bbind_ret : forall {A B} (a : A) (f : A -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind ops (bret ops a) f bs = f a bs.
Proof. reflexivity. Qed.
Lemma bbind_get_set0 : forall {C : Type} r (gg : bignum bptr -> bignum bptr) (K : unit -> BM (M := btree bptr) C) (bsK : ST),
  bbind ops (bbind ops (bget ops r) (fun n => bset ops r (gg n))) K bsK = K tt (setbn r (gg (getbn r bsK)) bsK).
Proof. reflexivity. Qed.
Lemma bbind_getst : forall {B} (f : ST -> BM (M := btree bptr) B) (bsK : ST), bbind ops (bgetst ops) f bsK = f bsK bsK.
Proof. reflexivity. Qed.
Lemma bbind_zero : forall {C : Type} r (K : unit -> BM (M := btree bptr) C) (bsK : ST),
  bbind ops (BN_zero ops r) K bsK = K tt (setbn r (bn_zero_pure (getbn r bsK)) bsK).
Proof. reflexivity. Qed.
Lemma bbind_getst_setmont : forall {C : Type} (fri fn0 : ST -> Z) (K : unit -> BM (M := btree bptr) C) (bsK : ST),
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops (fri st) (fn0 st))) K bsK = K tt (set_mont (fri bsK) (fn0 bsK) bsK).
Proof. reflexivity. Qed.

Definition ms_b3 (rmod rRi : bnref) (ri : Z) : BM (M := btree bptr) (ptr := bptr) unit :=
  bbind ops (bget ops rmod) (fun m =>
  if (bn_top m =? 0)%nat then bunr ops else
  let b0 := nth 0 (bn_buf m) 0 in
  bbind ops (bset ops RTmod (mkBN None [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0)) (fun _ =>
  ms_inv rRi ri)).
Definition ms_b2 (rmod rRi : bnref) : BM (M := btree bptr) (ptr := bptr) unit :=
  bbind ops (BN_num_bits ops rmod) (fun nb =>
  let ri := (nb + 63) / 64 * 64 in
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops ri (st_n0 st))) (fun _ =>
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (BN_set_bit ops RMontRR 64) (fun _ =>
  ms_b3 rmod rRi ri)))).
Lemma ms_mid_eq : forall rmod rRi,
  ms_mid rmod rRi = bbind ops (BN_copy ops RMontN rmod) (fun _ =>
                    bbind ops (bbind ops (bget ops RMontN) (fun n => bset ops RMontN (bn_with_neg n false))) (fun _ => ms_b2 rmod rRi)).
Proof. reflexivity. Qed.

Lemma bbind_num_bits : forall {C : Type} r (K : Z -> BM (M := btree bptr) (ptr := bptr) C) (bsK : ST), bg_ok (getbn r bsK) ->
  bbind ops (BN_num_bits ops r) K bsK = K (num_bits_pure (getbn r bsK)) bsK.
Proof.
  intros C r K bsK (_ & _ & _ & FL). unfold bbind at 1. unfold BN_num_bits. rewrite bbind_get. unfold has_flag.
  assert (EL4 : Z.land (bn_flags (getbn r bsK)) BN_FLG_CONSTTIME = 0) by (destruct FL as [E|E]; rewrite E; reflexivity).
  rewrite EL4. reflexivity.
Qed.

Lemma land_m64_small : forall x, 0 <= x < 32832 -> Z.land x 18446744073709551552 = x / 64 * 64.
Proof.
  intros x Hx.
  replace x with (64 * (x / 64) + x mod 64) at 1 by (symmetry; apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound x 64 ltac:(lia)) as HM.
  pose proof (Z.div_pos x 64 ltac:(lia) ltac:(lia)) as HD.
  assert (HQ : x / 64 < 513) by (apply Z.div_lt_upper_bound; lia).
  set (q := x / 64) in *. set (r := x mod 64) in *.
  change 18446744073709551552 with (Z.shiftl (Z.ones 58) 6).
  replace (64 * q + r) with (Z.lor (Z.shiftl q 6) r).
  2:{ rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
        destruct (Z.lt_ge_cases i 6) as [H6|H6]; [rewrite (Z.testbit_neg_r q (i - 6)) by lia; reflexivity|].
        rewrite (Z.bits_above_log2 r i); [apply andb_false_r| lia|]. destruct (Z.eq_dec r 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
        assert (2^6 <= 2^i) by (apply Z.pow_le_mono_r; lia). lia. }
      rewrite <- Z.add_nocarry_lxor. { rewrite Z.shiftl_mul_pow2 by lia. lia. }
      apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 6) as [H6|H6]; [rewrite (Z.testbit_neg_r q (i - 6)) by lia; reflexivity|].
      rewrite (Z.bits_above_log2 r i); [apply andb_false_r| lia|]. destruct (Z.eq_dec r 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      assert (2^6 <= 2^i) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite Z.land_lor_distr_l.
  rewrite <- Z.shiftl_land.
  replace (Z.land q (Z.ones 58)) with q by (symmetry; rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  replace (Z.land r (Z.shiftl (Z.ones 58) 6)) with 0.
  2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 6) as [H6|H6]; [rewrite (Z.testbit_neg_r (Z.ones 58) (i - 6)) by lia; apply andb_false_r|].
      rewrite (Z.bits_above_log2 r i); [reflexivity| lia|]. destruct (Z.eq_dec r 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      assert (2^6 <= 2^i) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite Z.lor_0_r. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Ltac fr_unf H := idtac.
Ltac fr_store_gen CF FBz SPz ENV LS ENV' LS' :=
  let STx := fresh "STx" in let MIx := fresh "MIx" in let FRx := fresh "FRx" in let FSZx := fresh "FSZx" in
  let MUx := fresh "MUx" in let WMx := fresh "WMx" in let SZx := fresh "SZx" in
  pose proof ENV as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _);
  fr_unf FRx; fr_unf FSZx; cbn [app] in FRx;
  assert (SZx : FBz + 72 <= SPz) by (cbn [app cells_size csize Nat.add] in FSZx; clear - FSZx; lia);
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(FBz, SPz)]%Z mm) as MUx; pose proof (wmono_refl bgbsegs mm) as WMx end;
  step;
  lazymatch type of FRx with
  | rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: _) =>
      destruct (CF _ [c0; c1; c2; c3; c4; c5; c6; c7] _ _ _ _ mx _
                  ENV LS MUx WMx STx MIx FRx ltac:(cbn [app cells_size csize Nat.add] in FSZx |- *; exact FSZx)) as (ENV' & LS')
  end;
  clear STx MIx FRx FSZx MUx WMx SZx.

Section FillStmt.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Definition fix_fill_stmt : Prop := forall (POST : machine_state -> Prop)
    (x1 gp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (OW LB : list block) (lo FB am D top cnt dmax : Z) (pr : bptr),
  AHEAP Σ OW LB m -> stk bgbsegs m lo FB -> mem_inv bgbsegs m -> ACEIL <= lo -> lo <= FB - 16 -> FB + 16 <= USTACK_TOP ->
  In (pr, D, 8 * dmax) OW -> rw_cells bgbsegs m am [C8 (Z_to_bv 64 D)] -> acc bgbsegs m am 24 -> am mod 8 = 0 -> 0 < am -> am + 24 <= FB - 16 ->
  (am + 24 <= SHLO \/ SHHI <= am) -> (am + 24 <= D \/ D + 8 * dmax <= am) ->
  0 <= top -> 0 < cnt -> top + cnt <= dmax -> dmax <= 512 ->
  x10 = Z_to_bv 64 (am + 8) -> x13 = Z_to_bv 64 (top + cnt) -> x14 = Z_to_bv 64 top -> x20 = Z_to_bv 64 am -> x24 = Z_to_bv 64 SHB ->
  (forall (mM : mem) (y5 y6 y7 y11 y14 y15 y16 y17 : word),
     mem_inv bgbsegs mM -> stk bgbsegs mM lo FB -> AHEAP Σ OW LB mM -> wmono bgbsegs m mM ->
     agree_on (fun a => aclient_addr (OW ++ LB) FB a /\ ~ (D + 8 * top <= a < D + 8 * top + 8 * cnt)) m mM ->
     bytes_at bgbsegs mM (D + 8 * top) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * cnt))) -> wr_at bgbsegs mM (D + 8 * top) (8 * cnt) ->
     evt bgbsegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y5 y6 y7 x8 x9 x10 y11 x12 x13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x226d04) fc None mM (seg_rom bgbsegs))) ->
  evt bgbsegs POST (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x226c90) fc None m (seg_rom bgbsegs)).
End FillStmt.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation FR := (@ar_FR AR).

Lemma MC_0 : MC = 0. Proof. reflexivity. Qed.

Lemma open_for_read_u : forall (LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW r ar K,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne -> 0 <= K -> lo <= FB - K ->
  exists D, rw_cells bgbsegs m ar (BnRepDefs.bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
    /\ u64arr bgbsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ stk bgbsegs m lo FB /\ mem_inv bgbsegs m
    /\ ar + 24 <= FB - K /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= FB - K
    /\ acc bgbsegs m ar 24 /\ ar mod 8 = 0
    /\ acc bgbsegs m D (8 * Z.of_nat (bn_top (getbn r ls))) /\ D mod 8 = 0
    /\ (0 <= D /\ D + 8 * Z.of_nat (bn_top (getbn r ls)) <= 140737488355328)
    /\ SHHI <= lo /\ 0 < ar
    /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r ls))) D.
Proof.
  intros LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW r ar K ENV LS HA NRO K0 LOK.
  pose proof ENV as (OK & HEAP & ST & MI & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  destruct (open_ro_shu Σ OW LB m ls PL EA SPv r ar HEAP LS FROK NOFR HA NRO) as (D & BN & OKB & U & A0 & AC & D0 & DC & ACC & AL & ACCD & ALD & UBT & _).
  pose proof OKB as (_ & TD & _).
  exists D. split; [exact BN|]. split; [exact OKB|]. split; [exact U|]. split; [exact ST|]. split; [exact MI|].
  split; [unfold BnHeapA.ACEIL in *; clear - AC CEIL LOK; lia|]. split; [unfold BnHeapA.ACEIL in *; clear - DC CEIL LOK; lia|].
  split; [exact ACC|]. split; [exact AL|]. split; [exact ACCD|]. split; [exact ALD|].
  split; [unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP, BnHeapA.ACEIL, bn_dmax in *; clear - D0 DC TD C1 C2 C3 CEIL LOFB FBSP SPT; lia|].
  split; [unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *; clear - C1 C2 C3 CEIL; lia|]. split; [exact A0 | exact UBT].
Qed.

Section Proofs.

  Variable CS : Z.
  Hypothesis CS112 : BN_NUM_BITS_STACK <= CS.
  Hypothesis CS16 : 16 <= CS.
  Hypothesis CSRT : RT_STACK <= CS.
  Hypothesis STK_START : BN_CTX_START_STACK <= CS.
  Hypothesis STK_GET : BN_CTX_GET_STACK <= CS.
  Hypothesis STK_END : BN_CTX_END_STACK <= CS.
  Hypothesis STK_SETW : BN_SET_WORD_STACK <= CS.
  Hypothesis STK_COPY : BN_COPY_STACK <= CS.
  Hypothesis STK_SETBIT : BN_SET_BIT_STACK <= CS.
  Hypothesis STK_LSH : BN_LSHIFT_W_STACK <= CS.
  Hypothesis STK_SUBW : W_sub_wordAF.BN_SUB_WORD_STACK <= CS.
  Hypothesis STK_DIV : BN_DIV_TOP_STACK <= CS.
  Hypothesis STK_ONE : BN_IS_ONE_STACK <= CS.
  Hypothesis STK_INV : InvClosedAF.MOD_INV_STACK_A <= CS.
  Hypothesis STK_INIT : BN_INIT_STACK <= CS.
  Hypothesis FILL : fix_fill_stmt.

  Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
  Local Ltac retpc n := rewrite (ret_pc_even n) by (clear; lia).
  Local Ltac mc0 := rewrite ?MC_0; clear; lia.
  Local Ltac pre_wk PRE STK := eapply bn_preA_wk; [exact PRE | exact STK | clear; lia].

  Section PhaseD.
    Variables (gp s0r : word) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (TOTAL : Z).
    Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
    Variables (am ac : Z) (qm qc : bptr) (f : Z) (g : nat) (junk : list byte).
    Hypothesis ES0 : bv_unsigned s0r = SPv.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis HPC : pl_ctx PL = Some (ac, qc).
    Hypothesis HPM : pl_mont PL = Some (am, qm).
    Hypothesis CTX : uk_ctx BN_MONT_CTX_SET (bv_unsigned raw :: ras).
    Variable Q : unit * ST -> rts RT -> machine_state -> Prop.
    Variable USED : Z.
    Hypothesis USEDT : USED <= TOTAL.

    Notation CENV := (cenvA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
    Notation KCALL := (kcallA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).

    Lemma LOF16 : lo <= FB - 16. Proof using LOF CS16. clear - LOF CS16. lia. Qed.
    Notation KZEROX := (zero_callA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOF16).

    Definition mfr (j0 : list byte) (c1 c2 c3 : cell) (j4 j5 : list byte) : list cell :=
      [CB 8 j0; c1; c2; c3; CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 f); CB g junk].

    Hypothesis EPI : forall j0 c1 c2 c3 j4 j5 Σk lsk mk OWk
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word) F' fc',
      CENV (mfr j0 c1 c2 c3 j4 j5) USED Σk lsk mk OWk -> lib_state lsk mk OWk PL EA ->
      implA (TRet (tt, lsk)) Σk Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) x19 (Z_to_bv 64 1) x21 x22 x23 x24 x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F' (wz 0x226d24) fc' None mk (seg_rom bgbsegs)).

    Lemma env_bounds : forall pre used Σ ls m OW, CENV pre used Σ ls m OW ->
      bv_unsigned (Z_to_bv 64 FB) = FB /\ bv_unsigned (Z_to_bv 64 SPv) = SPv /\ 12554240 <= FB /\ FB + 16 <= SPv /\ SPv + 16 <= 140737488355328.
    Proof using.
      intros pre used Σ ls m OW ENV. destruct (ESPs LB PL lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENV) as (E1 & E2).
      destruct ENV as ((CEIL & LOFB & FBSP & SPT & _) & HEAP & _). pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
      unfold SEGTOP_A, USTACK_TOP in *. split; [exact E2|]. split; [exact E1|]. clear - C1 CEIL LOFB FBSP SPT. lia.
    Qed.

    Lemma L_exit : forall j0 c1 c2 c3 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word) F1 fc1,
      CENV (mfr j0 c1 c2 c3 j4 j5) USED ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
      implA (ms_exit0 lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 1) x21 x22 x23 x24 x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226d1c) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK.
      unfold MallocRep.wz, ms_exit0.
      apply implA_from_evt. do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ USED 0 USED BN_CTX_END_STACK); [exact ES0 | exact ENVK | exact LSK | clear - LOF STK_END; lia | clear; lia | exact USEDT
        | intros PRE UW; eapply BN_CTX_end_walkA; [exact PRE | reflexivity | exact HPC | reflexivity]
        | intros v b o p a; cbv beta; intros [E _]; exact E |].
      intros u Σ' ls' m' OW' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F' fc' ENV' LS' RS'; cbv beta; intros (_ & EOW).
      retpc 2256164.
      destruct u. unfold bret. cbn [ret tree_ops]. eapply EPI; [exact ENV' | exact LS'].
    Qed.

    Lemma L_fix : forall j0 c1 c2 c3 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x25 t3 t4 t5 t6 : word) F1 fc1,
      CENV (mfr j0 c1 c2 c3 j4 j5) USED ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
      implA (ms_fix0 lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 x22 x23 (Z_to_bv 64 SHB) x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226c5c) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK.
      pose proof (ref_at_montRR lsK OWK PL am qm HPM) as HARR.
      pose proof (ref_at_montN lsK OWK PL am qm HPM) as HAN.
      pose proof (hpl_wref PL RMontRR (hpl_mont PL RMontRR am qm eq_refl HPM)) as WRR.
      unfold ms_fix0, MallocRep.wz. rewrite !bbind_get.
      set (rr := getbn RMontRR lsK) in *. set (n := getbn RMontN lsK) in *.
      destruct (Nat.ltb_spec (bn_dmax rr) (bn_top n)) as [LT|GE].
      { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
      rewrite bbind_set.
      destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ RMontN (am + 24) ENVK LSK HAN RMontN_not_one)
        as (DN & BNN & OKN & _ & _ & _ & SEPN & SHBC & ACCN & ALN & SLO & OFRN & AN0).
      fold n in BNN, OKN. pose proof OKN as (OKN1 & OKN2 & OKN3 & OKN4).
      destruct (cenv_struct_openA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ RMontRR am ENVK LSK HARR WRR)
        as (DR & BNR & OKR & ACCR & ALR & AR0 & SEPR & OFRR & STK & MIK & CLOSER).
      fold rr in BNR, OKR, CLOSER. pose proof OKR as (OKR1 & OKR2 & OKR3 & OKR4).
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNN, BNR. unfold BG_DMAX, bn_dmax in OKN3, OKR3, OKN2, OKR2.
      assert (TOPS : 0 <= Z.of_nat (bn_top rr) <= 512 /\ 0 <= Z.of_nat (bn_top n) <= 512) by (clear - OKN2 OKN3 OKR2 OKR3; lia).
      pose proof (munch_refl [(am, am + 24)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
      assert (OFF : offshW [(am, am + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFRR; lia).
      apply implA_from_evt.
      do 3 step. shl_with ACCR ALR. chk0.
      do 3 step. shl_with ACCN ALN. step. chk0.
      step.
      rewrite (sx32_small (Z.of_nat (bn_top rr))) by (clear - TOPS; lia).
      rewrite (sx32_small (Z.of_nat (bn_top n))) by (clear - TOPS; lia).

      step. if_cases KT; zify_cond KT; rewrite ?signed_small in KT by (clear - TOPS; lia).
      -
        assert (EBUF : splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr)) = bn_buf rr).
        { replace (bn_top n - bn_top rr)%nat with 0%nat by (clear - KT; lia). unfold splice. cbn [length repeat app]. rewrite Nat.add_0_r. apply firstn_skipn. }
        rewrite EBUF.
        shl_with ACCR ALR. chk0.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
        destruct (CLOSER m1 (mkBN (bn_d rr) (bn_buf rr) (bn_top n) (bn_neg rr) (bn_flags rr)) MU WM) as (ENV1 & LS1);
          [ exact BNR | reflexivity | reflexivity
          | unfold bg_ok, bn_dmax, BG_DMAX in *; cbn [bn_buf bn_top bn_flags]; split; [exact OKR1|]; split; [exact GE|]; split; [exact OKR3| exact OKR4]
          | exact STK | exact MIK |].
        do 2 step. apply evt_done.
        eapply L_exit; [exact ENV1 | exact LS1].
      -
        clear CLOSER MU WM OFF.
        pose proof ENVK as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
        pose proof OK1 as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & _ & NOFR).
        pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
        pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN in C1', C2', C3'.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSK HARR) as HVx2.
        destruct (lib_state_open [] lsK mK OWK PL EA RMontRR am LSK ND2 HARR ltac:(intros []) RMontRR_not_one) as ((Dr & BNr & ARRr) & _ & LSH).
        destruct (bn_arr_facts_w lsK OWK PL EA SPv USTACK_TOP ΣK LB mK RMontRR Dr HEAP2 PARTS2 FROK HVx2 WRR ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
        fold rr in BNr, ARRr, Ur, LENr, DrC, DrI, DSEPr.
        pose proof (DSEPr RMontRR am HARR) as SEPrr.
        destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 NOFR HARR RMontRR_not_one) as (qr2 & Ar2 & nr2 & Hinr2 & Rr21 & Rr22).
        pose proof ARRr as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL RMontRR mK OWK Dr _ PWF2 NOFR RMontRR_not_one ARRnb__ ltac:(solve_nbuf)) in ARRo.
        unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNr. clear BNR.
        assert (HDr : exists pr, bn_d rr = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax rr)) OWK).
        { unfold BnRepDefs.bn_arr in ARRo. fold rr in ARRo. destruct (bn_d rr) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRo)]|].
          exfalso. destruct ARRo as [_ E]. unfold bn_dmax in GE. rewrite E in GE. cbn in GE. clear - GE KT. lia. }
        destruct HDr as (pr & Edr & Hinpr).
        assert (LBR : length (bn_buf rr) = bn_dmax rr) by reflexivity.
        pose proof (munch_refl (@nil (Z * Z)) mK) as MU3.
        assert (HIDZ : 0 <= Z.of_nat (bn_top rr) < Z.of_nat (bn_top n) /\ Z.of_nat (bn_top n) <= Z.of_nat (bn_dmax rr) /\ Z.of_nat (bn_dmax rr) <= 512) by (clear - KT GE OKR3; unfold bn_dmax in *; lia).
        assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax rr) <= 140737488355328) by (unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - Dr0 DrC C1' C2' C3'; lia).
        clear DSEPr DrI.
        set (cnt := (bn_top n - bn_top rr)%nat).
        assert (Ecnt : Z.of_nat cnt = Z.of_nat (bn_top n) - Z.of_nat (bn_top rr)) by (subst cnt; clear - HIDZ; lia).

        pose proof Ur as Ur'.
        apply (proj1 (limbarr_split bgbsegs _ Dr (bn_buf rr) (bn_top rr) ltac:(rewrite LBR; clear - HIDZ; lia))) in Ur'. destruct Ur' as [U1 U23].
        apply (proj1 (limbarr_split bgbsegs _ _ (skipn (bn_top rr) (bn_buf rr)) cnt ltac:(rewrite length_skipn, LBR; clear - Ecnt HIDZ; lia))) in U23. destruct U23 as [_ U3].
        rewrite skipn_skipn in U3. replace (cnt + bn_top rr)%nat with (bn_top n) in U3 by (clear - Ecnt HIDZ; lia).
        replace (Dr + 8 * Z.of_nat (bn_top rr) + 8 * Z.of_nat cnt) with (Dr + 8 * Z.of_nat (bn_top n)) in U3 by (clear - Ecnt; lia).
        assert (LU1 : Z.of_nat (length (wlimbs (firstn (bn_top rr) (bn_buf rr)))) = Z.of_nat (bn_top rr)) by (rewrite wlimbs_len, firstn_length_le by (rewrite LBR; clear - HIDZ; lia); reflexivity).
        assert (LU3 : Z.of_nat (length (wlimbs (skipn (bn_top n) (bn_buf rr)))) = Z.of_nat (bn_dmax rr) - Z.of_nat (bn_top n)) by (rewrite wlimbs_len, length_skipn, LBR; clear - HIDZ; lia).
        eapply (FILL) with (Σ := ΣK) (OW := OWK) (LB := LB) (lo := lo) (FB := FB) (am := am) (D := Dr) (top := Z.of_nat (bn_top rr)) (cnt := Z.of_nat cnt)
                          (dmax := Z.of_nat (bn_dmax rr)) (pr := pr);
          [ exact HEAP2 | exact ST2 | exact MI2 | exact CEIL | exact LOF16 | unfold USTACK_TOP in *; clear - SPT FBSP; lia
          | exact Hinpr | exact (rw_cells_app_l mK am [C8 (Z_to_bv 64 Dr)] _ BNr) | exact ACCR | exact ALR | exact AR0 | exact SEPR | exact OFRR | clear - SEPrr; lia
          | clear - HIDZ; lia | clear - Ecnt HIDZ; lia | clear - Ecnt HIDZ; lia | clear - HIDZ; lia
          | reflexivity | f_equal; clear - Ecnt; lia | reflexivity | reflexivity | reflexivity |].
        intros mM y5 y6 y7 y11 y14 y15 y16 y17 MIM STM HEAPM WMM AGM BZ WRM.

        assert (INR : In (qr2, Ar2, nr2) (OWK ++ LB)) by (exact Hinr2).
        assert (INP : In (pr, Dr, 8 * Z.of_nat (bn_dmax rr)) (OWK ++ LB)) by (apply in_or_app; left; exact Hinpr).
        apply (rw_cells_agree _ _ _ _ _ AGM) in BNr.
        2:{ intros x Hx. cbn in Hx. split; [right; right; exists (qr2, Ar2, nr2); split; [exact INR| cbn [blk_addr blk_size fst snd]; clear - Hx Rr21 Rr22; lia]| clear - Hx SEPrr HIDZ Ecnt; lia]. }
        assert (U1M : u64arr bgbsegs mM Dr (wlimbs (firstn (bn_top rr) (bn_buf rr)))).
        { eapply (LibKitA.u64arr_agree _ _ _ _ _ AGM); [exact U1|]. intros x Hx. rewrite LU1 in Hx.
          split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax rr)); split; [exact INP| cbn [blk_addr blk_size fst snd]; clear - Hx HIDZ; lia]| clear - Hx; lia]. }
        assert (U3M : u64arr bgbsegs mM (Dr + 8 * Z.of_nat (bn_top n)) (wlimbs (skipn (bn_top n) (bn_buf rr)))).
        { eapply (LibKitA.u64arr_agree _ _ _ _ _ AGM); [exact U3|]. intros x Hx. rewrite LU3 in Hx.
          split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax rr)); split; [exact INP| cbn [blk_addr blk_size fst snd]; clear - Hx HIDZ; lia]| clear - Hx Ecnt; lia]. }
        assert (LSHM : lib_state_hc false [RMontRR] lsK mM OWK PL EA).
        { eapply (lib_state_h_icall ΣK LB [RMontRR] lsK mK mM OWK PL EA FB SPv (Dr + 8 * Z.of_nat (bn_top rr)) (8 * Z.of_nat cnt) HEAP2 LSH FROK ltac:(clear - FBSP; lia) AGM).
          eapply (w_limbs OWK LB lsK PL EA SPv false [RMontRR] _ RMontRR pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; clear - HIDZ; lia| cbn [fst snd]; fold rr; clear - Ecnt HIDZ; lia]. }
        pose proof (cenv_icallA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ _ (Dr + 8 * Z.of_nat (bn_top rr)) (8 * Z.of_nat cnt) _
                      ENVK Hinpr ltac:(cbn [blk_addr blk_size fst snd]; clear - HIDZ; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Ecnt HIDZ; lia) HEAPM STM MIM AGM) as EVM.
        assert (PZ : rw_cells bgbsegs mM (Dr + 8 * Z.of_nat (bn_top rr)) [CB (8 * cnt) (repeat (Z_to_bv 8 0) (8 * cnt))]).
        { replace (Z.to_nat (8 * Z.of_nat cnt)) with (8 * cnt)%nat in BZ by (clear; lia).
          split; [split; [cbn [cells_wf cell_wf]; rewrite repeat_length; clear; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ]|].
          cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * cnt + 0)) with (8 * Z.of_nat cnt) by (clear; lia). exact WRM. }
        set (nb := splice (bn_buf rr) (bn_top rr) (repeat 0 cnt)).
        assert (Lnb : length nb = bn_dmax rr) by (subst nb; rewrite splice_length; [exact LBR| rewrite repeat_length, LBR; clear - Ecnt HIDZ; lia]).
        assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKR1| apply limbs_repeat; unfold limb, BW; clear; lia]).
        assert (UFM : u64arr bgbsegs mM Dr (wlimbs nb)).
        { subst nb. unfold splice. rewrite repeat_length. replace (bn_top rr + cnt)%nat with (bn_top n) by (clear - Ecnt HIDZ; lia).
          apply limbarr_app. split; [exact U1M|]. rewrite firstn_length_le by (rewrite LBR; clear - HIDZ; lia). apply limbarr_app. rewrite repeat_length. split.
          - eapply CB_u64arr. rewrite lbytes_repeat0. exact PZ.
          - replace (Dr + 8 * Z.of_nat (bn_top rr) + 8 * Z.of_nat cnt) with (Dr + 8 * Z.of_nat (bn_top n)) by (clear - Ecnt; lia). exact U3M. }
        assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax rr)) by (rewrite wlimbs_len, Lnb; reflexivity).
        clear U1 U3 Ur U1M U3M PZ BZ WRM AGM ACCR MU3 HEAP2 ST2 MI2 LSH FR2 ENVK LSK AXP2 UW2 WMM ACCN BNN.
        pose proof EVM as (_ & _ & _ & _ & _ & _ & _ & _ & FRM & _ & _). cbn [app] in FRM.
        destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPM LSHM NOFR HARR RMontRR_not_one) as (ACRM & _ & OFRM).
        pose proof (munch_refl [(am, am + 24)]%Z mM) as MU5. pose proof (wmono_refl bgbsegs mM) as WM5.
        assert (OFF5 : offshW [(am, am + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFRM; lia).

        shl_with ACRM ALR. chk0.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (HWL5 : Forall (w_lib lsK OWK PL lo SPv) [(am, am + 24)]).
        { constructor; [w_lib_ref HARR RMontRR_not_one| constructor]. }
        assert (WOK5 : Forall (w_ok OWK LB lsK PL EA SPv [RMontRR]) [(am, am + 24)]).
        { constructor; [eapply (w_struct OWK LB lsK PL EA SPv false [RMontRR] _ RMontRR am); [left; reflexivity| exact HARR| exact RMontRR_not_one| cbn; clear; lia| cbn; clear; lia]| constructor]. }
        set (rr' := mkBN (bn_d rr) nb (bn_top n) (bn_neg rr) (bn_flags rr)).
        assert (EBL : length (bn_blocks rr') = length (bn_blocks (getbn RMontRR lsK))).
        { fold rr. unfold bn_blocks, bn_dmax, rr'. cbn [bn_d bn_buf]. rewrite Edr. reflexivity. }
        assert (LS4 : lib_state (setbn RMontRR rr' lsK) m4 OWK PL EA).
        { unfold lib_state. eapply (lib_state_close [] lsK m4 OWK PL EA RMontRR am); [| exact ND2| exact HARR| exact RMontRR_not_one| | |].
          - eapply (lib_state_frame ΣK LB SPv USTACK_TOP); [exact HEAPM| exact LSHM| exact MU5| exact WM5| exact FROK| exact WOK5].
          - exists Dr. split.
            + unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, rr', MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. rewrite Lnb. exact BNr.
            + apply (fun ARRnb__ => bn_arr_of_nofr PL RMontRR m4 OWK Dr _ PWF2 NOFR RMontRR_not_one ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, rr'. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| assumption].
          - unfold bg_ok, bn_dmax, rr'. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BG_DMAX in *.
            split; [exact LMnb|]. split; [clear - HIDZ; unfold bn_dmax in *; lia|]. split; [clear - OKR3; unfold bn_dmax in *; lia| exact OKR4].
          - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, rr'. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
        assert (ENV4 : CENV (mfr j0 c1 c2 c3 j4 j5) USED ΣK (setbn RMontRR rr' lsK) m4 OWK).
        { apply cenv_setbnA; [| exact HVx2 | exact EBL].
          eapply (cenv_silentA_p LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0); [exact EVM | exact PARTS2 | exact MU5 | exact WM5 | exact HWL5 | assumption | assumption | cbn [app]; eassumption | exact FSZ2]. }
        do 2 step. apply evt_done.
        eapply L_exit; [exact ENV4 | exact LS4].
    Qed.

    Lemma mont_open : forall pre used Σ ls m OW, CENV pre used Σ ls m OW -> lib_state ls m OW PL EA ->
      In (qm, am, 96) OW /\ rw_cells bgbsegs m (am + 72) (mont_cells ls) /\ acc bgbsegs m am 96 /\ am mod 8 = 0
      /\ 0 < am /\ am + 96 <= FB - 16 /\ (am + 96 <= SHLO \/ SHHI <= am).
    Proof using HPM LOF CS16.
      intros pre used Σ ls m OW ENV LS.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & _).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & (_ & _ & PM) & _). rewrite HPM in PM. unfold MONT_CTX_SZ in PM.
      pose proof (AH_range _ _ _ _ _ _ _ HEAP PM) as (M0 & M16 & _ & MC & MI).
      destruct (AH_acc _ _ _ _ (qm, am, 96) HEAP ltac:(apply in_or_app; left; exact PM)) as (_ & ACC). cbn [blk_addr blk_size fst snd] in ACC.
      pose proof (AH_offsh _ _ _ _ (qm, am, 96) HEAP ltac:(apply in_or_app; left; exact PM)) as OS. cbn [blk_addr blk_size fst snd] in OS.
      split; [exact PM|]. split; [exact (lib_state_mont_cells _ _ _ _ _ _ _ am qm LS HPM)|]. split; [exact ACC|].
      split; [clear - M16; Z.div_mod_to_equations; lia|]. split; [exact M0|]. split; [unfold BnHeapA.ACEIL in *; clear - MC CEIL LOF CS16; lia | exact OS].
    Qed.

    Lemma L_rr0 : forall ri j0 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x25 t3 t4 t5 t6 : word) F1 fc1,
      0 <= ri <= 32832 ->
      CENV (mfr j0 (C8 (Z_to_bv 64 (shad (am + 88)))) (C8 (Z_to_bv 64 (am + 88))) (C8 (Z_to_bv 64 (am + 24))) j4 j5) USED ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
      implA (ms_rr0 ri lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 x22 x23 (Z_to_bv 64 SHB) x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226c04) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros RIR ENVK LSK.
      pose proof (hpl_mont PL RMontRR am qm eq_refl HPM) as HPRR.
      pose proof (hpl_wref PL RMontRR HPRR) as WRR.
      destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      unfold ms_rr0, MallocRep.wz. rewrite bbind_zero.
      apply implA_from_evt. do 2 step.
      eapply KZEROX; [exact ENVK | exact LSK | exact (ref_at_montRR lsK OWK PL am qm HPM) | exact WRR |].
      intros mq1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ls1 ENV1 LS1. clear ENVK LSK.
      retpc 2255884. fold ls1.
      rewrite bbind_getst.
      destruct (Z.eqb_spec (st_ri ls1) ri) as [ERI|NRI]; cbn [negb]; cbv beta iota.
      2:{ apply evt_done. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
      destruct (mont_open _ _ _ _ _ _ ENV1 LS1) as (PM & MCELLS & ACCM & ALM & M0 & MSEP & MOFF).
      unfold mont_cells, MallocRep.wz in MCELLS. rewrite ERI in MCELLS.
      pose proof (munch_refl (@nil (Z * Z)) mq1) as MU1.
      pose proof ENV1 as (_ & _ & _ & _ & _ & _ & _ & _ & FRc & _). unfold mfr in FRc. cbn [app] in FRc.
      step.

      shl_with ACCM ALM. step. chk0.
      step. step.
      rewrite (sx32_small ri) by (clear - RIR; lia).
      ub.
      do 2 step.
      setreg 11%Z (Z_to_bv 64 (ri * 2)) ltac:(f_equal; rewrite (unsigned_lit ri) by (clear - RIR; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia);
                                              rewrite bn_swrap32_small by (clear - RIR; lia); clear; lia).
      step. apply evt_done. clear MCELLS ACCM MU1 FRc.
      eapply (KCALL _ _ _ _ _ USED MC USED CS); [exact ES0 | exact ENV1 | exact LS1 | exact LOF | mc0 | exact USEDT
        | intros PRE UW; eapply BN_set_bit_walkA; [pre_wk PRE STK_SETBIT | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226a54 CTX)
              | reflexivity | exact (ref_at_montRR ls1 OWK PL am qm HPM) | exact WRR | reflexivity | reflexivity | clear - RIR; lia]
        | hres |].
      intros u2 Σ2 ls2 mq2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
      clear ENV1 LS1.
      retpc 2255932.
      apply implA_from_evt.
      step. if_false.
      do 5 step. step. apply evt_done.
      unfold BN_mod.
      eapply (KCALL _ _ _ _ _ USED BN_DIV_FT_COST USED CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | unfold BN_DIV_FT_COST; mc0 | exact USEDT
        | intros PRE UW; eapply (BN_div_walkA) with (dv := None) (rm := Some RMontRR) (num := RMontRR) (dvs := RMontN) (adv := 0) (arm := am) (anum := am) (advs := am + 24) (ac := ac) (qc := qc);
            [ eapply bn_preA_wk; [exact PRE | exact STK_DIV | clear; lia] | exact UW
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226a70 CTX)
            | reflexivity | exact HPC | reflexivity | exact (ref_at_montRR ls2 OW2 PL am qm HPM) | exact (ref_at_montRR ls2 OW2 PL am qm HPM) | exact (ref_at_montN ls2 OW2 PL am qm HPM)
            | intros d0 E0; discriminate E0 | intros r0 E0; injection E0 as <-; exact HPRR | exact RMontRR_not_one | exact RMontN_not_one | exact (hpl_nbuf PL RMontRR HPRR)
            | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
        | hres |].
      intros u3 Σ3 ls3 mq3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & ->). unfold MallocRep.wz.
      clear ENV2 LS2.
      retpc 2255960.
      apply implA_from_evt.
      step. if_false. apply evt_done.
      eapply L_fix; [exact ENV3 | exact LS3].
    Qed.

  End PhaseD.

  Section PhaseC.
    Variables (gp s0r : word) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (LBo : list block) (PLo : placement) (EA : BnRepDefs.err_addrs) (TOTAL : Z).
    Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 mE : mem).
    Variables (am ac : Z) (qm qc : bptr) (f : Z) (g : nat) (junk : list byte) (qt qb : bptr).
    Variables (rRi : bnref) (aRi : Z) (ri : Z).
    Hypothesis ES0 : bv_unsigned s0r = SPv.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis HPC : pl_ctx PLo = Some (ac, qc).
    Hypothesis HPM : pl_mont PLo = Some (am, qm).
    Hypothesis HFT : pl_bn PLo RTmod = None.
    Hypothesis PWFo : pl_wf PLo.
    Hypothesis FROKo : frames_ok LBo PLo SPv USTACK_TOP.
    Hypothesis FALo : frames_al PLo.
    Hypothesis NOFRo : frames_lb PLo LBo.
    Hypothesis HF : In (f, 1%nat) FR.
    Hypothesis FRESH : forall b, In b LBo -> off_fr f 1 b.
    Hypothesis CTX : uk_ctx BN_MONT_CTX_SET (bv_unsigned raw :: ras).
    Hypothesis TOT2 : 2 <= TOTAL.
    Hypothesis HRiP : exists i, rRi = RPool i.
    Hypothesis RIR : 0 <= ri <= 32832.
    Variable Q : unit * ST -> rts RT -> machine_state -> Prop.

    Notation bt := (qt, f + 32, 24).
    Notation bb := (qb, f + 96, 16).
    Notation LB' := (bt :: bb :: LBo).
    Notation PL' := (pl_place_tmod PLo (f + 32) (f + 96)).
    Hypothesis ROOM' : fr_room 2 ls0 OW0 LB'.

    Hypothesis AXE : ax_pres LBo SPv (XW PLo) mE m0.

    Notation CENV := (cenvA LB' PL' lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
    Notation KCALL := (kcallA LB' PL' EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
    Notation KZEROX := (zero_callA LB' PL' EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF)).
    Notation KZERO := (is_zero_callA LB' PL' EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF)).
    Lemma LOFONE : lo <= FB - BN_IS_ONE_STACK. Proof using LOF STK_ONE. clear - LOF STK_ONE. lia. Qed.
    Notation KONE := (is_one_callA LB' PL' EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOFONE).
    Notation MFR w1 w3 j0 j4 j5 := (mfr f g junk j0 (C8 (Z_to_bv 64 (shad (am + 88)))) (C8 w1) (C8 w3) j4 j5).

    Lemma RiNT : rRi <> RTmod. Proof using HRiP. destruct HRiP as (i & ->). unfold RPool, RTmod, NFIX. clear. lia. Qed.
    Lemma RiNO : rRi <> ROne. Proof using HRiP. destruct HRiP as (i & ->). unfold RPool, ROne, NFIX. clear. lia. Qed.
    Lemma RiW : wref PL' rRi. Proof using HRiP. destruct HRiP as (i & ->). apply wref_pool. Qed.
    Lemma RiH : hpl PL' rRi. Proof using HRiP. destruct HRiP as (i & ->). apply hpl_pool. Qed.
    Lemma RiNB : nbuf PL' rRi. Proof using HRiP. destruct HRiP as (i & ->). apply nbuf_pool. Qed.
    Lemma TmNO : RTmod <> ROne. Proof using. unfold RTmod, ROne. clear. lia. Qed.

    Hypothesis EPI : forall mb j0 c1 c2 c3 j4 j5 Σk lsk mk OWk
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word) F' fc',
      ax_pres LBo SPv (XW PLo) mE mb ->
      cenvA LBo PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mb (mfr f g junk j0 c1 c2 c3 j4 j5) 2 Σk lsk mk OWk -> lib_state lsk mk OWk PLo EA ->
      implA (TRet (tt, lsk)) Σk Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) x19 (Z_to_bv 64 1) x21 x22 x23 x24 x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F' (wz 0x226d24) fc' None mk (seg_rom bgbsegs)).

    Lemma L_n0 : forall j0 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 t3 t4 t5 t6 : word) F1 fc1,
      CENV (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 2 ΣK lsK mK OWK -> lib_state lsK mK OWK PL' EA -> ref_at lsK OWK PL' rRi aRi ->
      implA (ms_n0 rRi ri lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 (Z_to_bv 64 aRi) x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226b18) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK HARi.
      pose proof RiNT as RNT. pose proof RiNO as RNO.
      destruct (env_bounds lo SPv FB s0w raw ras LB' PL' TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      unfold ms_n0, MallocRep.wz.
      apply implA_from_evt. do 5 step. step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 2 BN_DIV_FT_COST 2 CS); [exact ES0 | exact ENVK | exact LSK | exact LOF | unfold BN_DIV_FT_COST; mc0 | exact TOT2
        | intros PRE UW; eapply (BN_div_walkA) with (dv := Some rRi) (rm := None) (num := rRi) (dvs := RTmod) (adv := aRi) (arm := 0) (anum := aRi) (advs := f + 32) (ac := ac) (qc := qc);
            [ eapply bn_preA_wk; [exact PRE | exact STK_DIV | clear; lia] | exact UW
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226948 CTX)
            | reflexivity | exact HPC | exact HARi | reflexivity | exact HARi | apply ref_at_place_tmod_same
            | intros d0 E0; injection E0 as <-; exact RiW | intros r0 E0; discriminate E0 | exact RNO | exact TmNO | exact RiNB
            | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
        | hres |].
      intros u1 Σ1 ls1 mq1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & ->). unfold MallocRep.wz.
      pose proof (ref_at_stable _ _ _ _ PL' _ _ RS1 HARi) as HARi1.
      clear ENVK LSK HARi RS1.
      retpc 2255664.
      rewrite bbind_get. cbv zeta.
      set (x := getbn rRi ls1) in *. set (n0 := if (0 <? bn_top x)%nat then nth 0 (bn_buf x) 0 else 0) in *.
      rewrite (bbind_getst_setmont (fun st => st_ri st) (fun _ => n0)).

      destruct (open_for_read_u LB' PL' EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ rRi aRi 16 ENV1 LS1 HARi1 RNO ltac:(clear; lia) (LOF16 lo FB LOF))
        as (D & BNX & OKX & UX & ST1 & MI1 & SEPX & SEPD & ACCX & ALX & ACCD & ALD & BDX & SLO & AX0 & UBT).
      fold x in BNX, OKX, UX, SEPD, ACCD, BDX, UBT. pose proof OKX as (OKX1 & OKX2 & OKX3 & OKX4). unfold BG_DMAX, bn_dmax in OKX2, OKX3.
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNX.
      assert (TOPX : 0 <= Z.of_nat (bn_top x) <= 512) by (clear - OKX2 OKX3; lia).
      pose proof (munch_refl (@nil (Z * Z)) mq1) as MU1.
      pose proof ENV1 as (OK1 & HEAP1 & _ & _ & _ & _ & _ & _ & FRc & FSZc & _). unfold mfr in FRc. cbn [app] in FRc.
      pose proof OK1 as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK1 & _ & NOFR1).
      destruct (mont_open lo SPv FB s0w raw ras LB' PL' EA TOTAL Σ0 ls0 OW0 m0 am qm LOF HPM _ _ _ _ _ _ ENV1 LS1) as (PM & MCELLS & ACCM & ALM & M0 & MSEP & MOFF).
      unfold mont_cells, MallocRep.wz in MCELLS.

      lazymatch goal with |- implA ?t _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ _ _ ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ ?r28 ?r29 ?r30 ?r31) ?FF _ ?fcc _ _ _) =>
        assert (CONT : forall (a0' : word),
                  implA t Σ1 Q
                    (MS (mkR r1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) r5 r6 r7 s0r (Z_to_bv 64 FB) a0' (Z_to_bv 64 n0) r12 r13 r14 r15 r16 r17
                             (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 (Z_to_bv 64 aRi) x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32))
                             (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) r28 r29 r30 r31)
                        FF (Z_to_bv 64 0x226bb4) fcc None mq1 (seg_rom bgbsegs)))
      end.
      { intros a0'. clear BNX UX ACCX ACCD MU1.
        pose proof (munch_refl [(am + 72, am + 96)]%Z mq1) as MUm. pose proof (wmono_refl bgbsegs mq1) as WMm.
        assert (OFFm : offshW [(am + 72, am + 96)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - MOFF; lia).
        apply implA_from_evt.
        do 3 step. shl_with ACCM ALM. chk0.
        step. step. ub.
        do 3 step. shl_with ACCM ALM. chk0.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq2 end.

        pose proof (AH_nodup_l _ _ _ _ HEAP1) as ND1.
        assert (HWL : Forall (w_lib ls1 OW1 PL' lo SPv) [(am + 72, am + 96)]).
        { constructor; [| constructor]. right; left. exists (qm, am, 96). split; [exact PM|]. cbn [blk_addr blk_size fst snd]. clear. lia. }
        set (ls2 := set_mont (st_ri ls1) n0 ls1).
        assert (LS2 : lib_state ls2 mq2 OW1 PL' EA).
        { unfold lib_state, ls2. eapply (lib_state_set_mont Σ1 LB' SPv USTACK_TOP false [] ls1 mq1 mq2 OW1 PL' EA am qm (st_ri ls1) n0);
            [exact HEAP1 | exact LS1 | exact FROK1 | exact HPM | unfold MONT_CTX_SZ; exact MUm | exact WMm | unfold mont_cells, MallocRep.wz; cbn [st_n0 st_ri set_mont]; exact MCELLS]. }
        assert (ENV2 : CENV (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 2 Σ1 ls2 mq2 OW1).
        { apply cenv_set_montA.
          eapply (cenv_silentA LB' PL' EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0); [exact ENV1 | exact LS1 | exact MUm | exact WMm | exact HWL | assumption | assumption | unfold mfr; cbn [app]; eassumption | exact FSZc]. }
        clear MCELLS MUm WMm OFFm ACCM HWL ENV1 LS1 HEAP1 FRc ST1 MI1.
        apply evt_done.

        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 (ref_at_place_tmod_same ls2 OW1 PLo (f + 32) (f + 96))) as VT.
        eapply ms_rr_switch; [exact VT|]. intros ND.
        pose proof ENV2 as (_ & HEAP2 & ST2 & MI2 & AXP2 & _ & _ & _ & FR2 & FSZ2 & _). unfold mfr in FR2. cbn [app] in FR2.
        assert (INC : forall b, In b LBo -> In b LB') by (intros b Hb; right; right; exact Hb).
        assert (LS3 : lib_state (setbn RTmod (bn_nil 0) ls2) mq2 OW1 PLo EA).
        { unfold lib_state. eapply (lib_state_unplace_tmod false [] [] ls2 mq2 OW1 PLo EA (f + 32) (f + 96)); [exact LS2 | exact PWFo | exact HFT | exact ND | intros r []]. }
        assert (ENV3 : cenvA LB' PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mq2 (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 2 Σ1 (setbn RTmod (bn_nil 0) ls2) mq2 OW1).
        { apply cenv_setbnA; [| exact VT | unfold bn_blocks; rewrite ND; reflexivity].
          eapply cenv_switch_plA; [exact ENV2 | exact (frames_ok_incl LBo LB' PLo _ _ FROKo INC) | exact FALo | exact (frames_lb_incl PLo LBo LB' NOFRo INC)]. }
        assert (AX2 : ax_pres LBo SPv (XW PLo) m0 mq2).
        { eapply (ax_pres_unplace Σ1 OW1 LBo mq2 PLo (f + 32) (f + 96) bt bb SPv m0 mq2 HEAP2); [clear - CEIL LOFB FBSP; lia | | | | | exact AXP2]; cbn [blk_addr blk_size fst snd]; clear; lia. }

        pose proof (AH_fr_geo _ _ _ _ f 1%nat HEAP2 HF) as GEO. destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in *. unfold SEGTOP_A in G4.
        pose proof (AH_ceil _ _ _ _ HEAP2) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
        assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
        assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
        { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
          assert (f / 8 + 16 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 16); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia | lia]). lia. }
        assert (HEAPb : AHEAP Σ1 OW1 (bb :: LBo) mq2).
        { apply (frame_obj_close Σ1 OW1 (bb :: LBo) mq2 f 1%nat bt HF HEAP2). split; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia. }
        assert (HEAPc : AHEAP Σ1 OW1 LBo mq2).
        { apply (frame_obj_close Σ1 OW1 LBo mq2 f 1%nat bb HF HEAPb). split; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia. }
        destruct (AH_fr_wr _ _ _ _ f 1%nat HEAPc HF) as (_ & WS). change (fs_size 1) with 128 in WS.
        destruct (wr_at_rw_CB mq2 (shad f) _ WS ltac:(clear; lia)) as (js & FRS). change (Z.to_nat (128 / 8)) with 16%nat in FRS.
        apply (rw_cells_split_CB bgbsegs _ _ [] 16 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
        pose proof (munch_refl [(shad f, shad f + 16)]%Z mq2) as MU. pose proof (wmono_refl bgbsegs mq2) as WM.
        apply implA_from_evt.
        step.
        do 5 sbstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq3 end.

        assert (HEAP' : AHEAP Σ1 OW1 LBo mq3).
        { eapply (AH_frame_fr Σ1 OW1 LBo mq2 mq3 _ f 1%nat HF HEAPc MU WM); [| exact FRESH].
          constructor; [right; right; cbn [fst snd]; change (fs_size 1) with 128; clear; lia | constructor]. }
        destruct (cenv_scope_closeA [bt; bb] LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mq2
                    (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 2 Σ1 (setbn RTmod (bn_nil 0) ls2) mq2 mq3 OW1 _ f 1%nat
                    ENV3 LS3 HF FRESH MU WM
                    ltac:(constructor; [right; cbn [fst snd]; change (fs_size 1) with 128; clear; lia | constructor])
                    HEAPc HEAP' FROKo NOFRo ltac:(assumption) ltac:(assumption) ltac:(unfold mfr; cbn [app]; eassumption) FSZ2) as (ENV4 & LS4 & AX4).
        apply evt_done.
        eapply (L_rr0 gp s0r lo SPv FB s0w raw ras LBo PLo EA TOTAL Σ0 ls0 OW0 mq3 am ac qm qc f g junk ES0 LOF HPC HPM CTX Q 2 TOT2); [| exact RIR | exact ENV4 | exact LS4].
        intros. eapply (EPI mq3); [exact (ax_pres_trans _ _ _ _ _ _ AXE (ax_pres_trans _ _ _ _ _ _ AX2 AX4)) | eassumption | eassumption]. }
      apply implA_from_evt.
      step. if_false.
      ub.
      do 3 step. shl_with ACCX ALX. chk0.
      step. rewrite (sx32_small (Z.of_nat (bn_top x))) by (clear - TOPX; lia).
      step. rewrite lts_signed by (clear - TOPX; lia). if_cases KT; zify_cond KT.
      -
        assert (EN0 : n0 = 0) by (unfold n0; replace (0 <? bn_top x)%nat with false by (symmetry; apply Nat.ltb_ge; clear - KT; lia); reflexivity).
        step. apply evt_done. rewrite <- EN0. apply CONT.
      -
        assert (EN0 : n0 = nth 0 (bn_buf x) 0) by (unfold n0; replace (0 <? bn_top x)%nat with true by (symmetry; apply Nat.ltb_lt; clear - KT; lia); reflexivity).
        do 2 step. shl_with ACCX ALX. chk0.
        step.
        destruct (UBT ltac:(clear - KT; lia)) as (DPOS & _).
        ub.
        do 2 step. shl_limb ACCD ALD BDX 0%Z. chk0.

        assert (NTH0 : nth_error (wlimbs (bn_buf x)) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 (bn_buf x) 0))) by (apply (wlimbs_nth (bn_buf x) 0); clear - KT OKX2; lia).
        pose proof (u64arr_read bgbsegs mq1 D _ 0 _ (wa D) UX NTH0 ltac:(clear; lia) ltac:(f_equal; clear; lia)) as RD0.
        step. clear RD0 NTH0.
        step. apply evt_done. rewrite <- EN0. apply CONT.
    Qed.

    Lemma L_sub : forall j0 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 t3 t4 t5 t6 : word) F1 fc1,
      CENV (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 2 ΣK lsK mK OWK -> lib_state lsK mK OWK PL' EA -> ref_at lsK OWK PL' rRi aRi ->
      implA (ms_sub rRi ri lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 (Z_to_bv 64 aRi) x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226ad4) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK HARi.
      pose proof RiNT as RNT. pose proof RiNO as RNO.
      destruct (env_bounds lo SPv FB s0w raw ras LB' PL' TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      unfold ms_sub, MallocRep.wz.
      apply implA_from_evt. do 3 step. step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 2 MC 2 CS); [exact ES0 | exact ENVK | exact LSK | exact LOF | mc0 | exact TOT2
        | intros PRE UW; eapply BN_lshift_walkA; [pre_wk PRE STK_LSH | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_2268fc CTX)
              | reflexivity | exact HARi | exact RiH | exact HARi | exact RNO | exact RiNB
              | reflexivity | reflexivity | reflexivity | clear; change (2^31) with 2147483648; change (2^30) with 1073741824; lia]
        | hres |].
      intros u1 Σ1 ls1 mq1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (ref_at_stable _ _ _ _ PL' _ _ RS1 HARi) as HARi1.
      clear ENVK LSK HARi RS1.
      retpc 2255588.
      rewrite bbind_get.
      set (x := getbn rRi ls1) in *.
      apply implA_from_evt.
      step. if_false.
      do 2 step.
      eapply KZERO; [exact ENV1 | exact LS1 | exact HARi1 | exact RNO |].
      intros mq2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
      retpc 2255600. fold x.
      change ((bn_top x =? 0)%nat) with (is_zero_pure x).
      destruct (is_zero_pure x) eqn:EZ; cbn [negb Z.b2z]; cbv beta iota.
      -
        step. if_false.
        do 2 step. step. apply evt_done.
        eapply (KCALL _ _ _ _ _ 2 MC 2 CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | mc0 | exact TOT2
          | intros PRE UW; eapply BN_set_word_walkA with (w := BN_MASK2); [pre_wk PRE STK_SETW | exact UW
                | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226918 CTX)
                | reflexivity | exact HARi1 | exact RiW | reflexivity | apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity | vm_compute; split; [intros HH; discriminate HH | reflexivity]]
          | hres |].
        intros u3 Σ3 ls3 mq3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
        retpc 2255616.
        apply implA_from_evt. step. if_true. apply evt_done.
        eapply L_n0; [exact ENV3 | exact LS3 | exact (ref_at_stable _ _ _ _ PL' _ _ RS3 HARi1)].
      -
        destruct (Z.ltb_spec (lval (firstn (bn_top x) (bn_buf x))) 1) as [LV|LV].
        { apply evt_done. unfold bbind, bunr. cbn [bind unreachable tree_ops tbind]. apply implA_unr. }
        step. if_true.
        do 2 step. step. apply evt_done.
        eapply (KCALL _ _ _ _ _ 2 MC 2 CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | mc0 | exact TOT2
          | intros PRE UW; eapply W_sub_wordAF.BN_sub_word_walkA with (w := 1); [pre_wk PRE STK_SUBW | exact UW
                | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_22692c CTX)
                | reflexivity | exact HARi1 | exact RiW | reflexivity | reflexivity | clear; lia | fold x; clear - LV; lia]
          | hres |].
        intros u3 Σ3 ls3 mq3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
        retpc 2255636.
        apply implA_from_evt. step. if_false. apply evt_done.
        eapply L_n0; [exact ENV3 | exact LS3 | exact (ref_at_stable _ _ _ _ PL' _ _ RS3 HARi1)].
    Qed.

    Lemma L_inv : forall j0 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 t3 t4 t5 t6 : word) F1 fc1,
      CENV (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL' EA -> ref_at lsK OWK PL' rRi aRi ->
      implA (ms_inv rRi ri lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 (Z_to_bv 64 aRi) x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226aa4) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK HARi.
      pose proof RiNT as RNT. pose proof RiNO as RNO.
      destruct (env_bounds lo SPv FB s0w raw ras LB' PL' TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      destruct (open_for_call LB' PL' EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ rRi aRi ENVK LSK HARi RNO)
        as (_ & _ & _ & _ & _ & _ & SEPRi & _ & _ & _ & _ & _ & ARi0).
      unfold ms_inv, MallocRep.wz. rewrite bbind_get.
      apply implA_from_evt. do 2 step.
      eapply KONE; [exact ENVK | exact LSK | apply ref_at_place_tmod_same | exact TmNO |].
      intros mq1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
      retpc 2255532.
      destruct (is_one_pure (getbn RTmod lsK)) eqn:EONE; cbn [Z.b2z]; cbv beta iota.
      -
        step. if_false.
        do 2 step.
        eapply KZEROX; [exact ENV1 | exact LS1 | exact HARi | exact RiW |].
        intros mq2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ls2 ENV2 LS2. clear ENV1 LS1.
        retpc 2255544. rewrite bbind_zero. fold ls2.
        step. apply evt_done.
        eapply L_sub; [eapply cenv_used_le; [exact ENV2 | clear; lia] | exact LS2 | unfold ls2; apply ref_at_setbn; exact HARi].
      -
        step. if_true.
        do 4 step. step. apply evt_done.
        pose proof ENV1 as (_ & _ & _ & _ & _ & _ & CNT1 & _).
        eapply (KCALL _ _ _ _ _ 0 2 2 CS); [exact ES0 | exact ENV1 | exact LS1 | exact LOF | clear; lia | exact TOT2
          | intros PRE UW; eapply (InvClosedAF.BN_mod_inverse_closedA) with (rR := rRi) (ra_ := RMontRR) (rn := RTmod) (aR := aRi) (aa := am) (an := f + 32) (ac := ac) (qc := qc);
              [ eapply bn_preA_wk; [exact PRE | exact STK_INV | vm_compute; intros XXc; discriminate XXc] | exact (fr_room_eq 2 _ _ _ _ _ ROOM' CNT1) | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_2268e8 CTX)
              | reflexivity | exact HARi | exact RiH | apply ref_at_place_tmod; [discriminate | exact (ref_at_montRR lsK OWK PLo am qm HPM)] | exact RMontRR_not_one
              | apply ref_at_place_tmod_same | exact TmNO | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity ]
          | hres |].
        intros u3 Σ3 ls3 mq3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & ->). unfold MallocRep.wz.
        retpc 2255568.
        apply implA_from_evt.
        step. if_cases KR; rewrite ?unsigned_lit in KR by (clear - ARi0 SEPRi B2 B3; lia); zify_cond KR. { exfalso. clear - KR ARi0. lia. }
        apply evt_done.
        eapply L_sub; [exact ENV3 | exact LS3 | exact (ref_at_stable _ _ _ _ PL' _ _ RS3 HARi)].
    Qed.

  End PhaseC.

  Section PhaseB.
    Variables (gp s0r : word) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (LBo : list block) (PLo : placement) (EA : BnRepDefs.err_addrs) (TOTAL : Z).
    Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 mE : mem).
    Variables (am ac : Z) (qm qc : bptr) (f : Z) (g : nat) (junk : list byte) (qt qb : bptr).
    Variables (rd rRi : bnref) (ad aRi : Z).
    Hypothesis ES0 : bv_unsigned s0r = SPv.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis HPC : pl_ctx PLo = Some (ac, qc).
    Hypothesis HPM : pl_mont PLo = Some (am, qm).
    Hypothesis HFT : pl_bn PLo RTmod = None.
    Hypothesis FROKo : frames_ok LBo PLo SPv USTACK_TOP.
    Hypothesis FALo : frames_al PLo.
    Hypothesis NOFRo : frames_lb PLo LBo.
    Hypothesis HF : In (f, 1%nat) FR.
    Hypothesis FRESH : forall b, In b LBo -> off_fr f 1 b.
    Hypothesis CTX : uk_ctx BN_MONT_CTX_SET (bv_unsigned raw :: ras).
    Hypothesis TOT2 : 2 <= TOTAL.
    Hypothesis HRiP : exists i, rRi = RPool i.
    Hypothesis NROd : rd <> ROne.
    Variable Q : unit * ST -> rts RT -> machine_state -> Prop.

    Notation bt := (qt, f + 32, 24).
    Notation bb := (qb, f + 96, 16).
    Notation LB' := (bt :: bb :: LBo).
    Notation PL' := (pl_place_tmod PLo (f + 32) (f + 96)).
    Hypothesis ROOM' : fr_room 2 ls0 OW0 LB'.
    Hypothesis AXE : ax_pres LBo SPv (XW PLo) mE m0.

    Notation CENV := (cenvA LB' PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
    Notation MFR w1 w3 j0 j4 j5 := (mfr f g junk j0 (C8 (Z_to_bv 64 (shad (am + 88)))) (C8 w1) (C8 w3) j4 j5).

    Hypothesis EPI : forall mb j0 c1 c2 c3 j4 j5 Σk lsk mk OWk
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word) F' fc',
      ax_pres LBo SPv (XW PLo) mE mb ->
      cenvA LBo PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mb (mfr f g junk j0 c1 c2 c3 j4 j5) 2 Σk lsk mk OWk -> lib_state lsk mk OWk PLo EA ->
      implA (TRet (tt, lsk)) Σk Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) x19 (Z_to_bv 64 1) x21 x22 x23 x24 x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F' (wz 0x226d24) fc' None mk (seg_rom bgbsegs)).

    Lemma NFo : forall x, f <= x < f + 128 -> ~ rin_ivs (pl_frames PLo) x.
    Proof using NOFRo FRESH. intros x Hx. exact (fr_no_placed PLo LBo f 1%nat x NOFRo FRESH Hx). Qed.

    Lemma L_B3 : forall ri j0 j4 j5 (jb : list byte) ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F1 fc1,
      0 <= ri <= 32832 ->
      CENV (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PLo EA ->
      ref_at lsK OWK PLo rd ad -> ref_at lsK OWK PLo rRi aRi ->
      rw_cells bgbsegs mK (f + 32) [C8 (Z_to_bv 64 (f + 96)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
      rw_cells bgbsegs mK (f + 96) [CB 16 jb] ->
      implA (ms_b3 rd rRi ri lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 aRi) (Z_to_bv 64 ad) (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226a4c) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros RIR ENVK LSK HAd HARi TCELLS BCELLS.
      destruct (env_bounds lo SPv FB s0w raw ras LB' PLo TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      unfold ms_b3, MallocRep.wz. rewrite bbind_get. set (bm := getbn rd lsK) in *.
      destruct (Nat.eqb_spec (bn_top bm) 0) as [E0|NE0].
      { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
      cbv zeta. rewrite bbind_set.
      set (b0 := nth 0 (bn_buf bm) 0) in *.
      destruct (open_for_read_u LB' PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ rd ad 16 ENVK LSK HAd NROd ltac:(clear; lia) (LOF16 lo FB LOF))
        as (D & BNX & OKX & UX & ST1 & MI1 & SEPX & SEPD & ACCX & ALX & ACCD & ALD & BDX & SLO & AX0 & UBT).
      fold bm in BNX, OKX, UX, SEPD, ACCD, BDX, UBT. pose proof OKX as (OKX1 & OKX2 & OKX3 & OKX4). unfold BG_DMAX, bn_dmax in OKX2, OKX3.
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNX.
      assert (LB0 : 0 <= b0 < 2^64).
      { pose proof (limbs_nth (bn_buf bm) 0 OKX1) as H. fold b0 in H. unfold limb, BW in H. clear - H. lia. }
      pose proof (munch_refl (@nil (Z * Z)) mK) as MU1.
      pose proof ENVK as (OK1 & HEAP1 & _ & _ & _ & _ & _ & _ & FRc & FSZc & _). unfold mfr in FRc. cbn [app] in FRc.
      pose proof OK1 as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK1 & _ & NOFR1).
      pose proof (AH_fr_geo _ _ _ _ f 1%nat HEAP1 HF) as GEO. destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in *. unfold SEGTOP_A in G4.
      pose proof (AH_ceil _ _ _ _ HEAP1) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
      assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
      assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
      apply (rw_cells_split_CB bgbsegs _ _ [] 16 _ [] [8; 8]%nat) in BCELLS; [| reflexivity]. cbn [mk_CB_cells app] in BCELLS.
      apply implA_from_evt.
      ub.
      do 2 step. shl_with ACCX ALX. chk0.
      step.
      destruct (UBT ltac:(clear - NE0; lia)) as (DPOS & _).
      ub.
      do 2 step. shl_limb ACCD ALD BDX 0%Z. chk0.
      assert (NTH0 : nth_error (wlimbs (bn_buf bm)) (Z.to_nat 0) = Some (Z_to_bv 64 b0)) by (apply (wlimbs_nth (bn_buf bm) 0); clear - NE0 OKX2; lia).
      pose proof (u64arr_read bgbsegs mK D _ 0 _ (wa D) UX NTH0 ltac:(clear; lia) ltac:(f_equal; clear; lia)) as RD0.
      step. clear RD0 NTH0 MU1 BNX UX ACCX ACCD.
      pose proof (munch_refl [(f + 32, f + 56); (f + 96, f + 112)]%Z mK) as MU2. pose proof (wmono_refl bgbsegs mK) as WM2.
      remember (Z_to_bv 64 b0) as wb0 eqn:Ewb0.
      step. step. ub. step. subst wb0.
      do 2 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

      set (tm := mkBN (@None bptr) [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0) in *.
      rewrite v_sltu_b2z, !unsigned_lit in TCELLS by (clear - LB0; lia).
      replace (Z.b2z (0 <? b0)) with (Z.of_nat (if b0 =? 0 then 0%nat else 1%nat)) in TCELLS
        by (clear - LB0; destruct (Z.eqb_spec b0 0) as [E|E]; destruct (Z.ltb_spec 0 b0) as [H|H]; cbn; lia).

      assert (HW : Forall (w_fown [bt; bb] PLo lo SPv) [(f + 32, f + 56); (f + 96, f + 112)]).
      { constructor; [| constructor; [| constructor]]; right.
        - exists bt. split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. split; [clear; lia|]. split; [clear; lia|]. intros x Hx. apply NFo. clear - Hx. lia.
        - exists bb. split; [right; left; reflexivity|]. cbn [blk_addr blk_size fst snd]. split; [clear; lia|]. split; [clear; lia|]. intros x Hx. apply NFo. clear - Hx. lia. }
      destruct (cenv_own_storeA [bt; bb] LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0
                  (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 0 ΣK lsK mK m3 OWK _
                  ENVK LSK MU2 WM2 HW ltac:(assumption) ltac:(assumption) ltac:(unfold mfr; cbn [app]; eassumption) FSZc) as (ENV3 & LS3 & AX3).
      pose proof ENV3 as (_ & HEAP3 & _).

      pose proof LS3 as (_ & _ & _ & (WF3 & PWF3 & _ & (_ & M23 & _))).
      assert (VT : vref RTmod lsK) by (unfold vref; destruct WF3 as (ELn & _); rewrite ELn; unfold RTmod, NFIX; clear; lia).
      assert (GT : getbn RTmod lsK = bn_nil 0).
      { apply M23; [unfold RTmod, NFIX; clear; lia|]. rewrite pl_of_stored by exact stored_tmod. exact HFT. }
      assert (OKT : bg_ok tm).
      { unfold bg_ok, tm, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags length].
        split; [constructor; [unfold limb, BW; clear - LB0; lia| constructor; [unfold limb, BW; clear; lia| constructor]]|].
        split; [destruct (b0 =? 0); clear; lia|]. split; [clear; lia| left; reflexivity]. }
      assert (PWF' : pl_wf PL').
      { eapply (pl_wf_place_tmod ΣK OWK LBo m3 PLo (f + 32) (f + 96) SPv USTACK_TOP bt bb HEAP3 PWF3 FROKo HFT); cbn [blk_addr blk_size fst snd]; clear - G1; lia. }
      assert (ARR3 : u64arr bgbsegs m3 (f + 96) (wlimbs (bn_buf tm))).
      { destruct BCELLS as ((_ & BY) & WR). split; [exact BY | exact WR]. }
      assert (LSP : lib_state (setbn RTmod tm lsK) m3 OWK PL' EA).
      { unfold lib_state. eapply (lib_state_place_tmod false [] lsK m3 OWK PLo EA (f + 32) (f + 96) tm); [exact LS3 | exact PWF' | exact HFT | reflexivity | reflexivity | exact OKT | exact TCELLS | exact ARR3]. }
      assert (ENVP : cenvA LB' PL' lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m3 (MFR (Z_to_bv 64 (am + 88)) (Z_to_bv 64 (am + 24)) j0 j4 j5) 0 ΣK (setbn RTmod tm lsK) m3 OWK).
      { apply cenv_setbnA; [| exact VT | rewrite GT; reflexivity].
        eapply cenv_switch_plA; [exact ENV3 | | |].
        - eapply (frames_ok_place_tmod LBo PLo (f + 32) (f + 96) SPv USTACK_TOP bt bb FROKo); cbn [blk_addr blk_size fst snd]; clear; lia.
        - apply (frames_al_place_tmod PLo (f + 32) (f + 96) FALo); clear - F8; Z.div_mod_to_equations; lia.
        - eapply (frames_lb_place_tmod LBo PLo (f + 32) (f + 96) bt bb NOFRo); [clear - F8; Z.div_mod_to_equations; lia | clear - F8; Z.div_mod_to_equations; lia | | | |]; cbn [blk_addr blk_size fst snd]; clear; lia. }
      apply evt_done.
      eapply (L_inv gp s0r lo SPv FB s0w raw ras LBo PLo EA TOTAL Σ0 ls0 OW0 m3 mE am ac qm qc f g junk qt qb rRi aRi ri ES0 LOF HPC HPM HFT PWF3 FROKo FALo NOFRo HF FRESH CTX TOT2 HRiP RIR Q ROOM'
                (ax_pres_trans _ _ _ _ _ _ AXE AX3) EPI);
        [exact ENVP | exact LSP |].
      apply ref_at_setbn. apply ref_at_place_tmod; [destruct HRiP as (i & ->); unfold RPool, RTmod, NFIX; clear; lia | exact HARi].
    Qed.

    Notation KFLAGS := (get_flags_callA LB' PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF)).
    Lemma LOFNB : lo <= FB - BN_NUM_BITS_STACK. Proof using LOF CS112. clear - LOF CS112. lia. Qed.
    Notation KBITS := (num_bits_callA LB' PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
    Notation KZEROX := (zero_callA LB' PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF)).
    Notation KCALL := (kcallA LB' PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
    Local Ltac fr_store ENV LS ENV' LS' := fr_store_gen (cenv_frameA LB' PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0) FB SPv ENV LS ENV' LS'.
    Ltac fr_unf H ::= unfold mfr in H.

    Lemma L_B2 : forall j0 j1 j2 j4 j5 (jb : list byte) ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F1 fc1,
      CENV (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PLo EA ->
      ref_at lsK OWK PLo rd ad -> ref_at lsK OWK PLo rRi aRi ->
      rw_cells bgbsegs m0 (f + 32) [C8 (Z_to_bv 64 (f + 96)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
      rw_cells bgbsegs m0 (f + 96) [CB 16 jb] ->
      implA (ms_b2 rd rRi lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 aRi) (Z_to_bv 64 ad) (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x2269d8) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK HAd HARi TCELLS0 BCELLS0.
      destruct (env_bounds lo SPv FB s0w raw ras LB' PLo TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      destruct (open_for_call LB' PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ rd ad ENVK LSK HAd NROd)
        as (_ & _ & OKd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      pose proof OKd as (OKd1 & OKd2 & OKd3 & OKd4).
      set (bm := getbn rd lsK) in *. unfold BG_DMAX in OKd3.
      assert (CTd : Z.land (bn_flags bm) 4 = 0) by (destruct OKd4 as [E|E]; rewrite E; reflexivity).
      pose proof (W_int_invAF.nbits_range bm OKd) as NBR.
      unfold ms_b2, MallocRep.wz. rewrite (bbind_num_bits rd _ lsK OKd). fold bm. cbv zeta.
      set (nb := num_bits_pure bm) in *. set (ri := (nb + 63) / 64 * 64) in *.
      assert (RIR : 0 <= ri <= 32832).
      { unfold ri. clear - NBR. pose proof (Z.div_pos (nb + 63) 64 ltac:(lia) ltac:(lia)).
        pose proof (Z.mul_div_le (nb + 63) 64 ltac:(lia)). lia. }
      rewrite (bbind_getst_setmont (fun _ => ri) (fun st => st_n0 st)). rewrite bbind_zero.
      apply implA_from_evt. do 2 step. step.
      eapply KFLAGS; [exact ENVK | exact LSK | exact HAd | exact NROd |].
      intros mq1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
      retpc 2255332. fold bm. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTd.
      step. if_true. step. step.
      eapply KBITS; [exact ENV1 | exact LS1 | exact HAd | exact NROd | exact LOFNB |].
      intros mq2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
      retpc 2255356. fold bm. fold nb.
      step.
      setreg 11%Z (Z_to_bv 64 (nb + 63)) ltac:(f_equal; rewrite (unsigned_lit nb) by (clear - NBR; lia); rewrite bn_swrap32_small by (clear - NBR; lia); reflexivity).
      ub.
      step.
      fr_store ENV2 LS2 ENV2b LS2b. clear ENV2 LS2.
      do 2 step.
      destruct (mont_open lo SPv FB s0w raw ras LB' PLo EA TOTAL Σ0 ls0 OW0 m0 am qm LOF HPM _ _ _ _ _ _ ENV2b LS2b) as (PM & MCELLS & ACCM & ALM & M0 & MSEP & MOFF).
      setreg 10%Z (Z_to_bv 64 (shad (am + 88))) ltac:(f_equal; rewrite (unsigned_lit (am + 88)) by (clear - M0 MSEP B2 B3; lia); unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
      fr_store ENV2b LS2b ENV3 LS3. clear ENV2b LS2b.

      clear PM ACCM.
      destruct (mont_open lo SPv FB s0w raw ras LB' PLo EA TOTAL Σ0 ls0 OW0 m0 am qm LOF HPM _ _ _ _ _ _ ENV3 LS3) as (PM & MCELLS & ACCM & _ & _ & _ & _).
      unfold mont_cells, MallocRep.wz in MCELLS.
      pose proof ENV3 as (OK3 & HEAP3 & ST3 & MI3 & _ & _ & _ & _ & FR3 & FSZ3 & _). unfold mfr in FR3. cbn [app] in FR3.
      pose proof OK3 as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK3 & _ & NOFR3).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(am + 72, am + 96)]%Z mm) as MUm; pose proof (wmono_refl bgbsegs mm) as WMm end.
      assert (OFFm : offshW [(am + 72, am + 96)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - MOFF; lia).
      shl_with ACCM ALM. chk0.
      do 4 step.

      setreg 10%Z (Z_to_bv 64 ri)
        ltac:(f_equal; rewrite ?(unsigned_lit (nb + 63)) by (clear - NBR; lia); rewrite ?Z.shiftl_mul_pow2 by (clear; lia);
              rewrite ?(unsigned_lit ((nb + 63) * 2 ^ 1)) by (clear - NBR; lia);
              replace (((nb + 63) * 2 ^ 1) ≫ 58) with 0 by (symmetry; rewrite Z.shiftr_div_pow2 by (clear; lia); apply Z.div_small; clear - NBR; lia);
              rewrite Z.add_0_r; rewrite ?(unsigned_lit (nb + 63)) by (clear - NBR; lia);
              first [apply land_m64_small | symmetry; apply land_m64_small]; clear - NBR; lia).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq3 end.
      assert (HWL : Forall (w_lib lsK OWK PLo lo SPv) [(am + 72, am + 96)]).
      { constructor; [| constructor]. right; left. exists (qm, am, 96). split; [exact PM|]. cbn [blk_addr blk_size fst snd]. clear. lia. }
      set (ls4 := set_mont ri (st_n0 lsK) lsK).
      assert (LS4 : lib_state ls4 mq3 OWK PLo EA).
      { unfold lib_state, ls4. eapply (lib_state_set_mont ΣK LB' SPv USTACK_TOP false [] lsK _ mq3 OWK PLo EA am qm ri (st_n0 lsK));
          [exact HEAP3 | exact LS3 | exact FROK3 | exact HPM | unfold MONT_CTX_SZ; exact MUm | exact WMm | unfold mont_cells, MallocRep.wz; cbn [st_n0 st_ri set_mont]; exact MCELLS]. }
      assert (ENV4 : CENV (mfr f g junk j0 (C8 (Z_to_bv 64 (shad (am + 88)))) (C8 (Z_to_bv 64 (am + 88))) (C8 (Z_to_bv 64 (am + 24))) j4 j5) 0 ΣK ls4 mq3 OWK).
      { apply cenv_set_montA.
        eapply (cenv_silentA LB' PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0); [exact ENV3 | exact LS3 | exact MUm | exact WMm | exact HWL | assumption | assumption | unfold mfr; cbn [app]; eassumption | exact FSZ3]. }
      clear MCELLS MUm WMm OFFm ACCM HWL ENV3 LS3 HEAP3 FR3 ST3 MI3.

      do 2 step.
      eapply KZEROX; [exact ENV4 | exact LS4 | exact (ref_at_montRR ls4 OWK PLo am qm HPM) | exact (hpl_wref PLo RMontRR (hpl_mont PLo RMontRR am qm eq_refl HPM)) |].
      intros mq5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ls5 ENV5 LS5. clear ENV4 LS4.
      retpc 2255420. fold ls4. fold ls5.
      do 2 step. step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV5 | exact LS5 | exact LOF | mc0 | clear - TOT2; lia
        | intros PRE UW; eapply BN_set_bit_walkA with (n := 64); [pre_wk PRE STK_SETBIT | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226860 CTX)
              | reflexivity | exact (ref_at_montRR ls5 OWK PLo am qm HPM) | exact (hpl_wref PLo RMontRR (hpl_mont PLo RMontRR am qm eq_refl HPM)) | reflexivity | reflexivity | clear; lia]
        | hres |].
      intros u6 Σ6 ls6 mq6 OW6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F6 fc6 ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & -> & _). unfold MallocRep.wz.
      clear ENV5 LS5.
      retpc 2255432.
      assert (RS06 : refs_stable lsK OWK ls6 OW6).
      { eapply refs_stable_trans; [| exact RS6]. intros PL1 i a H. unfold ls5. apply ref_at_setbn. unfold ls4. apply ref_at_set_mont. exact H. }
      pose proof (obj_keep_inA bt LB' PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ (f + 32) _ ENV6 ltac:(left; reflexivity) TCELLS0
                    ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear; lia)
                    ltac:(intros x Hx; apply NFo; cbn [cells_size csize Nat.add] in Hx; clear - Hx; lia)) as TCELLS.
      pose proof (obj_keep_inA bb LB' PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ (f + 96) _ ENV6 ltac:(right; left; reflexivity) BCELLS0
                    ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear; lia)
                    ltac:(intros x Hx; apply NFo; cbn [cells_size csize Nat.add] in Hx; clear - Hx; lia)) as BCELLS.
      apply implA_from_evt.
      step. if_false. apply evt_done.
      eapply L_B3; [exact RIR | exact ENV6 | exact LS6 | exact (ref_at_stable _ _ _ _ PLo _ _ RS06 HAd) | exact (ref_at_stable _ _ _ _ PLo _ _ RS06 HARi) | exact TCELLS | exact BCELLS].
    Qed.

  End PhaseB.

  Section PhaseA.
    Variables (gp s0r : word) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (LBo : list block) (PLo : placement) (EA : BnRepDefs.err_addrs) (TOTAL : Z).
    Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 mE : mem).
    Variables (am ac : Z) (qm qc : bptr) (f : Z) (g : nat) (junk : list byte).
    Variables (rd : bnref) (ad : Z).
    Hypothesis ES0 : bv_unsigned s0r = SPv.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis HPC : pl_ctx PLo = Some (ac, qc).
    Hypothesis HPM : pl_mont PLo = Some (am, qm).
    Hypothesis HFT : pl_bn PLo RTmod = None.
    Hypothesis HF : In (f, 1%nat) FR.
    Hypothesis FRESH : forall b, In b LBo -> off_fr f 1 b.
    Hypothesis CTX : uk_ctx BN_MONT_CTX_SET (bv_unsigned raw :: ras).
    Hypothesis TOT2 : 2 <= TOTAL.
    Hypothesis NROd : rd <> ROne.
    Hypothesis ROOMX : forall objs : list block, (length objs <= 2)%nat -> fr_room 2 ls0 OW0 (objs ++ LBo) /\ cnt_ok ls0 OW0 (objs ++ LBo).
    Variable Q : unit * ST -> rts RT -> machine_state -> Prop.
    Hypothesis AXE : ax_pres LBo SPv (XW PLo) mE m0.

    Notation CENV := (cenvA LBo PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).

    Hypothesis EPI : forall mb j0 c1 c2 c3 j4 j5 Σk lsk mk OWk
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 t3 t4 t5 t6 : word) F' fc',
      ax_pres LBo SPv (XW PLo) mE mb ->
      cenvA LBo PLo lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mb (mfr f g junk j0 c1 c2 c3 j4 j5) 2 Σk lsk mk OWk -> lib_state lsk mk OWk PLo EA ->
      implA (TRet (tt, lsk)) Σk Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) x19 (Z_to_bv 64 1) x21 x22 x23 x24 x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F' (wz 0x226d24) fc' None mk (seg_rom bgbsegs)).

    Lemma L_B1 : forall rRi aRi j0 j1 j2 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F1 fc1,
      (exists i, rRi = RPool i) ->
      CENV (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PLo EA ->
      ref_at lsK OWK PLo rd ad -> ref_at lsK OWK PLo rRi aRi ->
      implA (ms_b2 rd rRi lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 (am + 24)) (Z_to_bv 64 aRi) (Z_to_bv 64 ad) (Z_to_bv 64 SHB) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226998) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros HRiP ENVK LSK HAd HARi.
      destruct (env_bounds lo SPv FB s0w raw ras LBo PLo TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      pose proof ENVK as (OK1 & HEAP1 & ST1 & MI1 & _ & _ & _ & _ & FRc & FSZc & _). unfold mfr in FRc. cbn [app] in FRc.
      pose proof OK1 as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROKo & FALo & NOFRo).
      pose proof (AH_fr_geo _ _ _ _ f 1%nat HEAP1 HF) as GEO. pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in *. unfold SEGTOP_A in G4.
      pose proof (AH_ceil _ _ _ _ HEAP1) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
      assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
      assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
      assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
      { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
        assert (f / 8 + 16 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 16); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia | lia]). lia. }
      destruct (AH_fr_wr _ _ _ _ f 1%nat HEAP1 HF) as (WF & WS). change (fs_size 1) with 128 in WF, WS.
      destruct (wr_at_rw_CB mK f _ WF ltac:(clear; lia)) as (jf & FRF). destruct (wr_at_rw_CB mK (shad f) _ WS ltac:(clear; lia)) as (js & FRS).
      change (Z.to_nat (128 - 8)) with 120%nat in FRF. change (Z.to_nat (128 / 8)) with 16%nat in FRS.
      apply (rw_cells_split_CB bgbsegs _ _ [] 120 _ [] [32; 24; 40; 16; 8]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
      apply (rw_cells_split_CB bgbsegs _ _ [] 16 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
      pose proof (munch_refl [(shad f, shad f + 16)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
      unfold MallocRep.wz.
      apply implA_from_evt.
      do 5 sbstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq1 end.

      lazymatch type of FRF with rw_cells _ _ _ [?h; ?t; ?r; ?b; ?e] =>
        pose proof (proj2 (proj1 (bk_rw_cells_app bgbsegs mq1 f [h] [t; r; b; e]) FRF)) as FR1;
        cbn [cells_size csize Nat.add] in FR1; replace (f + Z.of_nat 32) with (f + 32) in FR1 by (clear; lia);
        pose proof (proj1 (bk_rw_cells_app bgbsegs mq1 (f + 32) [t] [r; b; e]) FR1) as (TJ & FR2);
        cbn [cells_size csize Nat.add] in FR2; replace (f + 32 + Z.of_nat 24) with (f + 56) in FR2 by (clear; lia);
        pose proof (proj2 (proj1 (bk_rw_cells_app bgbsegs mq1 (f + 56) [r] [b; e]) FR2)) as FR3;
        cbn [cells_size csize Nat.add] in FR3; replace (f + 56 + Z.of_nat 40) with (f + 96) in FR3 by (clear; lia);
        pose proof (proj1 (proj1 (bk_rw_cells_app bgbsegs mq1 (f + 96) [b] [e]) FR3)) as BJ;
        clear FR1 FR2 FR3
      end.
      clear FRF.
      lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
        pose proof (proj2 (proj1 (bk_rw_cells_app bgbsegs mq1 (shad f) [c0; c1; c2; c3] rest) FRS)) as FRS4;
        cbn [cells_size csize Nat.add] in FRS4; replace (shad f + Z.of_nat 4) with (shad f + 4) in FRS4 by (clear; lia)
      end.
      lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
        pose proof (proj2 (proj1 (bk_rw_cells_app bgbsegs mq1 (shad f) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] rest) FRS)) as FRS12;
        cbn [cells_size csize Nat.add] in FRS12; replace (shad f + Z.of_nat 12) with (shad f + 12) in FRS12 by (clear; lia)
      end.
      assert (ACT : acc bgbsegs mq1 (f + 32) 24).
      { apply (acc_of_shadow_cells mq1 (shad f + 4) _ 0%nat (f + 32) 24 FRS4); [clear - F8; Z.div_mod_to_equations; lia | clear - G1; lia | clear; lia
          | rewrite (shad_aligned_add f 32 F8) by (clear; lia); change (32 / 8) with 4; clear; lia | cbn; clear; lia | reflexivity]. }
      assert (ACB : acc bgbsegs mq1 (f + 96) 16).
      { apply (acc_of_shadow_cells mq1 (shad f + 12) _ 0%nat (f + 96) 16 FRS12); [clear - F8; Z.div_mod_to_equations; lia | clear - G1; lia | clear; lia
          | rewrite (shad_aligned_add f 96 F8) by (clear; lia); change (96 / 8) with 12; clear; lia | cbn; clear; lia | reflexivity]. }
      clear FRS FRS4 FRS12.
      assert (HEAPa : AHEAP ΣK OWK LBo mq1).
      { eapply (AH_frame_fr ΣK OWK LBo mK mq1 _ f 1%nat HF HEAP1 MU WM); [| exact FRESH].
        constructor; [right; right; cbn [fst snd]; change (fs_size 1) with 128; clear; lia | constructor]. }
      destruct (bptr_fresh (map blk_id (OWK ++ LBo))) as [qb Hqb].
      destruct (bptr_fresh (qb :: map blk_id (OWK ++ LBo))) as [qt Hqt].
      assert (HEAPb : AHEAP ΣK OWK ((qb, f + 96, 16) :: LBo) mq1).
      { apply (frame_obj_open ΣK OWK LBo mq1 f 1%nat qb (f + 96) 16 HF HEAPa); try (clear; lia); [change (fs_size 1) with 128; clear; lia | exact ACB | exact Hqb |].
        intros b Hb. pose proof (FRESH b Hb) as O. unfold off_fr, blk_apart in *. change (fs_size 1) with 128 in O. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
      assert (HEAP' : AHEAP ΣK OWK ((qt, f + 32, 24) :: (qb, f + 96, 16) :: LBo) mq1).
      { apply (frame_obj_open ΣK OWK ((qb, f + 96, 16) :: LBo) mq1 f 1%nat qt (f + 32) 24 HF HEAPb); try (clear; lia); [change (fs_size 1) with 128; clear; lia | exact ACT | |].
        - intros Hin. apply Hqt. rewrite map_app in Hin |- *. cbn [map blk_id fst] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E|Hin]];
            [right; apply in_or_app; left; exact Hin | left; exact E | right; apply in_or_app; right; exact Hin].
        - intros b [<-|Hb]; [unfold blk_apart; cbn [blk_addr blk_size fst snd]; clear; lia|].
          pose proof (FRESH b Hb) as O. unfold off_fr, blk_apart in *. change (fs_size 1) with 128 in O. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
      set (bt := (qt, f + 32, 24)) in *. set (bb := (qb, f + 96, 16)) in *.
      destruct (ROOMX [bt; bb] ltac:(cbn; clear; lia)) as (ROOM' & CNT').
      destruct (cenv_scope_openA [bt; bb] LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0
                  (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5) (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5)
                  0 ΣK lsK mK mq1 OWK _ f 1%nat ENVK LSK HF FRESH MU WM
                  ltac:(constructor; [right; cbn [fst snd]; change (fs_size 1) with 128; clear; lia | constructor])
                  HEAP' CNT' ltac:(assumption) ltac:(assumption) ltac:(unfold mfr; cbn [app]; eassumption) FSZc) as (ENV1 & LS1 & AX1).
      clear MU WM ENVK LSK HEAP1 HEAPa HEAPb.

      do 2 step. apply evt_done.
      eapply implA_step_same.
      { eapply (bn_init_cpsA) with (A := f + 32) (bd := bt) (lo := lo) (OW := OWK) (LB := bt :: bb :: LBo); try reflexivity; rewrite ?ESP;
          first [ exact HEAP' | exact CEIL | exact FB16 | assumption | (clear - LOF STK_INIT; lia) | (unfold USTACK_TOP in *; clear - SPT FBSP; lia)
                | (apply in_or_app; right; left; reflexivity) | (unfold bt; cbn [blk_addr blk_size fst snd]; clear; lia) ]. }
      intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & TCELLS).
      rewrite (ret_pc_even 2255284) by (clear; lia). unfold MallocRep.wz.

      assert (NFT : forall x, f + 32 <= x < f + 32 + 24 -> ~ rin_ivs (pl_frames PLo) x).
      { intros x Hx. apply (fr_no_placed PLo LBo f 1%nat x NOFRo FRESH). change (fs_size 1) with 128. clear - Hx. lia. }
      destruct (cenv_obj_agreeA [bt; bb] LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mq1
                  (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5) 0 ΣK lsK mq1 mM OWK FB bt (f + 32) 24
                  ENV1 LS1 ltac:(left; reflexivity) ltac:(unfold bt; cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(unfold bt; cbn [blk_addr blk_size fst snd]; clear; lia)
                  NFT ltac:(clear; lia) AGM HEAPM STM MIM) as (ENV2 & LS2 & AX2).
      apply (rw_cells_agree _ _ _ _ _ AGM) in BJ.
      2:{ intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; right; exists bb; split; [apply in_or_app; right; right; left; reflexivity | unfold bb; cbn [blk_addr blk_size fst snd]; clear - Hx; lia] | clear - Hx; lia]. }
      unfold bn_cells, BnRepDefs.bn_cells, bn_nil, bn_dmax, MallocRep.wz in TCELLS. cbn [bn_top bn_buf bn_neg bn_flags bn_d length repeat Z.of_nat Z.b2z] in TCELLS.
      pose proof (obj_acc ΣK OWK (bt :: bb :: LBo) mM bt HEAPM ltac:(left; reflexivity)) as ACT'. unfold bt in ACT'. cbn [blk_addr blk_size fst snd] in ACT'.
      assert (ALT : (f + 32) mod 8 = 0) by (clear - F8; Z.div_mod_to_equations; lia).
      pose proof ENV2 as (_ & _ & ST2 & MI2 & _ & _ & _ & _ & FR2 & FSZ2 & _). unfold mfr in FR2. cbn [app] in FR2.
      clear ENV1 LS1 ACT ACB HEAP' AGM.
      pose proof (munch_refl [(f + 32, f + 56)]%Z mM) as MU2. pose proof (wmono_refl bgbsegs mM) as WM2.
      assert (OFF2 : offshW [(f + 32, f + 56)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - G4 G5 G1 G3 C1 C2 C3; unfold BnHeapA.ACEIL in *; lia).
      apply implA_from_evt.
      do 2 step. shl_with ACT' ALT. chk0.
      do 2 step.
      remember (Z_to_bv 64 (f + 96)) as wbuf eqn:Ewbuf. remember (Z_to_bv 64 2) as w2 eqn:Ew2.
      do 3 step. subst wbuf w2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq3 end.
      assert (HW : Forall (w_fown [bt; bb] PLo lo SPv) [(f + 32, f + 56)]).
      { constructor; [| constructor]; right. exists bt. split; [left; reflexivity|]. unfold bt. cbn [blk_addr blk_size fst snd]. split; [clear; lia|]. split; [clear; lia|].
        intros x Hx. apply NFT. clear - Hx. lia. }
      destruct (cenv_own_storeA [bt; bb] LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 mM
                  (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5) (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (C8 (Z_to_bv 64 (am + 24))) j4 j5) 0 ΣK lsK mM mq3 OWK _
                  ENV2 LS2 MU2 WM2 HW ltac:(assumption) ltac:(assumption) ltac:(unfold mfr; cbn [app]; eassumption) FSZ2) as (ENV3 & LS3 & AX3).
      apply evt_done.
      eapply (L_B2 gp s0r lo SPv FB s0w raw ras LBo PLo EA TOTAL Σ0 ls0 OW0 mq3 mE am ac qm qc f g junk qt qb rd rRi ad aRi ES0 LOF HPC HPM HFT FROKo FALo NOFRo HF FRESH CTX TOT2 HRiP NROd Q ROOM'
                (ax_pres_trans _ _ _ _ _ _ AXE (ax_pres_trans _ _ _ _ _ _ AX1 (ax_pres_trans _ _ _ _ _ _ AX2 AX3))) EPI);
        [exact ENV3 | exact LS3 | exact HAd | exact HARi | exact TCELLS | exact BJ].
    Qed.

    Notation KZERO := (is_zero_callA LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF)).
    Notation KFLAGS := (get_flags_callA LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF)).
    Notation KCALL := (kcallA LBo PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
    Local Ltac fr_store ENV LS ENV' LS' := fr_store_gen (cenv_frameA LBo PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0) FB SPv ENV LS ENV' LS'.
    Ltac fr_unf H ::= unfold mfr in H.

    Lemma L_A : forall j0 j1 j2 j3 j4 j5 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x25 t3 t4 t5 t6 : word) F1 fc1,
      CENV (mfr f g junk j0 (CB 8 j1) (CB 8 j2) (CB 8 j3) j4 j5) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PLo EA -> ref_at lsK OWK PLo rd ad ->
      implA (ms_all rd lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 am) x21 x22 (Z_to_bv 64 ad) (Z_to_bv 64 SHB) x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F1 (wz 0x226910) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK HAd.
      destruct (env_bounds lo SPv FB s0w raw ras LBo PLo TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
      pose proof (hpl_mont PLo RMontN am qm eq_refl HPM) as HPN. pose proof (hpl_wref PLo RMontN HPN) as WRN.
      destruct (mont_open lo SPv FB s0w raw ras LBo PLo EA TOTAL Σ0 ls0 OW0 m0 am qm LOF HPM _ _ _ _ _ _ ENVK LSK) as (_ & _ & _ & ALM & M0 & MSEP & _).
      destruct (open_for_call LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ rd ad ENVK LSK HAd NROd)
        as (_ & _ & OKd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (CTd : Z.land (bn_flags (getbn rd lsK)) 4 = 0) by (destruct OKd as (_ & _ & _ & [E|E]); rewrite E; reflexivity).
      unfold ms_all, MallocRep.wz. rewrite bbind_get.
      destruct (is_zero_pure (getbn rd lsK)) eqn:EZ.
      { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
      apply implA_from_evt. do 2 step.
      eapply KZERO; [exact ENVK | exact LSK | exact HAd | exact NROd |].
      intros mq1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
      retpc 2255128.
      change ((bn_top (getbn rd lsK) =? 0)%nat) with (is_zero_pure (getbn rd lsK)). rewrite EZ. cbn [Z.b2z].
      step. if_true.
      do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV1 | exact LS1 | exact LOF | mc0 | clear - TOT2; lia
        | intros PRE UW; eapply BN_CTX_start_walkA; [pre_wk PRE STK_START | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226744 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros u2 Σ2 ls2 mq2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV2 LS2 RS2 _. clear ENV1 LS1.
      retpc 2255148.
      apply implA_from_evt. do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | mc0 | clear - TOT2; lia
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_22674c CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rRi Σ3 ls3 mq3 OW3 ? ? ? yRi ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & (iRi & EiRi) & (aRi & HARi & EyRi) & _). clear ENV2 LS2.
      retpc 2255156. subst yRi. unfold MallocRep.wz in *.
      assert (RNO : rRi <> ROne) by (rewrite EiRi; unfold RPool, ROne, NFIX; clear; lia).
      destruct (open_for_call LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ rRi aRi ENV3 LS3 HARi RNO)
        as (_ & _ & _ & _ & _ & _ & SEPRi & _ & _ & _ & _ & _ & ARi0).
      pose proof (ref_at_stable _ _ _ _ PLo _ _ (refs_stable_trans _ _ _ _ _ _ RS2 RS3) HAd) as HAd3.
      apply implA_from_evt.
      step. if_cases KR; rewrite ?unsigned_lit in KR by (clear - ARi0 SEPRi B2 B3; lia); zify_cond KR. { exfalso. clear - KR ARi0. lia. }
      ub. step. ub. do 3 step. step. apply evt_done.
      rewrite ms_mid_eq.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV3 | exact LS3 | exact LOF | mc0 | clear - TOT2; lia
        | intros PRE UW; eapply BN_copy_walkA; [pre_wk PRE STK_COPY | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_set_226770 CTX)
              | reflexivity | exact (ref_at_montN ls3 OW3 PLo am qm HPM) | exact HAd3 | exact WRN | exact NROd | reflexivity | reflexivity]
        | hres |].
      intros u4 Σ4 ls4 mq4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ENV4 LS4 RS4 RES4. hnf in RES4. destruct RES4 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (ref_at_stable _ _ _ _ PLo _ _ RS4 HAd3) as HAd4. pose proof (ref_at_stable _ _ _ _ PLo _ _ RS4 HARi) as HARi4.
      clear ENV3 LS3 HAd3 HARi RS2 RS3 RS4 KR.
      retpc 2255192.
      rewrite (bbind_get_set0 RMontN (fun n => bn_with_neg n false)).
      destruct (open_for_call LBo PLo EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ rd ad ENV4 LS4 HAd4 NROd)
        as (_ & _ & OKd4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      assert (CTd4 : Z.land (bn_flags (getbn rd ls4)) 4 = 0) by (destruct OKd4 as (_ & _ & _ & [E|E]); rewrite E; reflexivity).
      apply implA_from_evt.
      step. if_cases KN; rewrite ?unsigned_lit in KN by (clear - M0 MSEP B2 B3; lia); zify_cond KN. { exfalso. clear - KN M0. lia. }
      do 2 step. step.
      eapply KFLAGS; [exact ENV4 | exact LS4 | exact HAd4 | exact NROd |].
      intros mq5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV5 LS5. clear ENV4 LS4.
      retpc 2255208. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTd4.
      step. if_true.

      destruct (cenv_struct_openA LBo PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ RMontN (am + 24) ENV5 LS5 (ref_at_montN ls4 OW4 PLo am qm HPM) WRN)
        as (DN & _ & _ & ACCN & ALN & AN0 & SEPN & OFRN & _ & _ & _).
      pose proof (munch_refl (@nil (Z * Z)) mq5) as MU5.
      do 3 step. shl_with ACCN ALN. chk0. clear MU5 ACCN.
      fr_store ENV5 LS5 ENV6 LS6. clear ENV5 LS5.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq6 end.
      destruct (cenv_struct_openA LBo PLo EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 (LOF16 lo FB LOF) _ _ _ _ _ _ RMontN (am + 24) ENV6 LS6 (ref_at_montN ls4 OW4 PLo am qm HPM) WRN)
        as (DN6 & BNN & OKN & _ & _ & _ & _ & _ & ST6 & MI6 & CLOSEN).
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNN.
      pose proof (munch_refl [(am + 24, am + 24 + 24)]%Z mq6) as MU6. pose proof (wmono_refl bgbsegs mq6) as WM6.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq7 end.
      destruct (CLOSEN mq7 (bn_with_neg (getbn RMontN ls4) false) MU6 WM6) as (ENV7 & LS7);
        [ exact BNN | reflexivity | reflexivity | exact OKN | assumption | assumption |].
      apply evt_done.
      eapply L_B1; [exists iRi; exact EiRi | exact ENV7 | exact LS7 | apply ref_at_setbn; exact HAd4 | apply ref_at_setbn; exact HARi4].
    Qed.

  End PhaseA.
End Proofs.
End WithRT.

Section Top.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Variable CS : Z.
  Hypothesis CS112 : BN_NUM_BITS_STACK <= CS.
  Hypothesis CS16 : 16 <= CS.
  Hypothesis CSRT : RT_STACK <= CS.
  Hypothesis STK_START : BN_CTX_START_STACK <= CS.
  Hypothesis STK_GET : BN_CTX_GET_STACK <= CS.
  Hypothesis STK_END : BN_CTX_END_STACK <= CS.
  Hypothesis STK_SETW : BN_SET_WORD_STACK <= CS.
  Hypothesis STK_COPY : BN_COPY_STACK <= CS.
  Hypothesis STK_SETBIT : BN_SET_BIT_STACK <= CS.
  Hypothesis STK_LSH : BN_LSHIFT_W_STACK <= CS.
  Hypothesis STK_SUBW : W_sub_wordAF.BN_SUB_WORD_STACK <= CS.
  Hypothesis STK_DIV : BN_DIV_TOP_STACK <= CS.
  Hypothesis STK_ONE : BN_IS_ONE_STACK <= CS.
  Hypothesis STK_INV : InvClosedAF.MOD_INV_STACK_A <= CS.
  Hypothesis STK_INIT : BN_INIT_STACK <= CS.
  Hypothesis FILL : forall AR1 : ARun, @fix_fill_stmt AR1.

  Definition BN_MONT_CTX_SET_STACK : Z := MONT_SET_FRAME + CS.
  Definition BN_MONT_CTX_SET_COST : Z := 3.

  Lemma BN_MONT_CTX_set_walkA : mont_set_stmtA BN_MONT_CTX_SET_STACK BN_MONT_CTX_SET_COST 3.
  Proof.
    unfold mont_set_stmtA. intros until qc. intros PRE ROOM UW CTX -> HAd NROd HPM HPC HFT -> -> ->.
    unfold BN_MONT_CTX_SET_STACK, BN_MONT_CTX_SET_COST in *.
    eapply (pro_mont_set _ _) with (d := 2%nat); [exact PRE | exact ROOM | exact UW | reflexivity | unfold MONT_SET_FRAME; clear - CSRT; lia | clear; lia |].
    intros Σ1 m1 f spa g junk gj ra' u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 u3 u4 u5 u6 F' fc' j0 j1 j2 j3 j4 j5 FE GSZ SAVJ FR.
    pose proof FE as (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO).
    pose proof (fr_env_cenv0 160 2 f 1 [] Σ ls m OW LB PL EA sp lo _ (3 - 1) s0 ra ras spa Σ1 m1
                  ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 f)] ++ [CB g junk])
                  FE ltac:(clear; lia) ltac:(unfold MONT_SET_FRAME, RT_STACK in *; clear - CSRT; lia) FR
                  ltac:(cbn [app cells_size csize Nat.add]; clear - GSZ; lia)) as EV0.
    cbn [app] in EV0 |- *.
    rewrite BN_MONT_CTX_set_eq.

    eapply (@L_A (push AR f 1) UK BE CS CS112 CS16 STK_START STK_GET STK_END STK_SETW STK_COPY STK_SETBIT STK_LSH STK_SUBW STK_DIV STK_ONE STK_INV STK_INIT (FILL (push AR f 1))
              gp sp lo (bv_unsigned sp) spa s0 ra ras LB PL EA (3 - 1) Σ1 ls OW m1 m1 am ac qm qc f g junk rd ad);
      try eassumption; try reflexivity.
    - unfold MONT_SET_FRAME in LOK. clear - LOK. lia.
    - left. reflexivity.
    - intros objs Hobjs. destruct (fr_room_push 2 f 1 ls OW LB objs ROOM Hobjs) as (_ & R & C). split; [exact R | exact C].
    - apply ax_pres_refl.
    - intros mb k0 c1 c2 c3 k4 k5 Σk lsk mk OWk rax z0 z1 z2 y0 y1 y2 y3 y4 y5 y6 y7 x19 x21 x22 x23 x24 x25 z3 z4 z5 z6 Fk fck AXB ENVk LSk.
      eapply (epi_mont_set tt _) with (mb := mb) (used := 2) (gj := gj) (d := 2%nat) (m1 := m1) (Σ1 := Σ1) (loc := [CB 8 k0; c1; c2; c3; CB 8 k4; CB 8 k5; C8 (Z_to_bv 64 f)]);
        [exact PRE | exact FE | unfold MONT_SET_FRAME, RT_STACK in *; clear - CSRT; lia | exact GSZ | exact SAVJ
        | exact (ax_pres_trans _ _ _ _ _ _ AXO AXB) | exact ENVk | exact LSk | clear; lia | split; reflexivity].
  Qed.
End Top.
