(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase ABytes AQConst ADepot_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit AKit2 AKitQ.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc_s.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_iseg F_afree_front F_afree_tail F_afree_icpt F_adealloc_front.
Module F_adealloc_icpt.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Lemma free_fast_D : forall (L : alayout) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb S pc : Z) (uw top bot : word) (sj tb2 : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0x16b588 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->

  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         SS TB2 LTB2 LTRT TRF TRU SPS STOP RS RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.

  eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S pc uw top bot sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB2
         | |- forall j, _ => exact IAM
         | |- map _ _ = _ => exact TRF
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ S _ => exact SS
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.

  eapply evtF_cut.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).

  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icpt.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aenqueue.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_tailR.
Module F_adealloc_icptR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_icptR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).

Definition free_to_refill_post_D (L : alayout) (full : bool)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo lst nx bsz S : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word) (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41390) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xd6458) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41b70) fc None m' (seg_rom asegs)
    /\ munch (toref_W L sp t hm n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -144)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xdacc0 (0xdacc0 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0)))

    /\ rw_cells asegs m' (bv_unsigned sp + -80)
         [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
    /\ ADEPOT DI L m'.

Lemma free_to_refill_D : forall (L : alayout) (full : bool) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb nx bsz S pc : Z) (uw maxc csz top bot : word) (sj hs tb2 : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0x16b588 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->

  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_to_refill_post_D L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz S hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         SS TB2 LTB2 LTRT TRF TRU SPS STOP RS RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.

  eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S pc uw top bot sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB2
         | |- forall j, _ => exact IAM
         | |- map _ _ = _ => exact TRF
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ S _ => exact SS
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (FULL1 : if full then 0 < nb /\ rw_cells asegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else nb = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL).
    xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; lia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; lia).
    split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
  clear FULL PC.

  eapply evtF_cut.
  { eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- @eq word _ _ => reflexivity
         | |- if _ then _ else _ => exact FULL1
         | |- _ \/ _ => first [ub DHT; lia | ub DTL; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR0
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
  destruct PP as (t0b & t1b & t2b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & j0
                  & -> & MUp & WMp & MIp & STp & SH2 & FRP & FRE & LBS).

  xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
  xport UW1 MUp WMp ltac:(lia).
  xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (toref_W L sp t hm n) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_to_refill_post_D. exists id. do 11 eexists. exists m2, sj1, j0.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  split; [exact FRP|]. split; [exact FRE|].
  split; [exact LBS|]. exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.

Lemma free_from_refill_D : forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj chunks hs : list word)
    (j0 : list byte) (S : Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->

  rw_cells asegs m (bv_unsigned sp + -80)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)] ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).
Proof.
  intros until S. cbv zeta.
  intros ST CEIL LO MI FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  eapply evtF_cut.
  { eapply (put_from_refill_spec full g t hm lst b RNG ra sp gp tp s0 s1 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icptR.

Module F_afree_icptC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afreeC_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Lemma dk_preC_pure : forall ek g RNG L t lst hm qb' m,
  dk_preC ek g RNG t lst hm qb' m -> dk_seps g L hm ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  (hm + 24 <= lst \/ lst + 8192 <= hm) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
  0 <= lst -> lst + 8192 <= ATOP -> (lst = 0 \/ 0x10007fff8000 <= lst) ->
     (hm + 24 <= dk_glst g lst \/ dk_glst g lst + 8 <= hm) /\ (t + 4096 <= dk_glst g lst \/ dk_glst g lst + 8 <= t)
  /\ (al_nodes L + 1048576 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_nodes L) /\ (al_store L + 8388608 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_store L)
  /\ 0 <= dk_glst g lst /\ dk_glst g lst + 8 <= ATOP /\ (dk_glst g lst = 0 \/ 0x10007fff8000 <= dk_glst g lst).
Proof.
  intros ek g RNG L t lst hm qb' m DK DS T0 H0 N0 R0 P1 P3 P5 P6 LNN LHI LZH. unfold AIMG_HI in *. band_lin.
  unfold dk_preC, dk_seps, dk_glst in *.
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL). rewrite EGD in *.
  destruct (g_full g); [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); specialize (DS eq_refl eq_refl) | destruct GFULL as [GNB0 GLST0]];
    atop_facts; lia.
Qed.

Section Transport.
Variables (L : alayout) (sp : word) (t hm lo : Z) (m m' : amem).
Hypothesis MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (0x1ab988, 0x5fb9d0); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'.
Hypothesis WM : wmono asegs m m'.
Hypotheses (CEIL : ATOP <= lo) (LO : lo <= bv_unsigned sp - 4096) (T0 : iclr t 4096) (T1 : t + 4096 <= ATOP)
           (H0 : AIMG_HI <= hm) (DHT : hm + 24 <= t \/ t + 4096 <= hm) (N0 : AIMG_HI <= al_nodes L) (R0 : AIMG_HI <= al_store L)
           (DTN : t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) (DTS : t + 4096 <= al_store L \/ al_store L + 8388608 <= t).

Lemma dk_preC_front : forall ek g RNG lst qb',
  dk_preC ek g RNG t lst hm qb' m -> dk_seps g L hm -> dk_preC ek g RNG t lst hm qb' m'.
Proof.
  intros ek g RNG lst qb' DK DS. unfold AIMG_HI in *. band_lin.
  unfold dk_preC, dk_seps in *.
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL).
  xport MX MU WM ltac:(lia). xport GC MU WM ltac:(lia).
  do 10 (split; [assumption|]).
  destruct (g_full g); [| exact GFULL].
  destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9). specialize (DS EGD eq_refl). destruct DS as (D1 & D2 & D3). atop_facts.
  xport GLB MU WM ltac:(lia). reasm.
Qed.
End Transport.

End CANSEC1.
Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Theorem free_torec : forall DI, free_torec_stmt DI.
Proof.
  intros DI. unfold free_torec_stmt.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_preC_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.

  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_preC_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.

  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_torec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP & SH2 & HD2 & QC2 & EKP & DKP).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in FRP by lia.

  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.

  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  assert (MU : munch (freeC_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_torec_post. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 6 eexists. exists sp. do 9 eexists. exists m2, sj1. do 2 eexists. exists junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP|].
  split; [exact SS1|]. split; [reflexivity|].
  split; [replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia; exact TB1|]. split; [reflexivity|].
  split; [exact FRS1|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End CANSEC2.
End F_afree_icptC.

Module F_adealloc_icptC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afreeC_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Import F_afree_icptC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Definition free_torec_post_D (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    let spP := bv_unsigned sp in
    ms' = MS (mkR (Z_to_bv 64 0x41168) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3eb38) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spP - 80)
    /\ 0 < id < 2^31

    /\ rw_cells asegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xdacc0 (0xdacc0 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Theorem free_torec_D : forall (L : alayout) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb S pc : Z) (uw top bot : word) (sj tb2 : list word) (sjunk : list byte) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0x16b588 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_torec_post_D L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         SS TB2 LTB2 LTRT TRF TRU SPS STOP RS RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_preC_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.

  eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S pc uw top bot sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB2
         | |- forall j, _ => exact IAM
         | |- map _ _ = _ => exact TRF
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ S _ => exact SS
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_preC_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.

  eapply evtF_cut.
  { eapply (put_torec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP & SH2 & HD2 & QC2 & EKP & DKP).

  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (freeC_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_torec_post_D. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 9 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icptC.

Module F_afree_icptRC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_icptR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afreeC_iface. Import F_afree_icptC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailRC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Theorem free_from_refill_torec : forall DI, free_from_refill_torec_stmt DI.
Proof.
  intros DI. unfold free_from_refill_torec_stmt.
  intros until trt. cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_preC_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -2128)) in *.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.

  eapply evtF_cut.
  { eapply (put_from_refill_torec full g t hm lst b RNG (Z_to_bv 64 0x5e5cc) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x5e55c) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP2 & SH2 & HD2 & QC2 & EKP & DKP).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in FRP2 by lia.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)) - 80)) with (Z_to_bv 64 (bv_unsigned sp - 2128 - 80)) by (f_equal; rewrite unsigned_lit by lia; lia).
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  assert (MU : munch (freeC_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_torec_post. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 6 eexists. exists sp. do 9 eexists. exists m2, sj. do 2 eexists. exists junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP2|].
  split; [exact SS|]. split; [reflexivity|].
  split; [replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia; exact TB|]. split; [reflexivity|].
  split; [exact FRS|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End CANSEC1.
End F_afree_icptRC.

Module F_adealloc_icptRC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.F_aenqueueR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_icptR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afreeC_iface. Import F_afree_icptC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afree_tailRC.
Import F_afree_icptRC. Import F_adealloc_icptC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd67c8, 0xd67c8 + 4); (0xd67d0, 0xd67d0 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Theorem free_from_refill_torec_D : forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj chunks hs : list word)
    (j0 : list byte) (S : Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->

  rw_cells asegs m (bv_unsigned sp + -80)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd6730); C8 (Z_to_bv 64 0x41230)] ->

  rw_cells asegs m 0xd6770 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF asegs RNG (free_torec_post_D DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41390) fc None m (seg_rom asegs)).
Proof.
  intros until S. cbv zeta.
  intros ST CEIL LO MI FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148261376 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_preC_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  eapply evtF_cut.
  { eapply (put_from_refill_torec full g t hm lst b RNG ra sp gp tp s0 s1 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP2 & SH2 & HD2 & QC2 & EKP & DKP).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  assert (MU : munch (freeC_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_torec_post_D. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 9 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP2|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icptRC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_adealloc_icpt.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Lemma free_fast_D : forall (L : alayout) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb S pc : Z) (uw top bot : word) (sj tb2 : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0x16d748 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->

  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (S + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         SS TB2 LTB2 LTRT TRF TRU SPS STOP RS RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.

  eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S pc uw top bot sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB2
         | |- forall j, _ => exact IAM
         | |- map _ _ = _ => exact TRF
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ S _ => exact SS
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.

  eapply evtF_cut.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).

  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icpt.

Module F_adealloc_icptR.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_icptR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).

Definition free_to_refill_post_D (L : alayout) (full : bool)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo lst nx bsz S : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word) (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x41d20) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0xd8618) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x42500) fc None m' (seg_rom bsegs)
    /\ munch (toref_W L sp t hm n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -144)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdce80 (0xdce80 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0)))

    /\ rw_cells bsegs m' (bv_unsigned sp + -80)
         [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)]
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr bsegs m' (lst + 24) hs else True)
    /\ ADEPOT DI L m'.

Lemma free_to_refill_D : forall (L : alayout) (full : bool) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb nx bsz S pc : Z) (uw maxc csz top bot : word) (sj hs tb2 : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0x16d748 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->

  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (S + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_to_refill_post_D L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz S hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         SS TB2 LTB2 LTRT TRF TRU SPS STOP RS RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.

  eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S pc uw top bot sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB2
         | |- forall j, _ => exact IAM
         | |- map _ _ = _ => exact TRF
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ S _ => exact SS
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (FULL1 : if full then 0 < nb /\ rw_cells bsegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else nb = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL).
    xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; lia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; lia).
    split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
  clear FULL PC.

  eapply evtF_cut.
  { eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- @eq word _ _ => reflexivity
         | |- if _ then _ else _ => exact FULL1
         | |- _ \/ _ => first [ub DHT; lia | ub DTL; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR0
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
  destruct PP as (t0b & t1b & t2b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & j0
                  & -> & MUp & WMp & MIp & STp & SH2 & FRP & FRE & LBS).

  xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
  xport UW1 MUp WMp ltac:(lia).
  xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (toref_W L sp t hm n) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_to_refill_post_D. exists id. do 11 eexists. exists m2, sj1, j0.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  split; [exact FRP|]. split; [exact FRE|].
  split; [exact LBS|]. exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.

Lemma free_from_refill_D : forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj chunks hs : list word)
    (j0 : list byte) (S : Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->

  rw_cells bsegs m (bv_unsigned sp + -80)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)] ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).
Proof.
  intros until S. cbv zeta.
  intros ST CEIL LO MI FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  eapply evtF_cut.
  { eapply (put_from_refill_spec full g t hm lst b RNG ra sp gp tp s0 s1 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icptR.

Module F_afree_icptC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afreeC_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Lemma dk_preC_pure : forall ek g RNG L t lst hm qb' m,
  dk_preC ek g RNG t lst hm qb' m -> dk_seps g L hm ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  (hm + 24 <= lst \/ lst + 8192 <= hm) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
  0 <= lst -> lst + 8192 <= ATOP -> (lst = 0 \/ 0x10007fff8000 <= lst) ->
     (hm + 24 <= dk_glst g lst \/ dk_glst g lst + 8 <= hm) /\ (t + 4096 <= dk_glst g lst \/ dk_glst g lst + 8 <= t)
  /\ (al_nodes L + 1048576 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_nodes L) /\ (al_store L + 8388608 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_store L)
  /\ 0 <= dk_glst g lst /\ dk_glst g lst + 8 <= ATOP /\ (dk_glst g lst = 0 \/ 0x10007fff8000 <= dk_glst g lst).
Proof.
  intros ek g RNG L t lst hm qb' m DK DS T0 H0 N0 R0 P1 P3 P5 P6 LNN LHI LZH. unfold AIMG_HI in *. band_lin.
  unfold dk_preC, dk_seps, dk_glst in *.
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL). rewrite EGD in *.
  destruct (g_full g); [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); specialize (DS eq_refl eq_refl) | destruct GFULL as [GNB0 GLST0]];
    atop_facts; lia.
Qed.

Section Transport.
Variables (L : alayout) (sp : word) (t hm lo : Z) (m m' : amem).
Hypothesis MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (0x1adb48, 0x5fdb90); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'.
Hypothesis WM : wmono bsegs m m'.
Hypotheses (CEIL : ATOP <= lo) (LO : lo <= bv_unsigned sp - 4096) (T0 : iclr t 4096) (T1 : t + 4096 <= ATOP)
           (H0 : AIMG_HI <= hm) (DHT : hm + 24 <= t \/ t + 4096 <= hm) (N0 : AIMG_HI <= al_nodes L) (R0 : AIMG_HI <= al_store L)
           (DTN : t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) (DTS : t + 4096 <= al_store L \/ al_store L + 8388608 <= t).

Lemma dk_preC_front : forall ek g RNG lst qb',
  dk_preC ek g RNG t lst hm qb' m -> dk_seps g L hm -> dk_preC ek g RNG t lst hm qb' m'.
Proof.
  intros ek g RNG lst qb' DK DS. unfold AIMG_HI in *. band_lin.
  unfold dk_preC, dk_seps in *.
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL).
  xport MX MU WM ltac:(lia). xport GC MU WM ltac:(lia).
  do 10 (split; [assumption|]).
  destruct (g_full g); [| exact GFULL].
  destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9). specialize (DS EGD eq_refl). destruct DS as (D1 & D2 & D3). atop_facts.
  xport GLB MU WM ltac:(lia). reasm.
Qed.
End Transport.

End CANSEC1.
Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Theorem free_torec : forall DI, free_torec_stmt DI.
Proof.
  intros DI. unfold free_torec_stmt.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_preC_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.

  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_preC_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.

  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_torec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP & SH2 & HD2 & QC2 & EKP & DKP).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in FRP by lia.

  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.

  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  assert (MU : munch (freeC_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_torec_post. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 6 eexists. exists sp. do 9 eexists. exists m2, sj1. do 2 eexists. exists junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP|].
  split; [exact SS1|]. split; [reflexivity|].
  split; [replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia; exact TB1|]. split; [reflexivity|].
  split; [exact FRS1|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End CANSEC2.
End F_afree_icptC.

Module F_adealloc_icptC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afreeC_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Import F_afree_icptC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc_front.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Definition free_torec_post_D (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    let spP := bv_unsigned sp in
    ms' = MS (mkR (Z_to_bv 64 0x41af8) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3f4c8) fc None m' (seg_rom bsegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (spP - 80)
    /\ 0 < id < 2^31

    /\ rw_cells bsegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdce80 (0xdce80 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Theorem free_torec_D : forall (L : alayout) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo nb fst0 lst qb S pc : Z) (uw top bot : word) (sj tb2 : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 (hm + 16) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 S -> a5 = Z_to_bv 64 1 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0x16d748 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (S + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> rng RNG S 2056 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_torec_post_D L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 AC PC HK QK GF FLG FL IAS IAM CT8 TT0 UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         SS TB2 LTB2 LTRT TRF TRU SPS STOP RS RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_preC_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.

  eapply evtF_cut.
  { eapply (free_front_D DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo S pc uw top bot sj tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB2
         | |- forall j, _ => exact IAM
         | |- map _ _ = _ => exact TRF
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ S _ => exact SS
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post_D in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1
                   & -> & MUf0 & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & DEP1).

  assert (MUf : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m1).
  { eapply munch_weaken; [| exact MUf0]. solve_sub_fp sp. }

  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_preC_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.

  eapply evtF_cut.
  { eapply (put_torec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP & SH2 & HD2 & QC2 & EKP & DKP).

  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.

  assert (MU : munch (freeC_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  apply evtF_done. unfold free_torec_post_D. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 9 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icptC.

Module F_afree_icptRC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_icptR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afreeC_iface. Import F_afree_icptC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailRC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Theorem free_from_refill_torec : forall DI, free_from_refill_torec_stmt DI.
Proof.
  intros DI. unfold free_from_refill_torec_stmt.
  intros until trt. cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_preC_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -2128)) in *.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.

  eapply evtF_cut.
  { eapply (put_from_refill_torec full g t hm lst b RNG (Z_to_bv 64 0x5ef5c) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x5eeec) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP2 & SH2 & HD2 & QC2 & EKP & DKP).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in FRP2 by lia.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)) - 80)) with (Z_to_bv 64 (bv_unsigned sp - 2128 - 80)) by (f_equal; rewrite unsigned_lit by lia; lia).
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  assert (MU : munch (freeC_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_torec_post. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 6 eexists. exists sp. do 9 eexists. exists m2, sj. do 2 eexists. exists junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP2|].
  split; [exact SS|]. split; [reflexivity|].
  split; [replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia; exact TB|]. split; [reflexivity|].
  split; [exact FRS|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End CANSEC1.
End F_afree_icptRC.

Module F_adealloc_icptRC.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_front.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tail.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aenqueue.TwinB.F_aenqueueR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_icptR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afreeC_iface. Import F_afree_icptC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afree_tailRC.
Import F_afree_icptRC. Import F_adealloc_icptC.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xd8988, 0xd8988 + 4); (0xd8990, 0xd8990 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

Theorem free_from_refill_torec_D : forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj chunks hs : list word)
    (j0 : list byte) (S : Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->

  rw_cells bsegs m (bv_unsigned sp + -80)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xd88f0); C8 (Z_to_bv 64 0x41bc0)] ->

  rw_cells bsegs m 0xd8930 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->

  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->

  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->

  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
  evtF bsegs RNG (free_torec_post_D DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41d20) fc None m (seg_rom bsegs)).
Proof.
  intros until S. cbv zeta.
  intros ST CEIL LO MI FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
  assert (SHB : 2148262400 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_preC_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.

  eapply evtF_cut.
  { eapply (put_from_refill_torec full g t hm lst b RNG ra sp gp tp s0 s1 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP2 & SH2 & HD2 & QC2 & EKP & DKP).

  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.

  assert (MU : munch (freeC_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_torec_post_D. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 9 eexists. exists m2, sj.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP2|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
End F_adealloc_icptRC.
End TwinB.
