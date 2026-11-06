(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AQConst ADepot_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 AKitQ F_aalloc_s. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind2. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_afree_s F_aintal F_afree_iseg. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_adealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc.F_adealloc. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aqchunk.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

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
Section WithDepot.
Variable DI : ADepotIface.

Notation front_W L sp t hm :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition free_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo : Z) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5e5cc) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 (hm + 16))
                  (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128))
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7
                  (Z_to_bv 64 0x5e55c) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4108c) fc None m' (seg_rom asegs)
    /\ munch (front_W L sp t hm) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x169548 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xdacc0 (0xdacc0 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0)))

    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ADEPOT DI L m'.

Lemma free_front_spec : forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot : Z) (uw : word) (sj : list word) (trt : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->

  allocA_cells m ctx t ->
  rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                             C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)] ->
  rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)] -> rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0x16b588 [C8 (Z_to_bv 64 0)] ->

  rw_cells asegs m 0x169548 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m 0xdacc0 (0xdacc0 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 24 <= ATOP ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
  evtF asegs RNG (free_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC HK FL IAS IAM CT8 TT0 SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
         HD HUW B1 B13 NR AL HLO HHI DHT DHC DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH. band_lin.
  pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO.
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.

  eapply evtF_cut.
  { eapply (ficptA_spec (hm + 16) ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ficptA_post in PA.
  destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRA & FRt & FRs & FL1 & IAS1 & IAM1).

  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 386396 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 386396 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 386396 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 386396) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 386396 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 386396) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.

  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  xport HD MUa WMa ltac:(lia). xport HUW MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; lia|]). apply Forall_nil. }
  clear DEP.
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.

  step.
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 386396 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 386396 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 386396 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU0" G end. }
  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  destruct PU as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & tb2
                  & -> & MUu & WMu & MIu & STu & SZ2 & TB2 & LTB2 & TRF2 & BP2 & UW2).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 386488)) with (Z_to_bv 64 386488) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport HD MU12 WMu ltac:(ub DHT; lia). xport HUW MU12 WMu ltac:(ub DHT; lia). xport HK MU12 WMu ltac:(lia).
  xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MU12 | exact WMu |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; lia|]). apply Forall_nil. }
  clear DEP1.

  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.

  zstep. zstep. step. step.
  step.
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_spec t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 n b1 actx ctx lo uw sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STu
         | |- mem_inv _ _ => exact MIu
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ AFHOOK _ => exact HK
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold dealloc_post in PD.
  destruct PD as (t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & sj3
                  & -> & MUd & WMd & MId & STd & HD3 & FC3 & STATS3 & LSJ3).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.

  xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
  xport CT MUd WMd ltac:(ub DHC; ub CT2; lia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; lia). xport TT0 MUd WMd ltac:(ub DHT; lia).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(ub DHT; lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP2 | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; lia|]). apply Forall_nil. }
  clear DEP2.

  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (qchunk_spec DI L t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
              (1 + Z.of_nat (length trt)) 386396 (Z_to_bv 64 18446744069414584320) (Z_to_bv 64 top) (Z_to_bv 64 bot) tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STd
         | |- mem_inv _ _ => exact MId
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact TB2
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 16) _ => exact FC3
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + -2128) _ => exact SS
         end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
  destruct PQ as (id & t0d & t1d & t2d & a6d & a7d & t3d & t4d & t5d & t6d & m4
                  & -> & MUq & WMq & MIq & STq & FC4 & IDR & DEP4).
  unname_sp. rewrite ?unsigned_lit in MUq by lia. rewrite ?unsigned_lit in STq by lia.

  xport HD3 MUq WMq ltac:(ub DHN; ub DHS; lia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; lia).
  xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; lia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
  xport SS MUq WMq ltac:(lia). xport TB2 MUq WMq ltac:(rewrite LTB2; lia). xport FRS MUq WMq ltac:(lia).
  assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at asegs m4 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
    intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM3.
  assert (MU : munch (front_W L sp t hm) m m4).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono asegs m m4).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WMd| exact WMq]. }
  apply evtF_done. unfold free_front_post.
  exists id. do 9 eexists. exists m4, sj3, tb2, junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
  split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
  split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|].
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|].
  split; [exact FRS|]. exact DEP4.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End WithDepot.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AQConst.TwinB ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB AKitQ.TwinB F_aalloc_s.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind2. Import F_afree_s.TwinB F_aintal.TwinB F_afree_iseg.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_adealloc.TwinB.F_adealloc. Import F_aqchunk.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

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
Section WithDepot.
Variable DI : ADepotIface.

Notation front_W L sp t hm :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition free_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n b1 actx lo : Z) (trt : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5ef5c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 (hm + 16))
                  (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128))
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7
                  (Z_to_bv 64 0x5eeec) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41a1c) fc None m' (seg_rom bsegs)
    /\ munch (front_W L sp t hm) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2128)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x16b708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdce80 (0xdce80 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0)))

    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
    /\ u64arr bsegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ADEPOT DI L m'.

Lemma free_front_spec : forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot : Z) (uw : word) (sj : list word) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->

  allocA_cells m ctx t ->
  rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                             C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)] ->
  rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)] -> rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0x16d748 [C8 (Z_to_bv 64 0)] ->

  rw_cells bsegs m 0x16b708 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xdce80 (0xdce80 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 24 <= ATOP ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->

  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->

  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
  evtF bsegs RNG (free_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo trt m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC HK FL IAS IAM CT8 TT0 SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
         HD HUW B1 B13 NR AL HLO HHI DHT DHC DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH. band_lin.
  pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO.
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.

  eapply evtF_cut.
  { eapply (ficptA_spec (hm + 16) ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ficptA_post in PA.
  destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRA & FRt & FRs & FL1 & IAS1 & IAM1).

  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 388844 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 388844 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 388844 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 388844) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 388844 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 388844) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.

  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  xport HD MUa WMa ltac:(lia). xport HUW MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; lia|]). apply Forall_nil. }
  clear DEP.
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.

  step.
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 388844 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 388844 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 388844 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STa
         | |- mem_inv _ _ => exact MIa
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => unboxed CT2
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU0" G end. }
  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  destruct PU as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & tb2
                  & -> & MUu & WMu & MIu & STu & SZ2 & TB2 & LTB2 & TRF2 & BP2 & UW2).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 388936)) with (Z_to_bv 64 388936) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport HD MU12 WMu ltac:(ub DHT; lia). xport HUW MU12 WMu ltac:(ub DHT; lia). xport HK MU12 WMu ltac:(lia).
  xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MU12 | exact WMu |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; lia|]). apply Forall_nil. }
  clear DEP1.

  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.

  zstep. zstep. step. step.
  step.
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_spec t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 n b1 actx ctx lo uw sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STu
         | |- mem_inv _ _ => exact MIu
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ AFHOOK _ => exact HK
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold dealloc_post in PD.
  destruct PD as (t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & sj3
                  & -> & MUd & WMd & MId & STd & HD3 & FC3 & STATS3 & LSJ3).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.

  xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
  xport CT MUd WMd ltac:(ub DHC; ub CT2; lia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; lia). xport TT0 MUd WMd ltac:(ub DHT; lia).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(ub DHT; lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at bsegs m3 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP2 | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; lia|]). apply Forall_nil. }
  clear DEP2.

  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (qchunk_spec DI L t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
              (1 + Z.of_nat (length trt)) 388844 (Z_to_bv 64 18446744069414584320) (Z_to_bv 64 top) (Z_to_bv 64 bot) tb2 trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STd
         | |- mem_inv _ _ => exact MId
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- u64arr _ _ _ _ => exact TB2
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 16) _ => exact FC3
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + -2128) _ => exact SS
         end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
  destruct PQ as (id & t0d & t1d & t2d & a6d & a7d & t3d & t4d & t5d & t6d & m4
                  & -> & MUq & WMq & MIq & STq & FC4 & IDR & DEP4).
  unname_sp. rewrite ?unsigned_lit in MUq by lia. rewrite ?unsigned_lit in STq by lia.

  xport HD3 MUq WMq ltac:(ub DHN; ub DHS; lia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; lia).
  xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; lia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
  xport SS MUq WMq ltac:(lia). xport TB2 MUq WMq ltac:(rewrite LTB2; lia). xport FRS MUq WMq ltac:(lia).
  assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at bsegs m4 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
    intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM3.
  assert (MU : munch (front_W L sp t hm) m m4).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono bsegs m m4).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WMd| exact WMq]. }
  apply evtF_done. unfold free_front_post.
  exists id. do 9 eexists. exists m4, sj3, tb2, junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
  split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
  split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|].
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|].
  split; [exact FRS|]. exact DEP4.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End WithDepot.
End CANSEC1.
End TwinB.
