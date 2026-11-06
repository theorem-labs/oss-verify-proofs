(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AQConst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 AKitQ F_aalloc_s. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind2. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aintal F_arealloc_iseg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Ltac ubr H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.

Notation realloc_pre_W sp t :=
  ([(bv_unsigned sp - 2304, bv_unsigned sp); (0xdacc0, 0xdacc0 + 0x81030); (0x169548, 0x169548 + 4); (t + 2800, t + 3169)]%Z) (only parsing).

Definition realloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (trc : list Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a7 t3 t4 t5 t6 : word) m' (sj' tb : list word) (junk0 junk2 junkR : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x3d734) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3d764) fc None m' (seg_rom asegs)
    /\ munch (realloc_pre_W sp t) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2208)

    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5e958); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x3d6ec)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5e9c8)]

    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trc))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m' (bv_unsigned sp + -2136 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AREALLOC_PC :: trc
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]

    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat

    /\ rw_cells asegs m' AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' AIA_BASE (AIA_BASE + AIA_SIZE)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma realloc_pre_spec : forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n ctx t lo top bot : Z) (tr trc : list Z) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 p -> 0 < p < 2^47 -> a1 = Z_to_bv 64 n -> 0 < n < 2^64 ->
  bv_unsigned sp mod 16 = 0 ->

  allocA_cells m ctx t ->
  rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                             C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)] ->
  rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  (bv_unsigned sp + 16 < top /\ uchain m top AREALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (realloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo trc sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until sj.
  intros ST CEIL LO MI TP Ha0 PR Ha1 NR SP16 AC GOT6 MCS CF34 GPG PGC FL IAS IAM TT SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RSTK RCTX RT. band_lin.
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AREALLOC_SYM, AREALLOC_PC in *.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1 in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR. atop_facts.
  box CT2.

  eapply evtF_cut.
  { eapply (ricptA_spec p n ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ricptA_post in PA.
  destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk0 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRp0 & FRA & FRt & FRs & FL1 & IAS1 & IAM1).

  pose proof FRs as FRs0. rw_split FRs0 8%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr0, uchain m top 387416 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr0 -> bv_unsigned sp + 16 < top ->
                uchain m1 top 387416 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr0)).
  { intros tr0 UC BTX. replace ([bv_unsigned ra] ++ tr0) with ((if bv_unsigned ra =? 387416 then [] else [bv_unsigned ra]) ++ tr0)
      by (replace (bv_unsigned ra =? 387416) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 387416 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr0); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 387416) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.

  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2128) with (bv_unsigned sp - 2136 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2136 + 16) in TB by lia.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 2136 + 2056) in BPJ by lia.

  step.
  name_sp sp (-2144).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2136) 387416 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
      eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 387416 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
           | |- stk _ _ _ _ => rewrite Hsp; exact STa
           | |- mem_inv _ _ => exact MIa
           | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
           | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
           | |- u64arr _ _ _ _ => exact TB
           | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr UC BT)
           | |- _ \/ _ => unboxed CT2
           | |- rng _ _ _ => solve_rng
           | |- rw_cells _ _ (_ + 152) _ => exact CT
           | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
           | |- rw_cells _ _ (_ + 40) _ => exact SW
           | |- rw_cells _ _ (_ + 3168) _ => exact UW
           end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 387416 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
           | |- stk _ _ _ _ => rewrite Hsp; exact STa
           | |- mem_inv _ _ => exact MIa
           | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
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
  replace (ret_pc (Z_to_bv 64 387508)) with (Z_to_bv 64 387508) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  assert (MU12 : munch [(bv_unsigned sp - 2304, bv_unsigned sp - 2144); (bv_unsigned sp - 2128, bv_unsigned sp - 2124); (bv_unsigned sp - 2120, bv_unsigned sp - 72); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ubr CT2; lia).
  xport FRp MU12 WMu ltac:(lia). xport FRp0 MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.

  eapply evtF_mono.
  { eapply (ricptB_spec RNG _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m2 p n ctx t lo sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STu
         | |- mem_inv _ _ => exact MIu
         | |- @eq word _ _ => exact TP
         | |- u64arr _ _ _ _ => exact STATS
         | |- rng _ _ _ => solve_rng
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMB" G end. }
  cbv beta. intros ms3 PB. unfold ricptB_post in PB.
  destruct PB as (t0c & t1c & t2c & a7c & t3c & t4c & t5c & t6c & m3 & sj' & junkR & -> & MUb & WMb & MIb & STb & FRR & FRa & STATS' & LSJ' & ESJ).
  xport FRp MUb WMb ltac:(lia). xport FRp0 MUb WMb ltac:(lia). xport TAG MUb WMb ltac:(lia). xport REST MUb WMb ltac:(lia).
  xport SZ2 MUb WMb ltac:(lia). xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  xport FL1 MUb WMb ltac:(lia). xport IAS1 MUb WMb ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xdacc8 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUb. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }

  replace (bv_unsigned sp - 2136 + 8) with (bv_unsigned sp + -2128) in SZ2 by lia.
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2136 + 2056) with (bv_unsigned sp + -80) in FRS by lia.
  unfold realloc_pre_post.
  exists t0c, t1c, t2c, a7c, t3c, t4c, t5c, t6c, m3, sj', tb2, junk0, junk2, junkR.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MU12]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [| exact WMb]; eapply wmono_trans; [exact WMa | exact WMu]|]. split; [exact MIb|].
  split; [exact STb|]. split; [exact FRR|]. split; [exact FRa|]. split; [exact FRp0|].
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) in SS by lia.
  replace (bv_unsigned sp - 2136 + 16) with (bv_unsigned sp + -2136 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. split; [exact UW2|].
  split; [exact STATS'|]. split; [exact LSJ'|]. split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AQConst.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB AKitQ.TwinB F_aalloc_s.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind2. Import F_aintal.TwinB F_arealloc_iseg.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Ltac ubr H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.

Notation realloc_pre_W sp t :=
  ([(bv_unsigned sp - 2304, bv_unsigned sp); (0xdce80, 0xdce80 + 0x81030); (0x16b708, 0x16b708 + 4); (t + 2800, t + 3169)]%Z) (only parsing).

Definition realloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n t lo : Z) (trc : list Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a7 t3 t4 t5 t6 : word) m' (sj' tb : list word) (junk0 junk2 junkR : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x3e0c4) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3e0f4) fc None m' (seg_rom bsegs)
    /\ munch (realloc_pre_W sp t) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2208)

    /\ rw_cells bsegs m' (bv_unsigned sp + -2208) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x5f2e8); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x3e07c)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2160) [CB 8 junkR; C8 (Z_to_bv 64 0x5f358)]

    /\ rw_cells bsegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trc))); C4 (Z_to_bv 64 0)]
    /\ u64arr bsegs m' (bv_unsigned sp + -2136 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AREALLOC_PC :: trc
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]

    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat

    /\ rw_cells bsegs m' AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' AIA_BASE (AIA_BASE + AIA_SIZE)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma realloc_pre_spec : forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p n ctx t lo top bot : Z) (tr trc : list Z) (sj : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 p -> 0 < p < 2^47 -> a1 = Z_to_bv 64 n -> 0 < n < 2^64 ->
  bv_unsigned sp mod 16 = 0 ->

  allocA_cells m ctx t ->
  rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                             C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)] ->
  rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->

  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  (bv_unsigned sp + 16 < top /\ uchain m top AREALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (realloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n t lo trc sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until sj.
  intros ST CEIL LO MI TP Ha0 PR Ha1 NR SP16 AC GOT6 MCS CF34 GPG PGC FL IAS IAM TT SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RSTK RCTX RT. band_lin.
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AREALLOC_SYM, AREALLOC_PC in *.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1 in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR. atop_facts.
  box CT2.

  eapply evtF_cut.
  { eapply (ricptA_spec p n ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
    all: try lazymatch goal with
         | |- rw_cells _ _ AIA_FLAG _ => exact FL
         | |- stk _ _ AIA_BASE _ => exact IAS
         | |- _ = true -> _ => exact IAM
         | |- rng _ _ _ => solve_rng
         end.
    all: match goal with |- ?G => idtac "REMA" G end. }
  cbv beta. intros ms1 PA. unfold ricptA_post in PA.
  destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk0 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRp0 & FRA & FRt & FRs & FL1 & IAS1 & IAM1).

  pose proof FRs as FRs0. rw_split FRs0 8%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr0, uchain m top 389864 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr0 -> bv_unsigned sp + 16 < top ->
                uchain m1 top 389864 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr0)).
  { intros tr0 UC BTX. replace ([bv_unsigned ra] ++ tr0) with ((if bv_unsigned ra =? 389864 then [] else [bv_unsigned ra]) ++ tr0)
      by (replace (bv_unsigned ra =? 389864) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 389864 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr0); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 389864) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.

  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2128) with (bv_unsigned sp - 2136 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2136 + 16) in TB by lia.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 2136 + 2056) in BPJ by lia.

  step.
  name_sp sp (-2144).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2136) 389864 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
      eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 389864 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
      all: try lazymatch goal with
           | |- stk _ _ _ _ => rewrite Hsp; exact STa
           | |- mem_inv _ _ => exact MIa
           | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
           | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
           | |- u64arr _ _ _ _ => exact TB
           | |- uchain _ _ _ _ _ _ _ => exact (UC1 tr UC BT)
           | |- _ \/ _ => unboxed CT2
           | |- rng _ _ _ => solve_rng
           | |- rw_cells _ _ (_ + 152) _ => exact CT
           | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
           | |- rw_cells _ _ (_ + 40) _ => exact SW
           | |- rw_cells _ _ (_ + 3168) _ => exact UW
           end.
      all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
      all: match goal with |- ?G => idtac "REMU" G end.
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2136) 389864 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
      all: try lazymatch goal with
           | |- stk _ _ _ _ => rewrite Hsp; exact STa
           | |- mem_inv _ _ => exact MIa
           | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
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
  replace (ret_pc (Z_to_bv 64 389956)) with (Z_to_bv 64 389956) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  assert (MU12 : munch [(bv_unsigned sp - 2304, bv_unsigned sp - 2144); (bv_unsigned sp - 2128, bv_unsigned sp - 2124); (bv_unsigned sp - 2120, bv_unsigned sp - 72); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ubr CT2; lia).
  xport FRp MU12 WMu ltac:(lia). xport FRp0 MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.

  eapply evtF_mono.
  { eapply (ricptB_spec RNG _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m2 p n ctx t lo sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STu
         | |- mem_inv _ _ => exact MIu
         | |- @eq word _ _ => exact TP
         | |- u64arr _ _ _ _ => exact STATS
         | |- rng _ _ _ => solve_rng
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMB" G end. }
  cbv beta. intros ms3 PB. unfold ricptB_post in PB.
  destruct PB as (t0c & t1c & t2c & a7c & t3c & t4c & t5c & t6c & m3 & sj' & junkR & -> & MUb & WMb & MIb & STb & FRR & FRa & STATS' & LSJ' & ESJ).
  xport FRp MUb WMb ltac:(lia). xport FRp0 MUb WMb ltac:(lia). xport TAG MUb WMb ltac:(lia). xport REST MUb WMb ltac:(lia).
  xport SZ2 MUb WMb ltac:(lia). xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  xport FL1 MUb WMb ltac:(lia). xport IAS1 MUb WMb ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at bsegs m3 (0xdce88 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUb. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }

  replace (bv_unsigned sp - 2136 + 8) with (bv_unsigned sp + -2128) in SZ2 by lia.
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2136 + 2056) with (bv_unsigned sp + -80) in FRS by lia.
  unfold realloc_pre_post.
  exists t0c, t1c, t2c, a7c, t3c, t4c, t5c, t6c, m3, sj', tb2, junk0, junk2, junkR.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MU12]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [| exact WMb]; eapply wmono_trans; [exact WMa | exact WMu]|]. split; [exact MIb|].
  split; [exact STb|]. split; [exact FRR|]. split; [exact FRa|]. split; [exact FRp0|].
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) in SS by lia.
  replace (bv_unsigned sp - 2136 + 16) with (bv_unsigned sp + -2136 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. split; [exact UW2|].
  split; [exact STATS'|]. split; [exact LSJ'|]. split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End CANSEC1.
End TwinB.
