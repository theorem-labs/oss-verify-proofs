(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_aalloc_s F_aalloc1 F_aalloc3 F_aunwind F_aunwind2 F_afree_s F_aintal F_afree_iseg F_afree_front F_afree_icpt.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_of_u64arr' : forall m A ws,
  u64arr bsegs m A ws -> rw_cells bsegs m A [CB (8 * length ws) (u64s ws)].
Proof. exact rw_cells_of_u64arr. Qed.

(* [comment removed for export] *)
Lemma dealloc_null_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x337cc) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  do 9 step.                                   (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep. step.                                 (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition free_null_post (sp : word) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4); (t + 3168, t + 3169)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x15f788 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xd0f00 (0xd0f00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma free_null_spec : forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx lo top bot : Z) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t ->
  rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828); C8 (Z_to_bv 64 0xcd4f8); C8 (Z_to_bv 64 0xcfcf8);
                             C8 (Z_to_bv 64 0xd09e8); C8 (Z_to_bv 64 0xd09f0); C8 (Z_to_bv 64 0xd09e0)] ->
  rw_cells bsegs m 0xd09fc [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16184a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xc72e8 [C8 (Z_to_bv 64 0x15f7a0)] -> rw_cells bsegs m 0x15f7a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x15f788 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xd0f00 (0xd0f00 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
  iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (free_null_post sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC FL IAS IAM CT8 TT0 SW UW CX0 C0 C1 T0 T1 CT2
         UNW S0NE B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  box CT2.
  pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (ficptA_spec 0 ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
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
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 348164 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
                uchain m1 top 348164 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
  { intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 348164 then [] else [bv_unsigned ra]) ++ tr)
      by (replace (bv_unsigned ra =? 348164) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply (uc_step m1 top 348164 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
    - rewrite Z_to_bv_bv_unsigned. exact BS0.
    - rewrite Z_to_bv_bv_unsigned. exact BRA.
    - replace (bv_unsigned ra =? 348164) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
      destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
      + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
      + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
  clear BS0 BRA.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 348164 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
  { destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
    - eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 348164 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
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
    - eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 348164 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
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
  replace (ret_pc (Z_to_bv 64 348256)) with (Z_to_bv 64 348256) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
  { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
  xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
  xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
  xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM1.
  (* [comment removed for export] *)
  rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (dealloc_null_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 lo);
      [rewrite Hsp; exact STu | exact CEIL | rewrite Hsp; lia | exact MIu | reflexivity | rewrite Hsp; eapply rng_sub; [exact RSTK| lia| lia]]. }
  cbv beta. intros ms3 PD.
  destruct PD as (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & -> & MUd & WMd & MId & STd).
  unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
  replace (ret_pc (Z_to_bv 64 348276)) with (Z_to_bv 64 348276) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
  xport UW2 MUd WMd ltac:(lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
  assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at bsegs m3 (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
    intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
  clear IAM2.
  apply rw_cells_of_u64arr' in TB2. rewrite LTB2 in TB2.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB2 | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]). }
  cbv beta. intros ms4 [-> ST4].
  assert (MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM : wmono bsegs m m3).
  { eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu| exact WMd]. }
  unfold free_null_post. do 15 eexists. exists m3.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact ST4|].
  split; [exact UW2|]. split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
  Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed.
End CANSEC1.
