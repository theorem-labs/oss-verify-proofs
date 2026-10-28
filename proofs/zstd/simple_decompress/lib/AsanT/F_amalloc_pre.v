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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AModelFacts APrimFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc1b F_aunwind F_aunwind2 F_amalloc_iseg F_amalloc_icpt.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition malloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t lo : Z) (trc : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (spA : word) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (s0A s1A s2A s3A s4A s5A s0i : word) (fr0 junk2 : list byte) (tb : list word) m',
    ms' = MS (mkR (Z_to_bv 64 0x33da8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x37f9c) fc None m' (seg_rom bsegs)
    /\ bv_unsigned spA = bv_unsigned sp - 2144
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 2272)
    /\ rw_cells bsegs m' (bv_unsigned sp - 2272)
         [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
          C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x33ad8)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x551d0)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))]
    /\ u64arr bsegs m' (bv_unsigned sp + -2128 + 16) tb /\ length tb = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = AMALLOC_PC :: trc
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Lemma malloc_pre_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n t lo top bot : Z) (tr trc : list Z),
  let ctx := al_ctx L in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n -> is_primary n = true ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xd09fc [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16184a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (bv_unsigned sp + 16 < top /\ uchain m top AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
   /\ rng RNG lo (top - lo))
  \/ (top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  0 <= bot -> bot < bv_unsigned sp -> bot + 4096 <= top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (malloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t lo trc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until trc. cbv zeta.
  intros ST CEIL LO MI TP Ha0 N PRIM SP16 AC PC LS1 CT8 GPG PGC CX8 TT0 TT SW UW CX0 CX1 CXS T0 T1 TAL TS CT2
         ARM S0NE B0 BB BTOP TOP RA4 RANE RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  assert (LTRC : (length trc <= 29)%nat) by (destruct ARM as [(_ & _ & L1 & -> & _)|(_ & _ & ->)]; cbn [length]; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (destruct ARM as [(X1 & _)|(_ & X2 & _)]; lia).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AMALLOC_SYM, AMALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  box CT2.
  destruct PC as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo);
      try eassumption; try lia; try solve_rng. }
  cbv beta. intros ms1 PA. unfold icptA_post in PA.
  destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRA & FRt & FRs).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
  (* [comment removed for export] *)
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
  xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
  pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
  change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
  pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
  replace (bv_unsigned sp + -2120) with (bv_unsigned sp - 2128 + 8) in SZC by lia.
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp - 2128 + 16) in TB by lia.
  replace (bv_unsigned sp + -72) with (bv_unsigned sp - 2128 + 2056) in BPJ by lia.
  (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp - 2128) 348516 (bv_unsigned sp) t _ _ gp tp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F fc lo trc m1).
  { destruct ARM as [(BT & UC & LTR & Etrc & RTOP)|(BT & BT2 & Etrc)]; rewrite Etrc.
    - (* [comment removed for export] *)
      assert (UC1 : uchain m1 top 348516 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
      { replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 348516 then [] else [bv_unsigned ra]) ++ tr)
          by (replace (bv_unsigned ra =? 348516) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        eapply (uc_step m1 top 348516 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
        - rewrite Z_to_bv_bv_unsigned. exact BS0.
        - rewrite Z_to_bv_bv_unsigned. exact BRA.
        - replace (bv_unsigned ra =? 348516) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
          destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
          + eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. split; [lia| exact I].
          + inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
      clear BS0 BRA UC.
      change (bv_unsigned ra :: tr) with ([bv_unsigned ra] ++ tr).
    eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 348516 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end.
    - (* [comment removed for export] *)
      clear BS0 BRA.
    eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 348516 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1)).
        all: try lazymatch goal with
             | |- stk _ _ _ _ => rewrite Hsp; exact STa
             | |- mem_inv _ _ => exact MIa
             | |- @eq word _ _ => first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
             | |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
             | |- u64arr _ _ _ _ => exact TB
             | |- uchain _ _ _ _ _ _ _ => exact UC1
             | |- _ \/ _ => unboxed CT2
             | |- rng _ _ _ => solve_rng
             | |- rw_cells _ _ (_ + 152) _ => exact CT
             | |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
             | |- rw_cells _ _ (_ + 40) _ => exact SW
             | |- rw_cells _ _ (_ + 3168) _ => exact UW
             end.
        all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
        all: match goal with |- ?G => idtac "REMU" G end. }

  cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
  destruct PU as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & tb2
                  & -> & MUu & WMu & MIu & STu & SZ2 & TB2 & LTB2 & TRF2 & BP2 & UW2).
  unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
  replace (ret_pc (Z_to_bv 64 348608)) with (Z_to_bv 64 348608) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptB_spec RNG); [exact STu | atop_facts; lia | lia | exact MIu | reflexivity | exact RIMG | solve_rng]. }
  cbv beta. intros ms3 PB. unfold icptB_post in PB. destruct PB as (m3 & -> & MUb & WMb & MIb & STb & FR16).
  (* [comment removed for export] *)
  assert (MU3 : munch [(bv_unsigned sp - 2288, bv_unsigned sp); (t + 3168, t + 3169)]%Z m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa]. all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM3 : wmono bsegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  assert (WM13 : wmono bsegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia).
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2128 + 8) with (bv_unsigned sp + -2120) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; clear -LTRC; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2144).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocA_pre_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2128) (al_ctx L) t lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- _ \/ _ => unboxed CT2
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocA_pre_post in PL.
  destruct PL as (t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m4 & -> & MUl & WMl & MIl & STl & [fr0 FRa]).
  rewrite ?Hsp in MUl. rewrite ?Hsp in STl. rewrite ?Hsp in FRa.
  xport FR16 MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(lia). xport FRS MUl WMl ltac:(lia).
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia).
  unfold malloc_pre_post. lazymatch type of Hsp with bv_unsigned ?spx = _ => exists spx end. do 11 eexists. do 7 eexists. exists fr0, junk2, tb2, m4.
  split; [reflexivity|]. split; [clear -Hsp; lia|].
  split.
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUl]]. eapply munch_weaken; [| exact MU3].
    all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
  split; [eapply wmono_trans; [exact WM3 | exact WMl]|]. split; [exact MIl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact STl|].
  split; [replace (bv_unsigned sp - 2272) with (bv_unsigned sp + -2144 - 128) by lia; exact FRa|].
  split; [exact FR16|].
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) in TB2 by lia.
  split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|]. split; [exact TRF2|]. split; [exact FRS|]. exact UW2.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End CANSEC1.
