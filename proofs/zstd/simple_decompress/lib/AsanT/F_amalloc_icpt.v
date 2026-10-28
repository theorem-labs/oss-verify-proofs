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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AModelFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc2 F_aunwind F_aalloc F_amalloc_iseg.
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
Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr bsegs m A ws -> rw_cells bsegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition malloc_fast_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells bsegs m' (t + 2784) [C8 stj']
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma malloc_fast_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt spacebeg AB UB PG pgw lo b0 b1 szh szl ctxj top bot : Z) (maxc csz stj idxw j1 j2 : word) (pj : byte)
    (chunks sj : list word) (sjunk uj : list byte) (tr : list Z),
  let ctx := al_ctx L in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= 448 ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xcd54d [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xcd524 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xc7f60 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x602cc0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x1617c0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m 0xd09fc [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16184a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells bsegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells bsegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 208 + c * 80 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  0 <= spacebeg < 2^47 ->
  (* [comment removed for export] *)
  AB = spacebeg + c * 2^32 + 16 * bv_unsigned idxw ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 56 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  uchain m top AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AMALLOC_PC :: bv_unsigned ra :: tr) (al_U L) -> (length tr <= 28)%nat ->
  0 <= bot -> bot < bv_unsigned sp -> bv_unsigned sp + 16 < top -> top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (top - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF bsegs RNG (malloc_fast_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP Ha0 N SP16 AC PC PP FLG LS1 LS2 HK SB MCS CF34 GPG PGC CT8 TT0 TT SW UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CR CH LCH CNT NTH IXS STS SBR HAB HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 UC S0NE TRU LTR B0 BB BT TOP RA4 RANE DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AMALLOC_SYM, AMALLOC_PC in *.
  word_range sp SPR. word_range s0 S0R. word_range ra RAR.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; clear -NSR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  destruct PC as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (icptA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo);
      try eassumption; try lia. solve_rng. }
  cbv beta. intros ms1 PA. unfold icptA_post in PA.
  destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRA & FRt & FRs).
  (* [comment removed for export] *)
  pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
  replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
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
  eapply evtF_cut.
  { eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp - 2128) 348516 (bv_unsigned sp) (al_ctx L) t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
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
    eapply munch_weaken; [| exact MUa]. all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM3 : wmono bsegs m m3). { eapply wmono_trans; [| exact WMb]. eapply wmono_trans; [exact WMa | exact WMu]. }
  assert (MU13 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUb]]. eapply munch_weaken; [| exact MUu].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM13 : wmono bsegs m1 m3). { eapply wmono_trans; [exact WMu | exact WMb]. }
  xport INI MU13 WM13 ltac:(lia). xport TI MU13 WM13 ltac:(lia). xport TK MU13 WM13 ltac:(lia). xport T88 MU13 WM13 ltac:(lia).
  xport TSD MU13 WM13 ltac:(lia). xport CT MU13 WM13 ltac:(ub CT2; lia). xport FRp MU13 WM13 ltac:(lia). xport TAG MU13 WM13 ltac:(lia).
  xport REST MU13 WM13 ltac:(lia).
  xport RSS MU3 WM3 ltac:(lia). xport IMAX MU3 WM3 ltac:(lia). xport PP MU3 WM3 ltac:(lia). xport FLG MU3 WM3 ltac:(lia).
  xport LS1 MU3 WM3 ltac:(lia). xport LS2 MU3 WM3 ltac:(lia). xport HK MU3 WM3 ltac:(lia). xport SB MU3 WM3 ltac:(lia).
  xport CT8 MU3 WM3 ltac:(ub CT2; lia). xport TT0 MU3 WM3 ltac:(lia). xport STATS MU3 WM3 ltac:(rewrite LSJ; lia).
  xport CR MU3 WM3 ltac:(lia). xport CH MU3 WM3 ltac:(rewrite LCH; lia). xport STS MU3 WM3 ltac:(lia).
  xport HDR MU3 WM3 ltac:(ub DJT; lia). xport UJ MU3 WM3 ltac:(ub DJT; lia). xport SHA MU3 WM3 ltac:(with_band TS lia). xport SHU MU3 WM3 ltac:(with_band TS lia).   (* [comment removed for export] *)
  xport GOT MU3 WM3 ltac:(lia). xport GOT80 MU3 WM3 ltac:(lia). xport REAL MU3 WM3 ltac:(lia).
  xport PC4 MU3 WM3 ltac:(lia). xport PC5 MU3 WM3 ltac:(lia). xport PC6 MU3 WM3 ltac:(lia). xport PC7 MU3 WM3 ltac:(lia).
  assert (SHP3 : n mod 8 <> 0 -> rw_cells bsegs m3 PG [C1 pj]). { intros NE. specialize (SHP NE). xport SHP MU3 WM3 ltac:(with_band TS lia). exact SHP. }
  assert (LH3 : 16 < rz_size n -> rw_cells bsegs m3 AB [C8 j1; C8 j2]). { intros RZ. specialize (LH RZ). xport LH MU3 WM3 ltac:(ub DJT; lia). exact LH. }
  assert (DEP3 : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEP | exact MU3 | exact WM3 |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; lia|]). apply Forall_nil. }
  clear SHP LH DEP.
  (* [comment removed for export] *)
  xport SZ2 MUb WMb ltac:(lia). replace (bv_unsigned sp - 2128 + 8) with (bv_unsigned sp + -2120) in SZ2 by lia.
  rw_join SZ2 TAG SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { cbn [length app]; lia. }
  rw_join FRp SZT SS.
  xport TB2 MUb WMb ltac:(rewrite LTB2; lia). xport BP2 MUb WMb ltac:(lia). xport UW2 MUb WMb ltac:(lia).
  replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
  (* [comment removed for export] *)
  name_sp sp (-2144).
  step.                                                          (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocate_fast_spec DI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n (bv_unsigned sp + -2128) t c cnt spacebeg AB UB PG pgw lo b0 b1 szh szl ctxj
              (1 + Z.of_nat (length (bv_unsigned ra :: tr))) 348516 maxc csz stj idxw j1 j2 pj chunks sj sjunk uj tb2 (bv_unsigned ra :: tr)).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STb
         | |- mem_inv _ _ => exact MIb
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP3
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => first [exact TB2 | exact CH]
         | |- u32arr _ _ _ _ => exact CH
         | |- uchain _ _ _ _ _ _ _ => exact UC1
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- In _ _ => exact TRU
         | |- map _ _ = _ => exact TRF2
         | |- ~ _ -> _ => exact SHP3
         | |- _ -> rw_cells _ _ _ _ => exact LH3
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (_ + -2128) _ => exact SS
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         end.
    all: try lazymatch goal with |- rng _ _ _ => solve_rng end.
    all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
    all: match goal with |- ?G => idtac "REMAL" G end. }
  cbv beta. intros ms4 PL. unfold allocate_post in PL.
  destruct PL as (id & t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m4 & sj4 & stj4
                  & -> & MUl & WMl & MIl & STl & IDR & CR4 & STS4 & STATS4 & LSJ4 & HDR4 & UF4 & LH4 & SHU4 & SHP4 & DEP4).
  unname_sp. rewrite ?unsigned_lit in MUl by lia. rewrite ?unsigned_lit in STl by lia.
  replace (ret_pc (Z_to_bv 64 211672)) with (Z_to_bv 64 211672) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FR16 MUl WMl ltac:(lia). xport SS MUl WMl ltac:(lia). xport UW2 MUl WMl ltac:(clear -TS T0 T1 TAL C16 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG HPW PW01 SB1 SB2 SB3 SB4 CEIL LO TOP BT N LSJ NI SI N1 R1 CX0 CX1 SPR DJT DTN DTS; ub DJT; ub DTN; ub DTS; with_band TS lia).   (* [comment removed for export] *)   (* [comment removed for export] *)
  xport TB2 MUl WMl ltac:(rewrite LTB2; lia). apply rw_cells_of_u64arr in TB2. rewrite LTB2 in TB2.
  rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
  replace (bv_unsigned sp - 2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
  xport FRS MUl WMl ltac:(lia).
  eapply evtF_mono.
  { eapply (icptC_spec RNG sp gp tp); [exact STl | atop_facts; lia | lia | exact MIl | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB2 | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]. }
  cbv beta. intros ms5 PCC. destruct PCC as (m5 & -> & MUc & WMc & MIc & STc).
  (* [comment removed for export] *)
  xport CR4 MUc WMc ltac:(exact I). xport STS4 MUc WMc ltac:(exact I). xport STATS4 MUc WMc ltac:(exact I).
  xport HDR4 MUc WMc ltac:(exact I). xport UF4 MUc WMc ltac:(exact I). xport SHU4 MUc WMc ltac:(exact I). xport UW2 MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells bsegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells bsegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHP4 NE). xport SHP4 MUc WMc ltac:(exact I). exact SHP4. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEP4 | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUl]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUb]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
    eapply munch_weaken; [| exact MUa].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono bsegs m m5).
  { eapply wmono_trans; [exact WM3|]. eapply wmono_trans; [exact WMl| exact WMc]. }
  unfold malloc_fast_post. exists id. do 14 eexists. exists m5, sj4, stj4. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CR4|]. split; [exact STS4|]. split; [exact STATS4|]. split; [exact LSJ4|]. split; [exact UW2|].
  split; [exact HDR4|]. split; [exact UF4|]. split; [exact LH5|]. split; [exact SHU4|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact STa; try exact STu.
Qed.
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
