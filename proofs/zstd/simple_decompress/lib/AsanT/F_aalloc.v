(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AModelFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc2 F_aalloc3.
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
(* [comment removed for export] *)
Lemma poison_cells_frame_b : forall m m' W,
  poison_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, AIMG_LO <= A -> A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI, AIMG_LO in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
  intros a k Ha Hl. destruct (Z.eq_dec a 0) as [->|]. { cbn in Hl. apply Z.pow_pos_nonneg; lia. }
  assert (K : 0 <= k) by (pose proof (Z.log2_nonneg a); lia).
  destruct (Z.lt_ge_cases a (2 ^ k)) as [L|G]; [exact L|]. exfalso.
  assert (k <= Z.log2 a). { rewrite <- (Z.log2_pow2 k) by lia. apply Z.log2_le_mono. lia. } lia.
Qed.
Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
  intros b1 Hb. unfold hdr_b1_mid.
  set (x := Z.lor (Z.land b1 18446744073709551612) 1).
  assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
  split. { apply Z.lor_nonneg. lia. }
  change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
  replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 16) with 4 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Notation allocate_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 1152, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocate_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (allocate_W L sp t c AB UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells bsegs m' (t + 2784) [C8 stj']
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma allocate_fast_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (n S t c cnt spacebeg AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (maxc csz stj idxw j1 j2 : word) (pj : byte)
    (chunks sj : list word) (sjunk uj : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1152 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xcd54d [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xcd524 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xc7f60 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x602cc0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x1617c0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 spacebeg)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
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
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF bsegs RNG (allocate_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 N AC PC PP FLG LS1 LS2 HK SB CT8 TT0 STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CR CH LCH CNT NTH IXS STS SBR HAB HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 SS SZ SZB TB LTB TRF TRU SPS S47 DEP
         RIMG RSTK RS RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; clear -NSR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m n S (al_ctx L) t c cnt spacebeg lo maxc csz stj chunks idxw);
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (with_box CT2 lia). all: try solve_rng. }
  cbv beta. intros ms1 PA. unfold allocA_post in PA. destruct_exs PA.
  destruct PA as (-> & MUa & WMa & MIa & STa & [fr0 FRa] & CRa & [stja STSa]).
  rewrite <- HAB.
  (* [comment removed for export] *)
  xport HDR MUa WMa ltac:(with_box DJT lia). xport SHA MUa WMa ltac:(with_band TS lia). xport SHU MUa WMa ltac:(with_band TS lia).   (* [comment removed for export] *)
  xport PP MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(with_box CT2 lia). xport TT0 MUa WMa ltac:(lia).
  xport SS MUa WMa ltac:(lia). xport TB MUa WMa ltac:(rewrite LTB; lia).
  xport STATS MUa WMa ltac:(rewrite LSJ; lia). xport CT MUa WMa ltac:(with_box CT2 lia).
  xport UJ MUa WMa ltac:(with_box DJT lia).
  xport FLG MUa WMa ltac:(lia). xport LS1 MUa WMa ltac:(lia). xport LS2 MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia).
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  assert (PC1 : poison_cells x13).
  { eapply poison_cells_frame_b; [exact PC | exact MUa | exact WMa |]. unfold AIMG_HI, AIMG_LO.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (SHP1 : n mod 8 <> 0 -> rw_cells bsegs x13 PG [C1 pj]).
  { intros NE. specialize (SHP NE). xport SHP MUa WMa ltac:(with_band TS lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells bsegs x13 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). xport LH MUa WMa ltac:(with_box DJT lia). exact LH. }
  assert (DEP1 : ADEPOT DI L x13).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; pose proof DTN as X1; unbox X1; pose proof DTS as X2; unbox X2; lia|]).
    apply Forall_nil. }
  clear SHP LH PC DEP.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_spec DI L RNG sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc x13 n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STa
         | |- mem_inv _ _ => exact MIa
         | |- poison_cells _ => exact PC1
         | |- ADEPOT _ _ _ => exact DEP1
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP1
         | |- _ -> rw_cells _ _ _ _ => exact LH1
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_post in PB. destruct_exs PB.
  destruct PB as (-> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(lia). xport TSD MUb WMb ltac:(lia).
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; with_band CXS lia).
  xport FLG MUb WMb ltac:(lia). xport LS1 MUb WMb ltac:(lia). xport LS2 MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia).
  destruct PC1 as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(lia). xport GOT80 MUb WMb ltac:(lia). xport REAL MUb WMb ltac:(lia).
  xport UJ MUb WMb ltac:(ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia). xport STSa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).
  assert (LH2 : 16 < rz_size n -> rw_cells bsegs x32 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH1 RZ). pose proof (rz_size_small_cases n N) as RZC.
    xport LH1 MUb WMb ltac:(ub DJN; ub DJS; lia). exact LH1. }
  clear LH1 SHP1.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocD_spec L RNG sp gp tp F fc x32 n t c AB UB lo b0 (hdr_b1_mid b1) x14 S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_post in PD. destruct_exs PD.
  destruct PD as (-> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  xport CRa MUd WMd ltac:(ub DJT; lia). xport STSa MUd WMd ltac:(ub DJT; lia).
  xport SHUb MUd WMd ltac:(with_band TS lia).   (* [comment removed for export] *)
  assert (SHPd : n mod 8 <> 0 -> rw_cells bsegs x47 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(with_band TS lia). exact SHPb. }
  assert (DEPd : ADEPOT DI L x47).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha SPR S47 CEIL LO T0 T1 TAL NI SI N0 N1 R0 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU : munch (allocate_W L sp t c AB UB PG pgw n) m x47).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUb]].
    eapply munch_weaken; [| exact MUa].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono bsegs m x47).
  { eapply wmono_trans; [| exact WMd]. eapply wmono_trans; [exact WMa | exact WMb]. }
  unfold allocate_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LHd|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb.
Qed.
End WithDepot.
End CANSEC2.
(* [comment removed for export] *)
