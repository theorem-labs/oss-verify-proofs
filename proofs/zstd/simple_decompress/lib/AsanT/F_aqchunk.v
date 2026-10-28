(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_aunwind.
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
Section QChunk.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition qchunk_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xcc970) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37c08) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)] /\ 0 < id < 2^31
    /\ ADEPOT DI L m'.

Lemma qchunk_spec : forall (L : alayout) (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx b1 actx lo sz pc : Z) (uw top bot : word) (tb : list word) (tr : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 - ADEPOT_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 hm -> a3 = Z_to_bv 64 S ->
  (* [comment removed for export] *)
  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> 0 <= n < 2^32 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] -> rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr -> In (pc :: tr) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  evtF bsegs RNG (qchunk_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37a90) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros ST CEIL LO MI TP -> -> -> HD UW B1 N H0 H1 TI TK T88 TSD CT CT8 TT CX0 C0 C1 T0 T1 SO TB LTB SZ SZB TR TU SPS STOP
         DEP N0 N1 R0 R1 DHN DHR DHT DHC DTN DTS DCN DCS RIMG RSTK RS RCTX RT RH RND RSR. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AQUAR_Q, ATSDI, ATSDK, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl bsegs m) as WM0.
  carve_frame 48%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  step. lstep. step. step. if_lit.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  box RT. box RH. box RS.
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. unbox RH. unbox RS. rename POST into ST. try rename MI0 into MI.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  rw_split SO 1%nat SOa SOb. apply rw_cells_C4C4_to_C8 in SOb; [|lia].
  step. lstep. step. step.                     (* [comment removed for export] *)
  box RT. box RH. box RCTX.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DEP1 : ADEPOT DI L mm)
      by (eapply (adi_frame DI); [exact DEP| exact MU0| exact WM0|];
          constructor; [| constructor]; cbn [fst snd]; intros a Ha; unfold AIMG_HI in *; lia) end.
  clear MU0 WM0 DEP.
  step. call_sp (adi_put DI L);
    [exact ST | exact CEIL | lia | exact MI | exact TP | reflexivity | reflexivity | exact SZ | exact SZB | exact TB | exact LTB | exact TR | exact TU
    | lia | lia | exact DEP1 | exact N0 | exact N1 | exact R0 | exact R1 | solve_rng | solve_rng | ].
  unbox RT. unbox RH. unbox RCTX. try rename MI0 into MI. clear DEP1.
  match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
  match goal with H : ADEPOT DI L ?mm |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into DEP2 end.
  match goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into ID; rename i into id end.
  zstep. zstep. zstep. zstep.                  (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small id 4294967296) by lia.
  snapshot [(hm + 16, hm + 24)]%Z MU1 WM1.
  step.                                        (* [comment removed for export] *)
  zstep. lstep. lstep. zstep. zstep.           (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold qchunk_post. finish.
  - exact UW.
  - lia.
  - lia.
  - eapply (adi_frame DI); [exact DEP2| exact MU1| exact WM1|].
    constructor; [|constructor]. cbn [fst snd]. intros a Ha. unfold AIMG_HI in *. lia.
Qed.
End QChunk.
End CANSEC1.
