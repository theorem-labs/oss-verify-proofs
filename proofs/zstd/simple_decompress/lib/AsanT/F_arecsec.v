(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanCtrlProps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AKit2 AKitQ ARep ARepKit ARepFrame
     F_apoison APoisonR_iface F_apoisonz F_aalloc3 F_agbb F_asecdealloc AFrameD.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?AD (le8 ?v)) _) =>
      let E := lazymatch AD with wa ?E => E | Z_to_bv 64 ?E => E end in
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Abbreviation SREC2_STACK := 624.

Section CANSEC1. Context {rc : runConstT}.
Lemma recycle_sec_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB CBA lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC2_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + 6128) ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells bsegs m 0xcc6d8 [C8 (Z_to_bv 64 4096)] -> rw_cells bsegs m 0xcc6e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells bsegs m 0xcc708 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xcc718 [C1 srt] -> junk_at m 0xcc720 32 ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xcc958 16 ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr bsegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells bsegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells bsegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS bsegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35b54) fc None m (seg_rom bsegs)).
Proof.
  intros until shj.
  intros ST CEIL LO SPHI MI TP -> -> ISB DSP SB0 I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR ACH NR BR MAL MLO MS8K MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT RA
         RIMG RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  pose proof (ablk_lin _ _ PA0) as (PL1 & PL2 & PL3 & PL4). pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in PL1, ML1, CXI.   (* [comment removed for export] *)
  pose proof MLO as MBND; unfold ablk, AIMG_HI, KLS in MBND. pose proof T0 as TBND; unfold sclr, KLS in TBND.   (* [comment removed for export] *)
  unfold ATP88, ATSD, K_SPACE_SIZE, K_SPACE_EXTRA in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xcc940, 0xcc944); (t + 2800, t + 3168)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xcc940, 0xcc944)]%Z m) as MUs.   (* [comment removed for export] *)
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  box I64. box I72. box NSC. box SRT. box JST. box JGL. box TI. box TK. box T88. box TSD. box CT. box STATS. box ARR. box HDR. box SH. box LHDR. box ACH.
  box DMT. box DMC. box DMP. box DPT. box DPC. box DCT.
  rewrite large_dealloc_unfold. iprefix.
  carve_frame 48%nat ST.
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct DSP as [DLO | DHI];
  [ step; if_cases K1; zify_cond K1; [ | exfalso; clear -K1 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K1 by lia; lia ]
  | step; if_cases K1; zify_cond K1;
    [ exfalso; clear -K1 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K1 by lia; lia
    | zstep; step; if_cases K2; zify_cond K2; [ | exfalso; clear -K2 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K2 by lia; lia ] ] ].
  all: zstep; step.                                            (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: pose proof I64 as I64o; pose proof I72 as I72o; pose proof NSC as NSCo; pose proof ARR as ARRo; pose proof HDR as HDRo.
  all: carry I64 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry I72 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry NSC MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry ARR MU WM ltac:(rewrite ?length_map; ub DPT; clear -CEIL LO SPR T0 PA0 PA1 LEN NSR Y PL1 PL2 PL3 TIC; lia).
  all: carry HDR MU WM ltac:(ub DMT; clear -CEIL LO SPR T0 MLO MCE MS8K Y ML1 ML2 ML3 TIC; lia).
  all: eapply evtF_cut;
       [ eapply (sec_gbb_spec RNG) with (p := mb + 6128) (PA := PA) (nres := nres) (nsec := nsec) (mb := mb) (ms := ms) (lo := lo) (bases := bases);
         lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR
         | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSC
         | |- rw_cells _ _ _ _ => assumption
         | |- u64arr _ _ _ _ => exact ARR
         | |- Forall _ _ => exact BR
         | |- In _ _ => eapply nth_error_In; exact NTHI
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (8 * _) => eapply rng_sub'; [exact RPA|]; clear -IDX NSR; lia
         | |- rng _ _ 32 => eapply rng_sub'; [exact RMB|]; clear -MS8K; lia
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
         | |- ablk _ _ => first [exact MLO | eapply ablk_sub; [exact PA0 | clear; lia | clear -IDX NSR NRB; lia]]   (* [comment removed for export] *)
         | |- _ => atop_facts; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI LEN IDX NSR PA0 PA1 MAL MLO MS8K MCE RA ML1 ML2 ML3 PL1 PL2 PL3; lia
         end
       | ].
  all: cbv beta; intros ms' PO; unfold gbb_post in PO; destruct_exs PO; destruct PO as (-> & MUg & WMg & MIg & STg & MTXg).
  all: rewrite !unsigned_lit in MUg, STg by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 220108)) with (Z_to_bv 64 220108 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: xport FR MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport ISB MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport I64 MUg WMg ltac:(clear -CEIL LO SPR; lia). all: xport I72 MUg WMg ltac:(clear -CEIL LO SPR; lia). all: xport NSC MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport ARR MUg WMg ltac:(rewrite ?length_map; clear -CEIL LO SPR PA0 PA1 LEN NSR PL1 PL2 PL3; lia).
  all: xport HDR MUg WMg ltac:(clear -CEIL LO SPR MLO MCE MS8K ML1 ML2 ML3; lia).
  all: clear MTX; rename MTXg into MTX.
  all: lazymatch type of MU with munch ?W0 ?me ?ma => lazymatch type of MUg with munch _ _ ?mb' =>
         assert (MU2 : munch W0 me mb') by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUg];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans bsegs _ _ _ WM WMg) as WM2 end end.
  all: lazymatch type of MUs with munch ?W0 ?me ?ma => lazymatch type of MUg with munch _ _ ?mb' =>
         assert (MUs2 : munch W0 me mb') by (eapply munch_trans; [exact MUs|]; eapply munch_weaken; [| exact MUg];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia) end end.
  all: clear MU MUs WM MUg WMg MI ST; rename MU2 into MU; rename MUs2 into MUs; rename WM2 into WM; rename MIg into MI; rename STg into ST.
  (* [comment removed for export] *)
  all: step; step; zstep.                                      (* [comment removed for export] *)
  1: step; if_cases K3; zify_cond K3; [ exfalso; clear -K3 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K3 by lia; lia | step ].
  2: step; if_cases K3; zify_cond K3; [ | exfalso; clear -K3 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K3 by lia; lia ];
     step; if_cases K4; zify_cond K4; [ | exfalso; clear -K4 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K4 by lia; lia ].
  (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: clear I64 I72 NSC ARR HDR.
  all: eapply evtF_cut;
       [ eapply (thread_stats_spec RNG ctx t lo);
         lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ (_ + 152) _ => carry CT MU WM ltac:(ub DCT; clear -CEIL LO SPR CX0 CX1 Y CXI; lia); exact CT
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 _)] => first [carry T88 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact T88 | carry TSD MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TSD]
         | |- rw_cells _ _ _ [C1 _] => carry TI MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TI
         | |- rw_cells _ _ _ [C4 _] => carry TK MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TK
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ 4096 => exact RCTX
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
         | |- iclr _ _ => assumption   (* [comment removed for export] *)
         | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR CX0 CX1 T0 T1 TIC CXI; lia
         end
       | ].
  all: cbv beta; intros ms' PO; destruct PO as (a1q & mq & -> & MUt & WMt & MIt & STt).
  all: rewrite !unsigned_lit in MUt, STt by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 220356)) with (Z_to_bv 64 220356 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: lazymatch type of MU with munch ?W0 ?me ?ma => lazymatch type of MUt with munch _ _ ?mb' =>
         assert (MU2 : munch W0 me mb') by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUt];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans bsegs _ _ _ WM WMt) as WM2 end end.
  all: lazymatch type of MUs with munch ?W0 ?me ?ma => lazymatch type of MUt with munch _ _ ?mb' =>
         assert (MUs2 : munch W0 me mb') by (eapply munch_trans; [exact MUs|]; eapply munch_weaken; [| exact MUt];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia) end end.
  all: xport FR MUt WMt ltac:(clear -CEIL LO SPR; lia). all: xport MTX MUt WMt ltac:(clear -CEIL LO SPR; lia). all: xport ISB MUt WMt ltac:(clear -CEIL LO SPR; lia).
  all: clear MU MUs WM MUt WMt MI ST; rename MU2 into MU; rename MUs2 into MUs; rename WM2 into WM; rename MIt into MI; rename STt into ST.
  all: carry STATS MUs WM ltac:(rewrite LSJ; clear -CEIL LO SPR T0 T1 TIC; lia). all: clear MUs.
  all: carry ACH MU WM ltac:(ub DMT; clear -CEIL LO SPR MLO MCE MS8K T0 Y ML1 ML2 ML3 TIC; lia).
  all: pose proof (rng_sub _ _ _ (t + 2800) 368 RT ltac:(clear; lia) ltac:(clear; lia)) as RSJ.
  all: step; step; clear ACH.                                  (* [comment removed for export] *)
  all: aload STATS 6 (t + 2800 + 48).                          (* [comment removed for export] *)
  all: aload STATS 5 (t + 2800 + 40).                          (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep.                             (* [comment removed for export] *)
  all: astore STATS 5.                                         (* [comment removed for export] *)
  all: astore STATS 6.                                         (* [comment removed for export] *)
  all: step; if_cases K5; zify_cond K5; [ exfalso; clear -K5 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K5 by lia; lia | ].   (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  1: step; if_cases K6; zify_cond K6; [ | exfalso; clear -K6 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K6 by lia; lia ].
  2: step; if_cases K6; zify_cond K6; [ exfalso; clear -K6 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K6 by lia; lia | ];
     zstep; step; if_cases K7; zify_cond K7; [ | exfalso; clear -K7 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K7 by lia; lia ].
  (* [comment removed for export] *)
  all: zstep; zstep; step.                                     (* [comment removed for export] *)
  all: do 7 step.                                              (* [comment removed for export] *)
  all: release_frame FR ST (bv_unsigned sp).
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  (* [comment removed for export] *)
  all: carry I64o MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry I72o MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry NSCo MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry SRT MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: unbox JST; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JST; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR T0 TIC; lia] end.
  all: unbox JGL; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JGL; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR T0 TIC; lia] end.
  all: carry TI MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry TK MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry T88 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry TSD MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry CT MU WM ltac:(ub DCT; clear -CEIL LO SPR CX0 CX1 T0 Y TIC CXI; lia).
  all: carry ARRo MU WM ltac:(rewrite ?length_map; ub DPT; clear -CEIL LO SPR T0 PA0 PA1 LEN NSR Y PL1 PL2 PL3 TIC; lia).
  all: carry HDRo MU WM ltac:(ub DMT; clear -CEIL LO SPR T0 MLO MCE MS8K Y ML1 ML2 ML3 TIC; lia).
  all: assert (SHR : 0x800bca00 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND MCE MS8K ML1 ML2 ML3; Z.div_mod_to_equations; lia).
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport bsegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR T0 TIC TBND; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR T0 TIC; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR T0 TIC; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR T0 TIC; lia|]); apply Forall_nil)).
  all: unbox LHDR.
  all: lazymatch goal with |- implF _ _ _ _ _ _ (MS _ _ _ _ _ ?mk _) =>
         assert (LHDRk : idx <> nsec - 1 ->
            rw_cells bsegs mk last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
            /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
            /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last))
         by (intros NE; destruct (LHDR NE) as (LH & L1 & L2 & L3 & L4 & L5 & L6); pose proof (ablk_lin _ _ L1) as (LL1 & LL2 & LL3 & LL4); unfold AIMG_HI in LL1;   (* [comment removed for export] *)
             split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| exact L6]]]]]];
             eapply cells_frame; [exact LH | exact MU | exact WM | cbn; clear -CEIL LO SPR T0 L1 L2 L4 TIC LL1; lia]) end.
  all: clear LHDR.
  all: eapply (sdealloc_spec RNG k st Q) with (mb := mb) (ms := ms) (idx := idx) (PA := PA) (nres := nres) (nsec := nsec) (last := last)
         (ctx := ctx) (t := t) (lo := lo) (bases := bases) (lw1 := lw1) (lw2 := lw2).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDRo
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSCo
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ _ _ => first [eassumption | exact SRT]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- u64arr _ _ _ (map _ _) => exact ARRo
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => rewrite !upd_length; exact LSJ
       | |- @eq (option Z) _ _ => assumption
       | |- @eq Z _ _ => assumption
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ 4096 => assumption
       | |- rng _ _ (8 * _) => exact RPA
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ (_ - _) => exact RSTK
       | |- rng _ _ _ => exact RMB
       | |- _ -> rng _ _ _ => exact RLH
       | |- _ -> _ /\ _ => exact LHDRk
       | |- _ \/ _ => first [unboxed DMT | unboxed DMC | unboxed DMP | unboxed DPT | unboxed DPC | unboxed DCT]
       | |- forall _, _ => idtac
       | |- ablk _ _ => assumption | |- iclr _ _ => assumption   (* [comment removed for export] *)
       | |- _ => try assumption; atop_facts; clear -CEIL LO LO0 SPR SPHI MLO MS8K MSAL MCE CX0 CX1 T0 T1 PA0 PA1 IDX NSR LEN RA MAL NR CXI TIC NRB ML1 ML2 ML3 PL1 PL2 PL3; lia
       end.
  (* [comment removed for export] *)
  all: intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF |].
  all: destruct PP as (MUd & REST); split; [| exact REST].
  all: eapply munch_trans; [eapply munch_weaken; [| exact MU] | exact MUd].
  all: unfold sdealloc_W; let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
Qed.
End CANSEC1.
