(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Gm_iface Gm_ropkit Gm_rasterop_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;   (* [comment removed for export] *)
              first [ xlia zchecker
                    | zn_lits; xlia zchecker
                    | zn_lits; zdiv_lits; xlia zchecker
                    | sf_unhide; unpark_all; zify_prune_sub;
                      first [ zn_lits; xlia zchecker
                            | zn_lits; zdiv_lits; xlia zchecker
                            | zn_lits; Z.div_mod_to_equations; xlia zchecker
                            | Zify.zify; xlia zchecker ]
                    | Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Section ROPE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Lemma rop_epi : forall (Σ S : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m mE : mem) (lo fr data dsz fb : Z) (pre : list cell)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word) (F' : bvmap 5 word) (fc' : bv 32),
  fdfs_only PMc -> mat_stable PMc ->
  ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo fb -> rw_cells asegs mE fb pre ->
  fb + Z.of_nat (cells_size pre) = bv_unsigned sp + -104 -> bv_unsigned sp - 240 <= fb ->
  rw_cells asegs mE (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
  LIBH mE -> io_ssp mE ->
  agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a /\ outside [(data, data + dsz)] a) m mE -> wmono asegs m mE ->
  rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
  rt_credit RT Σ - 1 <= rt_credit RT S ->
  (forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a /\ outside [(data, data + dsz)] a -> bv_unsigned sp <= a \/ a < lo) ->
  (forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a /\ outside [(data, data + dsz)] a ->
             (a < fr \/ fr + 128 <= a) /\ (a < fr / 8 + 2147450880 \/ (fr + 128) / 8 + 2147450880 <= a)) ->
  0 < fr -> fr + 128 <= rt_sp0 RT Σ - 8388608 -> fr mod 64 = 0 -> SEGTOP_A <= fr -> (fr + 128 <= 2147446784 \/ 17594333495296 <= fr) ->
  rt_sp0 RT Σ - 8388608 <= lo -> lo + (65536 + 1024 * 4) <= bv_unsigned sp -> bv_unsigned sp + 16 <= 140737488355328 ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT S PMc (eq (MS (mkR r1 (Z_to_bv 64 fb) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 (bv_unsigned sp)) r9 r10 r11 r12 r13 r14 r15 r16 r17
                                        (Z_to_bv 64 fr) r19 (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
                                   F' (Z_to_bv 64 0xa0670) fc' None mE (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra (Z_to_bv 64 (bv_unsigned sp)) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(data, data + dsz)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').
Proof using AF GP.
  intros Σ S PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mE lo fr data dsz fb pre
    r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F' fc'
    FDO MST ARTE MIE STE FRlo FBE FBL FRe WFE WSE LHE SSPE AGF WME EFR ELV ESP0 ECR PFS NFA FR0 FRHI FR64 FRSEG FRSH LOW LOR SPT SPA SPB.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  pose proof (af_sp0_range RT AF S mE ARTE) as SP0R. pose proof (af_sp0_win RT AF S mE ARTE) as SP0W. rewrite ESP0 in SP0R, SP0W.
  unfold lpost, keeps, keepsL.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(data, data + dsz)] a) in *.
  pose proof STE as (STa & STb & _).
  destruct (wr_at_rw_CB mE fr 120 WFE ltac:(lia)) as (jfE & FRME). destruct (wr_at_rw_CB mE (fr / 8 + 2147450880) 16 WSE ltac:(lia)) as (jsE & FSHE).
  change (Z.to_nat 120) with 120%nat in FRME. change (Z.to_nat 16) with 16%nat in FSHE.
  park_disj.
  walk_to AF MST [(usp - 240, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] [0xa0888].
  frame_release_g RT AF GP MST Σ fr 1%nat 128 PF AGF PFS usp lo 0xa0890
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
    ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                    destruct (NFA _ Hx) as [N1 N2]; clear - P N1 N2 LOR FR64 FBL;
                    repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
    ltac:(fun Hx => exact (proj1 Hx))
    ltac:(fun fl FLN => repeat match goal with H : rw_cells asegs _ fr _ |- _ => clear H | H : rw_cells asegs _ (fr / 8 + 2147450880) _ |- _ => clear H end).
  walk_to AF MST [(usp - 240, usp)] (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; clear - P LOR; split; [lia| exact I]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  split.
  + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [split; [exact ART2| split; [exact MIE| split; [exact WME|]]]| split; assumption]|].
    * eapply stk_release in FRlo; [| exact STE| lia].
      eapply stk_release in FRe; [| replace (usp + -104) with (fb + Z.of_nat (cells_size pre)) by lia; exact FRlo| lia].
      cbn [cells_size csize Nat.add] in FRe. replace (usp + -104 + Z.of_nat 104) with usp in FRe by lia. exact FRe.
    * intros a Ha Ho. apply AGF. split; [| exact Ho].
      repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Ha end. exact Ha.
  + repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
    repeat split; auto; lia.
Qed.
End ROPE.
