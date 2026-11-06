(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs2 A0_cmp_fsV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsA A0_cmp_fsS A0_cmp_fsJ A0_cmp_fsK A0_cmp_fsP.
Strategy 1000 [fs_ftab_zero fs_count fs_copy fs_accum fs_distrib fs_bh_zero fs_bh_init fs_sentinel fs_eclass fs_H_loop fs_H_iter
               fs_bucket_loop fs_bucket_iter fs_headers fs_skip0 fs_rebuild fqs_loop fallbackQSort3 fallbackSort
               fs_scan_set_unal fs_scan_word_ff fs_scan_set fs_scan_clr_unal fs_scan_word_00 fs_scan_clr].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Section A0FSZ.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Hypothesis YOFF : afenv_offsh X Y. Hypothesis AX : sanchor (ae_FB Y) (ae_SHF Y).
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation FB := (ae_FB Y). Notation SHF := (ae_SHF Y).
  Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y). Notation FCP := (ae_FCP Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X). Notation lo := (fe_lo X).
  Notation ec0 := (fe_ec X). Notation fm0 := (fe_fm X). Notation bh0 := (fe_bh X).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB (Z_to_bv 64 0) (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6).
  Ltac open XOK XSEP :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & ?AP1F & ?AP2F);
    let SPX := fresh "SPX" in pose proof (afenv_sepx_of X Y XOK YOK YSEP YOFF) as SPX; unfold afenv_sepx, apartv, SH_HI in SPX;
    cps_destruct SPX as (?AP1L & ?AP1H & ?AP2L & ?AP2H & ?APFL & ?APFH & ?AS1 & ?AS2 & ?ASF & ?ASL & ?ASH & ?HLP & ?HHP & ?HSP & ?HPH);
    box_ors.
  Ltac shc_move H MU WM H' := pose proof (shc_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation W4 := [(P + 184, P + 200); (P + 244, P + 1272)]%Z.
  Lemma A0_fs_S4 : forall (m : word -> option byte)
      (v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
    u8arr a0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m (P + 244) (zw32 fp_ft1 257) -> mem_inv a0segs m ->
    shzW a0segs W4 m A2 (A2 + ARR2_SIZE) ->
    (forall m' (y13 y14 : word),
       rw_cells a0segs m' (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                    C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 v200; C8 v208; C8 v216] ->
       u8arr a0segs m' A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m' (P + 244) (zw32 (fp_ft2 ec0 nb) 257) -> mem_inv a0segs m' ->
       munch W4 m m' -> wmono a0segs m m' -> (forall b, 0 <= zget (fp_ft2 ec0 nb) b <= nb)%Z ->
       evt a0segs Q (MS (RB (Z_to_bv 64 0x9ae08) t0 t1 t2 (Z_to_bv 64 FCP) (Z_to_bv 64 (P + 244)) (Z_to_bv 64 1024) y13 y14 a5 a6 a7
                            (Z_to_bv 64 FCP) (Z_to_bv 64 FB) s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x52a04) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (P + 244)) (Z_to_bv 64 FB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ad8c) fc None m (seg_rom a0segs)).
  Proof.
    intros m v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6
      SLb AR2 FTL MI SH2 K.
    open XOK XSEP. bz_params.
    pose proof (munch_refl W4 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length fp_ft1 257 ltac:(lia)) as LF.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|]. wstep. wstep.
    enter_with (A0_fs_count X Y Q XOK YOK (Z.to_nat nb) 0 fp_ft1 m m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| | exact AR2| exact FTL| exact MI| apply munch_refl| apply wmono_refl| |].
    { intros b. unfold fp_ft1. rewrite fs_ftab_zero_get, zget_znew. destruct (_ && _); lia. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    intros m2 y10 y11 y12 y13 y14. cbv zeta. intros AR2_2 FTL2 MI2 MU2 WM2 FT2B. bz_params.
    clear AR2 FTL MI. transport_after_call a0segs m m2 MU2 WM2. clear MU2 WM2.
    change (fs_count (Z.to_nat nb) fp_ft1 ec0 0) with (fp_ft2 ec0 nb) in FTL2, FT2B.
    pose proof (zw32_length (fp_ft2 ec0 nb) 257 ltac:(lia)) as LF2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite <- YSLO, <- YSHI in SLb.
    enter_with (K _ _ _); [st_eq| exact SLb| exact AR2_2| exact FTL2| assumption| exact MU| exact WM| exact FT2B].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation W5 := [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)]%Z.
  Lemma A0_fs_S5 : forall (m : word -> option byte)
      (v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
    u8arr a0segs m A1 (zb8 fm0 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m (P + 244) (zw32 (fp_ft2 ec0 nb) 257) -> mem_inv a0segs m ->
    shzW a0segs W5 m A1 (A1 + ARR1_SIZE) -> shzW a0segs W5 m A2 (A2 + ARR2_SIZE) ->
    (forall b, 0 <= zget (fp_ft2 ec0 nb) b <= nb)%Z -> fsf_distrib fm0 ec0 nb ->
    (forall m' (y3 y4 y5 y6 y7 : word),
       rw_cells a0segs m' (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                    C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
       u8arr a0segs m' A1 (zb8 (fp_fm1 fm0 ec0 nb) ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec0 ARR2_SIZE) ->
       u32arr a0segs m' (P + 244) (zw32 (fp_ft4 fm0 ec0 nb) 257) -> mem_inv a0segs m' ->
       munch W5 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (RB (Z_to_bv 64 634608) (Z_to_bv 64 nb) t1 t2 (Z_to_bv 64 FT) (Z_to_bv 64 0) (Z_to_bv 64 (4 * fp_nB nb)) y3 y4 y5 y6 y7
                            s2 s3 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ae08) fc None m (seg_rom a0segs)).
  Proof.
    intros m v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s10 s11 t3 t4 t5 t6
      SLb AR1 AR2 FTL MI SH1 SH2 FT2B FD K.
    open XOK XSEP. bz_params.
    pose proof (munch_refl W5 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    set (ft2 := fp_ft2 ec0 nb) in *.
    pose proof (zb8_length fm0 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft2 257 ltac:(lia)) as LF2.
    pose proof (FT2B 0%Z) as F20.
    (* [comment removed for export] *)
    pose proof (zw32_read a0segs m (P + 244) ft2 257 0 _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget ft2 0)) by lia. wstep. wstep.
    enter_with (A0_fs_accum X Y Q XOK YOK 256%nat 1 ft2 m m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| intros b Hb; apply FT2B| pose proof (FT2B (1 - 1)%Z); lia| exact FTL| exact MI| apply munch_refl| apply wmono_refl| | intros b Hb; pose proof (FT2B b); lia].
    intros m4 y10 y11 y13. cbv zeta. intros FTL4 MI4 MU4 WM4 FT3B.
    clear FTL MI. transport_after_call a0segs m m4 MU4 WM4. clear MU4 WM4.
    change (fs_accum 256 ft2 1) with (fp_ft3 ec0 nb) in FTL4, FT3B.
    set (ft3 := fp_ft3 ec0 nb) in *.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Knb'; zify_cond_z Knb'; [exfalso; lia|]. wstep. wstep. wstep. wstep. wstep.
    enter_with (A0_fs_distrib X Y Q XOK XSEP YOK (Z.to_nat nb) 0 ft3 fm0 m4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FD| reflexivity| exact AR1| exact AR2| exact FTL4| exact MI4| apply munch_refl| apply wmono_refl| | |].
    { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    intros m5 z10 z11 z12 z14 z15 z16 z17. cbv zeta. intros AR1_5 AR2_5 FTL5 MI5 MU5 WM5. bz_params.
    clear AR1 AR2 FTL4 MI4. transport_after_call a0segs m4 m5 MU5 WM5. clear MU5 WM5.
    assert (Edist : fs_distrib (Z.to_nat nb) ft3 fm0 ec0 0 = fp_dist fm0 ec0 nb (Z.to_nat nb)) by reflexivity.
    rewrite Edist in AR1_5, FTL5. clear Edist.
    change (snd (fp_dist fm0 ec0 nb (Z.to_nat nb))) with (fp_fm1 fm0 ec0 nb) in AR1_5.
    change (fst (fp_dist fm0 ec0 nb (Z.to_nat nb))) with (fp_ft4 fm0 ec0 nb) in FTL5.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K63; zify_cond_z K63; [exfalso; lia|].
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.div_small (nb * 2) 576460752303423488) by lia. rewrite Z.add_0_r.
    replace (nb / 32 * 4 + 8)%Z with (4 * fp_nB nb)%Z by (unfold fp_nB; lia).
    enter_with (K _ _ _ _ _ _); [st_eq| exact SLb| exact AR1_5| exact AR2_5| exact FTL5| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_S7 : forall (m : word -> option byte) (v0 v8 v16 v24 v32 v48 v56 v64 v72 h0 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 (Z_to_bv 64 FB); C8 v48; C8 v56; C8 v64; C8 v72] ->
    rw_cells a0segs m FB [C8 h0] -> mem_inv a0segs m ->
    (forall m', rw_cells a0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 (Z_to_bv 64 FB); C8 v48; C8 v56; C8 v64; C8 v72] ->
       rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x45e0360e)] -> mem_inv a0segs m' -> munch [(FB, FB + 8)]%Z m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x9c278) (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 FB) (Z_to_bv 64 2112) a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 FB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x3e404) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 FB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9c258) fc None m (seg_rom a0segs)).
  Proof.
    intros m v0 v8 v16 v24 v32 v48 v56 v64 v72 h0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SLa HD MI K.
    open XOK XSEP.
    pose proof (munch_refl [(FB, FB + 8)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    wstep. wstep. wstep.
    eapply K; [exact SLa| exact HD| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stk_join8 : forall segs m a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> (a <= b <= c)%Z -> stk segs m a c.
  Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
  Ltac stk_add8 ST K :=
    lazymatch type of K with stk _ _ ?b' ?c =>
    lazymatch type of ST with stk ?segs ?m ?lo ?b =>
      let H := fresh in pose proof (stk_join8 segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.
  Lemma stk_of_u32arr8 : forall segs m A ws, u32arr segs m A ws -> stk segs m A (A + 4 * Z.of_nat (length ws)).
  Proof.
    intros segs m A ws H. unfold u32arr in H.
    assert (U : u8arr segs m A (u32s ws)) by (unfold u8arr; rewrite u32s_length, Nat2Z.inj_mul; change (Z.of_nat 4) with 4%Z; exact H).
    pose proof (stk_of_rw_cells segs m A _ (rw_cells_of_u8arr segs m A _ U)) as S.
    cbn [cells_size csize] in S. rewrite Nat.add_0_r, u32s_length, Nat2Z.inj_mul in S. exact S.
  Qed.

  Lemma A0_fs_S8 : forall (m : word -> option byte) (ft : zarr) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 : word)
      (v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word) (v224 v232 : word) (j4 : list byte)
      (ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
    rw_cells a0segs m (P + 80) [C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
    rw_cells a0segs m (P + 224) [C8 v224; C8 v232; CB 4 j4] -> u32arr a0segs m (P + 244) (zw32 ft 257) ->
    stk a0segs m (P + 1272) (usp + -104) -> rw_cells a0segs m (usp + -104) (FSAVED X) -> stk a0segs m lo P ->
    (stk a0segs m lo usp ->
      evt a0segs Q (MS (mkR (fe_ra X) (fe_sp X) gp tp t0 t1 t2 (fe_s0 X) (fe_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                            (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X) t3 t4 t5 t6)
                       F (ret_pc (fe_ra X)) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (fe_sp X) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9c278) fc None m (seg_rom a0segs)).
  Proof.
    intros m ft v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 j4
      ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SLa SLb SLc FTL GAP SAV ST K.
    fsenv_open XOK. afenv_open YOK. unfold FSAVED in SAV.
    (* [comment removed for export] *)
    wstep. wstep. do 13 wstep. wstep.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells a0segs _ _ _ SLa) as K0. cbn [cells_size csize Nat.add] in K0. change (Z.of_nat 80) with 80%Z in K0.
    pose proof (stk_of_rw_cells a0segs _ _ _ SLb) as K1. cbn [cells_size csize Nat.add] in K1. change (Z.of_nat 144) with 144%Z in K1.
    pose proof (stk_of_rw_cells a0segs _ _ _ SLc) as K2. cbn [cells_size csize Nat.add] in K2. change (Z.of_nat 20) with 20%Z in K2.
    pose proof (stk_of_u32arr8 a0segs _ _ _ FTL) as K3. rewrite zw32_length_nat in K3.
    pose proof (stk_of_rw_cells a0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add] in K5. change (Z.of_nat 104) with 104%Z in K5.
    stk_add8 ST K0. stk_add8 ST K1. stk_add8 ST K2. stk_add8 ST K3. stk_add8 ST GAP. stk_add8 ST K5.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with usp in ST by lia end.
    replace (Z_to_bv 64 (usp + -1376 + 1376)) with (fe_sp X) by (rewrite <- (Z_to_bv_bv_unsigned (fe_sp X)) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep.
    exact (K ST).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (Jlo Jhi : list byte).
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  Notation W6 := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_A2 X, fe_A2 X + ARR2_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 24, ae_P Y + 224);
                  (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400); (ae_SHF Y + 4, ae_SHF Y + 112); (ae_FCP Y, ae_FCP Y + 1024)]%Z.
  Notation W6a := [(fe_FT X, fe_FT X + 262148); (ae_P Y + 24, ae_P Y + 224)]%Z.
  Notation HF := (fp_hsF fm0 ec0 bh0 nb).
  Notation RBF := (fs_rebuild (Z.to_nat nb) (fh_ec HF) (fp_fc0 ec0 nb) (fh_fm HF) 0 0).

  Lemma fp_hs_0 : forall fm ec bh n, fp_hs fm ec bh n 0 = fp_hs0 fm ec bh n.
  Proof. reflexivity. Qed.

  Lemma A0_fs_S6 : forall (m : word -> option byte) (v0 v8 v16 v24 v40 v48 v56 v64 v72 : word)
      (v80 v88 v104 v112 v128 v136 v144 v152 v160 v168 v176 v200 v208 v216 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word),
    (0x61e000 <= FT)%Z ->
    fsf_ft4 fm0 ec0 nb -> fsf_fm1 fm0 ec0 nb -> fsf_ec fm0 ec0 bh0 nb -> fsf_bucket fm0 ec0 bh0 nb -> fsf_rebuild fm0 ec0 bh0 nb ->
    rw_cells a0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 (Z_to_bv 64 (SHF + 120)); C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
    rw_cells a0segs m (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 (Z_to_bv 64 SHF); C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 v200; C8 v208; C8 v216] ->
    u8arr a0segs m A1 (zb8 (fp_fm1 fm0 ec0 nb) ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec0 ARR2_SIZE) ->
    u32arr a0segs m FT (zw32 (fs_bh_zero (Z.to_nat (fp_nB nb)) bh0 0) 65537) -> u32arr a0segs m (P + 244) (zw32 (fp_ft4 fm0 ec0 nb) 257) ->
    u32arr a0segs m FCP (zw32 (fp_fc0 ec0 nb) 256) -> u32arr a0segs m SHI (ovw znew Jhi 100) -> u32arr a0segs m SLO (ovw znew Jlo 100) ->
    rw_cells a0segs m (SHF + 4) (shc f8b) -> ro_cells a0segs m 0xc06b8 [C8 (Z_to_bv 64 0xbf950)] -> mem_inv a0segs m ->
    shzW a0segs W6 m A1 (A1 + ARR1_SIZE) -> shzW a0segs W6 m A2 (A2 + ARR2_SIZE) -> shzW a0segs W6 m FT (FT + 262144) -> shzW a0segs W6 m FCP (FCP + 1024) ->
    (forall m' (w56 w64 w72 : word) (lq nd rr Hh : Z) (u144 u160 u176 u200 u208 : word) (y0 y1 y2 y3 y4 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : word),
       rw_cells a0segs m' P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 FCP); C8 (Z_to_bv 64 (SHF + 120)); C8 v40; C8 (Z_to_bv 64 FB); C8 w56; C8 w64; C8 w72] ->
       rw_cells a0segs m' (P + 80) (SCq X Y lq nd u144 rr u160 Hh u176 u200 u208) ->
       u8arr a0segs m' A1 (zb8 (fh_fm HF) ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 (fst (fst RBF)) ARR2_SIZE) ->
       u32arr a0segs m' FT (zw32 (fh_bh HF) 65537) -> u32arr a0segs m' (P + 244) (zw32 (fp_ft4 fm0 ec0 nb) 257) ->
       u32arr a0segs m' FCP (zw32 (snd (fst RBF)) 256) -> u32arr a0segs m' SHI (ovw (fh_shi HF) Jhi 100) -> u32arr a0segs m' SLO (ovw (fh_slo HF) Jlo 100) ->
       rw_cells a0segs m' (SHF + 4) (shc f8b) -> mem_inv a0segs m' -> munch W6 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x9c258) (Z_to_bv 64 P) gp tp y0 y1 y2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (SHF + 120)) (Z_to_bv 64 128) y3 y4 y5 y6 y7 (Z_to_bv 64 FCP)
                             (Z_to_bv 64 FB) y10 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB y11 y12 y13 y14 y15 y16 y17 y18 y19)
                        F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 FCP) (Z_to_bv 64 FB) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 634608) fc None m (seg_rom a0segs)).
  Proof.
    intros m v0 v8 v16 v24 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 v136 v144 v152 v160 v168 v176 v200 v208 v216
      ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 IMGF FF4 FFM FEC FBK FRB SLa SLb AR1 AR2 FTB FTL FCB SHIc SLOc SHC GOTS MI SH1 SH2 SHFt SHCp K.
    open XOK XSEP. bz_params.
    assert (AP1C : (A1 + ARR1_SIZE <= FCP \/ FCP + 1024 <= A1)%Z) by (destruct YSEP as (S1 & _ & _); unfold apartv in S1; lia).
    assert (AP2C : (A2 + ARR2_SIZE <= FCP \/ FCP + 1024 <= A2)%Z) by (destruct YSEP as (_ & S2 & _); unfold apartv in S2; lia).
    assert (APFC : (FT + 262148 <= FCP \/ FCP + 1024 <= FT)%Z) by (destruct YSEP as (_ & _ & S3); unfold apartv in S3; lia).
    assert (APSC : (FCP + 1024 <= SHF \/ SHF + 264 <= FCP)%Z) by (destruct YOFF as (_ & _ & _ & O4); unfold SH_LO, SH_HI in O4; lia).
    box_ors.
    pose proof (munch_refl W6 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    pose proof (munch_refl W6a m) as MUa. pose proof (wmono_refl a0segs m) as WMa.
    change (rw_cells a0segs m (SHF + 4) (shc f8b)) with (id (rw_cells a0segs m (SHF + 4) (shc f8b))) in SHC.
    set (nB := fp_nB nb) in *. set (bhz := fs_bh_zero (Z.to_nat nB) bh0 0) in *.
    set (ft4 := fp_ft4 fm0 ec0 nb) in *. set (fm1 := fp_fm1 fm0 ec0 nb) in *. set (fc0 := fp_fc0 ec0 nb) in *.
    assert (BWz : bh_w32 bhz) by (subst bhz; apply fs_bh_zero_w32; exact BHOK).
    pose proof (zw32_length ft4 257 ltac:(lia)) as LF4. pose proof (zw32_length bhz 65537 ltac:(lia)) as LBz.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    enter_with (A0_fs_bhinit X Y Q XOK YOK 256%nat 0 ft4 bhz m m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FF4| exact BWz| exact FTL| exact FTB| exact MI| apply munch_refl| apply wmono_refl| |].
    { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m7 w10 w11 w12 w14 w15. cbv zeta. intros FTL7 FTB7 MI7 MU7 WM7 BW7.
    clear FTL FTB MI. transport_after_call a0segs m m7 MU7 WM7. clear MU7 WM7.
    set (bhi := fs_bh_init 256 bhz ft4 0) in *.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m7b := mm) in * end.
    enter_with (A0_fs_sentinel X Y Q XOK YOK 32%nat 0 bhi m7b m7b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact BW7| exact FTB7| assumption| apply munch_refl| apply wmono_refl| |].
    { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m8 x10 x11 x13 x14 x15. cbv zeta. intros FTB8 MI8 MU8 WM8 BW8.
    clear FTB7. transport_after_call a0segs m7b m8 MU8 WM8. clear MU8 WM8.
    set (bh3 := fs_sentinel 32 bhi nb 0) in *.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. clear GOTS. wstep. rewrite (Z.div_mul nb 4294967296) by lia.
    wstep. wstep. lit_store. wstep. wstep. lit_store. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep. wstep. lit_store. wstep. wstep. lit_store. wstep. lit_store.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m8b := mm) in * end.
    shc_move SHC MUa WMa SHC8. clear SHC MUa WMa.
    replace (A1 + -4)%Z with (A1 - 4)%Z in SLb by lia.
    enter_with (A0_hloop X Y Q Jlo Jhi fm0 ec0 bh0 XOK XSEP YOK YSEP YOFF AX LJlo LJhi FEC FBK (Z.to_nat 64) 0%nat HF m8b m8b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      rewrite ?fp_hs_0; cbn [fh_fm fh_ec fh_bh fh_H fh_slo fh_shi fh_done fp_hs0];
      [st_eq| reflexivity| unfold fp_hsF; reflexivity| unfold fp_hsF; apply fs_H_loop_64_done; lia| | | apply munch_refl| apply wmono_refl| |].
    { unfold hinv. split; [split; [lia| exact FFM]|]. split; [apply fp_fm1_zbok; exact FMOK|]. split; [exact ECOK|]. split; [exact BW8| lia]. }
    { unfold hmem.
      split; [exact AR1|]. split; [exact AR2|]. split; [exact FTB8|]. split; [|split; [exact SHIc| split; [exact SLOc| split; [exact SHC8| assumption]]]].
      exists (bv_unsigned v104), (bv_unsigned v112), (bv_unsigned v152), (bv_unsigned v168), v144, v160, v176, v200, v208. unfold SCq.
      rewrite !Z_to_bv_bv_unsigned. exact SLb. }
    { unfold hsh. split; [| split].
      - eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia].
      - eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia].
      - eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m9 u1 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u27 u28 u29 u30 u31 HM9 MU9 WM9 FMR9 FMOK9 ECOK9 BW9.
    cps_destruct HM9 as (AR1_9 & AR2_9 & FTB9 & SCx9 & SHI9 & SLO9 & SHC9 & MI9). bz_params.
    destruct SCx9 as (lq9 & nd9 & rr9 & H9 & w144 & w160 & w176 & w200 & w208 & SC9).
    clear AR1 AR2 FTB8 SLb SHIc SLOc. transport_after_call a0segs m8b m9 MU9 WM9. clear MU9 WM9.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Knb2; zify_cond_z Knb2; [exfalso; lia|]. wstep. wstep. wstep.
    enter_with (A0_rebuild X Y Q (fh_fm HF) XOK XSEP YOK YSEP FMR9 FMOK9 (Z.to_nat nb) 0 0 (fh_ec HF) fc0 m9 m9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| lia| exact ECOK9| | exact AR1_9| exact AR2_9| exact FCB| exact MI9| apply munch_refl| apply wmono_refl| | | |].
    { intros k Hk. exact (FRB k ltac:(lia)). }
    { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SHCp| exact MU| sub_fp_solve| lia| lia]. }
    intros m10 z10 z13 z14 z15. cbv zeta. intros AR1_10 AR2_10 FCB10 MI10 MU10 WM10 ECOK10 Hj10. bz_params.
    clear AR1_9 AR2_9 FCB MI9. 
    shc_move SHC9 MU10 WM10 SHC10. clear SHC9.
    transport_after_call a0segs m9 m10 MU10 WM10. clear MU10 WM10.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kj; zify_cond_z Kj; [| exfalso; lia].
    wstep. wstep. wstep.
    unfold id in SHC10.
    enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact SLa| exact SC9| exact AR1_10| exact AR2_10| exact FTB9| exact FTL7| exact FCB10| exact SHI9| exact SLO9| exact SHC10| assumption| exact MU| exact WM].
  Qed.

End A0FSZ.
End ACeilS1.
