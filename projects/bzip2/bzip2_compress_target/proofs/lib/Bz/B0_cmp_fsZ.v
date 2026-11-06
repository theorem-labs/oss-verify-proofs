(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs2 B0_cmp_fsV B0_cmp_fsW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsA B0_cmp_fsS B0_cmp_fsJ B0_cmp_fsK B0_cmp_fsP.
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

Section B0FSZ.
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
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 A2) s4 (Z_to_bv 64 A1) cSB s7 (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6).
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
  Lemma B0_fs_S7 : forall (m : word -> option byte) (v0 v8 v16 v24 v48 v56 v64 h0 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v48; C8 v56; C8 v64] ->
    rw_cells b0segs m FB [C8 h0] -> mem_inv b0segs m ->
    (forall m', rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v48; C8 v56; C8 v64] ->
       rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x45e0360e)] -> mem_inv b0segs m' -> munch [(FB, FB + 8)]%Z m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa6f04) (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 FB) (Z_to_bv 64 2112) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x3e2ec) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa6ee0) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v24 v48 v56 v64 h0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SLa HD MI K.
    open XOK XSEP.
    pose proof (munch_refl [(FB, FB + 8)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. lit_store.
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

  Lemma B0_fs_S8 : forall (m : word -> option byte) (ft : zarr) (v0 v8 v16 v24 v32 v40 v48 v56 v64 : word)
      (v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word) (v224 v232 : word) (j4 : list byte)
      (ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64] ->
    rw_cells b0segs m (P + 72) [C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
    rw_cells b0segs m (P + 224) [C8 v224; C8 v232; CB 4 j4] -> u32arr b0segs m (P + 244) (zw32 ft 257) ->
    stk b0segs m (P + 1272) (usp + -104) -> rw_cells b0segs m (usp + -104) (FSAVED X) -> stk b0segs m lo P ->
    (stk b0segs m lo usp ->
      evt b0segs Q (MS (mkR (fe_ra X) (fe_sp X) gp tp t0 t1 t2 (fe_s0 X) (fe_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                            (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X) t3 t4 t5 t6)
                       F (ret_pc (fe_ra X)) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (fe_sp X) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa6f04) fc None m (seg_rom b0segs)).
  Proof.
    intros m ft v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 j4
      ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SLa SLb SLc FTL GAP SAV ST K.
    fsenv_open XOK. afenv_open YOK. unfold FSAVED in SAV.
    (* [comment removed for export] *)
    wstep. wstep. do 13 wstep. wstep.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells b0segs _ _ _ SLa) as K0. cbn [cells_size csize Nat.add] in K0. change (Z.of_nat 72) with 72%Z in K0.
    pose proof (stk_of_rw_cells b0segs _ _ _ SLb) as K1. cbn [cells_size csize Nat.add] in K1. change (Z.of_nat 152) with 152%Z in K1.
    pose proof (stk_of_rw_cells b0segs _ _ _ SLc) as K2. cbn [cells_size csize Nat.add] in K2. change (Z.of_nat 20) with 20%Z in K2.
    pose proof (stk_of_u32arr8 b0segs _ _ _ FTL) as K3. rewrite zw32_length_nat in K3.
    pose proof (stk_of_rw_cells b0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add] in K5. change (Z.of_nat 104) with 104%Z in K5.
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
  Notation WZ := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_A2 X, fe_A2 X + ARR2_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 32, ae_P Y + 224); (ae_P Y + 244, ae_P Y + 1272);
                  (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400); (ae_SHF Y + 4, ae_SHF Y + 112); (ae_FCP Y, ae_FCP Y + 1024)]%Z.
  (* [comment removed for export] *)
  Notation WZa := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 32, ae_P Y + 224); (ae_P Y + 244, ae_P Y + 1272); (ae_FCP Y, ae_FCP Y + 1024)]%Z.
  Notation HF := (fp_hsF fm0 ec0 bh0 nb).
  Notation RBF := (fs_rebuild (Z.to_nat nb) (fh_ec HF) (fp_fc0 ec0 nb) (fh_fm HF) 0 0).

  Lemma fp_hs_0 : forall fm ec bh n, fp_hs fm ec bh n 0 = fp_hs0 fm ec bh n.
  Proof. reflexivity. Qed.

  Lemma B0_fs_body : forall (m : word -> option byte) (v0 v8 v16 v32 v40 v48 v56 v64 : word)
      (v72 v88 v96 v112 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word) (jft jfc : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word),
    fsf_distrib fm0 ec0 nb -> fsf_ft4 fm0 ec0 nb -> fsf_fm1 fm0 ec0 nb -> fsf_ec fm0 ec0 bh0 nb -> fsf_bucket fm0 ec0 bh0 nb -> fsf_rebuild fm0 ec0 bh0 nb ->
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 (SHF + 120)); C8 v32; C8 v40; C8 v48; C8 v56; C8 v64] ->
    rw_cells b0segs m (P + 72) [C8 v72; C8 (Z_to_bv 64 nb); C8 v88; C8 v96; C8 (Z_to_bv 64 SHF); C8 v112; C8 (Z_to_bv 64 0); C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
    rw_cells b0segs m (P + 244) [CB 1028 jft] -> rw_cells b0segs m FCP [CB 1024 jfc] ->
    u8arr b0segs m A1 (zb8 fm0 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr b0segs m FT (zw32 bh0 65537) ->
    u32arr b0segs m SHI (ovw znew Jhi 100) -> u32arr b0segs m SLO (ovw znew Jlo 100) ->
    rw_cells b0segs m (SHF + 4) (shc f8b) -> frdW b0segs WZ m 0xcda98%Z [C8 (Z_to_bv 64 0xccd30)] -> mem_inv b0segs m ->
    shzW b0segs WZ m A1 (A1 + ARR1_SIZE) -> shzW b0segs WZ m A2 (A2 + ARR2_SIZE) -> shzW b0segs WZ m FT (FT + 262144) -> shzW b0segs WZ m FCP (FCP + 1024) ->
    (forall m' (w48 w56 w64 : word) (nd hd : Z) (u112 u128 u136 u152 u160 u208 : word)
            (y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y20 y23 y25 y26 y27 y28 y29 y30 y31 : word),
       rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 (SHF + 120)); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 w48; C8 w56; C8 w64] ->
       rw_cells b0segs m' (P + 72) (SCb X Y nd hd u112 u128 u136 u152 u160 u208) ->
       u8arr b0segs m' A1 (zb8 (fh_fm HF) ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 (fst (fst RBF)) ARR2_SIZE) ->
       u32arr b0segs m' FT (zw32 (fh_bh HF) 65537) -> u32arr b0segs m' (P + 244) (zw32 (fp_ft4 fm0 ec0 nb) 257) ->
       u32arr b0segs m' FCP (zw32 (snd (fst RBF)) 256) -> u32arr b0segs m' SHI (ovw (fh_shi HF) Jhi 100) -> u32arr b0segs m' SLO (ovw (fh_slo HF) Jlo 100) ->
       rw_cells b0segs m' (SHF + 4) (shc f8b) -> mem_inv b0segs m' -> munch WZ m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa6ee0) (Z_to_bv 64 P) gp tp y5 y6 y7 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (SHF + 120)) (Z_to_bv 64 128) y12 y13 y14 y15 y16 y17
                             y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 A1) cSB y23 (Z_to_bv 64 FT) y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 120)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa4f64) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v32 v40 v48 v56 v64 v72 v88 v96 v112 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 jft jfc
      ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 FD FF4 FFM FEC FBK FRB SLa SLb FTJ FCJ AR1 AR2 FTB SHIc SLOc SHC GOTV MI SH1 SH2 SHFt SHCp K.
    open XOK XSEP. bz_params.
    assert (AP1C : (A1 + ARR1_SIZE <= FCP \/ FCP + 1024 <= A1)%Z) by (destruct YSEP as (S1 & _ & _); unfold apartv in S1; lia).
    assert (AP2C : (A2 + ARR2_SIZE <= FCP \/ FCP + 1024 <= A2)%Z) by (destruct YSEP as (_ & S2 & _); unfold apartv in S2; lia).
    assert (APFC : (FT + 262148 <= FCP \/ FCP + 1024 <= FT)%Z) by (destruct YSEP as (_ & _ & S3); unfold apartv in S3; lia).
    assert (APSC : (FCP + 1024 <= SHF \/ SHF + 264 <= FCP)%Z) by (destruct YOFF as (_ & _ & _ & O4); unfold SH_LO, SH_HI in O4; lia).
    box_ors.
    pose proof (munch_refl WZ m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof (munch_refl WZa m) as MUa. pose proof (wmono_refl b0segs m) as WMa.
    change (rw_cells b0segs m (SHF + 4) (shc f8b)) with (id (rw_cells b0segs m (SHF + 4) (shc f8b))) in SHC.
    pose proof (zb8_length fm0 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zw32_length bh0 65537 ltac:(lia)) as LB.
    pose proof (ovw_length znew Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length znew Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    change 1028%nat with (Z.to_nat (4 * 257)) in FTJ. pose proof (ovw_init b0segs _ _ 257 _ FTJ ltac:(lia)) as FTL. clear FTJ.
    change 1024%nat with (Z.to_nat (4 * 256)) in FCJ. pose proof (ovw_init b0segs _ _ 256 _ FCJ ltac:(lia)) as FC0. clear FCJ.
    pose proof (ovw_length znew jft 257 ltac:(lia)) as LF0. pose proof (ovw_length znew jfc 256 ltac:(lia)) as LC0.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kv; zify_cond_z Kv; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite <- YSLO, <- YSHI, <- YFCP in SLb.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mz end.
    enter_with (B0_fs_zero X Y Q XOK YOK 257%nat 0 znew jft mz mz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FTL| assumption| apply munch_refl| apply wmono_refl|].
    intros m1. cbv zeta. intros FTL1 MI1 MU1 WM1.
    clear FTL. transport_after_call b0segs mz m1 MU1 WM1. clear MU1 WM1.
    assert (FTL : u32arr b0segs m1 (P + 244) (zw32 fp_ft1 257)).
    { unfold fp_ft1. rewrite <- (ovw_defined_zw32 (fs_ftab_zero 257 znew 0) jft 257); [exact FTL1|].
      intros i Hi. rewrite fs_ftab_zero_def. replace ((0 <=? i) && (i <? 0 + Z.of_nat 257))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    clear FTL1. pose proof (zw32_length fp_ft1 257 ltac:(lia)) as LF.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|]. (wstep; flags). wstep. wstep. wstep. wstep.
    enter_with (B0_fs_count X Y Q XOK YOK (Z.to_nat nb) 0 fp_ft1 m1 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| | exact AR2| exact FTL| assumption| apply munch_refl| apply wmono_refl| |].
    { intros b. unfold fp_ft1. rewrite fs_ftab_zero_get, zget_znew. destruct (_ && _); lia. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    intros m2 y10 y13 y14 y15 y16 y17. cbv zeta. intros AR2_2 FTL2 MI2 MU2 WM2 FT2B. bz_params.
    clear AR2 FTL. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (fs_count (Z.to_nat nb) fp_ft1 ec0 0) with (fp_ft2 ec0 nb) in FTL2, FT2B.
    set (ft2 := fp_ft2 ec0 nb) in *.
    pose proof (zw32_length ft2 257 ltac:(lia)) as LF2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    enter_with (B0_fs_copy X Y Q XOK YOK 256%nat 0 ft2 znew jfc m2 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FT2B| exact FC0| exact FTL2| assumption| apply munch_refl| apply wmono_refl|].
    intros m3 z13. cbv zeta. intros FC3 FTL3 MI3 MU3 WM3.
    clear FC0 FTL2. transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
    set (fc0 := fp_fc0 ec0 nb) in *.
    assert (FCB : u32arr b0segs m3 FCP (zw32 fc0 256)).
    { unfold fc0, fp_fc0. fold ft2. rewrite <- (ovw_defined_zw32 (fs_copy 256 znew ft2 0) jfc 256); [exact FC3|].
      intros i Hi. rewrite fs_copy_def. replace ((0 <=? i) && (i <? 0 + Z.of_nat 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    clear FC3. pose proof (zw32_length fc0 256 ltac:(lia)) as LC.
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (B0_fs_accum X Y Q XOK YOK 256%nat 1 ft2 m3 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| intros b Hb; apply FT2B| pose proof (FT2B (1 - 1)%Z); lia| exact FTL3| assumption| apply munch_refl| apply wmono_refl| | intros b Hb; pose proof (FT2B b); lia].
    intros m4 w12 w13 w14. cbv zeta. intros FTL4 MI4 MU4 WM4 FT3B.
    clear FTL3. transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
    change (fs_accum 256 ft2 1) with (fp_ft3 ec0 nb) in FTL4, FT3B.
    set (ft3 := fp_ft3 ec0 nb) in *.
    (* [comment removed for export] *)
    wstep; if_cases Knb'; zify_cond_z Knb'; [exfalso; lia|]. wstep. wstep. (wstep; flags). wstep. (wstep; flags). wstep. wstep. wstep.
    enter_with (B0_fs_distrib X Y Q XOK XSEP YOK (Z.to_nat nb) 0 ft3 fm0 m4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FD| reflexivity| exact AR1| exact AR2_2| exact FTL4| assumption| apply munch_refl| apply wmono_refl| | |].
    { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    intros m5 q5 q6 q7 q10 q11 q12 q17 q28. cbv zeta. intros AR1_5 AR2_5 FTL5 MI5 MU5 WM5. bz_params.
    clear AR1 AR2_2 FTL4. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
    assert (Edist : fs_distrib (Z.to_nat nb) ft3 fm0 ec0 0 = fp_dist fm0 ec0 nb (Z.to_nat nb)) by reflexivity.
    rewrite Edist in AR1_5, FTL5. clear Edist.
    change (snd (fp_dist fm0 ec0 nb (Z.to_nat nb))) with (fp_fm1 fm0 ec0 nb) in AR1_5.
    change (fst (fp_dist fm0 ec0 nb (Z.to_nat nb))) with (fp_ft4 fm0 ec0 nb) in FTL5.
    set (fm1 := fp_fm1 fm0 ec0 nb) in *. set (ft4 := fp_ft4 fm0 ec0 nb) in *.
    pose proof (zw32_length ft4 257 ltac:(lia)) as LF4.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    wstep. wstep; if_cases K64; zify_cond_z K64; [exfalso; lia|].
    wstep. (wstep; flags). (wstep; flagsb). wstep. (wstep; flags). wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.div_small (nb * 2) 576460752303423488) by lia. rewrite ?Z.add_0_r.
    set (nB := (2 + nb / 32)%Z).
    assert (HnB : (2 <= nB <= 28127)%Z) by (subst nB; pose proof (Z.div_pos nb 32 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound nb 32 28125 ltac:(lia) ltac:(lia)); lia).
    rewrite (Z.div_mul (nb / 32 + 2) 4294967296) by lia || idtac.
    enter_with (B0_fs_bhzero X Y Q XOK YOK (Z.to_nat nB) 0 bh0 m5 m5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FTB| assumption| apply munch_refl| apply wmono_refl| |].
    { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m6 u10 u14 u15. cbv zeta. intros FTB6 MI6 MU6 WM6.
    clear FTB. transport_after_call b0segs m5 m6 MU6 WM6. clear MU6 WM6.
    set (bhz := fs_bh_zero (Z.to_nat nB) bh0 0) in *.
    assert (BWz : bh_w32 bhz) by (subst bhz; apply fs_bh_zero_w32; exact BHOK).
    pose proof (zw32_length bhz 65537 ltac:(lia)) as LBz.
    (* [comment removed for export] *)
    wstep. wstep. (wstep; flags). wstep.
    enter_with (B0_fs_bhinit X Y Q XOK YOK 256%nat 0 ft4 bhz m6 m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact FF4| exact BWz| exact FTL5| exact FTB6| assumption| apply munch_refl| apply wmono_refl| |].
    { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m7 w10 w15 w16 w17. cbv zeta. intros FTL7 FTB7 MI7 MU7 WM7 BW7.
    clear FTL5 FTB6. transport_after_call b0segs m6 m7 MU7 WM7. clear MU7 WM7.
    set (bhi := fs_bh_init 256 bhz ft4 0) in *.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    enter_with (B0_fs_sentinel X Y Q XOK YOK 32%nat 0 bhi m7 m7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact BW7| exact FTB7| assumption| apply munch_refl| apply wmono_refl| |].
    { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m8 x10 x14 x15 x16. cbv zeta. intros FTB8 MI8 MU8 WM8 BW8.
    clear FTB7. transport_after_call b0segs m7 m8 MU8 WM8. clear MU8 WM8.
    set (bh3 := fs_sentinel 32 bhi nb 0) in *.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (wstep; flags). wstep. wstep. wstep. wstep. wstep. wstep. wstep. (wstep; flagsb). wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. (wstep; flags).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (GOTV mm MU) as RO end.
    wstep. clear RO.
    (* [comment removed for export] *)
    wstep. wstep. lit_store. wstep. wstep. lit_store. wstep. wstep. lit_store. wstep. wstep. lit_store. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep. wstep. lit_store. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m8b := mm) in * end.
    shc_move SHC MUa WMa SHC8. clear SHC MUa WMa.
    enter_with (B0_hloop X Y Q Jlo Jhi fm0 ec0 bh0 XOK XSEP YOK YSEP YOFF AX LJlo LJhi FEC FBK (Z.to_nat 64) 0%nat HF m8b m8b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      rewrite ?fp_hs_0; cbn [fh_fm fh_ec fh_bh fh_H fh_slo fh_shi fh_done fp_hs0];
      [st_eq| reflexivity| unfold fp_hsF; reflexivity| unfold fp_hsF; apply fs_H_loop_64_done; lia| | | apply munch_refl| apply wmono_refl| |].
    { unfold hinv. split; [split; [lia| exact FFM]|]. split; [apply fp_fm1_zbok; exact FMOK|]. split; [exact ECOK|]. split; [exact BW8| lia]. }
    { unfold hmem.
      split; [exact AR1_5|]. split; [exact AR2_5|]. split; [exact FTB8|]. split; [|split; [exact SHIc| split; [exact SLOc| split; [exact SHC8| assumption]]]].
      exists (bv_unsigned v88), (bv_unsigned v96), v112, v128, v136, v152, v160, v208. unfold SCb.
      rewrite !Z_to_bv_bv_unsigned. exact SLb. }
    { unfold hsh. split; [| split].
      - eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia].
      - eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia].
      - eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m9 o1 o5 o7 o10 o11 o12 o13 o14 o15 o16 o17 o20 o26 o28 o30 o31 HM9 MU9 WM9 FMR9 FMOK9 ECOK9 BW9.
    cps_destruct HM9 as (AR1_9 & AR2_9 & FTB9 & SCx9 & SHI9 & SLO9 & SHC9 & MI9). bz_params.
    destruct SCx9 as (nd9 & hd9 & w112 & w128 & w136 & w152 & w160 & w208 & SC9).
    clear AR1_5 AR2_5 FTB8 SLb SHIc SLOc. transport_after_call b0segs m8b m9 MU9 WM9. clear MU9 WM9.
    pose proof SC9 as SC9f. unfold SCb in SC9.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kv2; zify_cond_z Kv2; [exfalso; lia|]. wstep; if_cases Knb2; zify_cond_z Knb2; [exfalso; lia|].
    wstep. wstep. wstep. wstep. wstep. wstep. (wstep; flags).
    enter_with (B0_rebuild X Y Q (fh_fm HF) XOK XSEP YOK YSEP FMR9 FMOK9 (Z.to_nat nb) 0 0 (fh_ec HF) fc0 m9 m9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| lia| exact ECOK9| | exact AR1_9| exact AR2_9| exact FCB| exact MI9| apply munch_refl| apply wmono_refl| | | | | |].
    { intros k Hk. exact (FRB k ltac:(lia)). }
    { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SHCp| exact MU| sub_fp_solve| lia| lia]. }
    { eapply (frdW_cell_at b0segs _ _ (P + 72)%Z _ 128%nat); [apply frdW_intro; [exact SC9| cbn [disjoint_from cells_size csize Nat.add]; lia]| reflexivity| lia]. }
    { eapply (frdW_cell_at b0segs _ _ (P + 72)%Z _ 144%nat); [apply frdW_intro; [exact SC9| cbn [disjoint_from cells_size csize Nat.add]; lia]| reflexivity| lia]. }
    intros m10 z5 z6 z7 z10 z11 z28. cbv zeta. intros AR1_10 AR2_10 FCB10 MI10 MU10 WM10 ECOK10 Hj10. bz_params.
    clear AR1_9 AR2_9 FCB MI9.
    shc_move SHC9 MU10 WM10 SHC10. clear SHC9.
    transport_after_call b0segs m9 m10 MU10 WM10. clear MU10 WM10.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    unfold id in SHC10.
    enter_with (K _ _ _ _ nd9 hd9 w112 w128 w136 w152 w160 w208 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact SLa| exact SC9f| exact AR1_10| exact AR2_10| exact FTB9| exact FTL7| exact FCB10| exact SHI9| exact SLO9| exact SHC10| assumption| exact MU| exact WM].
  Qed.

End B0FSZ.
End ACeilS1.
