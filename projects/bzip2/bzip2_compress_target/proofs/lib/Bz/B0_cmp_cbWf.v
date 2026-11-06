(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 DecTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut BzCNumZ CmpLaws CmpCutCB CmpCutCBw CmpArith CmpArith2 CmpSdTac BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT BzWalkArith4 CmpCutBsw CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV CmpSmKit CmpHmKit B0_cmp_cbV B0_cmp_cbWc.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpMsKit2.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)

Section B0CBWF.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation nblock := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Notation EH1b := (EH1b X g e). Notation EH2b := (EH2b X g e). Notation AR2b := (AR2b X e).
  Notation cbF_W := (cbF_W X).

  (* [comment removed for export] *)
  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         cSB s3 s4 (Z_to_bv 64 FB) s6 s7 (Z_to_bv 64 FB) s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6).

  Ltac prepW :=
    let CX := ident:(CX) in let SEP := ident:(SEP) in
    cbenv_open XOK; acenv_open YOK; cb_ranges CX;
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE in S; cbv zeta in S; cps_destruct S as (_ & ?AEA2 & _); box_ors.
  Ltac openW EH1 EH2 := unfold B0_cmp_cbWc.EH1b, EHEAD1 in EH1; unfold B0_cmp_cbWc.EH2b, EHEAD2 in EH2; cbn_est_in EH1; cbn_est_in EH2; rewrite Gbs in EH2; rewrite Gzb in EH1.
  Ltac closeW1 EH1 := unfold B0_cmp_cbWc.EH1b, EHEAD1; cbn_est; rewrite Gzb; unfold bw_emit; cbn [bw_numZ]; exact EH1.
  Ltac closeW2 EH2 := unfold B0_cmp_cbWc.EH2b, EHEAD2; cbn_est; rewrite Gbs; unfold bw_emit; cbn [bw_buff bw_live]; exact EH2.

  (* [comment removed for export] *)
  Ltac flush_body b m EH2 AR2 pc_blt :=
    let RB := fresh "RB" in let SO := fresh "SO" in
    pose proof (rw_cells_read_byte3 b0segs m (E + 640) _ 0%nat _ _ EH2 eq_refl eq_refl) as RB;
    rewrite unsigned_lit in RB by lia;
    wstep; clear RB; cbv beta delta [zxb]; rewrite (unsigned_lit8 (bw_buff b / 16777216)) by lia;
    (* [comment removed for export] *)
    brun;
    pose proof (u8arr_store_ok b0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO;
    wstep;
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      let AR2' := fresh "AR2'" in
      pose proof (zb8_write1 b0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2';
      clear AR2; store_done; rename AR2' into AR2 end;
    (* [comment removed for export] *)
    brun_to pc_blt;
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z; [rewrite low32_mod; apply low32_shl8_sx32|];
    try rewrite (sx32_of_Z (bw_live b + -8)) by lia;
    try (replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia);
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2
      by (rewrite zbl_emit by lia; unfold wr8; f_equal; rewrite shiftr_div24; rewrite unsigned_lit by lia; reflexivity).

  (* [comment removed for export] *)
  Lemma B0_cb_flush1 : forall (f : nat) (b : bw) (me m : word -> option byte)
      (ra t1 t2 a0 s6 t3 t4 t5 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (nblock + bw_numZ b + Z.of_nat f <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv b0segs m -> munch cbF_W me m -> wmono b0segs me m ->
    shzW b0segs cbF_W me E (E + ESTATE_SIZE) -> shzW b0segs cbF_W me A2 (A2 + ARR2_SIZE) ->
    (forall b1 m' (a0' t1' t2' t3' t4' : word),
        b1 = bs_needw f b -> EH1b m' b1 -> EH2b m' b1 -> AR2b m' b1 -> mem_inv b0segs m' -> munch cbF_W me m' -> wmono b0segs me m' ->
        (0 <= bw_live b1 < 8)%Z -> bw_ok b1 -> (bw_numZ b1 <= bw_numZ b + Z.of_nat f)%Z ->
        evt b0segs Q (MS (RW ra (Z_to_bv 64 (bw_live b1)) t1' t2' a0' (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 3) (Z_to_bv 64 (SHE + 14))
                             (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116)) s6 (Z_to_bv 64 E)
                             (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5 (Z_to_bv 64 (E + 80)))
                          F (Z_to_bv 64 0x89f40) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra (Z_to_bv 64 (bw_live b)) t1 t2 a0 (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 3) (Z_to_bv 64 (SHE + 14))
                         (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116)) s6 (Z_to_bv 64 E)
                         (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 t4 t5 (Z_to_bv 64 (E + 80)))
                      F (Z_to_bv 64 0x89e38) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros b me m ra t1 t2 a0 s6 t3 t4 t5 OK L8 Lf ROOM EH1 EH2 AR2 MI MU WM SHe SH2 K; [lia|].
    prepW. openW EH1 EH2. unfold B0_cmp_cbWc.cbF_W, ESTATE_SIZE in MU, SHe, SH2.
    cps_destruct OK as (OKb & OKl & OKn). bz_params.
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    brun.
    flush_body b m EH2 AR2 0x89ef0%Z.
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (bw_emit b) me mm ra _ _ _ s6 _ _ t5); [st_eq| unfold bw_ok; lia| lia| lia| lia| closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| exact SHe| exact SH2|] end.
      intros b1 m' a0' t1' t2' t3' t4' Eb1 EH1' EH2' AR2' MI' MU' WM' L1 OK1 NZ1. eapply K; [| exact EH1'| exact EH2'| exact AR2'| exact MI'| exact MU'| exact WM'| exact L1| exact OK1| lia].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| lia| unfold bw_ok; lia| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_cb_flush2 : forall (f : nat) (b : bw) (me m : word -> option byte)
      (ra t2 a0 a2 s6 t3 t4 t5 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (nblock + bw_numZ b + Z.of_nat f <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv b0segs m -> munch cbF_W me m -> wmono b0segs me m ->
    shzW b0segs cbF_W me E (E + ESTATE_SIZE) -> shzW b0segs cbF_W me A2 (A2 + ARR2_SIZE) ->
    (forall b1 m' (a0' t2' t3' t4' t5' : word),
        b1 = bs_needw f b -> EH1b m' b1 -> EH2b m' b1 -> AR2b m' b1 -> mem_inv b0segs m' -> munch cbF_W me m' -> wmono b0segs me m' ->
        (0 <= bw_live b1 < 8)%Z -> bw_ok b1 -> (bw_numZ b1 <= bw_numZ b + Z.of_nat f)%Z ->
        evt b0segs Q (MS (RW ra (Z_to_bv 64 7) (Z_to_bv 64 (bw_live b1)) t2' a0' (Z_to_bv 64 (SHE + 80)) a2 (Z_to_bv 64 7) (Z_to_bv 64 (SHE + 80))
                             (Z_to_bv 64 3) (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 7) (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116)) s6 (Z_to_bv 64 E)
                             (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' (Z_to_bv 64 (E + 80)))
                          F (Z_to_bv 64 0x8a0c4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra (Z_to_bv 64 7) (Z_to_bv 64 (bw_live b)) t2 a0 (Z_to_bv 64 (SHE + 80)) a2 (Z_to_bv 64 7) (Z_to_bv 64 (SHE + 80))
                         (Z_to_bv 64 3) (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 7) (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116)) s6 (Z_to_bv 64 E)
                         (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 t4 t5 (Z_to_bv 64 (E + 80)))
                      F (Z_to_bv 64 0x89fbc) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros b me m ra t2 a0 a2 s6 t3 t4 t5 OK L8 Lf ROOM EH1 EH2 AR2 MI MU WM SHe SH2 K; [lia|].
    prepW. openW EH1 EH2. unfold B0_cmp_cbWc.cbF_W, ESTATE_SIZE in MU, SHe, SH2.
    cps_destruct OK as (OKb & OKl & OKn). bz_params.
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    brun.
    flush_body b m EH2 AR2 0x8a074%Z.
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (bw_emit b) me mm ra _ _ a2 s6 _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| lia| closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| exact SHe| exact SH2|] end.
      intros b1 m' a0' t2' t3' t4' t5' Eb1 EH1' EH2' AR2' MI' MU' WM' L1 OK1 NZ1. eapply K; [| exact EH1'| exact EH2'| exact AR2'| exact MI'| exact MU'| exact WM'| exact L1| exact OK1| lia].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| lia| unfold bw_ok; lia| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_cb_finish : forall (f : nat) (b : bw) (me m : word -> option byte)
      (ra t0 t1 t2 a7 s3 s7 t3 t6 : word),
    (0 <= bw_buff b < 4294967296)%Z -> (0 < bw_live b <= 32)%Z -> (0 <= bw_numZ b)%Z -> (bw_live b <= 8 * Z.of_nat f)%Z ->
    (nblock + bw_numZ b + Z.of_nat f <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv b0segs m -> munch cbF_W me m -> wmono b0segs me m ->
    shzW b0segs cbF_W me E (E + ESTATE_SIZE) -> shzW b0segs cbF_W me A2 (A2 + ARR2_SIZE) ->
    (forall m' (a0' a7' t0' t1' t2' t3' : word),
        let b' := bs_finish f b in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv b0segs m' -> munch cbF_W me m' -> wmono b0segs me m' -> (bw_numZ b' <= bw_numZ b + Z.of_nat f)%Z ->
        evt b0segs Q (MS (RW ra t0' t1' t2' a0' (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 3) (Z_to_bv 64 (SHE + 14))
                             (Z_to_bv 64 7) (Z_to_bv 64 7) a7' s3 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 E) s7
                             (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 10)) t6)
                          F (Z_to_bv 64 0x8ac34) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 3) (Z_to_bv 64 (SHE + 14))
                         (Z_to_bv 64 7) (Z_to_bv 64 7) a7 s3 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 E) s7
                         (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 10)) t6)
                      F (Z_to_bv 64 0x8ab30) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros b me m ra t0 t1 t2 a7 s3 s7 t3 t6 OKb OKl OKn Lf ROOM EH1 EH2 AR2 MI MU WM SHe SH2 K; [lia|].
    prepW. openW EH1 EH2. unfold B0_cmp_cbWc.cbF_W, ESTATE_SIZE in MU, SHe, SH2.
    bz_params.
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    cbn [bs_finish] in K. replace (0 <? bw_live b)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
    brun.
    flush_body b m EH2 AR2 0x8abe4%Z.
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; [apply CmpMsKit2.bgtz_taken in Kc; [|lia] | apply CmpMsKit2.bgtz_not_taken in Kc; [|lia]].
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (bw_emit b) me mm ra _ _ _ _ s3 s7 _ t6); [st_eq| lia| lia| lia| lia| lia| closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| exact SHe| exact SH2|] end.
      intros m' a0' a7' t0' t1' t2' t3'. cbv zeta. intros EH1' EH2' AR2' MI' MU' WM' NZ'. eapply K; [exact EH1'| exact EH2'| exact AR2'| exact MI'| exact MU'| exact WM'| lia].
    - wstep.
      destruct f as [|f']; cbn [bs_finish] in K.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _); [st_eq| closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| lia] end.
      + replace (0 <? bw_live (bw_emit b))%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _); [st_eq| closeW1 EH1| closeW2 EH2| exact AR2| exact MI| exact MU| exact WM| lia] end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End B0CBWF.

End ACeilS1.
