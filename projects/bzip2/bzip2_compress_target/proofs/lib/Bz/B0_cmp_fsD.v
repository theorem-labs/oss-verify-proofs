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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variables l1 r1 : Z.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - fe_A2 X)%Z.
  Notation WS := [(A1, A1 + ARR1_SIZE)]%Z.
  (* [comment removed for export] *)
  Notation QS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) (Z_to_bv 64 A2) (Z_to_bv 64 r1) (Z_to_bv 64 A1) cSB (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) (Z_to_bv 64 l1) (Z_to_bv 64 NA2) t3 t4 t5 t6).
  (* [comment removed for export] *)

  Ltac prep XOK XSEP fm ec :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & _ & _);
    let L1 := fresh "L1" in let L2 := fresh "L2" in
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1; pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
  Ltac rd_fm fm j AR1 FMOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 b0segs mm A1 fm ARR1_SIZE j _ AR1 ltac:(lia) ltac:(lia) FMOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac rd_ec ec x AR2 ECOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 b0segs mm A2 ec ARR2_SIZE x _ AR2 ltac:(lia) ltac:(lia) ECOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac st_fm fm i AR1 :=
    let SO := fresh "SO" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok b0segs mm A1 _ (4 * i) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end;
    wstep; zb8_store4 AR1 i; try clear SO.

  (* [comment removed for export] *)
  Lemma B0_fss_in4 : forall (f : nat) (j hi lo i et tmp : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t2 a0 a6 a7 t3 t4 t5 t6 : word),
    (lo <= i)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 4 <= j <= hi + 4)%Z -> (hi - j + 4 <= 4 * Z.of_nat f)%Z ->
    (0 <= et < nb)%Z -> (0 <= tmp < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m ->
    munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) -> shzW b0segs WS me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x5 x6 x7 x10 : word), let r := fss_in f fm ec et j hi 4 in
      u8arr b0segs m' A1 (zb8 (fst r) ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m' ->
      munch WS me m' -> wmono b0segs me m' -> fm_range (fst r) nb -> zbok (fst r) -> (i + 4 <= snd r <= hi + 4)%Z ->
      evt b0segs Q (MS (QS ra x5 x6 x7 x10 (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 (Z_to_bv 64 (snd r)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa5cb0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 (Z_to_bv 64 j) t2 a0 (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa5b9c) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros j hi lo i et tmp fm ec me m ra t0 t2 a0 a6 a7 t3 t4 t5 t6 Hlo Hlo0 Hhi Hj Hf Het Htmp FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM SH1 SH2 K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_in fst snd] in K.
      wstep. wstep; if_cases Kj; zify_cond_z Kj; [| exfalso; lia].
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia]. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_in_S in K.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kj; zify_cond_z Kj.
    - (* [comment removed for export] *)
      replace (j <=? hi)%Z with false in K by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd] in K.
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
    - replace (j <=? hi)%Z with true in K by (symmetry; apply Z.leb_le; lia). cbn [andb] in K.
      pose proof (proj2 FMR j ltac:(lia)) as Fj. pose proof (ECR (rd32 fm j) ltac:(lia)) as Ej.
      (* [comment removed for export] *)
      brun. rd_fm fm j AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm j)) by lia.
      (* [comment removed for export] *)
      brun. rd_ec ec (rd32 fm j) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm j))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      + replace (rd32 ec (rd32 fm j) <? et)%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
      + replace (rd32 ec (rd32 fm j) <? et)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        (* [comment removed for export] *)
        brun. st_fm fm (j - 4)%Z AR1. rewrite (unsigned_lit (rd32 fm j)) in AR1 by lia.
        (* [comment removed for export] *)
        brun_to 0xa5b9c%Z.
        enter_with (IH (j + 4)%Z hi lo i et tmp (wr32 fm (j - 4) (rd32 fm j)) ec me);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact K].
        apply fm_range_wr32; [exact FMR| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_fss_out4 : forall (r : nat) (i hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 t5 t6 : word),
    (i - lo + 1 = Z.of_nat r)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 4 <= hi)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m ->
    munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) -> shzW b0segs WS me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x5 x6 x7 x10 x11 x12 x13 x17 : word), let fm' := fss_outer r fm ec i hi 4 in
      u8arr b0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m' ->
      munch WS me m' -> wmono b0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt b0segs Q (MS (QS ra x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa5d40) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 i) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa5adc) fc None m (seg_rom b0segs)).
  Proof.
    induction r as [|r IH]; intros i hi lo fm ec me m ra t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 t5 t6 Hr Hlo Hhi Hi FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM SH1 SH2 K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_outer] in K.
      wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK']. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_outer_S' in K. unfold fss_iter in K.
    pose proof (proj2 FMR i ltac:(lia)) as Fi. pose proof (ECR (rd32 fm i) ltac:(lia)) as Ei.
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    (* [comment removed for export] *)
    brun. rd_fm fm i AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm i)) by lia.
    (* [comment removed for export] *)
    brun. rd_ec ec (rd32 fm i) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm i))) by lia.
    enter_with (B0_fss_in4 (S (Z.to_nat (hi - i))) (i + 4)%Z hi lo i (rd32 ec (rd32 fm i)) (rd32 fm i) fm ec me);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact SH1| exact SH2|].
    intros m' x5 x6 x7 x10. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK'' Hjf.
    destruct (fss_in (S (Z.to_nat (hi - i))) fm ec (rd32 ec (rd32 fm i)) (i + 4) hi 4) as [fm1 jf] eqn:Efi. cbn [fst snd] in *.
    clear AR1 AR2 MI MU WM. rename MI' into MI. bz_params.
    pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
    (* [comment removed for export] *)
    brun. st_fm fm1 (jf - 4)%Z AR1'. rewrite (unsigned_lit (rd32 fm i)) in AR1' by lia.
    (* [comment removed for export] *)
    brun_to 0xa5adc%Z.
    enter_with (IH (i - 1)%Z hi lo (wr32 fm1 (jf - 4) (rd32 fm i)) ec me);
      [st_eq| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK''| exact ECOK'| exact AR1'| exact AR2'| exact MI| exact MU'| exact WM'| exact SH1| exact SH2| exact K].
    apply fm_range_wr32; [exact FMR'| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_fss_in1 : forall (f : nat) (j hi lo i et tmp : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t2 a0 a6 a7 t3 t4 t5 t6 : word),
    (lo <= i)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 1 <= j <= hi + 1)%Z -> (hi - j + 1 <= Z.of_nat f)%Z ->
    (0 <= et < nb)%Z -> (0 <= tmp < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m ->
    munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) -> shzW b0segs WS me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x5 x6 x7 x10 : word), let r := fss_in f fm ec et j hi 1 in
      u8arr b0segs m' A1 (zb8 (fst r) ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m' ->
      munch WS me m' -> wmono b0segs me m' -> fm_range (fst r) nb -> zbok (fst r) -> (i + 1 <= snd r <= hi + 1)%Z ->
      evt b0segs Q (MS (QS ra x5 x6 x7 x10 (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 (Z_to_bv 64 (snd r)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa5f10) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 (Z_to_bv 64 j) t2 a0 (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa5e0c) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros j hi lo i et tmp fm ec me m ra t0 t2 a0 a6 a7 t3 t4 t5 t6 Hlo Hlo0 Hhi Hj Hf Het Htmp FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM SH1 SH2 K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_in fst snd] in K.
      wstep. wstep; if_cases Kj; zify_cond_z Kj; [| exfalso; lia].
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia]. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_in_S in K.
    wstep. wstep; if_cases Kj; zify_cond_z Kj.
    - replace (j <=? hi)%Z with false in K by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd] in K.
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
    - replace (j <=? hi)%Z with true in K by (symmetry; apply Z.leb_le; lia). cbn [andb] in K.
      pose proof (proj2 FMR j ltac:(lia)) as Fj. pose proof (ECR (rd32 fm j) ltac:(lia)) as Ej.
      brun. rd_fm fm j AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm j)) by lia.
      brun. rd_ec ec (rd32 fm j) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm j))) by lia.
      wstep; if_cases Kc; zify_cond_z Kc.
      + replace (rd32 ec (rd32 fm j) <? et)%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
      + replace (rd32 ec (rd32 fm j) <? et)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        brun. st_fm fm (j - 1)%Z AR1. rewrite (unsigned_lit (rd32 fm j)) in AR1 by lia.
        brun_to 0xa5e0c%Z.
        enter_with (IH (j + 1)%Z hi lo i et tmp (wr32 fm (j - 1) (rd32 fm j)) ec me);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact K].
        apply fm_range_wr32; [exact FMR| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_fss_out1 : forall (r : nat) (i hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 t5 t6 : word),
    (i - lo + 1 = Z.of_nat r)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 1 <= hi)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m ->
    munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) -> shzW b0segs WS me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x5 x6 x7 x10 x11 x12 x13 x17 : word), let fm' := fss_outer r fm ec i hi 1 in
      u8arr b0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m' ->
      munch WS me m' -> wmono b0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt b0segs Q (MS (QS ra x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa5ac0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 i) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa5d4c) fc None m (seg_rom b0segs)).
  Proof.
    induction r as [|r IH]; intros i hi lo fm ec me m ra t0 t1 t2 a0 a1 a2 a6 a7 t3 t4 t5 t6 Hr Hlo Hhi Hi FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM SH1 SH2 K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_outer] in K.
      wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK']. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_outer_S' in K. unfold fss_iter in K.
    pose proof (proj2 FMR i ltac:(lia)) as Fi. pose proof (ECR (rd32 fm i) ltac:(lia)) as Ei.
    wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    brun. rd_fm fm i AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm i)) by lia.
    brun. rd_ec ec (rd32 fm i) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm i))) by lia.
    enter_with (B0_fss_in1 (S (Z.to_nat (hi - i))) (i + 1)%Z hi lo i (rd32 ec (rd32 fm i)) (rd32 fm i) fm ec me);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact SH1| exact SH2|].
    intros m' x5 x6 x7 x10. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK'' Hjf.
    destruct (fss_in (S (Z.to_nat (hi - i))) fm ec (rd32 ec (rd32 fm i)) (i + 1) hi 1) as [fm1 jf] eqn:Efi. cbn [fst snd] in *.
    clear AR1 AR2 MI MU WM. rename MI' into MI. bz_params.
    pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
    brun. st_fm fm1 (jf - 1)%Z AR1'. rewrite (unsigned_lit (rd32 fm i)) in AR1' by lia.
    brun_to 0xa5d4c%Z.
    enter_with (IH (i - 1)%Z hi lo (wr32 fm1 (jf - 1) (rd32 fm i)) ec me);
      [st_eq| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK''| exact ECOK'| exact AR1'| exact AR2'| exact MI| exact MU'| exact WM'| exact SH1| exact SH2| exact K].
    apply fm_range_wr32; [exact FMR'| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_fss : forall (hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a0 a1 a3 a6 a7 t3 t4 t5 t6 : word),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo - 1 <= hi)%Z -> (hi - lo < 10)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m ->
    munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) -> shzW b0segs WS me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x5 x6 x7 x10 x11 x12 x13 x17 : word), let fm' := fallbackSimpleSort fm ec lo hi in
      u8arr b0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m' ->
      munch WS me m' -> wmono b0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt b0segs Q (MS (QS ra x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa5ac0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 (Z_to_bv 64 (hi - lo)) a3 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa5abc) fc None m (seg_rom b0segs)).
  Proof.
    intros hi lo fm ec me m ra t0 t1 t2 a0 a1 a3 a6 a7 t3 t4 t5 t6 Hlo Hhi Hlh Hsm FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM SH1 SH2 K; cbv zeta in K.
    prep XOK XSEP fm ec. bz_params. unfold fallbackSimpleSort in K.
    (* [comment removed for export] *)
    wstep; if_cases K0; zify_cond_z K0.
    2:{ replace (lo =? hi)%Z with true in K by (symmetry; apply Z.eqb_eq; lia).
        enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK']. }
    replace (lo =? hi)%Z with false in K by (symmetry; apply Z.eqb_neq; lia).
    assert (P2 : forall m1 fm1 (y5 y6 y7 y10 y11 y12 y13 y17 : word),
      u8arr b0segs m1 A1 (zb8 fm1 ARR1_SIZE) -> u8arr b0segs m1 A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m1 ->
      munch WS me m1 -> wmono b0segs me m1 -> fm_range fm1 nb -> zbok fm1 ->
      (forall m' (x5 x6 x7 x10 x11 x12 x13 x17 : word), let fm' := fss_outer (Z.to_nat (hi - 1 - lo + 1)) fm1 ec (hi - 1) hi 1 in
        u8arr b0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m' ->
        munch WS me m' -> wmono b0segs me m' -> fm_range fm' nb -> zbok fm' ->
        evt b0segs Q (MS (QS ra x5 x6 x7 x10 x11 x12 x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 x17 t3 t4 t5 t6)
                         F (Z_to_bv 64 0xa5ac0) fc None m' (seg_rom b0segs))) ->
      evt b0segs Q (MS (QS ra y5 y6 y7 y10 y11 y12 y13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a6 y17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa5d40) fc None m1 (seg_rom b0segs))).
    { intros m1 fm1 y5 y6 y7 y10 y11 y12 y13 y17 AR1' AR2' MI' MU' WM' FMR' FMOK'' KK. cbv zeta in KK.
      pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
      (* [comment removed for export] *)
      brun_to 0xa5d4c%Z.
      destruct (Z_lt_le_dec hi lo) as [Hhl|Hhl].
      - (* [comment removed for export] *)
        replace (Z.to_nat (hi - 1 - lo + 1)) with 0%nat in KK by lia. cbn [fss_outer] in KK.
        wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
        enter_with (KK m1 _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''].
      - enter_with (B0_fss_out1 (Z.to_nat (hi - 1 - lo + 1)) (hi - 1)%Z hi lo fm1 ec me m1);
          [st_eq| lia| lia| lia| lia| exact FMR'| exact ECR| exact FMOK''| exact ECOK'| exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact SH1| exact SH2|].
        intros m' x5 x6 x7 x10 x11 x12 x13 x17. exact (KK m' x5 x6 x7 x10 x11 x12 x13 x17). }
    (* [comment removed for export] *)
    wstep. wstep; if_cases K4; zify_cond_z K4.
    - replace (3 <? hi - lo)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
      eapply (P2 m fm); [exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| exact K].
    - replace (3 <? hi - lo)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      brun_to 0xa5adc%Z.
      enter_with (B0_fss_out4 (Z.to_nat (hi - 4 - lo + 1)) (hi - 4)%Z hi lo fm ec me m);
        [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact SH1| exact SH2|].
      intros m' x5 x6 x7 x10 x11 x12 x13 x17. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK''.
      eapply (P2 m' _); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact K].
  Qed.
End B0FS.
End ACeilS1.
