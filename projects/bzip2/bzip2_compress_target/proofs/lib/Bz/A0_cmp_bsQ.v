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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
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
Import BzCSewC.BzCSewB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msW A0_cmp_bsR.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation RO := (am_RO Y). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  Notation WS1 := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P + 16, P + 104); (P + 136, P + 144); (P + 152, P + 200);
                   (P + 216, P + 384); (P + 384, P + 416)]%Z.

  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.

  Lemma A0_bs_seg1 : forall (q r : nat) (a1 a2 ft : zarr)
      (v16 v24 v32 w40 w48 w56 v64 w72 w80 w88 w96 v136 v152 v160 v168 w184 v192 v384 : word)
      (w216 w224 w232 w240 w256 w264 w272 v280 w288 v296 v304 v312 w320 w328 w336 w344 w352 w360 w368 w376 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let j0 := Z.shiftl (rd8 a2 0) 8 in
    let r1 := ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 in let a2r := fst (fst r1) in let ft1 := snd (fst r1) in
    let a2o := ms_overshoot 34 a2r qo n 0 in let ft3 := ms_accum 65536 ft1 1 in let s0 := Z.shiftl (rd8 a2o 0) 8 in
    (qo = n + Z.land n 1 + 34)%Z ->
    (Z.of_nat q = n / 4)%Z -> (Z.of_nat r = n mod 4)%Z ->
    zbok a1 -> zbok a2 -> (forall v, 0 <= v <= 65536 -> zget ft v = 0)%Z -> (forall v, 0 <= zget ft v < 4294967296)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft3 v <= n)%Z -> r2ok n (Z.to_nat n) a1 a2o ft3 (n - 1) s0 ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) ->
    rw_cells a0segs m (P + 16) [C8 v16; C8 v24; C8 v32; C8 w40; C8 w48; C8 w56; C8 v64; C8 w72; C8 w80; C8 w88; C8 w96] ->
    rw_cells a0segs m (P + 136) [C8 v136] ->
    rw_cells a0segs m (P + 152) [C8 v152; C8 v160; C8 v168; C8 (Z_to_bv 64 SHF); C8 w184; C8 v192] ->
    rw_cells a0segs m (P + 216) [C8 w216; C8 w224; C8 w232; C8 w240; C8 (Z_to_bv 64 0); C8 w256; C8 w264; C8 w272; C8 v280; C8 w288; C8 v296; C8 v304; C8 v312;
                                 C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376] ->
    rw_cells a0segs m (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] ->
    mem_inv a0segs m -> munch WS1 me m -> wmono a0segs me m ->
    shzW a0segs WS1 me A1 (A1 + ARR1_SIZE) -> shzW a0segs WS1 me A2 (A2 + ARR2_SIZE) -> shzW a0segs WS1 me FT (FT + 262144) -> shpW a0segs WS1 me FT (FT + 262148) ->
    (forall m' (SH2 : Z) (a2b ftb a1c ftc : zarr) (jb sc : Z) (y5 y6 y13 y14 y15 y16 y17 y24 : word),
      saddr A2 SH2 ->
      ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 = (a2b, ftb, jb) ->
      let a2o' := ms_overshoot 34 a2b qo n 0 in
      ms_radix2 (Z.to_nat n) a1 a2o' (ms_accum 65536 ftb 1) (n - 1) (Z.shiftl (rd8 a2o' 0) 8) = (a1c, ftc, sc) ->
      zbok a1c -> zbok a2o' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftc v <= n)%Z -> (forall k, 0 <= k < n -> zget a2o' k = zget a2 k)%Z ->
      u8arr a0segs m' A1 (zb8 a1c ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2o' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ftc 65537) ->
      rw_cells a0segs m' (P + 16) [C8 (Z_to_bv 64 (n - 1)); C8 v24; C8 v32; C8 w40; C8 w48; C8 w56; C8 v64; C8 w72; C8 w80; C8 w88; C8 w96] ->
      rw_cells a0segs m' (P + 136) [C8 (Z_to_bv 64 FB)] ->
      rw_cells a0segs m' (P + 152) [C8 v152; C8 (Z_to_bv 64 CE); C8 (Z_to_bv 64 CS); C8 (Z_to_bv 64 SHF); C8 w184; C8 v192] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ w216 w224 w232 w240 w256 w264 w272 w288 w320 w328 w336 w344 w352 w360 w368 w376)) ->
      rw_cells a0segs m' (P + 384) (scc_cells X) ->
      mem_inv a0segs m' -> munch WS1 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x984d4) (Z_to_bv 64 P) gp tp y5 y6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 BD) (Z_to_bv 64 0) (Z_to_bv 64 256) y13 y14 y15 y16 y17
                            (Z_to_bv 64 A2) cSB (Z_to_bv 64 (A2 + n)) x21 (Z_to_bv 64 SH2) (Z_to_bv 64 FT) y24 x25 x26 (Z_to_bv 64 RO) (Z_to_bv 64 A1) x29 x30 x31)
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB (Z_to_bv 64 n) x21 x22 (Z_to_bv 64 FT) (Z_to_bv 64 FB) x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97cb8) fc None m (seg_rom a0segs)).
  Proof.
    intros q r a1 a2 ft v16 v24 v32 w40 w48 w56 v64 w72 w80 w88 w96 v136 v152 v160 v168 w184 v192 v384
           w216 w224 w232 w240 w256 w264 w272 v280 w288 v296 v304 v312 w320 w328 w336 w344 w352 w360 w368 w376
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x25 x26 x27 x28 x29 x30 x31 me m.
    intros j0 r1 a2r ft1 a2o ft3 s0 HQO Hq Hr A1OK A2OK FT0 FTNN FACC FR2 AR1 AR2 FTB SL0 S136 SK0 SQ0 SC0 MI MU WM SH1 SH2r SHFz SHFp K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _). box_ors.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    (* [comment removed for export] *)
    wstep. arun_to 0x97cd0%Z.
    pose proof (saddr_intro A2) as ASH2. set (SH2 := (A2 / 8 + 2147450880)%Z) in *. clearbody SH2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. replace (FB + 32)%Z with SLO by lia. wstep.
    wstep. replace (FB + 496)%Z with SHI by lia. wstep. wstep. replace (FB + 960)%Z with SD by lia. wstep. wstep.
    (* [comment removed for export] *)
    wstep. replace (FB + 1424)%Z with RO by lia. wstep. rdblk AR2 A2OK 0%Z. wstep. wstep. wstep. wstep. wstep. wstep.
    replace (FB + 2896)%Z with CS by lia. wstep.
    (* [comment removed for export] *)
    replace (FB + 2576)%Z with BD by lia. wstep. wstep. replace (BD + 1472)%Z with CE by lia. wstep.
    wstep. rewrite zext32_id. wstep. rewrite zext32_x2. wstep. wstep. wstep. rewrite zext32_id.
    replace (n + Z.land n 1 + 34)%Z with qo by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    replace (n + -1)%Z with (n - 1)%Z in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mr := mm) in * end.
    pose proof (frdW_intro a0segs (WR X) mr _ _ SQ0 ltac:(unfold WR; cbn [disjoint_from cells_size csize length Nat.add]; lia)) as VQ.
    pose proof (frdW_intro a0segs (WR X) mr _ _ SC0 ltac:(unfold WR; cbn [disjoint_from cells_size csize length Nat.add]; lia)) as VC.
    pose proof (frdW_cell_at a0segs _ mr _ _ 32 _ (P + 248)%Z VQ eq_refl ltac:(lia)) as V248.
    pose proof (frdW_cell_at a0segs _ mr _ _ 64 _ (P + 280)%Z VQ eq_refl ltac:(lia)) as V280.
    pose proof (frdW_cell_at a0segs _ mr _ _ 16 _ (P + 400)%Z VC eq_refl ltac:(lia)) as V400.
    enter_with (A0_bs_radix X Y Q XOK XSEP SH2 ASH2 q r a1 a2 ft _ _ _ _ _ _ _ _ _ _ _ _ _ mr mr);
      [st_eq| exact Hq| exact Hr| exact A1OK| exact A2OK| exact FT0| exact FTNN| exact FACC| exact FR2| exact AR1| exact AR2| exact FTB| exact MI
      | apply munch_refl| apply wmono_refl| exact V248| exact V280| exact V400
      | eapply (shzW_sub a0segs); [exact SH1| exact MU| unfold WR; sub_fp_solve| lia| lia]
      | eapply (shzW_sub a0segs); [exact SH2r| exact MU| unfold WR; sub_fp_solve| lia| lia]
      | eapply (shzW_sub a0segs); [exact SHFz| exact MU| unfold WR; sub_fp_solve| lia| lia]
      | eapply (shpW_sub a0segs); [exact SHFp| exact MU| unfold WR; sub_fp_solve| lia| lia]|].
    intros m4 a2b ftb a1c ftc jb sc y5 y6 y13 y14 y15 y16 y17 y24 Er. cbv zeta.
    intros Eqn OK1c OKo FTCc LOWo AR1c AR2o FTBc MI4 MU4 WM4.
    clear AR1 AR2 FTB MI V248 V280 V400 VQ VC. unfold WR in MU4. transport_after_call a0segs mr m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm SH2 a2b ftb a1c ftc jb sc _ _ _ _ _ _ _ _) end;
      [st_eq| exact ASH2| exact Er| exact Eqn| exact OK1c| exact OKo| exact FTCc| exact LOWo| exact AR1c| exact AR2o| exact FTBc
      | exact SL0| exact S136| exact SK0| exact SQ0| exact SC0| exact MI4| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
