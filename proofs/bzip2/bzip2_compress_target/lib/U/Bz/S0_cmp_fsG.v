(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0 S0_cmp_fsD.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0 S0_cmp_fsD.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsF UKit.
Module S0_cmp_fsE.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop. Variables Hh qsp l1 r1 l8 : Z.
  Variables (str sv : word) (nnd rr : Z).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation QR ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 (Z_to_bv 64 (qsp - 1)) a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 r1) (Z_to_bv 64 (-1)) (Z_to_bv 64 qsp) (Z_to_bv 64 l1) (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).
  Notation WP := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (bv_unsigned (fe_sp X) - 3056 + 64, bv_unsigned (fe_sp X) - 3056 + 72)]%Z.
  Notation SC tv := (SCq X Hh str sv nnd rr tv).

  Ltac prep XOK XSEP fm ec :=
    fsenv_open XOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & _ & _);
    let L1 := fresh "L1" in let L2 := fresh "L2" in
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1; pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
  Ltac rd_fm fm j AR1 FMOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 s0segs mm A1 fm ARR1_SIZE j _ AR1 ltac:(lia) ltac:(lia) FMOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac rd_ec ec x AR2 ECOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 s0segs mm A2 ec ARR2_SIZE x _ AR2 ltac:(lia) ltac:(lia) ECOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac st_fm fm i AR1 :=
    let SO := fresh "SO" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok s0segs mm A1 _ (4 * i) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end;
    wstep; zb8_store4 AR1 i; try clear SO.
  Ltac key_left i :=
    try lazymatch goal with |- context [Z_to_bv 64 (?x + fe_A1 X)] => replace (x + fe_A1 X)%Z with (fe_A1 X + 4 * i)%Z by lia end.

  (* [comment removed for export] *)
  Lemma S0_plo : forall (f : nat) (u unHi ltLo gtHi med hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 a3 a4 t5 t6 : word),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo <= ltLo <= u)%Z -> (u <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (unHi - u + 2 <= Z.of_nat f)%Z ->
    (0 <= med < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> rw_cells s0segs m (p + 8) (SC ltLo) -> mem_inv s0segs m ->
    munch WP me m -> wmono s0segs me m ->
    (forall m' (x1 x5 x7 x28 x29 x30 x31 : word), let p' := fpart_lo f ec med (FP fm u unHi ltLo gtHi) in
      u8arr s0segs m' A1 (zb8 (fp_fm p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> rw_cells s0segs m' (p + 8) (SC (fp_ltLo p')) -> mem_inv s0segs m' ->
      munch WP me m' -> wmono s0segs me m' -> fm_range (fp_fm p') nb -> zbok (fp_fm p') ->
      fp_unHi p' = unHi -> fp_gtHi p' = gtHi -> (ltLo <= fp_ltLo p' <= fp_unLo p')%Z -> (u <= fp_unLo p' <= unHi + 1)%Z ->
      evt s0segs Q (MS (QR x1 x5 (Z_to_bv 64 med) x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 (fp_unLo p')) (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x22ecc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 (Z_to_bv 64 med) (Z_to_bv 64 u) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 u) (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 (A1 + 4 * u)) (Z_to_bv 64 (A1 + 4 * u)) t5 t6)
                     F (Z_to_bv 64 0x22de0) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros u unHi ltLo gtHi med hi lo fm ec me m ra t0 a3 a4 t5 t6 Hlo Hhi Hlt Hu Hg Hf Hmed FMR ECR FMOK' ECOK' AR1 AR2 SC MI MU WM K; cbv zeta in K; [lia|].
    prep XOK XSEP fm ec. bz_params. unfold SCq in SC, K.
    rewrite fpart_lo_S in K. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
    replace (unHi <? u)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
    pose proof (proj2 FMR u ltac:(lia)) as Fu. pose proof (ECR (rd32 fm u) ltac:(lia)) as Eu. pose proof (proj2 FMR ltLo ltac:(lia)) as Fl.
    (* [comment removed for export] *)
    urun_to 0x22e00%Z. rd_fm fm u AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm u)) by lia.
    urun_to 0x22e2c%Z. rd_ec ec (rd32 fm u) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm u))) by lia.
    (* [comment removed for export] *)
    urun_to 0x22e3c%Z. wstep; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      replace (rd32 ec (rd32 fm u) - med =? 0)%Z with true in K by (symmetry; apply Z.eqb_eq; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
      (* [comment removed for export] *)
      urun_to 0x22e8c%Z. key_left ltLo. rd_fm fm ltLo AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm ltLo)) by lia.
      (* [comment removed for export] *)
      st_fm fm u AR1. rewrite (unsigned_lit (rd32 fm ltLo)) in AR1 by lia.
      (* [comment removed for export] *)
      pose proof (zb8_length (wr32 fm u (rd32 fm ltLo)) ARR1_SIZE ltac:(lia)) as L1'.
      urun_to 0x22ea0%Z. st_fm (wr32 fm u (rd32 fm ltLo)) ltLo AR1. rewrite (unsigned_lit (rd32 fm u)) in AR1 by lia.
      change (wr32 (wr32 fm u (rd32 fm ltLo)) ltLo (rd32 fm u)) with (fswap fm u ltLo) in AR1.
      assert (FMR1 : fm_range (fswap fm u ltLo) nb) by (apply fswap_range; [exact FMR| lia| lia]).
      (* [comment removed for export] *)
      urun_to 0x22ebc%Z. wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        urun_to 0x22de0%Z.
        enter_with (IH (u + 1)%Z unHi (ltLo + 1)%Z gtHi med hi lo (fswap fm u ltLo) ec me);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR1| exact ECR| unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK'| exact ECOK'| exact AR1| exact AR2| unfold SCq; exact SC| exact MI| exact MU| exact WM|].
        intros m' x1 x5 x7 x28 x29 x30 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK'' E1 E2 R1 R2.
        eapply (K m' x1 x5 x7 x28 x29 x30 x31); [exact AR1'| exact AR2'| unfold SCq in SC'; exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact E1| exact E2| lia| lia].
      + (* [comment removed for export] *)
        urun_to 0x22ecc%Z.
        rewrite fpart_lo_stop in K by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
        enter_with (K _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK'| reflexivity| reflexivity| lia| lia].
    - replace (rd32 ec (rd32 fm u) - med =? 0)%Z with false in K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kp; zify_cond_z Kp.
      + (* [comment removed for export] *)
        replace (0 <? rd32 ec (rd32 fm u) - med)%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
        enter_with (K m _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| reflexivity| reflexivity| lia| lia].
      + (* [comment removed for export] *)
        replace (0 <? rd32 ec (rd32 fm u) - med)%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
        (* [comment removed for export] *)
        urun_to 0x22e5c%Z. wstep; if_cases Kc; zify_cond_z Kc.
        * enter_with (IH (u + 1)%Z unHi ltLo gtHi med hi lo fm ec me);
            [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| unfold SCq; exact SC| exact MI| exact MU| exact WM|].
          intros m' x1 x5 x7 x28 x29 x30 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK'' E1 E2 R1 R2.
          eapply (K m' x1 x5 x7 x28 x29 x30 x31); [exact AR1'| exact AR2'| unfold SCq in SC'; exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact E1| exact E2| lia| lia].
        * (* [comment removed for export] *)
          urun_to 0x22ecc%Z.
          rewrite fpart_lo_stop in K by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
          enter_with (K m _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| reflexivity| reflexivity| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Definition KB978 (hi lo med : Z) (ec : zarr) (me : word -> option byte) (a3 a4 : word) (pf : fpart) : Prop :=
    forall m' (x1 x5 x7 x28 x29 x30 x31 : word),
      u8arr s0segs m' A1 (zb8 (fp_fm pf) ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> rw_cells s0segs m' (p + 8) (SC (fp_ltLo pf)) -> mem_inv s0segs m' ->
      munch WP me m' -> wmono s0segs me m' -> fm_range (fp_fm pf) nb -> zbok (fp_fm pf) ->
      fp_ok lo hi pf -> (fp_unHi pf < fp_unLo pf)%Z ->
      evt s0segs Q (MS (QR x1 x5 (Z_to_bv 64 med) x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 (fp_unLo pf)) (Z_to_bv 64 (fp_unHi pf)) (Z_to_bv 64 (fp_gtHi pf)) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x22ff8) fc None m' (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition KC864 (hi lo med : Z) (ec : zarr) (me : word -> option byte) (a3 a4 : word) (sz f' : nat) (pf : fpart) : Prop :=
    forall (p3 : fpart) m' (x1 x5 x15 x28 x29 x30 x31 : word),
      fp_ok lo hi p3 -> (fp_unHi p3 - fp_unLo p3 + 2 <= 2 * Z.of_nat f')%Z ->
      fpart_loop f' sz ec med p3 = pf ->
      u8arr s0segs m' A1 (zb8 (fp_fm p3) ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> rw_cells s0segs m' (p + 8) (SC (fp_ltLo p3)) -> mem_inv s0segs m' ->
      munch WP me m' -> wmono s0segs me m' -> fm_range (fp_fm p3) nb -> zbok (fp_fm p3) ->
      evt s0segs Q (MS (QR x1 x5 (Z_to_bv 64 med) (Z_to_bv 64 (fp_unLo p3)) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 x15 (Z_to_bv 64 (fp_unHi p3)) (Z_to_bv 64 (fp_gtHi p3)) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x22db8) fc None m' (seg_rom s0segs)).

  (* [comment removed for export] *)
  Lemma S0_phi : forall (f : nat) (uh unLo ltLo g med hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 a3 a4 t5 t6 : word) (sz f' : nat) (pf : fpart),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= uh)%Z -> (uh <= g <= hi)%Z -> (uh - unLo + 2 <= Z.of_nat f)%Z ->
    (hi - lo + 1 = Z.of_nat sz)%Z -> (uh - unLo <= 2 * Z.of_nat f')%Z ->
    (0 <= med < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec -> (med < rd32 ec (rd32 fm unLo))%Z ->
    (let p2 := fpart_hi f ec med (FP fm unLo uh ltLo g) in
     (if (fp_unHi p2 <? fp_unLo p2)%Z then p2
      else fpart_loop f' sz ec med (FP (fswap (fp_fm p2) (fp_unLo p2) (fp_unHi p2)) (fp_unLo p2 + 1) (fp_unHi p2 - 1) (fp_ltLo p2) (fp_gtHi p2))) = pf) ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> rw_cells s0segs m (p + 8) (SC ltLo) -> mem_inv s0segs m ->
    munch WP me m -> wmono s0segs me m ->
    KB978 hi lo med ec me a3 a4 pf -> KC864 hi lo med ec me a3 a4 sz f' pf ->
    evt s0segs Q (MS (QR ra t0 (Z_to_bv 64 med) (Z_to_bv 64 (A1 + 4 * uh)) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 unLo) (Z_to_bv 64 uh) (Z_to_bv 64 g) (Z_to_bv 64 uh) (Z_to_bv 64 (A1 + 4 * uh)) t5 t6)
                     F (Z_to_bv 64 0x22ee4) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros uh unLo ltLo g med hi lo fm ec me m ra t0 a3 a4 t5 t6 sz f' pf Hlo Hhi Hlt Hu Hg Hf Hsz Hf' Hmed FMR ECR FMOK' ECOK' HNP RES AR1 AR2 SC MI MU WM KB KC; cbv zeta in RES; [lia|].
    prep XOK XSEP fm ec. bz_params. unfold KB978, KC864 in KB, KC. bz_params. unfold SCq in SC, KB, KC.
    rewrite fpart_hi_S in RES. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
    replace (uh <? unLo)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia).
    pose proof (proj2 FMR uh ltac:(lia)) as Fu. pose proof (ECR (rd32 fm uh) ltac:(lia)) as Eu.
    pose proof (proj2 FMR g ltac:(lia)) as Fg. pose proof (proj2 FMR unLo ltac:(lia)) as Fl.
    (* [comment removed for export] *)
    urun_to 0x22f04%Z. rd_fm fm uh AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm uh)) by lia.
    urun_to 0x22f30%Z. rd_ec ec (rd32 fm uh) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm uh))) by lia.
    (* [comment removed for export] *)
    urun_to 0x22f40%Z. wstep; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      replace (rd32 ec (rd32 fm uh) - med =? 0)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia). cbv iota in RES.
      assert (Hne : uh <> unLo) by (intros E; rewrite E in K0; lia).
      assert (HNP1 : (med < rd32 ec (rd32 (fswap fm uh g) unLo))%Z) by (rewrite rd32_fswap_other by lia; exact HNP).
      (* [comment removed for export] *)
      urun_to 0x22f88%Z. key_left g. rd_fm fm g AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm g)) by lia.
      (* [comment removed for export] *)
      st_fm fm uh AR1. rewrite (unsigned_lit (rd32 fm g)) in AR1 by lia.
      pose proof (zb8_length (wr32 fm uh (rd32 fm g)) ARR1_SIZE ltac:(lia)) as L1'.
      urun_to 0x22f98%Z. st_fm (wr32 fm uh (rd32 fm g)) g AR1. rewrite (unsigned_lit (rd32 fm uh)) in AR1 by lia.
      change (wr32 (wr32 fm uh (rd32 fm g)) g (rd32 fm uh)) with (fswap fm uh g) in AR1.
      assert (FMR1 : fm_range (fswap fm uh g) nb) by (apply fswap_range; [exact FMR| lia| lia]).
      assert (FMOK1 : zbok (fswap fm uh g)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
      (* [comment removed for export] *)
      urun_to 0x22fac%Z. wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        urun_to 0x22ee4%Z.
        enter_with (IH (uh - 1)%Z unLo ltLo (g - 1)%Z med hi lo (fswap fm uh g) ec me _ _ _ a3 a4 _ _ sz f' pf);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact FMR1| exact ECR| exact FMOK1| exact ECOK'| exact HNP1| exact RES| exact AR1| exact AR2| unfold SCq; exact SC| exact MI| exact MU| exact WM| exact KB| exact KC].
      + (* [comment removed for export] *)
        urun_to 0x22ff8%Z.
        rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
        replace (uh - 1 <? unLo)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
        enter_with (KB _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| exact FMOK1| unfold fp_ok; cbn; lia| cbn; lia].
    - replace (rd32 ec (rd32 fm uh) - med =? 0)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia). cbv iota in RES.
      (* [comment removed for export] *)
      destruct (Z.ltb_spec (rd32 ec (rd32 fm uh) - med) 0) as [Kn|Kn].
      + (* [comment removed for export] *)
        wstep; notrap.
        replace (rd32 ec (rd32 fm uh) - med <? 0)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbv iota in RES.
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
        assert (Hne : uh <> unLo) by (intros E; rewrite E in Kn; lia).
        replace (uh <? unLo)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia).
        (* [comment removed for export] *)
        urun_to 0x22fd4%Z. rd_fm fm unLo AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm unLo)) by lia.
        (* [comment removed for export] *)
        st_fm fm unLo AR1. rewrite (unsigned_lit (rd32 fm uh)) in AR1 by lia.
        pose proof (zb8_length (wr32 fm unLo (rd32 fm uh)) ARR1_SIZE ltac:(lia)) as L1'.
        urun_to 0x22fe0%Z. st_fm (wr32 fm unLo (rd32 fm uh)) uh AR1. rewrite (unsigned_lit (rd32 fm unLo)) in AR1 by lia.
        change (wr32 (wr32 fm unLo (rd32 fm uh)) uh (rd32 fm unLo)) with (fswap fm unLo uh) in AR1.
        assert (FMR1 : fm_range (fswap fm unLo uh) nb) by (apply fswap_range; [exact FMR| lia| lia]).
        assert (FMOK1 : zbok (fswap fm unLo uh)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
        (* [comment removed for export] *)
        urun_to 0x22db8%Z.
        enter_with (KC (FP (fswap fm unLo uh) (unLo + 1) (uh - 1) ltLo g) _ _ _ _ _ _ _ _);
          [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| unfold fp_ok; cbn; lia| cbn; lia| exact RES| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| exact FMOK1].
      + (* [comment removed for export] *)
        wstep; notrap.
        replace (rd32 ec (rd32 fm uh) - med <? 0)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). cbv iota in RES.
        (* [comment removed for export] *)
        urun_to 0x22f60%Z. wstep; if_cases Kc; zify_cond_z Kc.
        * enter_with (IH (uh - 1)%Z unLo ltLo g med hi lo fm ec me m _ _ a3 a4 _ _ sz f' pf);
            [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact HNP| exact RES| exact AR1| exact AR2| unfold SCq; exact SC| exact MI| exact MU| exact WM| exact KB| exact KC].
        * (* [comment removed for export] *)
          urun_to 0x22ff8%Z.
          rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
          replace (uh - 1 <? unLo)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
          enter_with (KB _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| unfold fp_ok; cbn; lia| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_ploop : forall (f' : nat) (pp : fpart) (med hi lo : Z) (ec : zarr) (me m : word -> option byte) (ra t0 a3 a4 a5 t3 t4 t5 t6 : word) (sz : nat) (pf : fpart),
    (0 <= lo)%Z -> (hi < nb)%Z -> fp_ok lo hi pp -> (hi - lo + 1 = Z.of_nat sz)%Z ->
    (fp_unHi pp - fp_unLo pp + 2 <= 2 * Z.of_nat f')%Z -> fpart_loop f' sz ec med pp = pf ->
    (0 <= med < nb)%Z -> fm_range (fp_fm pp) nb -> ec_range ec nb -> zbok (fp_fm pp) -> zbok ec ->
    u8arr s0segs m A1 (zb8 (fp_fm pp) ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> rw_cells s0segs m (p + 8) (SC (fp_ltLo pp)) -> mem_inv s0segs m ->
    munch WP me m -> wmono s0segs me m ->
    KB978 hi lo med ec me a3 a4 pf ->
    evt s0segs Q (MS (QR ra t0 (Z_to_bv 64 med) (Z_to_bv 64 (fp_unLo pp)) (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 a5 (Z_to_bv 64 (fp_unHi pp)) (Z_to_bv 64 (fp_gtHi pp)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22db8) fc None m (seg_rom s0segs)).
  Proof.
    induction f' as [|f' IH]; intros pp med hi lo ec me m ra t0 a3 a4 a5 t3 t4 t5 t6 sz pf Hlo Hhi OK Hsz Hf RES Hmed FMR ECR FMOK' ECOK' AR1 AR2 SC MI MU WM KB; [unfold fp_ok in OK; lia|].
    destruct pp as [fm unLo unHi ltLo gtHi]. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *. unfold fp_ok in OK. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in OK.
    prep XOK XSEP fm ec. bz_params. pose proof KB as KB'. unfold KB978 in KB'. unfold SCq in SC, KB'.
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd.
    - rewrite fpart_loop_S in RES. cbv zeta in RES.
      urun_to 0x22de0%Z.
      enter_with (S0_plo (S sz) unLo unHi ltLo gtHi med hi lo fm ec me _ _ _ a3 a4 _ _);
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| unfold SCq; exact SC| exact MI| exact MU| exact WM|].
      intros m' x1 x5 x7 x28 x29 x30 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK2 E1 E2 R1 R2.
      remember (fpart_lo (S sz) ec med (FP fm unLo unHi ltLo gtHi)) as p1 eqn:Ep1.
      destruct p1 as [fm1 unLo1 unHi1 ltLo1 gtHi1]. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *. subst unHi1 gtHi1.
      clear AR1 AR2 SC MI MU WM. bz_params. unfold SCq in SC'.
      pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      + (* [comment removed for export] *)
        rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
        replace (unHi <? unLo1)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
        enter_with (KB' _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1'| exact AR2'| exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK2| unfold fp_ok; cbn; lia| cbn; lia].
      + pose proof (fpart_lo_exit (S sz) ec med (FP fm unLo unHi ltLo gtHi) ltac:(cbn; lia)) as HNP.
        rewrite <- Ep1 in HNP. cbn [fp_fm fp_unLo fp_unHi] in HNP. destruct HNP as [HNP|HNP]; [lia|].
        (* [comment removed for export] *)
        urun_to 0x22ee4%Z.
        enter_with (S0_phi (S sz) unHi unLo1 ltLo1 gtHi med hi lo fm1 ec me m' _ _ a3 a4 _ _ sz f' pf);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact FMR'| exact ECR| exact FMOK2| exact ECOK'| exact HNP| exact RES| exact AR1'| exact AR2'| unfold SCq; exact SC'| exact MI'| exact MU'| exact WM'| exact KB|].
        (* [comment removed for export] *)
        unfold KC864. intros p3 m'' y1 y5 y15 y28 y29 y30 y31 H2 H3 H4 AR1'' AR2'' SC'' MI'' MU'' WM'' FMR'' FMOK3.
        eapply (IH p3 med hi lo ec me m'' _ _ a3 a4 _ _ _ _ _ sz pf); try eassumption; try lia.
    - rewrite fpart_loop_stop in RES by (cbn; lia). subst pf.
      urun_to 0x22ecc%Z. wstep; notrap.
      enter_with (KB' _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| unfold fp_ok; cbn; lia| cbn; lia].
  Qed.
End S0FS.

End ACeilS1.
End S0_cmp_fsE.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsG.S0_cmp_fsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Lemma med_idx_eq : forall ec fm r3 lo hi,
  (if r3 =? 0 then rd32 ec (rd32 fm lo) else if r3 =? 1 then rd32 ec (rd32 fm (Z.shiftr (lo + hi) 1)) else rd32 ec (rd32 fm hi))%Z
  = rd32 ec (rd32 fm (med_idx r3 lo hi)).
Proof.
  intros. unfold med_idx. destruct (r3 =? 0)%Z; [reflexivity|]. destruct (r3 =? 1)%Z; [|reflexivity].
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma fqs_iter_unfold : forall ec fm sp slo shi rr,
  fqs_iter ec (FQS fm sp slo shi rr) =
  (let lo := zget slo (sp - 1) in let hi := zget shi (sp - 1) in
   if (hi - lo <? 10)%Z then FQS (fallbackSimpleSort fm ec lo hi) (sp - 1) slo shi rr
   else let r' := (((rr * 7621) + 1) mod 32768)%Z in
        let med := rd32 ec (rd32 fm (med_idx (r' mod 3) lo hi)) in
        let sz := Z.to_nat (hi - lo + 1) in
        qtail sp lo hi r' slo shi (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi))).
Proof.
  intros. unfold fqs_iter, qtail. cbn [fq_fm fq_sp fq_slo fq_shi fq_r]. rewrite <- med_idx_eq. reflexivity.
Qed.

Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop. Variables Hh l1 r1 l8 : Z.
  Variables (str sv : word) (nnd : Z) (ec : zarr) (Jlo Jhi : list byte).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Hypothesis ECR : ec_range ec nb. Hypothesis ECOK' : zbok ec.
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  (* [comment removed for export] *)
  Notation QL ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 r1) (Z_to_bv 64 (-1)) s7 (Z_to_bv 64 l1)
         (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).
  Notation Wq := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (bv_unsigned (fe_sp X) - 3056 + 56, bv_unsigned (fe_sp X) - 3056 + 72);
                  (bv_unsigned (fe_sp X) - 3056 + 2152, bv_unsigned (fe_sp X) - 3056 + 2952)]%Z.

  Lemma S0_qloop : forall (f : nat) (q qfin : fqs) (tv : Z) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    (0 < fq_sp q)%Z -> (0 <= fq_r q < 32768)%Z -> fm_range (fq_fm q) nb -> zbok (fq_fm q) -> stk_def (fq_slo q) (fq_shi q) (fq_sp q) ->
    (forall v, qfacts nb (fqs_loop v ec q)) -> fqs_loop f ec q = qfin -> (fq_sp qfin <= 0)%Z ->
    u8arr s0segs m A1 (zb8 (fq_fm q) ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) ->
    rw_cells s0segs m (p + 8) (SCq X Hh str sv nnd (fq_r q) tv) ->
    u32arr s0segs m (p + 2152) (ovw (fq_shi q) Jhi 100) -> u32arr s0segs m (p + 2552) (ovw (fq_slo q) Jlo 100) -> mem_inv s0segs m ->
    munch Wq me m -> wmono s0segs me m ->
    (forall m' (tv' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
      u8arr s0segs m' A1 (zb8 (fq_fm qfin) ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells s0segs m' (p + 8) (SCq X Hh str sv nnd (fq_r qfin) tv') ->
      u32arr s0segs m' (p + 2152) (ovw (fq_shi qfin) Jhi 100) -> u32arr s0segs m' (p + 2552) (ovw (fq_slo qfin) Jlo 100) -> mem_inv s0segs m' ->
      munch Wq me m' -> wmono s0segs me m' -> fm_range (fq_fm qfin) nb -> zbok (fq_fm qfin) -> (0 <= fq_r qfin < 32768)%Z ->
      evt s0segs Q (MS (QL x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31) F (Z_to_bv 64 0x23380) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QL ra t0 t1 t2 a0 a1 (Z_to_bv 64 (fq_sp q)) a3 a4 a5 a6 a7 s7 t3 t4 t5 t6) F (Z_to_bv 64 0x22988) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros q qfin tv me m ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 Hsp Hr FMR FMOK' SD QF RES FIN AR1 AR2 SC SHI SLO MI MU WM K.
    { cbn [fqs_loop] in RES. subst qfin. lia. }
    rewrite fqs_loop_S in RES. replace (0 <? fq_sp q)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia).
    cps_pose (QF 0%nat ltac:(cbn; lia)) as (Hsp98 & Glo0 & Glh & Ghi). cbn [fqs_loop] in Hsp98, Glo0, Glh, Ghi.
    assert (QF' : forall v, qfacts nb (fqs_loop v ec (fqs_iter ec q))).
    { intros v. specialize (QF (S v)). rewrite fqs_loop_S in QF. replace (0 <? fq_sp q)%Z with true in QF by (symmetry; apply Z.ltb_lt; lia). exact QF. }
    clear QF. destruct q as [fm sp slo shi rr]. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in *.
    set (lo := zget slo (sp - 1)) in *. set (hi := zget shi (sp - 1)) in *.
    fsenv_open XOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F).
    bz_params. pose proof SC as SC0. unfold SCq in SC.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length shi Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length slo Jlo 100 ltac:(lia)) as LL.
    destruct (SD (sp - 1)%Z ltac:(lia)) as [Dlo Dhi].
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    (* [comment removed for export] *)
    urun_to 0x229d4%Z.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (p + 2552) slo Jlo 100 (sp - 1) _ SLO ltac:(lia) Dlo ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold lo. try rewrite (sx32_of_Z_signed lo) by lia. try rewrite (sx32_of_Z lo) by lia.
    pose proof (ovw_read s0segs m (p + 2152) shi Jhi 100 (sp - 1) _ SHI ltac:(lia) Dhi ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold hi. try rewrite (sx32_of_Z_signed hi) by lia. try rewrite (sx32_of_Z hi) by lia.
    (* [comment removed for export] *)
    urun_to 0x229f0%Z.
    rewrite fqs_iter_unfold in RES, QF'. cbv zeta in RES, QF'. fold lo hi in RES, QF'.
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd.
    - (* [comment removed for export] *)
      replace (hi - lo <? 10)%Z with false in RES, QF' by (symmetry; apply Z.ltb_ge; lia).
      enter_with (S0_qmed X Q Hh sp l1 r1 str sv nnd XOK XSEP hi lo rr tv fm ec m m _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact SC0| exact MI| apply munch_refl| apply wmono_refl|].
      intros m1 y15. cbv zeta. intros AR1_1 AR2_1 SC1 MI1 MU1 WM1 Hmed.
      clear AR1 AR2 SC SC0 MI. transport_after_call s0segs m m1 MU1 WM1.
      set (r' := ((rr * 7621 + 1) mod 32768)%Z) in *. set (med := rd32 ec (rd32 fm (med_idx (r' mod 3) lo hi))) in *.
      set (sz := Z.to_nat (hi - lo + 1)) in *.
      assert (Hr' : (0 <= r' < 32768)%Z) by (subst r'; apply Z.mod_pos_bound; lia).
      eapply (S0_ploop X Q Hh sp l1 r1 str sv nnd r' XOK XSEP (S sz) (FP fm lo hi lo hi) med hi lo ec m1 m1 _ _ _ _ _ _ _ _ _ sz (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi)));
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi];
        [lia| lia| unfold fp_ok; cbn; lia| lia| lia| reflexivity| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1_1| exact AR2_1| exact SC1| exact MI1| apply munch_refl| apply wmono_refl|].
      (* [comment removed for export] *)
      unfold KB978. intros m2 z1 z5 z7 z28 z29 z30 z31 AR1_2 AR2_2 SC2 MI2 MU2 WM2 FMR2 FMOK2 OK2 BR2. bz_params.
      clear AR1_1 AR2_1 SC1 MI1 MU1 WM1. transport_after_call s0segs m1 m2 MU2 WM2.
      enter_with (S0_qpush X Q Hh sp l1 r1 str sv nnd XOK XSEP (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi)) hi lo r' slo shi Jlo Jhi m2 m2 _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| exact OK2| exact BR2| exact FMR2| exact FMOK2| exact SD| reflexivity| reflexivity| exact LJlo| exact LJhi| exact AR1_2| exact SC2| exact SHI| exact SLO| exact MI2| apply munch_refl| apply wmono_refl|].
      intros m3 z1' z5' z6 z7' z10 z11 z13 z14 z15 z16 z17 z28' z29' z30' z31'. cbv zeta. intros AR1_3 SC3 SHI3 SLO3 MI3 MU3 WM3 FMR3 FMOK3 SD3 Hsp3 Hr3. bz_params.
      clear AR1_2 MI2 SC2 SHI SLO MU2 WM2. transport_after_call s0segs m2 m3 MU3 WM3.
      set (q' := qtail sp lo hi r' slo shi (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi))) in *.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        enter_with (IH q' qfin (fp_ltLo (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi))) me m3);
          [st_eq| lia| rewrite Hr3; lia| exact FMR3| exact FMOK3| exact SD3| exact QF'| exact RES| exact FIN| exact AR1_3| exact AR2_2| rewrite Hr3; exact SC3| exact SHI3| exact SLO3| exact MI3| exact MU| exact WM| exact K].
      + (* [comment removed for export] *)
        wstep.
        assert (Kc' : (fq_sp q' <= 0)%Z) by lia.
        assert (E : qfin = q').
        { clearbody q'. clear -RES Kc'. destruct f; [cbn [fqs_loop] in RES; symmetry; exact RES|]. rewrite fqs_loop_S in RES.
          replace (0 <? fq_sp q')%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). symmetry; exact RES. }
        clear RES. subst qfin.
        enter_with (K m3 (fp_ltLo (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| exact AR1_3| exact AR2_2| rewrite Hr3; exact SC3| exact SHI3| exact SLO3| exact MI3| exact MU| exact WM| exact FMR3| exact FMOK3| rewrite Hr3; lia].
    - (* [comment removed for export] *)
      replace (hi - lo <? 10)%Z with true in RES, QF' by (symmetry; apply Z.ltb_lt; lia).
      enter_with (S0_fss X Q sp l1 r1 XOK XSEP hi lo fm ec m m _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| apply munch_refl| apply wmono_refl|].
      intros m' x5 x6 x7 x13 x14 x15 x16 x17. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK''. bz_params.
      clear AR1 AR2 MI. transport_after_call s0segs m m' MU' WM'.
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        enter_with (IH (FQS (fallbackSimpleSort fm ec lo hi) (sp - 1) slo shi rr) qfin tv me m'); cbn [fq_fm fq_sp fq_slo fq_shi fq_r];
          [st_eq| lia| lia| exact FMR'| exact FMOK''| | exact QF'| exact RES| exact FIN| exact AR1'| exact AR2'| exact SC0| exact SHI| exact SLO| exact MI'| exact MU| exact WM| exact K].
        intros i Hi. apply SD. lia.
      + (* [comment removed for export] *)
        wstep.
        assert (E : qfin = FQS (fallbackSimpleSort fm ec lo hi) (sp - 1) slo shi rr).
        { destruct f; cbn [fqs_loop] in RES; [symmetry; exact RES|]. cbn [fq_sp] in RES. replace (0 <? sp - 1)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). symmetry; exact RES. }
        clear RES. subst qfin. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
        enter_with (K m' tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact AR2'| exact SC0| exact SHI| exact SLO| exact MI'| exact MU| exact WM| exact FMR'| exact FMOK''| lia].
  Qed.
End S0FS.

End ACeilS1.
