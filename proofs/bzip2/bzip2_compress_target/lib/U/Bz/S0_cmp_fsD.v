(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasFs BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpFsKit0.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop. Variables qsp l1 r1 : Z.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  (* [comment removed for export] *)
  Notation QR ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 (Z_to_bv 64 (qsp - 1)) a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 r1) (Z_to_bv 64 (-1)) (Z_to_bv 64 qsp) (Z_to_bv 64 l1)
         (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).
  Definition ec_range (ec : zarr) (n : Z) : Prop := forall k, (0 <= k < n -> 0 <= rd32 ec k < n)%Z.

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

  (* [comment removed for export] *)
  Lemma S0_fss_in4 : forall (f : nat) (j hi lo i et tmp : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t2 a6 a7 t3 t4 t5 t6 : word),
    (lo <= i)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 4 <= j <= hi + 4)%Z -> (hi - j + 4 <= 4 * Z.of_nat f)%Z ->
    (0 <= et < nb)%Z -> (0 <= tmp < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x17 : word), let r := fss_in f fm ec et j hi 4 in
      u8arr s0segs m' A1 (zb8 (fst r) ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> fm_range (fst r) nb -> zbok (fst r) -> (i + 4 <= snd r <= hi + 4)%Z ->
      evt s0segs Q (MS (QR ra x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) (Z_to_bv 64 (snd r)) x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22b1c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 (Z_to_bv 64 j) t2 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22a8c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros j hi lo i et tmp fm ec me m ra t0 t2 a6 a7 t3 t4 t5 t6 Hlo Hlo0 Hhi Hj Hf Het Htmp FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_in fst snd] in K.
      wstep. wstep; if_cases Kj; zify_cond_z Kj; [| exfalso; lia].
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia]. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_in_S in K.
    wstep. wstep; if_cases Kj; zify_cond_z Kj.
    - replace (j <=? hi)%Z with false in K by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd] in K.
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
    - replace (j <=? hi)%Z with true in K by (symmetry; apply Z.leb_le; lia). cbn [andb] in K.
      pose proof (proj2 FMR j ltac:(lia)) as Fj. pose proof (ECR (rd32 fm j) ltac:(lia)) as Ej.
      (* [comment removed for export] *)
      urun_to 0x22abc%Z. rd_fm fm j AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm j)) by lia.
      (* [comment removed for export] *)
      urun_to 0x22ad4%Z. rd_ec ec (rd32 fm j) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm j))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        replace (rd32 ec (rd32 fm j) <? et)%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
      + replace (rd32 ec (rd32 fm j) <? et)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        (* [comment removed for export] *)
        urun_to 0x22b10%Z. st_fm fm (j - 4)%Z AR1. rewrite (unsigned_lit (rd32 fm j)) in AR1 by lia.
        (* [comment removed for export] *)
        urun_to 0x22a8c%Z.
        enter_with (IH (j + 4)%Z hi lo i et tmp (wr32 fm (j - 4) (rd32 fm j)) ec me);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact K].
        apply fm_range_wr32; [exact FMR| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_fss_out4 : forall (r : nat) (i hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a3 a4 a5 a7 t3 t4 t5 t6 : word),
    (i - lo + 1 = Z.of_nat r)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 4 <= hi)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x13 x14 x15 x16 x17 : word), let fm' := fss_outer r fm ec i hi 4 in
      u8arr s0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt s0segs Q (MS (QR ra x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x13 x14 x15 x16 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22b5c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 t1 t2 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 a5 (Z_to_bv 64 i) a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22a10) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]; intros i hi lo fm ec me m ra t0 t1 t2 a3 a4 a5 a7 t3 t4 t5 t6 Hr Hlo Hhi Hi FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_outer] in K.
      wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK']. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_outer_S' in K. unfold fss_iter in K.
    pose proof (proj2 FMR i ltac:(lia)) as Fi. pose proof (ECR (rd32 fm i) ltac:(lia)) as Ei.
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    (* [comment removed for export] *)
    urun_to 0x22a48%Z. rd_fm fm i AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm i)) by lia.
    (* [comment removed for export] *)
    urun_to 0x22a88%Z. rd_ec ec (rd32 fm i) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm i))) by lia.
    (* [comment removed for export] *)
    enter_with (S0_fss_in4 (S (Z.to_nat (hi - i))) (i + 4)%Z hi lo i (rd32 ec (rd32 fm i)) (rd32 fm i) fm ec me);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM|].
    intros m' x5 x6 x7 x17. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK'' Hjf.
    destruct (fss_in (S (Z.to_nat (hi - i))) fm ec (rd32 ec (rd32 fm i)) (i + 4) hi 4) as [fm1 jf] eqn:Efi. cbn [fst snd] in *.
    clear AR1 AR2 MI MU WM. rename MI' into MI. bz_params.
    pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
    (* [comment removed for export] *)
    urun_to 0x22b50%Z. st_fm fm1 (jf - 4)%Z AR1'. rewrite (unsigned_lit (rd32 fm i)) in AR1' by lia.
    (* [comment removed for export] *)
    urun_to 0x22a10%Z.
    (* [comment removed for export] *)
    enter_with (IH (i - 1)%Z hi lo (wr32 fm1 (jf - 4) (rd32 fm i)) ec me);
      [st_eq| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK''| exact ECOK'| exact AR1'| exact AR2'| exact MI| exact MU'| exact WM'| exact K].
    apply fm_range_wr32; [exact FMR'| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_fss_in1 : forall (f : nat) (j hi lo i et tmp : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t2 a6 a7 t3 t4 t5 t6 : word),
    (lo <= i)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 1 <= j <= hi + 1)%Z -> (hi - j + 1 <= Z.of_nat f)%Z ->
    (0 <= et < nb)%Z -> (0 <= tmp < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x17 : word), let r := fss_in f fm ec et j hi 1 in
      u8arr s0segs m' A1 (zb8 (fst r) ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> fm_range (fst r) nb -> zbok (fst r) -> (i + 1 <= snd r <= hi + 1)%Z ->
      evt s0segs Q (MS (QR ra x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) (Z_to_bv 64 (snd r)) x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22c70) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 (Z_to_bv 64 j) t2 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 i) (Z_to_bv 64 tmp) (Z_to_bv 64 et) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22be0) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros j hi lo i et tmp fm ec me m ra t0 t2 a6 a7 t3 t4 t5 t6 Hlo Hlo0 Hhi Hj Hf Het Htmp FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_in fst snd] in K.
      wstep. wstep; if_cases Kj; zify_cond_z Kj; [| exfalso; lia].
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia]. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_in_S in K.
    wstep. wstep; if_cases Kj; zify_cond_z Kj.
    - replace (j <=? hi)%Z with false in K by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd] in K.
      enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
    - replace (j <=? hi)%Z with true in K by (symmetry; apply Z.leb_le; lia). cbn [andb] in K.
      pose proof (proj2 FMR j ltac:(lia)) as Fj. pose proof (ECR (rd32 fm j) ltac:(lia)) as Ej.
      (* [comment removed for export] *)
      urun_to 0x22c10%Z. rd_fm fm j AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm j)) by lia.
      (* [comment removed for export] *)
      urun_to 0x22c28%Z. rd_ec ec (rd32 fm j) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm j))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        replace (rd32 ec (rd32 fm j) <? et)%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with (K m _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| lia].
      + replace (rd32 ec (rd32 fm j) <? et)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        (* [comment removed for export] *)
        urun_to 0x22c64%Z. st_fm fm (j - 1)%Z AR1. rewrite (unsigned_lit (rd32 fm j)) in AR1 by lia.
        (* [comment removed for export] *)
        urun_to 0x22be0%Z.
        enter_with (IH (j + 1)%Z hi lo i et tmp (wr32 fm (j - 1) (rd32 fm j)) ec me);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact K].
        apply fm_range_wr32; [exact FMR| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_fss_out1 : forall (r : nat) (i hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a3 a4 a5 a7 t3 t4 t5 t6 : word),
    (i - lo + 1 = Z.of_nat r)%Z -> (0 <= lo)%Z -> (hi < nb)%Z -> (i + 1 <= hi)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x13 x14 x15 x16 x17 : word), let fm' := fss_outer r fm ec i hi 1 in
      u8arr s0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt s0segs Q (MS (QR ra x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x13 x14 x15 x16 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x229f8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 t1 t2 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 a5 (Z_to_bv 64 i) a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22b64) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]; intros i hi lo fm ec me m ra t0 t1 t2 a3 a4 a5 a7 t3 t4 t5 t6 Hr Hlo Hhi Hi FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM K; cbv zeta in K.
    { prep XOK XSEP fm ec. bz_params. cbn [fss_outer] in K.
      wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK']. }
    prep XOK XSEP fm ec. bz_params. rewrite fss_outer_S' in K. unfold fss_iter in K.
    pose proof (proj2 FMR i ltac:(lia)) as Fi. pose proof (ECR (rd32 fm i) ltac:(lia)) as Ei.
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    (* [comment removed for export] *)
    urun_to 0x22b9c%Z. rd_fm fm i AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm i)) by lia.
    (* [comment removed for export] *)
    urun_to 0x22bdc%Z. rd_ec ec (rd32 fm i) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm i))) by lia.
    (* [comment removed for export] *)
    enter_with (S0_fss_in1 (S (Z.to_nat (hi - i))) (i + 1)%Z hi lo i (rd32 ec (rd32 fm i)) (rd32 fm i) fm ec me);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM|].
    intros m' x5 x6 x7 x17. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK'' Hjf.
    destruct (fss_in (S (Z.to_nat (hi - i))) fm ec (rd32 ec (rd32 fm i)) (i + 1) hi 1) as [fm1 jf] eqn:Efi. cbn [fst snd] in *.
    clear AR1 AR2 MI MU WM. rename MI' into MI. bz_params.
    pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
    (* [comment removed for export] *)
    urun_to 0x22ca4%Z. st_fm fm1 (jf - 1)%Z AR1'. rewrite (unsigned_lit (rd32 fm i)) in AR1' by lia.
    (* [comment removed for export] *)
    urun_to 0x22b64%Z.
    enter_with (IH (i - 1)%Z hi lo (wr32 fm1 (jf - 1) (rd32 fm i)) ec me);
      [st_eq| lia| lia| lia| lia| | exact ECR| apply zbok_wr32; exact FMOK''| exact ECOK'| exact AR1'| exact AR2'| exact MI| exact MU'| exact WM'| exact K].
    apply fm_range_wr32; [exact FMR'| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_fss_p2 : forall (hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo - 1 <= hi)%Z -> (lo <> hi) ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x13 x14 x15 x16 x17 : word), let fm' := fss_outer (Z.to_nat (hi - 1 - lo + 1)) fm ec (hi - 1) hi 1 in
      u8arr s0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt s0segs Q (MS (QR ra x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x13 x14 x15 x16 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x229f8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 t1 t2 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22b5c) fc None m (seg_rom s0segs)).
  Proof.
    intros hi lo fm ec me m ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hlo Hhi Hlh Hne FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM K; cbv zeta in K.
    prep XOK XSEP fm ec. bz_params.
    (* [comment removed for export] *)
    urun_to 0x22b64%Z.
    destruct (Z_lt_le_dec hi lo) as [Hhl|Hhl].
    - (* [comment removed for export] *)
      replace (Z.to_nat (hi - 1 - lo + 1)) with 0%nat in K by lia. cbn [fss_outer] in K.
      wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'].
    - (* [comment removed for export] *)
      enter_with (S0_fss_out1 (Z.to_nat (hi - 1 - lo + 1)) (hi - 1)%Z hi lo fm ec me m);
        [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM|].
      intros m' x5 x6 x7 x13 x14 x15 x16 x17. exact (K m' x5 x6 x7 x13 x14 x15 x16 x17).
  Qed.

  (* [comment removed for export] *)
  Lemma S0_fss : forall (hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a3 a4 a6 a7 t3 t4 t5 t6 : word),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo - 1 <= hi)%Z -> (hi - lo < 10)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x13 x14 x15 x16 x17 : word), let fm' := fallbackSimpleSort fm ec lo hi in
      u8arr s0segs m' A1 (zb8 fm' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> fm_range fm' nb -> zbok fm' ->
      evt s0segs Q (MS (QR ra x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x13 x14 x15 x16 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x229f8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (QR ra t0 t1 t2 (Z_to_bv 64 hi) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 (hi - lo)) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x229f4) fc None m (seg_rom s0segs)).
  Proof.
    intros hi lo fm ec me m ra t0 t1 t2 a3 a4 a6 a7 t3 t4 t5 t6 Hlo Hhi Hlh Hsm FMR ECR FMOK' ECOK' AR1 AR2 MI MU WM K; cbv zeta in K.
    prep XOK XSEP fm ec. bz_params. unfold fallbackSimpleSort in K.
    (* [comment removed for export] *)
    wstep; if_cases K0; zify_cond_z K0.
    - replace (lo =? hi)%Z with false in K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep. wstep; if_cases K4; zify_cond_z K4.
      + (* [comment removed for export] *)
        replace (3 <? hi - lo)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
        eapply (S0_fss_p2 hi lo fm ec me m); [lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact K].
      + replace (3 <? hi - lo)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        (* [comment removed for export] *)
        urun_to 0x22a10%Z.
        (* [comment removed for export] *)
        enter_with (S0_fss_out4 (Z.to_nat (hi - 4 - lo + 1)) (hi - 4)%Z hi lo fm ec me m);
          [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| exact MU| exact WM|].
        intros m' x5 x6 x7 x13 x14 x15 x16 x17. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK''. bz_params.
        eapply (S0_fss_p2 hi lo _ ec me m'); [lia| lia| lia| lia| exact FMR'| exact ECR| exact FMOK''| exact ECOK'| exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact K].
    - replace (lo =? hi)%Z with true in K by (symmetry; apply Z.eqb_eq; lia).
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact FMR| exact FMOK'].
  Qed.
End S0FS.

End ACeilS1.
