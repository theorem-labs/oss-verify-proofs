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
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variables Hh r5 : Z.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - fe_A2 X)%Z.
  Notation WH := [(FT, FT + 262148)]%Z.
  (* [comment removed for export] *)
  Notation RH ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 (Z_to_bv 64 Hh) t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) (Z_to_bv 64 A2) (Z_to_bv 64 r5) (Z_to_bv 64 A1) cSB (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) s10 (Z_to_bv 64 NA2) t3 (Z_to_bv 64 nb) t5 t6).
  (* [comment removed for export] *)

  Lemma B0_headers : forall (n : nat) (i cc : Z) (fm ec bh : zarr) (me m : word -> option byte) (ra t0 t2 a1 a5 a6 a7 t3 t5 t6 : word),
    (i + Z.of_nat n = r5 + 1)%Z -> (1 <= n)%nat -> (0 <= i)%Z -> (r5 < nb)%Z -> (cc = -1 \/ 0 <= cc < nb)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec -> bh_w32 bh ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> u32arr b0segs m FT (zw32 bh 65537) -> mem_inv b0segs m ->
    munch WH me m -> wmono b0segs me m ->
    shzW b0segs WH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WH me A2 (A2 + ARR2_SIZE) -> shzW b0segs WH me FT (FT + 262144) ->
    frdW b0segs WH me (P + 216) [C8 (Z_to_bv 64 1)] ->
    (forall m' (x11 x14 x15 x16 : word), let bh' := fs_headers n bh ec fm i cc in
      u8arr b0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> u32arr b0segs m' FT (zw32 bh' 65537) -> mem_inv b0segs m' ->
      munch WH me m' -> wmono b0segs me m' -> bh_w32 bh' ->
      evt b0segs Q (MS (RH ra t0 t2 (Z_to_bv 64 (A1 + 4 * (r5 + 1))) x11 (Z_to_bv 64 (A1 + 4 * (r5 + 1))) (Z_to_bv 64 (r5 + 1)) x14 x15 x16 a7 (Z_to_bv 64 (r5 + 1)) t3 t5 t6)
                       F (Z_to_bv 64 0xa55bc) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RH ra t0 t2 (Z_to_bv 64 (A1 + 4 * i)) a1 (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 cc) a5 a6 a7 (Z_to_bv 64 i) t3 t5 t6)
                     F (Z_to_bv 64 0xa6bcc) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]; intros i cc fm ec bh me m ra t0 t2 a1 a5 a6 a7 t3 t5 t6 Hi Hn Hi0 Hr Hcc FMR ECR FMOK' ECOK' BW AR1 AR2 FTB MI MU WM SH1 SH2 SHF V216 K; cbv zeta in K; [lia|].
    fsenv_open XOK. afenv_open YOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    pose proof (proj2 FMR i ltac:(lia)) as Fi. pose proof (ECR (rd32 fm i) ltac:(lia)) as Ei.
    (* [comment removed for export] *)
    brun.
    pose proof (V216 m MU) as RO. wstep. clear RO.
    (* [comment removed for export] *)
    brun.
    pose proof (zb8_read4 b0segs m A1 fm ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) FMOK' ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (zx32_of_Z (rd32 fm i)) by lia.
    (* [comment removed for export] *)
    brun_to 0xa6c28%Z. flagsb.
    (* [comment removed for export] *)
    brun.
    pose proof (zb8_read4 b0segs m A2 ec ARR2_SIZE (rd32 fm i) _ AR2 ltac:(lia) ltac:(lia) ECOK' ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (rd32 ec (rd32 fm i))) by lia.
    (* [comment removed for export] *)
    assert (TAIL : forall m1 bh1 cc1 (x11 x16 : word),
      fs_headers n bh1 ec fm (i + 1) cc1 = fs_headers (S n) bh ec fm i cc -> (cc1 = -1 \/ 0 <= cc1 < nb)%Z -> bh_w32 bh1 ->
      u8arr b0segs m1 A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m1 A2 (zb8 ec ARR2_SIZE) -> u32arr b0segs m1 FT (zw32 bh1 65537) -> mem_inv b0segs m1 ->
      munch WH me m1 -> wmono b0segs me m1 ->
      evt b0segs Q (MS (RH ra t0 t2 (Z_to_bv 64 (A1 + 4 * i)) x11 (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 cc1) (Z_to_bv 64 (rd32 ec (rd32 fm i))) x16 a7 (Z_to_bv 64 i) t3 t5 t6)
                       F (Z_to_bv 64 0xa6c94) fc None m1 (seg_rom b0segs))).
    { intros m1 bh1 cc1 x11 x16 E Hcc1 BW1 AR1' AR2' FTB1 MI1 MU1 WM1.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (i + 1)) by lia. brun; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z cc1 fm ec bh1 me m1); [st_eq| lia| lia| lia| lia| exact Hcc1| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact BW1| exact AR1'| exact AR2'| exact FTB1| exact MI1| exact MU1| exact WM1| exact SH1| exact SH2| exact SHF| exact V216|].
        intros m' y11 y14 y15 y16. cbv zeta. rewrite E. exact (K m' y11 y14 y15 y16).
      - (* [comment removed for export] *)
        assert (n = 0)%nat by lia. subst n. cbn [fs_headers] in E, K. rewrite <- E in K.
        wstep.
        enter_with (K m1 _ _ _ _); [st_eq| exact AR1'| exact AR2'| exact FTB1| exact MI1| exact MU1| exact WM1| exact BW1]. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ecc : cc = rd32 ec (rd32 fm i)) by (destruct Hcc as [Hcc|Hcc]; [subst cc; exfalso; clear -Kc Ei; mlia| lia]).
      eapply (TAIL m bh cc _ _); [| exact Hcc| exact BW| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM].
      rewrite fs_headers_S. cbv zeta. replace (cc =? rd32 ec (rd32 fm i))%Z with true by (symmetry; apply Z.eqb_eq; exact Ecc). reflexivity.
    - (* [comment removed for export] *)
      assert (Ncc : cc <> rd32 ec (rd32 fm i)) by (destruct Hcc as [Hcc|Hcc]; [subst cc; lia| lia]).
      assert (Hw : (0 <= i / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      pose proof (BW (i / 32)%Z) as Bw.
      (* [comment removed for export] *)
      brun_to 0xa6c6c%Z. flagsb.
      (* [comment removed for export] *)
      brun.
      pose proof (zw32_read b0segs m FT bh 65537 (i / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD.
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (u32arr_store_ok b0segs m FT _ (i / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. zw32_store FTB (i / 32)%Z (Z.lor (zget bh (i / 32)) (Z.shiftl 1 (Z.land i 31)))%Z (first [apply set_bh_store_b | apply set_bh_store_a]).
      (* [comment removed for export] *)
      wstep.
      eapply (TAIL _ (zset bh (i / 32) (Z.lor (zget bh (i / 32)) (Z.shiftl 1 (Z.land i 31)))) (rd32 ec (rd32 fm i)) _ _);
        [| right; lia| | exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM].
      + rewrite fs_headers_S. cbv zeta. replace (cc =? rd32 ec (rd32 fm i))%Z with false by (symmetry; apply Z.eqb_neq; exact Ncc). cbn [negb].
        unfold set_bh, bh_word. rewrite shiftr5_div. reflexivity.
      + pose proof (set_bh_w32 bh i BW) as Y'. unfold set_bh, bh_word in Y'. rewrite shiftr5_div in Y'. exact Y'.
  Qed.
End B0FS.
End ACeilS1.
