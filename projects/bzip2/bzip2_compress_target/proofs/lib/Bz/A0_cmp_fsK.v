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
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma fs_skip0_S : forall f fc j, fs_skip0 (S f) fc j = (if (zget fc j =? 0)%Z then fs_skip0 f fc (j + 1) else j).
Proof. reflexivity. Qed.
Lemma fs_skip0_ge : forall f fc j, (j <= fs_skip0 f fc j)%Z.
Proof. induction f as [|f IH]; intros fc j; cbn [fs_skip0]; [lia|]. destruct (zget fc j =? 0)%Z; [| lia]. specialize (IH fc (j + 1)%Z). lia. Qed.

(* [comment removed for export] *)
Definition rb_ok (nb : Z) (fc : zarr) (j : Z) : Prop :=
  let j' := fs_skip0 258%nat fc j in (0 <= j /\ j' <= 255 /\ (zget fc j' =? 0) = false /\ 1 <= zget fc j' <= nb)%Z.

Section A0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop.
  Variable fm : zarr.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation FCP := (ae_FCP Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis FMR : fm_range fm nb. Hypothesis FMOK' : zbok fm.
  Notation Wr := [(fe_A2 X, fe_A2 X + ARR2_SIZE); (ae_FCP Y, ae_FCP Y + 1024)]%Z.
  (* [comment removed for export] *)
  Notation RB ra t1 t2 a0 a1 a2 a3 a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 FCP)
         s2 s3 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma A0_skip0 : forall (f : nat) (j : Z) (fcA : zarr) (me m : word -> option byte) (ra t1 t2 a1 a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= j)%Z -> let j' := fs_skip0 f fcA j in (j' <= 255)%Z -> (zget fcA j' =? 0)%Z = false -> (1 <= zget fcA j' <= nb)%Z ->
    u32arr a0segs m FCP (zw32 fcA 256) -> munch Wr me m -> shzW a0segs Wr me FCP (FCP + 1024) ->
    evt a0segs Q (MS (RB ra t1 t2 (Z_to_bv 64 (FCP + 4 * (j' + 1))) a1 (Z_to_bv 64 j') (Z_to_bv 64 (FCP + 4 * (j' + 1))) (Z_to_bv 64 (zget fcA j')) a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9c1b4) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (RB ra t1 t2 (Z_to_bv 64 (FCP + 4 * j)) a1 (Z_to_bv 64 (j - 1)) (Z_to_bv 64 (FCP + 4 * j)) a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9c17c) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros j fcA me m ra t1 t2 a1 a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hj j' Hj' STOP VAL FCB MU SHC K; subst j'.
    - cbn [fs_skip0] in *. fsenv_open XOK. afenv_open YOK. pose proof (zw32_length fcA 256 ltac:(lia)) as LF. apply Z.eqb_neq in STOP.
      arun.
      pose proof (zw32_read a0segs m FCP fcA 256 j _ FCB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget fcA j)) by lia.
      arun. if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
      wstep.
      enter_with K; st_eq.
    - rewrite fs_skip0_S in *. fsenv_open XOK. afenv_open YOK. pose proof (zw32_length fcA 256 ltac:(lia)) as LF.
      destruct (Z.eqb_spec (zget fcA j) 0) as [Ez|Ez].
      + pose proof (fs_skip0_ge f fcA (j + 1)) as G.
        arun.
        pose proof (zw32_read a0segs m FCP fcA 256 j _ FCB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
        wstep. clear RD. rewrite Ez. try rewrite (sx32_of_Z 0) by lia.
        arun_to 0x9c19c%Z. wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
        enter_with (IH (j + 1)%Z fcA me m); [st_eq| lia| exact Hj'| exact STOP| exact VAL| exact FCB| exact MU| exact SHC| exact K].
      + apply Z.eqb_neq in STOP.
        arun.
        pose proof (zw32_read a0segs m FCP fcA 256 j _ FCB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
        wstep. clear RD. try rewrite (sx32_of_Z (zget fcA j)) by lia.
        arun. if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
        wstep.
        enter_with K; st_eq.
  Qed.

  Ltac store_addr E' :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?ad ?bs) _) =>
      replace (write_to_mem m0 ad bs) with (write_to_mem m0 (wa E') bs) by (f_equal; unfold wa; f_equal; lia) end.

  (* [comment removed for export] *)
  Lemma A0_rebuild : forall (n : nat) (i j : Z) (ec fcA : zarr) (me m : word -> option byte) (ra t1 t2 a0 a3 a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nb)%Z -> (1 <= n)%nat -> (0 <= i)%Z -> (0 <= j <= 255)%Z -> zbok ec ->
    (forall k, (0 <= k < Z.of_nat n)%Z -> let st := fs_rebuild (Z.to_nat k) ec fcA fm i j in rb_ok nb (snd (fst st)) (snd st)) ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec ARR2_SIZE) -> u32arr a0segs m FCP (zw32 fcA 256) -> mem_inv a0segs m ->
    munch Wr me m -> wmono a0segs me m ->
    shzW a0segs Wr me A1 (A1 + ARR1_SIZE) -> shzW a0segs Wr me A2 (A2 + ARR2_SIZE) -> shzW a0segs Wr me FCP (FCP + 1024) ->
    (forall m' (x10 x13 x14 x15 : word), let r := fs_rebuild n ec fcA fm i j in
      u8arr a0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 (fst (fst r)) ARR2_SIZE) -> u32arr a0segs m' FCP (zw32 (snd (fst r)) 256) -> mem_inv a0segs m' ->
      munch Wr me m' -> wmono a0segs me m' -> zbok (fst (fst r)) -> (0 <= snd r <= 255)%Z ->
      evt a0segs Q (MS (RB ra t1 t2 x10 (Z_to_bv 64 nb) (Z_to_bv 64 (snd r)) x13 x14 x15 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9c23c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t1 t2 a0 (Z_to_bv 64 i) (Z_to_bv 64 j) a3 a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9c168) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]; intros i j ec fcA me m ra t1 t2 a0 a3 a4 a5 a6 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hn Hi0 Hj ECOK' RF AR1 AR2 FCB MI MU WM SH1 SH2 SHC K; cbv zeta in K; [lia|].
    fsenv_open XOK. afenv_open YOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F).
    pose proof YSEP as SPY. unfold afenv_sep, apartv in SPY. cps_destruct SPY as (AP1B & AP2B & _). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length fcA 256 ltac:(lia)) as LF.
    pose proof (RF 0%Z ltac:(lia)) as R0. change (Z.to_nat 0) with 0%nat in R0. cbn [fs_rebuild fst snd] in R0. unfold rb_ok in R0. cbv zeta in R0. cps_destruct R0 as (_ & Hj' & STOP & VAL).
    set (j' := fs_skip0 258 fcA j) in *. pose proof (fs_skip0_ge 258 fcA j) as G. fold j' in G.
    rewrite fs_rebuild_S in K. cbv zeta in K. fold j' in K.
    pose proof (proj2 FMR i ltac:(lia)) as Fi.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z j) by lia. wstep. wstep. wstep. wstep.
    enter_with (A0_skip0 258 j fcA me m); [st_eq| lia| exact Hj'| exact STOP| exact VAL| exact FCB| exact MU| exact SHC|]. fold j'.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm FCP _ j' _ FCB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. store_addr (FCP + 4 * j')%Z. zw32_store FCB j' (zget fcA j' - 1)%Z wval_lit. try clear SO.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 a0segs mm A1 fm ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) FMOK' ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (zx32_of_Z (rd32 fm i)) by lia.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok a0segs mm A2 _ (rd32 fm i) 1 _ AR2 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end.
    wstep. store_addr (A2 + rd32 fm i)%Z.
    first [ zb8_store1 AR2 (rd32 fm i); rewrite (unsigned_lit j') in AR2 by lia
          | lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?ad [Z_to_bv 8 ?z]) _) =>
              let H := fresh "ARRw" in
              pose proof (zb8_write1_lit a0segs m0 A2 ec ARR2_SIZE (rd32 fm i) z AR2 ltac:(lia)) as H; clear AR2; store_done; rename H into AR2 end ].
    try clear SO.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - (* [comment removed for export] *)
      enter_with (IH (i + 1)%Z j' (wr8 ec (rd32 fm i) j') (zset fcA j' (zget fcA j' - 1)) me _);
        [st_eq| lia| lia| lia| lia| apply zbok_wr8; exact ECOK'| | exact AR1| exact AR2| exact FCB| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact SHC| exact K].
      intros k Hk. specialize (RF (k + 1)%Z ltac:(lia)). replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) in RF by lia.
      rewrite fs_rebuild_S in RF. cbv zeta in RF. exact RF.
    - (* [comment removed for export] *)
      assert (n = 0)%nat by lia. subst n. cbn [fs_rebuild fst snd] in K.
      wstep.
      enter_with (K _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact FCB| exact MI| exact MU| exact WM| apply zbok_wr8; exact ECOK'| lia].
  Qed.
End A0FS.

End ACeilS1.
