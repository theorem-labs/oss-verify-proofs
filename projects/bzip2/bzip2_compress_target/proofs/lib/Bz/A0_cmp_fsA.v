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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation ec0 := (fe_ec X). Notation fm0 := (fe_fm X).
  Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_count : forall (r : nat) (i : Z) (ft : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = nb)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    (forall b, 0 <= zget ft b <= i)%Z ->
    u8arr a0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m (P + 244) (zw32 ft 257) -> mem_inv a0segs m ->
    munch [(P + 244, P + 1272)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(P + 244, P + 1272)]%Z me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x10 x11 x12 x13 x14 : word), let ft' := fs_count r ft ec0 i in
      u8arr a0segs m' A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m' (P + 244) (zw32 ft' 257) -> mem_inv a0segs m' ->
      munch [(P + 244, P + 1272)]%Z me m' -> wmono a0segs me m' ->
      (forall b, 0 <= zget ft' b <= nb)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) x10 x11 x12 x13 x14 a5 a6 a7
                            (Z_to_bv 64 (P + 244)) s3 (Z_to_bv 64 A2) s5 cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9ade4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 (nb - i)) (Z_to_bv 64 (A2 + i)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 (P + 244)) s3 (Z_to_bv 64 A2) s5 cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9ad9c) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft me m ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr Hft AR2 FTL MI MU WM SH2 K.
    fsenv_open XOK. afenv_open YOK. bz_params.
    pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    (* [comment removed for export] *)
    arun.
    pose proof (zb8_read1 a0segs m A2 ec0 ARR2_SIZE i _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. pose proof (ECOK i) as Bi. rewrite (unsigned_lit8 (zget ec0 i)) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (zw32_read a0segs m (P + 244) ft 257 (zget ec0 i) _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (Hft (zget ec0 i)) as Fb. rewrite (sx32_of_Z (zget ft (zget ec0 i))) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m (P + 244) _ (zget ec0 i) _ FTL ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zw32_write a0segs m (P + 244) ft 257 (zget ec0 i) (Z_to_bv 64 (zget ft (zget ec0 i) + 1)) (zget ft (zget ec0 i) + 1) FTL ltac:(lia) ltac:(rewrite unsigned_lit by lia; reflexivity)) as FTL'.
    clear FTL. store_done. rename FTL' into FTL.
    rewrite fs_count_S in K.
    (* [comment removed for export] *)
    arun. if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zincr ft (rd8 ec0 i)) me); [st_eq| lia| lia| lia| | exact AR2| | exact MI| exact MU| exact WM| exact SH2| ].
      + intros b'. unfold zincr, rd8. rewrite zget_zset. pose proof (Hft b'). destruct (Z.eqb_spec b' (zget ec0 i)); [subst b'; lia| lia].
      + unfold zincr, rd8. exact FTL.
      + intros m' x10 x11 x12 x13 x14. exact (K m' x10 x11 x12 x13 x14).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_count] in K.
      wstep.
      enter_with (K _ _ _ _ _ _); [st_eq| exact AR2| | exact MI| exact MU| exact WM|].
      + unfold zincr, rd8. exact FTL.
      + intros b'. unfold zincr, rd8. rewrite zget_zset. pose proof (Hft b'). destruct (Z.eqb_spec b' (zget ec0 i)); [subst b'; lia| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_accum : forall (r : nat) (i : Z) (ft : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 257)%Z -> (1 <= i)%Z -> (1 <= r)%nat ->
    (forall b, i <= b -> 0 <= zget ft b <= nb)%Z -> (0 <= zget ft (i - 1) <= i * nb)%Z ->
    u32arr a0segs m (P + 244) (zw32 ft 257) -> mem_inv a0segs m ->
    munch [(P + 244, P + 1272)]%Z me m -> wmono a0segs me m ->
    (forall m' (x10 x11 x13 : word), let ft' := fs_accum r ft i in
      u32arr a0segs m' (P + 244) (zw32 ft' 257) -> mem_inv a0segs m' ->
      munch [(P + 244, P + 1272)]%Z me m' -> wmono a0segs me m' ->
      (forall b, 0 <= b < 257 -> 0 <= zget ft' b <= (b + 1) * nb)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) x10 x11 (Z_to_bv 64 (P + 1272)) x13 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9ae28) fc None m' (seg_rom a0segs))) ->
    (forall b, 0 <= b < i -> 0 <= zget ft b <= (b + 1) * nb)%Z ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (zget ft (i - 1))) (Z_to_bv 64 (P + 244 + 4 * i)) (Z_to_bv 64 (P + 1272)) a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9ae14) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft me m ra t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi1 Hr Hft Hacc FTL MI MU WM K Hdone.
    fsenv_open XOK. afenv_open YOK.
    pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    (* [comment removed for export] *)
    pose proof (zw32_read a0segs m (P + 244) ft 257 i _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (Hft i ltac:(lia)) as Fi. rewrite (sx32_of_Z (zget ft i)) by lia.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok a0segs m (P + 244) _ i _ FTL ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zw32_write a0segs m (P + 244) ft 257 i (Z_to_bv 64 (zget ft i + zget ft (i - 1))) (zget ft i + zget ft (i - 1)) FTL ltac:(lia) ltac:(rewrite unsigned_lit by lia; reflexivity)) as FTL'.
    clear FTL. store_done. rename FTL' into FTL.
    rewrite fs_accum_S in K.
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset ft i (zget ft i + zget ft (i - 1))) me); [st_eq| lia| lia| lia| | | exact FTL| exact MI| exact MU| exact WM| |].
      + cbv delta [mkR]. rewrite zget_zset. replace (i + 1 - 1 =? i)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      + intros b' Hb'. rewrite zget_zset. destruct (Z.eqb_spec b' i); [lia|]. apply Hft. lia.
      + rewrite zget_zset. replace (i + 1 - 1 =? i)%Z with true by (symmetry; apply Z.eqb_eq; lia). lia.
      + intros m' x10 x11 x13. exact (K m' x10 x11 x13).
      + intros b' Hb'. rewrite zget_zset. destruct (Z.eqb_spec b' i); [subst b'; lia|]. apply Hdone. lia.
    - assert (r = 0)%nat by lia. subst r. cbn [fs_accum] in K.
      enter_with (K _ _ _ _); [st_eq| exact FTL| exact MI| exact MU| exact WM|].
      intros b' Hb'. rewrite zget_zset. destruct (Z.eqb_spec b' i); [subst b'; lia|]. apply Hdone. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_distrib : forall (r : nat) (i : Z) (ft fm : zarr) (me m : word -> option byte)
      (ra t1 t2 a1 a6 a7 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = nb)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    fsf_distrib fm0 ec0 nb -> fp_dist fm0 ec0 nb (Z.to_nat i) = (ft, fm) ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m (P + 244) (zw32 ft 257) -> mem_inv a0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)]%Z me A1 (A1 + ARR1_SIZE) ->
    shzW a0segs [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)]%Z me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x10 x11 x12 x14 x15 x16 x17 : word), let r' := fs_distrib r ft fm ec0 i in
      u8arr a0segs m' A1 (zb8 (snd r') ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs m' (P + 244) (zw32 (fst r') 257) -> mem_inv a0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) x10 x11 x12 (Z_to_bv 64 (P + 244)) x14 x15 x16 x17
                            s2 s3 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9aec4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A2 + i)) a1 (Z_to_bv 64 i) (Z_to_bv 64 (P + 244)) (Z_to_bv 64 (nb - i)) (Z_to_bv 64 (A2 + i)) a6 a7
                          s2 s3 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9ae44) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft fm me m ra t1 t2 a1 a6 a7 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr FD CUR AR1 AR2 FTL MI MU WM SH1 SH2 K.
    fsenv_open XOK. afenv_open YOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & _ & _). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    pose proof (FD i ltac:(lia)) as Fk. rewrite CUR in Fk. cbn [fst] in Fk.
    (* [comment removed for export] *)
    arun.
    pose proof (zb8_read1 a0segs m A2 ec0 ARR2_SIZE i _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. pose proof (ECOK i) as Bi. rewrite (unsigned_lit8 (zget ec0 i)) by lia.
    change (rd8 ec0 i) with (zget ec0 i) in Fk.
    (* [comment removed for export] *)
    arun.
    pose proof (zw32_read a0segs m (P + 244) ft 257 (zget ec0 i) _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget ft (zget ec0 i))) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m (P + 244) _ (zget ec0 i) _ FTL ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTL (zget ec0 i) (zget ft (zget ec0 i) - 1)%Z wval_lit.
    (* [comment removed for export] *)
    arun_to 0x9ae78%Z.
    replace (zget ft (zget ec0 i) * 4 + A1 + -4)%Z with (A1 + 4 * (zget ft (zget ec0 i) - 1))%Z by lia.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok a0segs mm A1 _ (4 * (zget ft (zget ec0 i) - 1)) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO2
    end.
    wstep. zb8_store4 AR1 (zget ft (zget ec0 i) - 1)%Z. rewrite (unsigned_lit i) in AR1 by lia.
    rewrite fs_distrib_S in K. cbv zeta in K. change (rd8 ec0 i) with (zget ec0 i) in K.
    (* [comment removed for export] *)
    arun. if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset ft (zget ec0 i) (zget ft (zget ec0 i) - 1)) (wr32 fm (zget ft (zget ec0 i) - 1) i) me);
        [st_eq| lia| lia| lia| exact FD| | exact AR1| exact AR2| exact FTL| exact MI| exact MU| exact WM| exact SH1| exact SH2| ].
      + rewrite fp_dist_step, CUR by lia. reflexivity.
      + intros m' x10 x11 x12 x14 x15 x16 x17. exact (K m' x10 x11 x12 x14 x15 x16 x17).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_distrib] in K.
      wstep.
      enter_with (K _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact FTL| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_bhinit : forall (r : nat) (i : Z) (ft bh : zarr) (me m : word -> option byte)
      (ra t1 t2 a0 a4 a5 a6 a7 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 256)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft b <= nb)%Z -> bh_w32 bh ->
    u32arr a0segs m (P + 244) (zw32 ft 257) -> u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(FT, FT + 262148)]%Z me FT (FT + 262144) ->
    (forall m' (x10 x11 x12 x14 x15 : word), let bh' := fs_bh_init r bh ft i in
      u32arr a0segs m' (P + 244) (zw32 ft 257) -> u32arr a0segs m' FT (zw32 bh' 65537) -> mem_inv a0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono a0segs me m' -> bh_w32 bh' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) x10 x11 x12 (Z_to_bv 64 1) x14 x15 a6 a7
                            s2 s3 s4 s5 cSB s7 (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9af50) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 (Z_to_bv 64 (P + 244 + 4 * i)) (Z_to_bv 64 (256 - i)) (Z_to_bv 64 1) a4 a5 a6 a7
                          s2 s3 s4 s5 cSB s7 (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9af00) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft bh me m ra t1 t2 a0 a4 a5 a6 a7 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr Hft BW FTL FTB MI MU WM SHF K.
    fsenv_open XOK. afenv_open YOK.
    pose proof (zw32_length ft 257 ltac:(lia)) as LF. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    pose proof (Hft i ltac:(lia)) as Fi.
    assert (Hw : (0 <= zget ft i / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    pose proof (zw32_read a0segs m (P + 244) ft 257 i _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (zx32_of_Z (zget ft i)) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (zw32_read a0segs m FT bh 65537 (zget ft i / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (BW (zget ft i / 32)%Z) as Bw.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m FT _ (zget ft i / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTB (zget ft i / 32)%Z (Z.lor (zget bh (zget ft i / 32)) (Z.shiftl 1 (Z.land (zget ft i) 31)))%Z (apply set_bh_store_a).
    rewrite fs_bh_init_S in K. unfold set_bh, bh_word in K. rewrite shiftr5_div in K.
    assert (BW' : bh_w32 (zset bh (zget ft i / 32) (Z.lor (zget bh (zget ft i / 32)) (Z.shiftl 1 (Z.land (zget ft i) 31))))).
    { pose proof (set_bh_w32 bh (zget ft i) BW) as Y'. unfold set_bh, bh_word in Y'. rewrite shiftr5_div in Y'. exact Y'. }
    (* [comment removed for export] *)
    arun. if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ft _ me); [st_eq| lia| lia| lia| exact Hft| exact BW'| exact FTL| exact FTB| exact MI| exact MU| exact WM| exact SHF| ].
      intros m' x10 x11 x12 x14 x15. exact (K m' x10 x11 x12 x14 x15).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_bh_init] in K.
      wstep.
      enter_with (K _ _ _ _ _ _); [st_eq| exact FTL| exact FTB| exact MI| exact MU| exact WM| exact BW'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_sentinel : forall (r : nat) (i : Z) (bh : zarr) (me m : word -> option byte)
      (ra t1 t2 a0 a4 a5 a6 a7 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 32)%Z -> (0 <= i)%Z -> (1 <= r)%nat -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(FT, FT + 262148)]%Z me FT (FT + 262144) ->
    (forall m' (x10 x11 x13 x14 x15 : word), let bh' := fs_sentinel r bh nb i in
      u32arr a0segs m' FT (zw32 bh' 65537) -> mem_inv a0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono a0segs me m' -> bh_w32 bh' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) x10 x11 (Z_to_bv 64 1) x13 x14 x15 a6 a7
                            s2 s3 s4 s5 cSB s7 (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9aff4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 (Z_to_bv 64 (32 - i)) (Z_to_bv 64 1) (Z_to_bv 64 (nb + 2 * i)) a4 a5 a6 a7
                          s2 s3 s4 s5 cSB s7 (Z_to_bv 64 FT) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9af64) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i bh me m ra t1 t2 a0 a4 a5 a6 a7 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr BW FTB MI MU WM SHF K.
    fsenv_open XOK. afenv_open YOK.
    pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    assert (Hw1 : (0 <= (nb + 2 * i) / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    assert (Hw2 : (0 <= (nb + 2 * i + 1) / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    arun.
    pose proof (zw32_read a0segs m FT bh 65537 ((nb + 2 * i) / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (BW ((nb + 2 * i) / 32)%Z) as Bw1.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m FT _ ((nb + 2 * i) / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTB ((nb + 2 * i) / 32)%Z (Z.lor (zget bh ((nb + 2 * i) / 32)) (Z.shiftl 1 (Z.land (nb + 2 * i) 31)))%Z (apply set_bh_store_b).
    set (bh1 := zset bh _ _) in FTB.
    assert (BW1 : bh_w32 bh1).
    { pose proof (set_bh_w32 bh (nb + 2 * i) BW) as Y'. unfold set_bh, bh_word in Y'. rewrite shiftr5_div in Y'. exact Y'. }
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read a0segs mm FT bh1 65537 ((nb + 2 * i + 1) / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. pose proof (BW1 ((nb + 2 * i + 1) / 32)%Z) as Bw2.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm FT _ ((nb + 2 * i + 1) / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO2 end.
    wstep. zw32_store FTB ((nb + 2 * i + 1) / 32)%Z (Z.land (zget bh1 ((nb + 2 * i + 1) / 32)) (Z.lxor (Z.shiftl 1 (Z.land (nb + 2 * i + 1) 31)) 4294967295))%Z (apply clear_bh_store_b).
    assert (BW2 : bh_w32 (zset bh1 ((nb + 2 * i + 1) / 32) (Z.land (zget bh1 ((nb + 2 * i + 1) / 32)) (Z.lxor (Z.shiftl 1 (Z.land (nb + 2 * i + 1) 31)) 4294967295)))).
    { pose proof (clear_bh_w32 bh1 (nb + 2 * i + 1) BW1) as Y'. unfold clear_bh, bh_word in Y'. rewrite shiftr5_div in Y'. exact Y'. }
    rewrite fs_sentinel_S in K. unfold clear_bh, set_bh, bh_word in K. rewrite !shiftr5_div in K. subst bh1.
    (* [comment removed for export] *)
    arun. if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z _ me); [st_eq| lia| lia| lia| exact BW2| exact FTB| exact MI| exact MU| exact WM| exact SHF| ].
      intros m' x10 x11 x13 x14 x15. exact (K m' x10 x11 x13 x14 x15).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_sentinel] in K.
      wstep.
      enter_with (K _ _ _ _ _ _); [st_eq| exact FTB| exact MI| exact MU| exact WM| exact BW2].
  Qed.

End A0FS.
End ACeilS1.
