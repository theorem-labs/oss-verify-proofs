(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasFs BzCFactsFs BzCFactsFs2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).

  Lemma U0_fs_zero : forall (r : nat) (i : Z) (ft : zarr) (J : list byte) (me m : word -> option byte)
      (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 257)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    u32arr s0segs m (p + 1124) (ovw ft J 257) -> mem_inv s0segs m ->
    munch [(p + 1124, p + 2152)]%Z me m -> wmono s0segs me m ->
    (forall m', let ft' := fs_ftab_zero r ft i in
      u32arr s0segs m' (p + 1124) (ovw ft' J 257) -> mem_inv s0segs m' ->
      munch [(p + 1124, p + 2152)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 2152)) (Z_to_bv 64 (p + 2152)) a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22358) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 1124 + 4 * i)) (Z_to_bv 64 (p + 2152)) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x2234c) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft J me m ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr FTL MI MU WM K.
    fsenv_open XOK.
    pose proof (ovw_length ft J 257 ltac:(lia)) as LF.
    pose proof (u32arr_store_ok s0segs m (p + 1124) _ i _ FTL ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store FTL i 0%Z (rewrite unsigned_lit by lia; reflexivity).
    rewrite fs_ftab_zero_S in K.
    wstep.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset ft i 0) J me); [st_eq| lia| lia| lia| exact FTL| exact MI| exact MU| exact WM| exact K].
    - assert (r = 0)%nat by lia. subst r. cbn [fs_ftab_zero] in K.
      enter_with (K _); [st_eq| exact FTL| exact MI| exact MU| exact WM].
  Qed.

  Lemma U0_fs_copy : forall (r : nat) (i : Z) (ft fcp : zarr) (Jc : list byte) (me m : word -> option byte)
      (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 256)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    (forall b, 0 <= zget ft b <= nb)%Z ->
    u32arr s0segs m (p + 100) (ovw fcp Jc 256) -> u32arr s0segs m (p + 1124) (zw32 ft 257) -> mem_inv s0segs m ->
    munch [(p + 100, p + 1124)]%Z me m -> wmono s0segs me m ->
    (forall m' (x13 : word), let fcp' := fs_copy r fcp ft i in
      u32arr s0segs m' (p + 100) (ovw fcp' Jc 256) -> u32arr s0segs m' (p + 1124) (zw32 ft 257) -> mem_inv s0segs m' ->
      munch [(p + 100, p + 1124)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 1124)) (Z_to_bv 64 (p + 2148)) (Z_to_bv 64 (p + 1124)) x13 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x223e0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 100 + 4 * i)) (Z_to_bv 64 (p + 1124 + 4 * i)) (Z_to_bv 64 (p + 1124)) a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x223cc) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft fcp Jc me m ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr Hft FC FTL MI MU WM K.
    fsenv_open XOK.
    pose proof (ovw_length fcp Jc 256 ltac:(lia)) as LC. pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    pose proof (Hft i) as Fi.
    pose proof (zw32_read s0segs m (p + 1124) ft 257 i _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget ft i)) by lia.
    pose proof (u32arr_store_ok s0segs m (p + 100) _ i _ FC ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store FC i (zget ft i) wval_lit.
    rewrite fs_copy_S in K.
    wstep. wstep.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ft (zset fcp i (zget ft i)) Jc me); [st_eq| lia| lia| lia| exact Hft| exact FC| exact FTL| exact MI| exact MU| exact WM| exact K].
    - assert (r = 0)%nat by lia. subst r. cbn [fs_copy] in K.
      enter_with (K _ _); [st_eq| exact FC| exact FTL| exact MI| exact MU| exact WM].
  Qed.

  Lemma U0_fs_bhzero : forall (r : nat) (i : Z) (bh : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 2 + nb / 32)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x15 : word), let bh' := fs_bh_zero r bh i in
      u32arr s0segs m' FT (zw32 bh' 65537) -> mem_inv s0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 1)
                            (Z_to_bv 64 (FT + 4 * (2 + nb / 32))) (Z_to_bv 64 (FT + 4 * (2 + nb / 32))) x15 a6 a7
                            s2 s3 (Z_to_bv 64 FT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22544) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 (2 + nb / 32 - i)) (Z_to_bv 64 1)
                          (Z_to_bv 64 (FT + 4 * i)) (Z_to_bv 64 (FT + 4 * i)) a5 a6 a7
                          s2 s3 (Z_to_bv 64 FT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22510) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i bh me m ra t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr FTB MI MU WM K.
    fsenv_open XOK.
    pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    assert (HnB : (0 <= nb / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    urun_to 0x22530%Z.
    pose proof (u32arr_store_ok s0segs m FT _ i _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTB i 0%Z (rewrite unsigned_lit by lia; reflexivity).
    rewrite fs_bh_zero_S in K.
    wstep. wstep. wstep.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset bh i 0) me); [st_eq| lia| lia| lia| exact FTB| exact MI| exact MU| exact WM| exact K].
    - assert (r = 0)%nat by lia. subst r. cbn [fs_bh_zero] in K.
      enter_with (K _ _); [st_eq| exact FTB| exact MI| exact MU| exact WM].
  Qed.
End S0FS.

End ACeilS1.
