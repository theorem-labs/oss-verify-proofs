(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs2 BzCLemmasMs3 CmpMsKit2 S0_cmp_msV.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  Tactic Notation "zw32_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.

  (* [comment removed for export] *)
  Lemma S0_cinit : forall (cnt : nat) (j ss : Z) (ft cs ce : zarr) (sb : scb)
      (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v < 4194304)%Z ->
    u32arr s0segs m FT (zw32 ft 65537) -> u32arr s0segs m (p + 1364) (zw32 cs 256) -> u32arr s0segs m (p + 340) (zw32 ce 256) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(p + 340, p + 2388)]%Z me m -> wmono s0segs me m ->
    (forall m' (x15' x16' : word), let r := ms_copy_init cnt cs ce ft ss j in
      u32arr s0segs m' FT (zw32 ft 65537) -> u32arr s0segs m' (p + 1364) (zw32 (fst r) 256) -> u32arr s0segs m' (p + 340) (zw32 (snd r) 256) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(p + 340, p + 2388)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 0) (Z_to_bv 64 (p + 340 + 4 * 256)) (Z_to_bv 64 (4 * (256 * 256 + ss + 1))) (Z_to_bv 64 (p + 1364 + 4 * 256))
                            (Z_to_bv 64 (4 * (256 * 256 + ss))) x15' x16'
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21d6c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                          (Z_to_bv 64 (256 - j)) (Z_to_bv 64 (p + 340 + 4 * j)) (Z_to_bv 64 (4 * (256 * j + ss + 1))) (Z_to_bv 64 (p + 1364 + 4 * j))
                          (Z_to_bv 64 (4 * (256 * j + ss))) x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21d10) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j ss ft cs ce sb x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m
           Hcnt Hj Hss FTV FTB CS CE SB MI MU WM K.
    msenv_open XOK.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    rewrite ms_copy_init_S in K. rewrite shl8 in K.
    pose proof (FTV (256 * j + ss)%Z ltac:(lia)) as V0. pose proof (FTV (256 * j + ss + 1)%Z ltac:(lia)) as V1.
    unfold scb_cells in SB.
    wstep. wstep. notrap.
    wstep. wstep. rd32_at FTB (256 * j + ss)%Z.
    wstep. wstep. rewrite land_CM64 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 1364) _ j _ CS ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
    wstep. zw32_store_at CS j (clearmask (zget ft (256 * j + ss))) (apply unsigned_lit_mod32).
    wstep. wstep. notrap.
    wstep. wstep. rd32_at FTB (256 * j + ss + 1)%Z.
    wstep. wstep. wstep. wstep. wstep. rewrite land_CM64 by lia. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 340) _ j _ CE ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO2 end.
    wstep. zw32_store_at CE j (clearmask (zget ft (256 * j + ss + 1)) - 1)%Z (apply unsigned_lit_mod32).
    wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (j + 1)%Z ss ft _ _ sb x1 x5 x6 x7 x8 x9 _ _ x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me mm) end;
        [st_eq| lia| lia| lia| exact FTV| exact FTB| exact CS| exact CE| exact SB| exact MI| exact MU| exact WM| exact K].
    - assert (cnt = 0%nat) as -> by lia. cbn [ms_copy_init] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact FTB| exact CS| exact CE| exact SB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  Lemma S0_mark : forall (cnt : nat) (j ss : Z) (ft : zarr) (sb : scb)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> ftv ft ->
    u32arr s0segs m FT (zw32 ft 65537) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x11' x12' : word), let ft' := ms_mark cnt ft ss j in ftv ft' ->
      u32arr s0segs m' FT (zw32 ft' 65537) -> rw_cells s0segs m' (p + 120) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 0) x11' x12' x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (4 * ss + 1024 * 256)) x20 x21 x22 x23 x24
                            (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21fc0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                          (Z_to_bv 64 (256 - j)) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (4 * ss + 1024 * j)) x20 x21 x22 x23 x24
                          (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21f98) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j ss ft sb x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 me m
           Hcnt Hj Hss FTV FTB SB MI MU WM K.
    msenv_open XOK. pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    rewrite ms_mark_S in K. cbv zeta in K. rewrite shl8 in K.
    pose proof (FTV (256 * j + ss)%Z ltac:(lia)) as V0.
    unfold scb_cells in SB.
    wstep. wstep. notrap.
    wstep. wstep. rd32_at FTB (256 * j + ss)%Z.
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ (256 * j + ss)%Z _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store_at FTB (256 * j + ss)%Z (Z.lor (zget ft (256 * j + ss)) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
    pose proof (ftv_mark1 ft (256 * j + ss)%Z FTV ltac:(lia)) as FTV1.
    wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (j + 1)%Z ss _ sb x1 x5 x6 x7 x8 x9 _ _ x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 me mm) end;
        [st_eq| lia| lia| lia| exact FTV1| exact FTB| exact SB| exact MI| exact MU| exact WM| exact K].
    - assert (cnt = 0%nat) as -> by lia. cbn [ms_mark] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact FTV1| exact FTB| exact SB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
