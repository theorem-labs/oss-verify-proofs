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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  Notation WCI := [(CS, CS + 1024); (CE, CE + 1024)]%Z.

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.
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
  Lemma A0_cinit : forall (cnt : nat) (j ss : Z) (ft cs ce : zarr)
      (x1 x5 x6 x7 x11 x13 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v < 4194304)%Z ->
    u32arr a0segs m FT (zw32 ft 65537) -> u32arr a0segs m CS (zw32 cs 256) -> u32arr a0segs m CE (zw32 ce 256) -> mem_inv a0segs m ->
    munch WCI me m -> wmono a0segs me m ->
    shzW a0segs WCI me FT (FT + 262144) -> shpW a0segs WCI me FT (FT + 262148) ->
    (forall m' (x5' x11' x17' : word), let r := ms_copy_init cnt cs ce ft ss j in
      u32arr a0segs m' FT (zw32 ft 65537) -> u32arr a0segs m' CS (zw32 (fst r) 256) -> u32arr a0segs m' CE (zw32 (snd r) 256) -> mem_inv a0segs m' ->
      munch WCI me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5' x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (FT + 4 * ss + 1024 * 256)) x11' (Z_to_bv 64 (FT + 4 + 4 * ss + 1024 * 256)) x13 (Z_to_bv 64 0)
                            (Z_to_bv 64 (CS + 4 * 256)) (Z_to_bv 64 (CE + 4 * 256)) x17'
                            x18 cSB x20 (Z_to_bv 64 18446744073707454463) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x99b34) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (FT + 4 * ss + 1024 * j)) x11 (Z_to_bv 64 (FT + 4 + 4 * ss + 1024 * j)) x13 (Z_to_bv 64 (256 - j))
                          (Z_to_bv 64 (CS + 4 * j)) (Z_to_bv 64 (CE + 4 * j)) x17
                          x18 cSB x20 (Z_to_bv 64 18446744073707454463) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x99ab8) fc None m (seg_rom a0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j ss ft cs ce x1 x5 x6 x7 x11 x13 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m
           Hcnt Hj Hss FTV FTB CSB CEB MI MU WM SHF SHP K.
    msenv_open XOK. amenv_open YOK.
    pose proof (amsx_F_CS X Y YSX) as APa. pose proof (amsx_F_CE X Y YSX) as APb. box_ors.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    rewrite ms_copy_init_S in K. rewrite shl8 in K.
    pose proof (FTV (256 * j + ss)%Z ltac:(lia)) as V0. pose proof (FTV (256 * j + ss + 1)%Z ltac:(lia)) as V1.
    (* [comment removed for export] *)
    arun. rd32_at FTB (256 * j + ss)%Z.
    wstep. wstep. rewrite land_CM64 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm CS _ j _ CSB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
    wstep. zw32_store_at CSB j (clearmask (zget ft (256 * j + ss))) (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    arun_to 0x99ae0%Z. ack_rd (FT + 4 * ss + 1024 * j + 4)%Z 4%Z. ack_merge.
    rd32_at FTB (256 * j + ss + 1)%Z.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite land_CM64 by lia. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm CE _ j _ CEB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO2 end.
    wstep. zw32_store_at CEB j (clearmask (zget ft (256 * j + ss + 1)) - 1)%Z (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (j + 1)%Z ss ft _ _ x1 _ x6 x7 _ x13 _ x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me mm) end;
        [st_eq| lia| lia| lia| exact FTV| exact FTB| exact CSB| exact CEB| exact MI| exact MU| exact WM| exact SHF| exact SHP| exact K].
    - assert (cnt = 0%nat) as -> by lia. cbn [ms_copy_init] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact FTB| exact CSB| exact CEB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_mark : forall (cnt : nat) (j ss : Z) (ft : zarr)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> ftv ft ->
    u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m -> munch [(FT, FT + 262148)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(FT, FT + 262148)]%Z me FT (FT + 262144) ->
    (forall m' (x11' x12' : word), let ft' := ms_mark cnt ft ss j in ftv ft' ->
      u32arr a0segs m' FT (zw32 ft' 65537) -> mem_inv a0segs m' -> munch [(FT, FT + 262148)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 0) x11' x12' x13 x14 x15 x16 x17
                            x18 cSB (Z_to_bv 64 (FT + 4 * ss + 1024 * 256)) x21 x22 x23 x24 x25 (Z_to_bv 64 (FT + 4 * ss + 1024 * 256)) x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x99e24) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (256 - j)) x11 x12 x13 x14 x15 x16 x17
                          x18 cSB (Z_to_bv 64 (FT + 4 * ss + 1024 * j)) x21 x22 x23 x24 x25 (Z_to_bv 64 (FT + 4 * ss + 1024 * j)) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x99de0) fc None m (seg_rom a0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j ss ft x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 me m Hcnt Hj Hss FTV FTB MI MU WM SHF K.
    msenv_open XOK. pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    rewrite ms_mark_S in K. cbv zeta in K. rewrite shl8 in K.
    pose proof (FTV (256 * j + ss)%Z ltac:(lia)) as V0.
    (* [comment removed for export] *)
    arun. rd32_at FTB (256 * j + ss)%Z.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm FT _ (256 * j + ss)%Z _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store_at FTB (256 * j + ss)%Z (Z.lor (zget ft (256 * j + ss)) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
    pose proof (ftv_mark1 ft (256 * j + ss)%Z FTV ltac:(lia)) as FTV1.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (j + 1)%Z ss _ x1 x5 x6 x7 _ _ x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 me mm) end;
        [st_eq| lia| lia| lia| exact FTV1| exact FTB| exact MI| exact MU| exact WM| exact SHF| exact K].
    - assert (cnt = 0%nat) as -> by lia. cbn [ms_mark] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end; [st_eq| exact FTV1| exact FTB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
