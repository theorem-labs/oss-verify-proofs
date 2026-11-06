(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasMs2 CmpMsKit2 S0_cmp_msV.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasMs2 CmpMsKit2 S0_cmp_msV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Module S0_cmp_msI.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasMs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutMS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMsKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_gtu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasMs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMsKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msV.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac sw_ptr AR1 j :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of AR1 with u8arr ?segs m ?A (zb8 ?a ?nn) =>
        let H := fresh "ARw" in
        pose proof (zb8_write4 segs m A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1
      end end.

  (* [comment removed for export] *)
  Lemma S0_vswap1 : forall (lo hi : Z) (a2v : zarr) (f : nat) (c p1 p2 : Z) (a1 : zarr) (x5 x16 : word)
      (xra x6 x7 x8 x10 x12 x13 x14 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 : word) (me m : word -> option byte),
    (1 <= c)%Z -> (c <= Z.of_nat f)%Z -> (0 <= lo)%Z -> (lo <= p1)%Z -> (p1 + c <= p2)%Z -> (p2 + c <= hi + 1)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x16' : word), let a1' := mvswap f a1 p1 p2 c in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6 x7 x8 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A1 + 4 * (p1 + c))) x10 (Z_to_bv 64 (A1 + 4 * (p2 + c))) x12 x13 x14 (Z_to_bv 64 (A1 + 4 * (p1 + c))) x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a098) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A1 + 4 * p1)) x10 (Z_to_bv 64 (A1 + 4 * p2)) x12 x13 x14 (Z_to_bv 64 (A1 + 4 * (p1 + c))) x16
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a07c) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi a2v. induction f as [|f IH]; [intros; lia|].
    intros c p1 p2 a1 x5 x16 xra x6 x7 x8 x10 x12 x13 x14 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me m
           Hc Hf Hlo Hp1 Hp12 Hp2 Hhi A1OK PR AR1 MI MU WM K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    rewrite mvswap_S in K. replace (0 <? c) with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (PR p1 ltac:(lia)) as P1. set (v1 := rd32 a1 p1) in *. assert (E1 : rd32 a1 p1 = v1) by reflexivity. clearbody v1.
    pose proof (PR p2 ltac:(lia)) as P2. set (v2 := rd32 a1 p2) in *. assert (E2 : rd32 a1 p2 = v2) by reflexivity. clearbody v2.
    (* [comment removed for export] *)
    rdptr AR1 A1OK p2. rewrite E2. rdptr AR1 A1OK p1. rewrite E1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * p1)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * p1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 p1. rewrite (unsigned_lit v2) in AR1 by lia.
    pose proof (zb8_length (wr32 a1 p1 v2) ARR1_SIZE ltac:(lia)) as L1b.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * p2)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * p2) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 p2. rewrite (unsigned_lit v1) in AR1 by lia.
    rewrite <- E1, <- E2 in AR1. change (wr32 (wr32 a1 p1 (rd32 a1 p2)) p2 (rd32 a1 p1)) with (mswap a1 p1 p2) in AR1.
    set (a1s := mswap a1 p1 p2) in *.
    assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
    assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
    (* [comment removed for export] *)
    wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (c - 1)%Z (p1 + 1)%Z (p2 + 1)%Z a1s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact PRs| exact AR1| assumption| assumption| assumption|].
      intros m' x5' x16'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      enter_with (K m' x5' x16'); [st_eq| exact AR1'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'].
    - assert (c = 1)%Z by lia. subst c. rewrite mvswap_0 in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact AR1| assumption| assumption| assumption| exact OKs| exact PRs].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_vswap2 : forall (lo hi : Z) (a2v : zarr) (f : nat) (c p1 p2 : Z) (a1 : zarr) (x15 x16 : word)
      (xra x5 x6 x7 x8 x10 x12 x13 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 : word) (me m : word -> option byte),
    (1 <= c)%Z -> (c <= Z.of_nat f)%Z -> (0 <= lo)%Z -> (lo <= p1)%Z -> (p1 + c <= p2)%Z -> (p2 + c <= hi + 1)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x15' x16' : word), let a1' := mvswap f a1 p1 p2 c in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A1 + 4 * (p1 + c))) x10 (Z_to_bv 64 (A1 + 4 * (p2 + c))) x12 x13 (Z_to_bv 64 (A1 + 4 * (p1 + c))) x15' x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a0f4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A1 + 4 * p1)) x10 (Z_to_bv 64 (A1 + 4 * p2)) x12 x13 (Z_to_bv 64 (A1 + 4 * (p1 + c))) x15 x16
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a0d8) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi a2v. induction f as [|f IH]; [intros; lia|].
    intros c p1 p2 a1 x15 x16 xra x5 x6 x7 x8 x10 x12 x13 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me m
           Hc Hf Hlo Hp1 Hp12 Hp2 Hhi A1OK PR AR1 MI MU WM K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    rewrite mvswap_S in K. replace (0 <? c) with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (PR p1 ltac:(lia)) as P1. set (v1 := rd32 a1 p1) in *. assert (E1 : rd32 a1 p1 = v1) by reflexivity. clearbody v1.
    pose proof (PR p2 ltac:(lia)) as P2. set (v2 := rd32 a1 p2) in *. assert (E2 : rd32 a1 p2 = v2) by reflexivity. clearbody v2.
    (* [comment removed for export] *)
    rdptr AR1 A1OK p2. rewrite E2. rdptr AR1 A1OK p1. rewrite E1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * p1)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * p1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 p1. rewrite (unsigned_lit v2) in AR1 by lia.
    pose proof (zb8_length (wr32 a1 p1 v2) ARR1_SIZE ltac:(lia)) as L1b.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * p2)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * p2) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 p2. rewrite (unsigned_lit v1) in AR1 by lia.
    rewrite <- E1, <- E2 in AR1. change (wr32 (wr32 a1 p1 (rd32 a1 p2)) p2 (rd32 a1 p1)) with (mswap a1 p1 p2) in AR1.
    set (a1s := mswap a1 p1 p2) in *.
    assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
    assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
    wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (c - 1)%Z (p1 + 1)%Z (p2 + 1)%Z a1s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact PRs| exact AR1| assumption| assumption| assumption|].
      intros m' x15' x16'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      enter_with (K m' x15' x16'); [st_eq| exact AR1'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'].
    - assert (c = 1)%Z by lia. subst c. rewrite mvswap_0 in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact AR1| assumption| assumption| assumption| exact OKs| exact PRs].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
End S0_cmp_msI.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasMs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMsKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msJ.S0_cmp_msI.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S0_push3 : forall (qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (sb : scb)
      (xra x8 x23 x24 x25 x30 x31 : word) (me m : word -> option byte),
    (1 <= qsp <= 98)%Z ->
    (forall v, In v [v0l; v0h; v0d; v1l; v1h; v1d; v2l; v2h; v2d] -> - 2147483648 <= v < 2147483648)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr s0segs m (p + 4424) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4024) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3624) (ovw sd Jd 100) ->
    rw_cells s0segs m (p + 144) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(p + 144, p + 292); (p + 3624, p + 4824)]%Z me m -> wmono s0segs me m ->
    (forall m' (x6' x7' x10' x11' x14' x15' : word),
      u32arr s0segs m' (p + 4424) (ovw (zset (zset (zset slo (qsp - 1) v0l) qsp v1l) (qsp + 1) v2l) Jlo 100) ->
      u32arr s0segs m' (p + 4024) (ovw (zset (zset (zset shi (qsp - 1) v0h) qsp v1h) (qsp + 1) v2h) Jhi 100) ->
      u32arr s0segs m' (p + 3624) (ovw (zset (zset (zset sd (qsp - 1) v0d) qsp v1d) (qsp + 1) v2d) Jd 100) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB (k144 sb) (k152 sb) (k168 sb) (k176 sb) (k184 sb) (k192 sb) (k200 sb) (k208 sb) (k216 sb)
                                       (Z_to_bv 64 (qsp + 2)) (k232 sb) (k240 sb) (k248 sb) (k256 sb) (k264 sb) (k272 sb) (k288 sb))) ->
      mem_inv s0segs m' -> munch [(p + 144, p + 292); (p + 3624, p + 4824)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x6' x7' (Z_to_bv 64 (p + 4424)) x8 (Z_to_bv 64 FT)
                            (Z_to_bv 64 v2l) x10' (Z_to_bv 64 v2h) (Z_to_bv 64 v2d) x11' x14' x15' (Z_to_bv 64 v1l)
                            (Z_to_bv 64 (qsp + 2)) x23 (Z_to_bv 64 A2) x24 (Z_to_bv 64 n) (Z_to_bv 64 (p + 4424 + 4 * (qsp - 1))) x25
                            (Z_to_bv 64 (p + 4024 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 3624 + 4 * (qsp - 1))) (Z_to_bv 64 A1)
                            (Z_to_bv 64 (p + 4024)) (Z_to_bv 64 (p + 3624)) x30 x31)
                       F (Z_to_bv 64 0x1a210) fc None m' (seg_rom s0segs))) ->
    forall (x6 x7 x28 x29 : word),
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp (Z_to_bv 64 v1d) x6 x7 x8 (Z_to_bv 64 FT)
                          (Z_to_bv 64 v2l) (Z_to_bv 64 v0h) (Z_to_bv 64 v2h) (Z_to_bv 64 v2d) (Z_to_bv 64 v1h) (Z_to_bv 64 v0d) (Z_to_bv 64 v0l) (Z_to_bv 64 v1l)
                          (Z_to_bv 64 qsp) x23 (Z_to_bv 64 A2) x24 (Z_to_bv 64 n) (Z_to_bv 64 (p + 4424 + 4 * (qsp - 1))) x25
                          (Z_to_bv 64 (p + 4024 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 3624 + 4 * (qsp - 1))) (Z_to_bv 64 A1)
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x1a19c) fc None m (seg_rom s0segs)).
  Proof.
    intros qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d slo shi sd Jlo Jhi Jd sb xra x8 x23 x24 x25 x30 x31 me m
           Hq HV LJlo LJhi LJd SLO SHI SD SCB MI MU WM K x6 x7 x28 x29.
    msenv_open XOK. open_sc_in SCB.
    assert (R0l := HV v0l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R0h := HV v0h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R0d := HV v0d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])).
    assert (R1l := HV v1l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R1h := HV v1h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R1d := HV v1d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])).
    assert (R2l := HV v2l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R2h := HV v2h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R2d := HV v2d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). clear HV.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4424) _ (qsp - 1) _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store SLO (qsp - 1)%Z v0l (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4024) _ (qsp - 1) _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
    wstep. ovw_store SHI (qsp - 1)%Z v0h (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3624) _ (qsp - 1) _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
    wstep. ovw_store SD (qsp - 1)%Z v0d (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    do 12 wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4424) _ qsp _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO4 end.
    wstep. ovw_store SLO qsp v1l (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4024) _ qsp _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO5 end.
    wstep. ovw_store SHI qsp v1h (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3624) _ qsp _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO6 end.
    wstep. ovw_store SD qsp v1d (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4424) _ (qsp + 1) _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO7 end.
    wstep. ovw_store SLO (qsp + 1)%Z v2l (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4024) _ (qsp + 1) _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO8 end.
    wstep. ovw_store SHI (qsp + 1)%Z v2h (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3624) _ (qsp + 1) _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO9 end.
    wstep. ovw_store SD (qsp + 1)%Z v2d (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _) end;
      [st_eq| exact SLO| exact SHI| exact SD| | assumption| assumption| assumption].
    match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_qswap1 : forall (lo hi ltLo unLo unHi gtHi b : Z) (a1 : zarr) (sb : scb)
      (xra x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x30 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    (- 2147483648 <= b < 2147483648)%Z -> k272 sb = Z_to_bv 64 b ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells s0segs m (p + 144) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x9' x11' x15' x16' : word),
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells s0segs m' (p + 144) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6 x7 x8 (Z_to_bv 64 FT)
                            x9' (Z_to_bv 64 ltLo) x11' (Z_to_bv 64 unLo) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) x15' x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 (Z_to_bv 64 b) x24 x25 (Z_to_bv 64 A1) x27 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x30)
                       F (Z_to_bv 64 0x1a098) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 ltLo) (Z_to_bv 64 (lo * 4)) (Z_to_bv 64 unLo) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) x15 x16
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x30)
                     F (Z_to_bv 64 0x1a040) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi b a1 sb xra x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x30 me m
           Hlo Hlt Hun Hgt Hhi Hb K272 A1OK PR AR1 SCB MI MU WM K.
    msenv_open XOK. bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    assert (JOIN : forall (x16' : word),
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 ltLo) (Z_to_bv 64 (lo * 4)) (Z_to_bv 64 unLo) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi)
                            (Z_to_bv 64 (mmin (ltLo - lo) (unLo - ltLo))) x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x30)
                       F (Z_to_bv 64 0x1a050) fc None m (seg_rom s0segs))).
    2:{ wstep; if_cases Kc; zify_cond_z Kc.
        - enter_with (JOIN (Z_to_bv 64 (unLo - ltLo))). unfold mmin. replace (ltLo - lo <? unLo - ltLo) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep. enter_with (JOIN (Z_to_bv 64 (unLo - ltLo))). unfold mmin. replace (ltLo - lo <? unLo - ltLo) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    intros x16'.
    set (nn := mmin (ltLo - lo) (unLo - ltLo)) in *.
    assert (Hnn : (nn <= ltLo - lo /\ nn <= unLo - ltLo /\ (nn = ltLo - lo \/ nn = unLo - ltLo))%Z).
    { subst nn. unfold mmin. destruct (Z.ltb_spec (ltLo - lo) (unLo - ltLo)); lia. }
    clearbody nn.
    (* [comment removed for export] *)
    wstep. rewrite K272. wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - (* [comment removed for export] *)
      rewrite mvswap_S in K. replace (0 <? nn) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
        [st_eq| exact AR1| | exact MI| exact MU| exact WM| exact A1OK| exact PR].
      match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. rewrite zext32_x4. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_vswap1 X Q XOK lo hi a1 (S (Z.to_nat nn)) nn lo (unLo - nn)%Z a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact MI| apply munch_refl| apply wmono_refl|].
      intros m' x5' x16''. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      clear AR1 MI. transport_after_call s0segs m m' MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
        [st_eq| exact AR1'| | exact MI'| exact MU| exact WM| exact OK'| exact PR'].
      match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_qswap2 : forall (lo hi ltLo unLo unHi gtHi b : Z) (a1 : zarr) (sb : scb)
      (xra x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x20 x22 x24 x25 x27 x30 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    (- 2147483648 <= b < 2147483648)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells s0segs m (p + 144) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x9' x11' x14' x15' x16' : word),
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1' := mvswap (S (Z.to_nat mm)) a1 unLo (hi - mm + 1) mm in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells s0segs m' (p + 144) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                            x9' (Z_to_bv 64 ltLo) x11' (Z_to_bv 64 unLo) (Z_to_bv 64 (gtHi - unHi)) x14' x15' x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 (Z_to_bv 64 b) x24 x25 (Z_to_bv 64 A1) x27 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x30)
                       F (Z_to_bv 64 0x1a0f4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                          x9 (Z_to_bv 64 ltLo) x11 (Z_to_bv 64 unLo) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) x15 x16
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 (Z_to_bv 64 b) x24 x25 (Z_to_bv 64 A1) x27 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x30)
                     F (Z_to_bv 64 0x1a098) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi b a1 sb xra x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x20 x22 x24 x25 x27 x30 me m
           Hlo Hlt Hun Hgt Hhi Hb A1OK PR AR1 SCB MI MU WM K.
    msenv_open XOK. bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    wstep. wstep.
    assert (JOIN :
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (mmin (hi - gtHi) (gtHi - unHi))) (Z_to_bv 64 ltLo) x11 (Z_to_bv 64 unLo) (Z_to_bv 64 (gtHi - unHi)) (Z_to_bv 64 unHi) x15 x16
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 (Z_to_bv 64 b) x24 x25 (Z_to_bv 64 A1) x27 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x30)
                       F (Z_to_bv 64 0x1a0a8) fc None m (seg_rom s0segs))).
    2:{ wstep; if_cases Kc; zify_cond_z Kc.
        - enter_with JOIN. unfold mmin. replace (hi - gtHi <? gtHi - unHi) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep. enter_with JOIN. unfold mmin. replace (hi - gtHi <? gtHi - unHi) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    set (mm := mmin (hi - gtHi) (gtHi - unHi)) in *.
    assert (Hmm : (mm <= hi - gtHi /\ mm <= gtHi - unHi /\ (mm = hi - gtHi \/ mm = gtHi - unHi))%Z).
    { subst mm. unfold mmin. destruct (Z.ltb_spec (hi - gtHi) (gtHi - unHi)); lia. }
    clearbody mm.
    (* [comment removed for export] *)
    wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - rewrite mvswap_S in K. replace (0 <? mm) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _) end;
        [st_eq| exact AR1| | exact MI| exact MU| exact WM| exact A1OK| exact PR].
      match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. rewrite zext32_x4. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
        enter_with (S0_vswap2 X Q XOK lo hi a1 (S (Z.to_nat mm)) mm unLo (hi - mm + 1)%Z a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm0 mm0) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact MI| apply munch_refl| apply wmono_refl|].
      intros m' x15' x16'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      clear AR1 MI. transport_after_call s0segs m m' MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _) end;
        [st_eq| exact AR1'| | exact MI'| exact MU| exact WM| exact OK'| exact PR'].
      match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_qnext : forall (lo hi d ltLo unLo gu qsp b : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (sb : scb)
      (xra x5 x6 x7 x9 x11 x14 x15 x16 x25 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= hi + 1)%Z -> (0 <= gu <= hi + 1 - unLo)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 98)%Z -> (- 2147483648 <= b < 2147483648)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr s0segs m (p + 4424) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4024) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3624) (ovw sd Jd 100) ->
    rw_cells s0segs m (p + 144) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(p + 144, p + 292); (p + 3624, p + 4824)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' : word),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - gu + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      u32arr s0segs m' (p + 4424) (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr s0segs m' (p + 4024) (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr s0segs m' (p + 3624) (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB (k144 sb) (k152 sb) (k168 sb) (k176 sb) (k184 sb) (k192 sb) (k200 sb) (k208 sb) (k216 sb)
                                       (Z_to_bv 64 (qsp + 2)) (k232 sb) (k240 sb) (k248 sb) (k256 sb) (k264 sb) (k272 sb) (k288 sb))) ->
      mem_inv s0segs m' -> munch [(p + 144, p + 292); (p + 3624, p + 4824)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x9' x10' x11' x12' x13' x14' x15' x16'
                            (Z_to_bv 64 (qsp + 2)) x25 (Z_to_bv 64 A2) (Z_to_bv 64 20) (Z_to_bv 64 n) (Z_to_bv 64 (p + 4424 + 4 * (qsp - 1))) (Z_to_bv 64 b)
                            (Z_to_bv 64 (p + 4024 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 3624 + 4 * (qsp - 1))) (Z_to_bv 64 A1)
                            (Z_to_bv 64 (p + 4024)) (Z_to_bv 64 (p + 3624)) (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x1a210) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 d) (Z_to_bv 64 FT)
                          x9 (Z_to_bv 64 ltLo) x11 (Z_to_bv 64 unLo) (Z_to_bv 64 gu) x14 x15 x16
                          (Z_to_bv 64 qsp) x25 (Z_to_bv 64 A2) (Z_to_bv 64 20) (Z_to_bv 64 n) (Z_to_bv 64 (p + 4424 + 4 * (qsp - 1))) (Z_to_bv 64 b)
                          (Z_to_bv 64 (p + 4024 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 3624 + 4 * (qsp - 1))) (Z_to_bv 64 A1)
                          x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x1a0f4) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d ltLo unLo gu qsp b slo shi sd Jlo Jhi Jd sb xra x5 x6 x7 x9 x11 x14 x15 x16 x25 x28 x31 me m
           Hlo Hlt Hun Hgu Hhi Hd Hq Hb LJlo LJhi LJd SLO SHI SD SCB MI MU WM K.
    msenv_open XOK. open_sc_in SCB.
    cbv zeta in K.
    set (kn := (lo + unLo - ltLo - 1)%Z) in K. set (km := (hi - gu + 1)%Z) in K. unfold srt2 in K. cbv beta iota delta [nsz] in K.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kc1; zify_cond_z Kc1.
    - (* [comment removed for export] *)
      replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
      wstep. wstep. wstep. wstep. wstep.
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        wstep. wstep. wstep. wstep. wstep. wstep. wstep.
        (* [comment removed for export] *)
        wstep. wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
        * (* [comment removed for export] *)
          replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
      + (* [comment removed for export] *)
        replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        wstep. wstep. wstep. wstep.
        (* [comment removed for export] *)
        wstep. wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
        * (* [comment removed for export] *)
          replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
    - (* [comment removed for export] *)
      replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
      wstep. wstep. wstep.
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        wstep. wstep. wstep. wstep. wstep. wstep. wstep.
        (* [comment removed for export] *)
        wstep. wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (hi - km <? kn - lo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
        * (* [comment removed for export] *)
          replace (hi - km <? kn - lo) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
      + (* [comment removed for export] *)
        replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        wstep. wstep. wstep. wstep.
        (* [comment removed for export] *)
        wstep. wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
        * (* [comment removed for export] *)
          replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          wstep. wstep. wstep. wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ mm mm) end;
            [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| exact SLO| exact SHI| exact SD| | exact MI| apply munch_refl| apply wmono_refl| ].
          { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
          intros m' x6' x7' x10' x11' x14' x15'. intros SLO' SHI' SD' SCB' MI' MU' WM'.
          clear SLO SHI SD MI. match goal with H : rw_cells _ m (p + 144)%Z _ |- _ => clear H end.
          transport_after_call s0segs m m' MU' WM'.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCB'| exact MI'| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
