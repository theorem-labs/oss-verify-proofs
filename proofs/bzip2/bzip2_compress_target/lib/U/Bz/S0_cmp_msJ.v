(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2 CmpMsKit2 S0_cmp_msV.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2 CmpMsKit2 S0_cmp_msV.
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
Module S0_cmp_msI.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_gtu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msV.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
Lemma zsub_mod64 : forall a b : Z, Z_to_bv 64 (a mod 18446744073709551616 - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof. intros a b. apply Z_to_bv_eqm. rewrite (Zminus_mod a b). reflexivity. Qed.
Local Ltac UKit.u_norm ::= rewrite ?zext32_id, ?zsub_mod64.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
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
  Ltac scb_ex := match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end.

  (* [comment removed for export] *)
  Lemma S0_vswap1 : forall (lo hi : Z) (a2v : zarr) (f : nat) (c p1 p2 : Z) (a1 : zarr) (sb : scb)
      (xra x6 x7 x8 x9 x11 x12 x14 x15 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= c)%Z -> (c <= Z.of_nat f)%Z -> (0 <= lo)%Z -> (lo <= p1)%Z -> (p1 + c <= p2)%Z -> (p2 + c <= hi + 1)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x10' x13' x16' x17' x28' : word), let a1' := mvswap f a1 p1 p2 c in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells s0segs m' (p + 120) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' x8 x9 x10' x11 x12 x13' x14 x15 x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28' x29 x30 x31)
                       F (Z_to_bv 64 0x21438) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp (Z_to_bv 64 p2) x6 x7 x8 x9 (Z_to_bv 64 (A1 + 4 * p1)) x11 x12 (Z_to_bv 64 (c + 1)) x14 x15
                          (Z_to_bv 64 (A1 + 4 * p1)) (Z_to_bv 64 p1)
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x213c4) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi a2v. induction f as [|f IH]; [intros; lia|].
    intros c p1 p2 a1 sb xra x6 x7 x8 x9 x11 x12 x14 x15 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m
           Hc Hf Hlo Hp1 Hp12 Hp2 Hhi A1OK PR AR1 SCB MI MU WM K.
    msenv_open XOK. bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    rewrite mvswap_S in K. replace (0 <? c) with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (PR p1 ltac:(lia)) as P1. set (v1 := rd32 a1 p1) in *. assert (E1 : rd32 a1 p1 = v1) by reflexivity. clearbody v1.
    pose proof (PR p2 ltac:(lia)) as P2. set (v2 := rd32 a1 p2) in *. assert (E2 : rd32 a1 p2 = v2) by reflexivity. clearbody v2.
    (* [comment removed for export] *)
    urun_to 0x21404%Z.
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
    urun_to 0x21434%Z.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (c - 1)%Z (p1 + 1)%Z (p2 + 1)%Z a1s sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact PRs| exact AR1| scb_ex| assumption| assumption| assumption|].
      intros m' x5' x6' x7' x10' x13' x16' x17' x28'. cbv zeta. intros AR1' SCB' MI' MU' WM' OK' PR'.
      enter_with (K m' x5' x6' x7' x10' x13' x16' x17' x28'); [st_eq| exact AR1'| exact SCB'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'].
    - assert (c = 1)%Z by lia. subst c. rewrite mvswap_0 in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| scb_ex| assumption| assumption| assumption| exact OKs| exact PRs].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_vswap2 : forall (lo hi : Z) (a2v : zarr) (f : nat) (c p1 p2 : Z) (a1 : zarr) (sb : scb)
      (xra x5 x6 x7 x8 x9 x10 x11 x15 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= c)%Z -> (c <= Z.of_nat f)%Z -> (0 <= lo)%Z -> (lo <= p1)%Z -> (p1 + c <= p2)%Z -> (p2 + c <= hi + 1)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x12' x13' x14' x16' x17' : word), let a1' := mvswap f a1 p1 p2 c in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells s0segs m' (p + 120) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' x8 x9 x10 x11 x12' x13' x14' x15 x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21504) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (A1 + 4 * p1)) (Z_to_bv 64 (c + 1)) (Z_to_bv 64 p2) x15
                          (Z_to_bv 64 (A1 + 4 * p1)) (Z_to_bv 64 p1)
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21490) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi a2v. induction f as [|f IH]; [intros; lia|].
    intros c p1 p2 a1 sb xra x5 x6 x7 x8 x9 x10 x11 x15 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m
           Hc Hf Hlo Hp1 Hp12 Hp2 Hhi A1OK PR AR1 SCB MI MU WM K.
    msenv_open XOK. bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    rewrite mvswap_S in K. replace (0 <? c) with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (PR p1 ltac:(lia)) as P1. set (v1 := rd32 a1 p1) in *. assert (E1 : rd32 a1 p1 = v1) by reflexivity. clearbody v1.
    pose proof (PR p2 ltac:(lia)) as P2. set (v2 := rd32 a1 p2) in *. assert (E2 : rd32 a1 p2 = v2) by reflexivity. clearbody v2.
    (* [comment removed for export] *)
    urun_to 0x214cc%Z.
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
    urun_to 0x21500%Z.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (c - 1)%Z (p1 + 1)%Z (p2 + 1)%Z a1s sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact PRs| exact AR1| scb_ex| assumption| assumption| assumption|].
      intros m' x5' x6' x7' x12' x13' x14' x16' x17'. cbv zeta. intros AR1' SCB' MI' MU' WM' OK' PR'.
      enter_with (K m' x5' x6' x7' x12' x13' x14' x16' x17'); [st_eq| exact AR1'| exact SCB'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'].
    - assert (c = 1)%Z by lia. subst c. rewrite mvswap_0 in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| scb_ex| assumption| assumption| assumption| exact OKs| exact PRs].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
End S0_cmp_msI.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msJ.S0_cmp_msI.
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
Local Ltac UKit.u_norm ::= rewrite ?zext32_id, ?zsub_mod64.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac scb_ex := match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end.
  Ltac nx_step NX i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of NX with u32arr ?segs mm ?A ?ws =>
        let SO := fresh "SO" in
        pose proof (u32arr_store_ok segs mm A ws i _ NX ltac:(rewrite ?upd_length; lia) eq_refl) as SO
      end end;
    wstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of NX with u32arr ?segs m ?A ?ws =>
        let H := fresh "NXw" in let E := addr_expr ad in
        pose proof (u32arr_write segs m A ws i w NX ltac:(rewrite ?upd_length; lia)) as H;
        replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear NX; store_done; rename H into NX
      end end.
  Ltac xor_fix :=
    lazymatch goal with |- context [Z.lxor ?X ?Y] =>
      let E := fresh "EX" in
      assert (E : X = Y) by (rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r; reflexivity);
      rewrite E, Z.lxor_nilpotent; clear E; change (Z.b2z (0 <? 0)) with 0%Z
    end.
  Ltac q_tail K mm :=
    repeat match goal with H : u32arr _ mm _ (ovw _ _ _) |- _ => clear H end;
    repeat match goal with H : rw_cells _ mm _ _ |- _ => clear H end;
    repeat match goal with H : mem_inv _ mm |- _ => clear H end;
    let m' := fresh "m'" in let w1 := fresh "w" in let w2 := fresh "w" in
    let H1 := fresh "SLOn" in let H2 := fresh "SHIn" in let H3 := fresh "SDn" in let H4 := fresh "SCBn" in
    let H5 := fresh "MIn" in let H6 := fresh "MUn" in let H7 := fresh "WMn" in
    intros m' w1 w2 H1 H2 H3 H4 H5 H6 H7;
    transport_after_call s0segs mm m' H6 H7;
    match goal with HN : u32arr _ m' (p + 3668)%Z ?ws |- _ =>
      enter_with (K m' _ _ _ _ _ _ _ _ _ _ _ ws);
        [st_eq| exact H1| exact H2| exact H3| rewrite ?upd_length; lia| exact HN| exact H4| exact H5| assumption| assumption]
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S0_push3 : forall (qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (sb : scb)
      (xra x5 x8 x9 x16 x18 x19 x20 x21 x24 x25 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= qsp <= 98)%Z ->
    (forall v, In v [v0l; v0h; v0d; v1l; v1h; v1d; v2l; v2h; v2d] -> - 2147483648 <= v < 2147483648)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr s0segs m (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(p + 120, p + 336); (p + 3704, p + 4904)]%Z me m -> wmono s0segs me m ->
    (forall m' (x11' x12' : word),
      u32arr s0segs m' (p + 4504) (ovw (zset (zset (zset slo (qsp - 1) v0l) qsp v1l) (qsp + 1) v2l) Jlo 100) ->
      u32arr s0segs m' (p + 4104) (ovw (zset (zset (zset shi (qsp - 1) v0h) qsp v1h) (qsp + 1) v2h) Jhi 100) ->
      u32arr s0segs m' (p + 3704) (ovw (zset (zset (zset sd (qsp - 1) v0d) qsp v1d) (qsp + 1) v2d) Jd 100) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) (k144 sb) (k152 sb) (k168 sb) (k176 sb) (k184 sb)
                                       (Z_to_bv 64 (qsp + 2)) (k232 sb) (k240 sb) (k248 sb) (k256 sb) (k288 sb))) ->
      mem_inv s0segs m' -> munch [(p + 120, p + 336); (p + 3704, p + 4904)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 (Z_to_bv 64 v1h) (Z_to_bv 64 v1l) x8 x9
                            (Z_to_bv 64 (qsp + 2)) x11' x12' (Z_to_bv 64 v1d) (Z_to_bv 64 v2d) (Z_to_bv 64 v2h) x16 (Z_to_bv 64 v2l)
                            x18 x19 x20 x21 (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) x24 x25
                            (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1))) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21c0c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 (Z_to_bv 64 v1h) (Z_to_bv 64 v1l) x8 x9
                          (Z_to_bv 64 v0l) (Z_to_bv 64 v0h) (Z_to_bv 64 v0d) (Z_to_bv 64 v1d) (Z_to_bv 64 v2d) (Z_to_bv 64 v2h) x16 (Z_to_bv 64 v2l)
                          x18 x19 x20 x21 (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) x24 x25
                          (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1))) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21b2c) fc None m (seg_rom s0segs)).
  Proof.
    intros qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d slo shi sd Jlo Jhi Jd sb xra x5 x8 x9 x16 x18 x19 x20 x21 x24 x25 x28 x29 x30 x31 me m
           Hq HV LJlo LJhi LJd SLO SHI SD SCB MI MU WM K.
    msenv_open XOK. open_sc_in SCB.
    assert (R0l := HV v0l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R0h := HV v0h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R0d := HV v0d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])).
    assert (R1l := HV v1l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R1h := HV v1h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R1d := HV v1d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])).
    assert (R2l := HV v2l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R2h := HV v2h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R2d := HV v2d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). clear HV.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4504) _ (qsp - 1) _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store SLO (qsp - 1)%Z v0l (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4104) _ (qsp - 1) _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
    wstep. ovw_store SHI (qsp - 1)%Z v0h (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3704) _ (qsp - 1) _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
    wstep. ovw_store SD (qsp - 1)%Z v0d (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    urun_to 0x21b5c%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4504) _ qsp _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO4 end.
    wstep. ovw_store SLO qsp v1l (apply unsigned_lit_mod32).
    urun_to 0x21b78%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4104) _ qsp _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO5 end.
    wstep. ovw_store SHI qsp v1h (apply unsigned_lit_mod32).
    urun_to 0x21b90%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3704) _ qsp _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO6 end.
    wstep. ovw_store SD qsp v1d (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    urun_to 0x21bbc%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4504) _ (qsp + 1) _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO7 end.
    wstep. ovw_store SLO (qsp + 1)%Z v2l (apply unsigned_lit_mod32).
    urun_to 0x21bd8%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4104) _ (qsp + 1) _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO8 end.
    wstep. ovw_store SHI (qsp + 1)%Z v2h (apply unsigned_lit_mod32).
    urun_to 0x21c00%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3704) _ (qsp + 1) _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO9 end.
    wstep. ovw_store SD (qsp + 1)%Z v2d (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    urun_to 0x21c0c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
      [st_eq| exact SLO| exact SHI| exact SD| | assumption| assumption| assumption].
    scb_ex.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_qswap1 : forall (lo hi ltLo unLo unHi gtHi : Z) (a1 : zarr) (sb : scb)
      (xra x5 x6 x7 x8 x9 x13 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x10' x13' x16' x17' x28' : word),
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells s0segs m' (p + 120) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' x8 x9
                            x10' (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) x13' (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28' (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x21438) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                          (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) x13 (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x21380) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi a1 sb xra x5 x6 x7 x8 x9 x13 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x31 me m
           Hlo Hlt Hun Hgt Hhi A1OK PR AR1 SCB MI MU WM K.
    msenv_open XOK. bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    urun_to 0x213a0%Z.
    (* [comment removed for export] *)
    assert (JOIN : forall (x16' x17' : word),
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) (Z_to_bv 64 (mmin (ltLo - lo) (unLo - ltLo)))
                            (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x213a8) fc None m (seg_rom s0segs))).
    2:{ wstep; if_cases Kc; zify_cond_z Kc.
        - lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
            enter_with (JOIN r16 r17) end.
          unfold mmin. replace (ltLo - lo <? unLo - ltLo) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep.
          lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
            enter_with (JOIN r16 r17) end.
          unfold mmin. replace (ltLo - lo <? unLo - ltLo) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    intros x16' x17'.
    set (nn := mmin (ltLo - lo) (unLo - ltLo)) in *.
    assert (Hnn : (nn <= ltLo - lo /\ nn <= unLo - ltLo /\ (nn = ltLo - lo \/ nn = unLo - ltLo))%Z).
    { subst nn. unfold mmin. destruct (Z.ltb_spec (ltLo - lo) (unLo - ltLo)); lia. }
    clearbody nn.
    (* [comment removed for export] *)
    urun_to 0x213b4%Z.
    wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - (* [comment removed for export] *)
      rewrite mvswap_S in K. replace (0 <? nn) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| scb_ex| exact MI| exact MU| exact WM| exact A1OK| exact PR].
    - (* [comment removed for export] *)
      urun_to 0x213c4%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_vswap1 X Q XOK lo hi a1 (S (Z.to_nat nn)) nn lo (unLo - nn)%Z a1 sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| scb_ex| exact MI| apply munch_refl| apply wmono_refl|].
      intros m' x5' x6' x7' x10' x13' x16'' x17'' x28'. cbv zeta. intros AR1' SCB' MI' MU' WM' OK' PR'.
      clear AR1 MI SCB. transport_after_call s0segs m m' MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1'| exact SCB'| exact MI'| exact MU| exact WM| exact OK'| exact PR'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_qswap2 : forall (lo hi ltLo unLo unHi gtHi : Z) (a1 : zarr) (sb : scb)
      (xra x5 x6 x7 x8 x9 x10 x13 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x12' x13' x14' x16' x17' : word),
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1' := mvswap (S (Z.to_nat mm)) a1 unLo (hi - mm + 1) mm in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells s0segs m' (p + 120) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' x8 x9
                            (Z_to_bv 64 (gtHi - unHi)) (Z_to_bv 64 unLo) x12' x13' x14' (Z_to_bv 64 ltLo) x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x21504) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                          x10 (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) x13 (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x21438) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi a1 sb xra x5 x6 x7 x8 x9 x10 x13 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x31 me m
           Hlo Hlt Hun Hgt Hhi A1OK PR AR1 SCB MI MU WM K.
    msenv_open XOK. bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    urun_to 0x21458%Z.
    assert (JOIN : forall (x14' : word),
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 (gtHi - unHi)) (Z_to_bv 64 unLo) (Z_to_bv 64 (gtHi - unHi)) (Z_to_bv 64 (mmin (hi - gtHi) (gtHi - unHi))) x14'
                            (Z_to_bv 64 ltLo) x16 x17
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) x20 (Z_to_bv 64 2) x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x21460) fc None m (seg_rom s0segs))).
    2:{ wstep; if_cases Kc; zify_cond_z Kc.
        - lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?r14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
            enter_with (JOIN r14) end.
          unfold mmin. replace (hi - gtHi <? gtHi - unHi) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep.
          lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ ?r14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
            enter_with (JOIN r14) end.
          unfold mmin. replace (hi - gtHi <? gtHi - unHi) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    intros x14'.
    set (mm := mmin (hi - gtHi) (gtHi - unHi)) in *.
    assert (Hmm : (mm <= hi - gtHi /\ mm <= gtHi - unHi /\ (mm = hi - gtHi \/ mm = gtHi - unHi))%Z).
    { subst mm. unfold mmin. destruct (Z.ltb_spec (hi - gtHi) (gtHi - unHi)); lia. }
    clearbody mm.
    (* [comment removed for export] *)
    urun_to 0x21478%Z.
    wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - rewrite mvswap_S in K. replace (0 <? mm) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| scb_ex| exact MI| exact MU| exact WM| exact A1OK| exact PR].
    - (* [comment removed for export] *)
      urun_to 0x21490%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
        enter_with (S0_vswap2 X Q XOK lo hi a1 (S (Z.to_nat mm)) mm unLo (hi - mm + 1)%Z a1 sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm0 mm0) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| scb_ex| exact MI| apply munch_refl| apply wmono_refl|].
      intros m' x5' x6' x7' x12' x13' x14'' x16' x17'. cbv zeta. intros AR1' SCB' MI' MU' WM' OK' PR'.
      clear AR1 MI SCB. transport_after_call s0segs m m' MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1'| exact SCB'| exact MI'| exact MU| exact WM| exact OK'| exact PR'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_qnext : forall (lo hi d ltLo unLo gu qsp : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (nx : list word) (sb : scb)
      (xra x5 x6 x7 x9 x12 x13 x14 x16 x17 x18 x19 x20 x21 x25 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= hi + 1)%Z -> (0 <= gu <= hi + 1 - unLo)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 98)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u32arr s0segs m (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(p + 120, p + 336); (p + 3668, p + 4904)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x29' : word) (nx' : list word),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - gu + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      u32arr s0segs m' (p + 4504) (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr s0segs m' (p + 4104) (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr s0segs m' (p + 3704) (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) (k144 sb) (k152 sb) (k168 sb) (k176 sb) (k184 sb)
                                       (Z_to_bv 64 (qsp + 2)) (k232 sb) (k240 sb) (k248 sb) (k256 sb) (k288 sb))) ->
      mem_inv s0segs m' -> munch [(p + 120, p + 336); (p + 3668, p + 4904)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 (p + 3668)) x9
                            (Z_to_bv 64 (qsp + 2)) x11' x12' x13' x14' x15' x16' x17'
                            x18 x19 x20 x21 (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) (Z_to_bv 64 d) x25
                            (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1))) x28 x29' (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x21c0c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 (p + 3668)) x9
                          (Z_to_bv 64 gu) (Z_to_bv 64 unLo) x12 x13 x14 (Z_to_bv 64 ltLo) x16 x17
                          x18 x19 x20 x21 (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) (Z_to_bv 64 d) x25
                          (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1))) x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x21504) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d ltLo unLo gu qsp slo shi sd Jlo Jhi Jd nx sb xra x5 x6 x7 x9 x12 x13 x14 x16 x17 x18 x19 x20 x21 x25 x28 x31 me m
           Hlo Hlt Hun Hgu Hhi Hd Hq LJlo LJhi LJd LNX SLO SHI SD NX SCB MI MU WM K.
    msenv_open XOK. open_sc_in SCB.
    cbv zeta in K.
    set (kn := (lo + unLo - ltLo - 1)%Z) in K. set (km := (hi - gu + 1)%Z) in K. unfold srt2 in K. cbv beta iota delta [nsz] in K.
    (* [comment removed for export] *)
    urun_to 0x21548%Z.
    nx_step NX 0%Z. nx_step NX 3%Z. nx_step NX 6%Z.
    urun_to 0x21564%Z. nx_step NX 7%Z.
    urun_to 0x21578%Z. nx_step NX 4%Z.
    urun_to 0x21590%Z. nx_step NX 1%Z.
    urun_to 0x215ac%Z. nx_step NX 8%Z.
    urun_to 0x215c4%Z. nx_step NX 5%Z.
    urun_to 0x215e4%Z. nx_step NX 2%Z.
    (* [comment removed for export] *)
    urun_to 0x215fc%Z.
    wstep; if_cases Kc1; zify_cond_z Kc1.
    - (* [comment removed for export] *)
      replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
      urun_to 0x21a58%Z. xor_fix.
      urun_to 0x21a78%Z.
      (* [comment removed for export] *)
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        urun_to 0x21ae8%Z.
        (* [comment removed for export] *)
        wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
        * (* [comment removed for export] *)
          replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          nx_step NX 6%Z. nx_step NX 7%Z. nx_step NX 0%Z. nx_step NX 1%Z. nx_step NX 3%Z. nx_step NX 4%Z.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
      + (* [comment removed for export] *)
        replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        nx_step NX 4%Z. nx_step NX 5%Z. nx_step NX 7%Z. nx_step NX 8%Z.
        urun_to 0x21a9c%Z. nx_step NX 1%Z. nx_step NX 2%Z.
        (* [comment removed for export] *)
        urun_to 0x21ae8%Z.
        wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
        * (* [comment removed for export] *)
          replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          nx_step NX 6%Z. nx_step NX 7%Z. nx_step NX 0%Z. nx_step NX 1%Z. nx_step NX 3%Z. nx_step NX 4%Z.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
    - (* [comment removed for export] *)
      replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
      urun_to 0x21608%Z.
      nx_step NX 3%Z. nx_step NX 4%Z. nx_step NX 6%Z. nx_step NX 7%Z.
      (* [comment removed for export] *)
      urun_to 0x21a58%Z. xor_fix.
      urun_to 0x21a78%Z.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        urun_to 0x21ae8%Z.
        (* [comment removed for export] *)
        wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (hi - km <? kn - lo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
        * (* [comment removed for export] *)
          replace (hi - km <? kn - lo) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          nx_step NX 6%Z. nx_step NX 7%Z. nx_step NX 0%Z. nx_step NX 1%Z. nx_step NX 3%Z. nx_step NX 4%Z.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
      + (* [comment removed for export] *)
        replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        nx_step NX 4%Z. nx_step NX 5%Z. nx_step NX 7%Z. nx_step NX 8%Z.
        urun_to 0x21a9c%Z. nx_step NX 1%Z. nx_step NX 2%Z.
        (* [comment removed for export] *)
        urun_to 0x21ae8%Z.
        wstep; if_cases Kc3; zify_cond_z Kc3.
        * (* [comment removed for export] *)
          replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
        * (* [comment removed for export] *)
          replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          nx_step NX 6%Z. nx_step NX 7%Z. nx_step NX 0%Z. nx_step NX 1%Z. nx_step NX 3%Z. nx_step NX 4%Z.
          urun_to 0x21b2c%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (S0_push3 qsp (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z slo shi sd Jlo Jhi Jd sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
              [st_eq| lia| intros v Hv; cbn in Hv; lia| exact LJlo| exact LJhi| exact LJd| assumption| assumption| assumption| scb_ex| assumption| apply munch_refl| apply wmono_refl| ];
            q_tail K mm end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
