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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation W1 := [(A1, A1 + ARR1_SIZE)]%Z.

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
  Ltac ptr_at AR1 jj :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      assert (SO : store_ok a0segs mm (wa (A1 + 4 * jj)) 4 = true)
        by (eapply (u8arr_storeN_ok a0segs _ A1 _ (4 * jj) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]);
      wstep; sw_ptr AR1 jj; try clear SO end.

  (* [comment removed for export] *)
  Lemma A0_vswap1 : forall (lo hi : Z) (f : nat) (c p1 p2 : Z) (a1 : zarr) (x29 x30 : word)
      (x5 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word) (me m : word -> option byte),
    (1 <= c)%Z -> (c <= Z.of_nat f)%Z -> (0 <= lo)%Z -> (lo <= p1)%Z -> (p1 + c <= p2)%Z -> (p2 + c <= hi + 1)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> mem_inv a0segs m ->
    munch W1 me m -> wmono a0segs me m -> shzW a0segs W1 me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x29' x30' : word), let a1' := mvswap f a1 p1 p2 c in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> mem_inv a0segs m' ->
      munch W1 me m' -> wmono a0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 (Z_to_bv 64 (A1 + 4 * (p2 + c))) x7 (me_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A1 + 4 * (p1 + c))) (Z_to_bv 64 (A1 + 4 * (p2 + c))) (Z_to_bv 64 (A1 + 4 * (p1 + c))) x13 x14 x15 x16 x17 (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 1) x29' x30' x31)
                       F (Z_to_bv 64 0x99040) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 (Z_to_bv 64 (A1 + 4 * p2)) x7 (me_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A1 + 4 * p1)) (Z_to_bv 64 (A1 + 4 * p2)) (Z_to_bv 64 (A1 + 4 * p1)) x13 x14 x15 x16 x17 (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (c + 1)) x29 x30 x31)
                     F (Z_to_bv 64 0x98fd4) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi. induction f as [|f IH]; [intros; lia|].
    intros c p1 p2 a1 x29 x30 x5 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x31 me m
           Hc Hf Hlo Hp1 Hp12 Hp2 Hhi A1OK PR AR1 MI MU WM SH1 K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    rewrite mvswap_S in K. replace (0 <? c) with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (PR p1 ltac:(lia)) as P1. set (v1 := rd32 a1 p1) in *. assert (E1 : rd32 a1 p1 = v1) by reflexivity. clearbody v1.
    pose proof (PR p2 ltac:(lia)) as P2. set (v2 := rd32 a1 p2) in *. assert (E2 : rd32 a1 p2 = v2) by reflexivity. clearbody v2.
    (* [comment removed for export] *)
    arun. rdptr AR1 A1OK p1. rewrite E1. arun. rdptr AR1 A1OK p2. rewrite E2.
    arun. ptr_at AR1 p1. rewrite (unsigned_lit v2) in AR1 by lia.
    pose proof (zb8_length (wr32 a1 p1 v2) ARR1_SIZE ltac:(lia)) as L1b.
    arun. ptr_at AR1 p2. rewrite (unsigned_lit v1) in AR1 by lia.
    rewrite <- E1, <- E2 in AR1. change (wr32 (wr32 a1 p1 (rd32 a1 p2)) p2 (rd32 a1 p1)) with (mswap a1 p1 p2) in AR1.
    set (a1s := mswap a1 p1 p2) in *.
    assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
    assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (c - 1)%Z (p1 + 1)%Z (p2 + 1)%Z a1s _ _ x5 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x31 me mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact PRs| exact AR1| assumption| assumption| assumption| exact SH1|].
      intros m' x29' x30'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      enter_with (K m' x29' x30'); [st_eq| exact AR1'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'].
    - assert (c = 1)%Z by lia. subst c. rewrite mvswap_0 in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact AR1| assumption| assumption| assumption| exact OKs| exact PRs].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_vswap2 : forall (lo hi : Z) (f : nat) (c p1 p2 : Z) (a1 : zarr) (x28 x29 : word)
      (x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word) (me m : word -> option byte),
    (1 <= c)%Z -> (c <= Z.of_nat f)%Z -> (0 <= lo)%Z -> (lo <= p1)%Z -> (p1 + c <= p2)%Z -> (p2 + c <= hi + 1)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> mem_inv a0segs m ->
    munch W1 me m -> wmono a0segs me m -> shzW a0segs W1 me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x28' x29' : word), let a1' := mvswap f a1 p1 p2 c in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> mem_inv a0segs m' ->
      munch W1 me m' -> wmono a0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (A1 + 4 * (p1 + c))) (Z_to_bv 64 (A1 + 4 * (p2 + c))) (Z_to_bv 64 1) (me_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A1 + 4 * (p2 + c))) (Z_to_bv 64 (A1 + 4 * (p1 + c))) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 x28' x29' x30 x31)
                       F (Z_to_bv 64 0x990ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (A1 + 4 * p1)) (Z_to_bv 64 (A1 + 4 * p2)) (Z_to_bv 64 (c + 1)) (me_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A1 + 4 * p2)) (Z_to_bv 64 (A1 + 4 * p1)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x99080) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi. induction f as [|f IH]; [intros; lia|].
    intros c p1 p2 a1 x28 x29 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 me m
           Hc Hf Hlo Hp1 Hp12 Hp2 Hhi A1OK PR AR1 MI MU WM SH1 K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    rewrite mvswap_S in K. replace (0 <? c) with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (PR p1 ltac:(lia)) as P1. set (v1 := rd32 a1 p1) in *. assert (E1 : rd32 a1 p1 = v1) by reflexivity. clearbody v1.
    pose proof (PR p2 ltac:(lia)) as P2. set (v2 := rd32 a1 p2) in *. assert (E2 : rd32 a1 p2 = v2) by reflexivity. clearbody v2.
    (* [comment removed for export] *)
    arun. rdptr AR1 A1OK p1. rewrite E1. arun. rdptr AR1 A1OK p2. rewrite E2.
    arun. ptr_at AR1 p1. rewrite (unsigned_lit v2) in AR1 by lia.
    pose proof (zb8_length (wr32 a1 p1 v2) ARR1_SIZE ltac:(lia)) as L1b.
    arun. ptr_at AR1 p2. rewrite (unsigned_lit v1) in AR1 by lia.
    rewrite <- E1, <- E2 in AR1. change (wr32 (wr32 a1 p1 (rd32 a1 p2)) p2 (rd32 a1 p1)) with (mswap a1 p1 p2) in AR1.
    set (a1s := mswap a1 p1 p2) in *.
    assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
    assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (c - 1)%Z (p1 + 1)%Z (p2 + 1)%Z a1s _ _ x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 me mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact PRs| exact AR1| assumption| assumption| assumption| exact SH1|].
      intros m' x28' x29'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      enter_with (K m' x28' x29'); [st_eq| exact AR1'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'].
    - assert (c = 1)%Z by lia. subst c. rewrite mvswap_0 in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact AR1| assumption| assumption| assumption| exact OKs| exact PRs].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
