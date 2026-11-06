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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_msG.
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
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
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
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.

  (* [comment removed for export] *)
  Lemma S0_plo : forall (lo hi d med unHi gtHi : Z) (a2 : zarr)
      (xra x10 x12 x18 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (f : nat) (unLo ltLo : Z) (a1 : zarr) (x5 x6 x27 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < Z.of_nat f)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' x6' x7' x16' x27' : word), let p' := mpart_lo f a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unHi p' = unHi -> mp_gtHi p' = gtHi ->
      (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (unLo <= mp_unLo p' <= unHi + 1)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x10 (Z_to_bv 64 (mp_ltLo p')) x12 (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) (Z_to_bv 64 med) x16'
                            x18 x19 (Z_to_bv 64 A2) x21 (Z_to_bv 64 n) x23 x24 x25 x26 (Z_to_bv 64 A1) x27' x28 x29 x30)
                       F (Z_to_bv 64 0x19d2c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp (Z_to_bv 64 (A1 + 4 * unLo)) x6 (Z_to_bv 64 (unHi - unLo + 1)) (Z_to_bv 64 d) (Z_to_bv 64 FT)
                          x10 (Z_to_bv 64 ltLo) x12 (Z_to_bv 64 unLo) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) (Z_to_bv 64 med) (Z_to_bv 64 unHi)
                          x18 x19 (Z_to_bv 64 A2) x21 (Z_to_bv 64 n) x23 x24 x25 x26 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x19ccc) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d med unHi gtHi a2 xra x10 x12 x18 x19 x21 x23 x24 x25 x26 x28 x29 x30 x31.
    induction f as [|f IH]; [intros; lia|].
    intros unLo ltLo a1 x5 x6 x27 me m Hlo Hlt Hun Hgt Hhi Hd Hmed A1OK A2OK PR Hf AR1 AR2 MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite mpart_lo_S in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
    replace (unHi <? unLo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv zeta in K.
    pose proof (PR unLo ltac:(lia)) as Pu. set (pu := rd32 a1 unLo) in *.
    assert (Epu : rd32 a1 unLo = pu) by reflexivity. clearbody pu.
    (* [comment removed for export] *)
    rdptr AR1 A1OK unLo. rewrite Epu. wstep. wstep. wstep. rewrite zext32_id. wstep.
    rdblk AR2 A2OK (pu + d)%Z. unfold rd8 in K.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - (* [comment removed for export] *)
      replace (zget a2 (pu + d) - med =? 0) with true in K by (symmetry; apply Z.eqb_eq; lia).
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      pose proof (PR ltLo ltac:(lia)) as Pl. set (pl := rd32 a1 ltLo) in *. assert (Epl : rd32 a1 ltLo = pl) by reflexivity. clearbody pl.
      wstep. wstep. rdptr AR1 A1OK ltLo. rewrite Epl. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO : store_ok s0segs mm (wa (A1 + 4 * unLo)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * unLo) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 unLo. rewrite (unsigned_lit pl) in AR1 by lia.
      pose proof (zb8_length (wr32 a1 unLo pl) ARR1_SIZE ltac:(lia)) as L1b.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * ltLo)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * ltLo) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 ltLo. rewrite (unsigned_lit pu) in AR1 by lia.
      change (wr32 (wr32 a1 unLo pl) ltLo pu) with (wr32 (wr32 a1 unLo (rd32 a1 ltLo)) ltLo (rd32 a1 unLo)) in AR1 || (rewrite <- Epl, <- Epu in AR1).
      change (wr32 (wr32 a1 unLo (rd32 a1 ltLo)) ltLo (rd32 a1 unLo)) with (mswap a1 unLo ltLo) in AR1.
      set (a1s := mswap a1 unLo ltLo) in *.
      assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
      assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
      (* [comment removed for export] *)
      wstep.
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        wstep. wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|]. wstep. wstep. wstep. wstep. wstep. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (unLo + 1)%Z (ltLo + 1)%Z a1s _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact A2OK| exact PRs| lia| exact AR1| exact AR2| assumption| assumption| assumption|].
        intros m' x5' x6' x7' x16' x27'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2.
        eapply (K m' x5' x6' x7' x16' x27'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia].
      + (* [comment removed for export] *)
        wstep. wstep.
        assert (EQ : mpart_lo f a2 d med (MP a1s (unLo + 1) unHi (ltLo + 1) gtHi) = MP a1s (unLo + 1) unHi (ltLo + 1) gtHi).
        { destruct f as [|f']; [reflexivity|]. rewrite mpart_lo_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
          replace (unHi <? unLo + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact OKs| exact PRs| reflexivity| reflexivity| lia| lia].
    - replace (zget a2 (pu + d) - med =? 0) with false in K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kg; zify_cond_z Kg.
      + replace (0 <? zget a2 (pu + d) - med) with true in K by (symmetry; apply Z.ltb_lt; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
      + replace (0 <? zget a2 (pu + d) - med) with false in K by (symmetry; apply Z.ltb_ge; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        wstep; if_cases Kc; zify_cond_z Kc.
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (IH (unLo + 1)%Z ltLo a1 _ _ _ me mm) end;
            [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| assumption| assumption| assumption| ].
          intros m' x5' x6' x7' x16' x27'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2.
          eapply (K m' x5' x6' x7' x16' x27'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia].
        * wstep. wstep.
          assert (EQ : mpart_lo f a2 d med (MP a1 (unLo + 1) unHi ltLo gtHi) = MP a1 (unLo + 1) unHi ltLo gtHi).
          { destruct f as [|f']; [reflexivity|]. rewrite mpart_lo_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
            replace (unHi <? unLo + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.


  (* [comment removed for export] *)
  Lemma S0_phi : forall (lo hi d med unLo ltLo : Z) (a2 : zarr)
      (xra x9 x11 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 : word)
      (f : nat) (unHi gtHi u0 : Z) (a1 : zarr) (x6 x26 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (unHi <= u0 <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < Z.of_nat f)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5' : word), let p' := mpart_hi f a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unLo p' = unLo -> mp_ltLo p' = ltLo ->
      (unLo <= mp_unHi p' <= unHi)%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      (zget a2 (rd32 (mp_a1 p') (mp_unHi p') + d) < med)%Z -> (mp_unHi p' <= bv_unsigned x5' <= hi)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp (Z_to_bv 64 (A1 + 4 * mp_unHi p')) (Z_to_bv 64 (mp_unHi p' + 1)) (Z_to_bv 64 (rd32 (mp_a1 p') (mp_unHi p'))) (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x9 (Z_to_bv 64 ltLo) x11 (Z_to_bv 64 unLo) (Z_to_bv 64 (mp_gtHi p')) x5' (Z_to_bv 64 med) (Z_to_bv 64 (mp_unHi p'))
                            x16 x17 (Z_to_bv 64 A2) x18 (Z_to_bv 64 n) x20 x22 x23 x24 (Z_to_bv 64 A1) (Z_to_bv 64 (zget a2 (rd32 (mp_a1 p') (mp_unHi p') + d))) x27 x28 x29)
                       F (Z_to_bv 64 0x19d9c) fc None m' (seg_rom s0segs))) ->
    (forall m' (x4' x5' x6' x16' x26' : word), let p' := mpart_hi f a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unLo p' = unLo -> mp_ltLo p' = ltLo ->
      (mp_unHi p' < unLo)%Z -> (unLo <= mp_unHi p' + 1)%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x4' x5' x6' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x9 (Z_to_bv 64 ltLo) x11 (Z_to_bv 64 unLo) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 med) x16'
                            x16 x17 (Z_to_bv 64 A2) x18 (Z_to_bv 64 n) x20 x22 x23 x24 (Z_to_bv 64 A1) x26' x27 x28 x29)
                       F (Z_to_bv 64 0x19dcc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp (Z_to_bv 64 (A1 + 4 * unHi)) (Z_to_bv 64 (unHi + 1)) x6 (Z_to_bv 64 d) (Z_to_bv 64 FT)
                          x9 (Z_to_bv 64 ltLo) x11 (Z_to_bv 64 unLo) (Z_to_bv 64 gtHi) (Z_to_bv 64 u0) (Z_to_bv 64 med) (Z_to_bv 64 unHi)
                          x16 x17 (Z_to_bv 64 A2) x18 (Z_to_bv 64 n) x20 x22 x23 x24 (Z_to_bv 64 A1) x26 x27 x28 x29)
                     F (Z_to_bv 64 0x19d44) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d med unLo ltLo a2 xra x9 x11 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30.
    induction f as [|f IH]; [intros; lia|].
    intros unHi gtHi u0 a1 x6 x26 me m Hlo Hlt Hun Hgt Hu0 Hhi Hd Hmed A1OK A2OK PR Hf AR1 AR2 MI MU WM K1 K2.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite mpart_hi_S in K1, K2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1, K2.
    replace (unHi <? unLo) with false in K1, K2 by (symmetry; apply Z.ltb_ge; lia). cbv zeta in K1. cbv zeta in K2.
    pose proof (PR unHi ltac:(lia)) as Pu. set (pu := rd32 a1 unHi) in *.
    assert (Epu : rd32 a1 unHi = pu) by reflexivity. clearbody pu.
    (* [comment removed for export] *)
    rdptr AR1 A1OK unHi. rewrite Epu. wstep. wstep. wstep. rewrite zext32_id. wstep.
    rdblk AR2 A2OK (pu + d)%Z. unfold rd8 in K1, K2.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - replace (zget a2 (pu + d) - med =? 0) with true in K1, K2 by (symmetry; apply Z.eqb_eq; lia).
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1, K2.
      pose proof (PR gtHi ltac:(lia)) as Pg. set (pg := rd32 a1 gtHi) in *. assert (Epg : rd32 a1 gtHi = pg) by reflexivity. clearbody pg.
      (* [comment removed for export] *)
      wstep. wstep. rdptr AR1 A1OK gtHi. rewrite Epg. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO : store_ok s0segs mm (wa (A1 + 4 * unHi)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * unHi) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 unHi. rewrite (unsigned_lit pg) in AR1 by lia.
      pose proof (zb8_length (wr32 a1 unHi pg) ARR1_SIZE ltac:(lia)) as L1b.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * gtHi)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * gtHi) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 gtHi. rewrite (unsigned_lit pu) in AR1 by lia.
      rewrite <- Epg, <- Epu in AR1.
      change (wr32 (wr32 a1 unHi (rd32 a1 gtHi)) gtHi (rd32 a1 unHi)) with (mswap a1 unHi gtHi) in AR1.
      set (a1s := mswap a1 unHi gtHi) in *.
      assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
      assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
      (* [comment removed for export] *)
      wstep.
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        wstep. wstep. wstep. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (unHi - 1)%Z (gtHi - 1)%Z (unHi - 1)%Z a1s _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact A2OK| exact PRs| lia| exact AR1| exact AR2| assumption| assumption| assumption| |].
        * intros m' x5'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3 B4.
          eapply (K1 m' x5'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| exact B3| lia].
        * intros m' x4' x5' x6' x16' x26'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3.
          eapply (K2 m' x4' x5' x6' x16' x26'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| lia].
      + (* [comment removed for export] *)
        wstep. wstep. wstep.
        assert (EQ : mpart_hi f a2 d med (MP a1s unLo (unHi - 1) ltLo (gtHi - 1)) = MP a1s unLo (unHi - 1) ltLo (gtHi - 1)).
        { destruct f as [|f']; [reflexivity|]. rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
          replace (unHi - 1 <? unLo) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        rewrite EQ in K2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K2.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K2 mm _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact OKs| exact PRs| reflexivity| reflexivity| lia| lia| lia].
    - replace (zget a2 (pu + d) - med =? 0) with false in K1, K2 by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kg; zify_cond_z Kg.
      + replace (zget a2 (pu + d) - med <? 0) with true in K1 by (symmetry; apply Z.ltb_lt; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1. rewrite <- Epu.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm (Z_to_bv 64 u0)) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia| rewrite Epu; lia| rewrite unsigned_lit by lia; lia].
      + replace (zget a2 (pu + d) - med <? 0) with false in K1, K2 by (symmetry; apply Z.ltb_ge; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1, K2.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        wstep; if_cases Kc; zify_cond_z Kc.
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (IH (unHi - 1)%Z gtHi u0 a1 _ _ me mm) end;
            [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| assumption| assumption| assumption| |].
          -- intros m' x5'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3 B4.
             eapply (K1 m' x5'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| exact B3| lia].
          -- intros m' x4' x5' x6' x16' x26'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3.
             eapply (K2 m' x4' x5' x6' x16' x26'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| lia].
        * (* [comment removed for export] *)
          wstep. wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|]. wstep. wstep.
          assert (EQ : mpart_hi f a2 d med (MP a1 unLo (unHi - 1) ltLo gtHi) = MP a1 unLo (unHi - 1) ltLo gtHi).
          { destruct f as [|f']; [reflexivity|]. rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
            replace (unHi - 1 <? unLo) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          rewrite EQ in K2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K2.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K2 mm _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
End S0_cmp_msG.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasMs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMsKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msH.S0_cmp_msG.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
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
  Lemma S0_part : forall (lo hi d med : Z) (sz : nat) (a2 : zarr)
      (xra x9 x11 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 : word)
      (f : nat) (unLo unHi ltLo gtHi : Z) (a1 : zarr) (x4 x6 x12 x15 x26 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    (Z.of_nat sz = hi - lo + 1)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < 2 * Z.of_nat f)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x4' x5' x6' x15' x26' : word), let p' := mpart_loop f sz a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) ->
      (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (mp_unHi p' < mp_unLo p')%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x4' x5' x6' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x9 (Z_to_bv 64 (mp_ltLo p')) x11 (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 med) x15'
                            x16 x17 (Z_to_bv 64 A2) x18 (Z_to_bv 64 n) x20 x22 x23 x24 (Z_to_bv 64 A1) x26' x27 x28 x29)
                       F (Z_to_bv 64 0x19dcc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x4 (Z_to_bv 64 unLo) x6 (Z_to_bv 64 d) (Z_to_bv 64 FT)
                          x9 (Z_to_bv 64 ltLo) x11 x12 (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) (Z_to_bv 64 med) x15
                          x16 x17 (Z_to_bv 64 A2) x18 (Z_to_bv 64 n) x20 x22 x23 x24 (Z_to_bv 64 A1) x26 x27 x28 x29)
                     F (Z_to_bv 64 0x19ca8) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d med sz a2 xra x9 x11 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29.
    induction f as [|f IH]; [intros; lia|].
    intros unLo unHi ltLo gtHi a1 x4 x6 x12 x15 x26 me m Hlo Hlt Hun Hgt Hhi Hd Hmed Hsz A1OK A2OK PR Hf AR1 AR2 MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite mpart_loop_S in K.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|]. wstep. wstep. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_plo X Q XOK XSEP lo hi d med unHi gtHi a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S sz) unLo ltLo a1 _ _ _ me mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| exact MI| exact MU| exact WM|].
    intros m1 y5 y6 y7 y16 y27. cbv zeta. intros AR1_1 AR2_1 MI1 MU1 WM1 OK1 PR1 U1 G1 B1 B2.
    set (p1 := mpart_lo (S sz) a2 d med (MP a1 unLo unHi ltLo gtHi)) in *.
    destruct p1 as [a1p unLo1 unHi1 ltLo1 gtHi1] eqn:EP1. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unHi1 gtHi1.
    cbv zeta in K. bz_params.
    pose proof (zb8_length a1p ARR1_SIZE ltac:(lia)) as L1p.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    { assert (EQ : mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi) = MP a1p unLo1 unHi ltLo1 gtHi).
      { rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi <? unLo1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      replace (unHi <? unLo1) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
        [st_eq| exact AR1_1| exact AR2_1| exact MI1| exact MU1| exact WM1| exact OK1| exact PR1| lia| lia| lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_phi X Q XOK XSEP lo hi d med unLo1 ltLo1 a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S sz) unHi gtHi unHi a1p _ _ me mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact OK1| exact A2OK| exact PR1| lia| exact AR1_1| exact AR2_1| exact MI1| exact MU1| exact WM1| |].
    - (* [comment removed for export] *)
      intros m2 z5. cbv zeta. intros AR1_2 AR2_2 MI2 MU2 WM2 OK2 PR2 U2 G2 C1 C2 C3 C4.
      set (p2 := mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi)) in *.
      destruct p2 as [a1q unLo2 unHi2 ltLo2 gtHi2] eqn:EP2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unLo2 ltLo2.
      replace (unHi2 <? unLo1) with false in K by (symmetry; apply Z.ltb_ge; lia).
      bz_params.
      pose proof (zb8_length a1q ARR1_SIZE ltac:(lia)) as L1q.
      pose proof (PR2 unLo1 ltac:(lia)) as Pl. set (pl := rd32 a1q unLo1) in *. assert (Epl : rd32 a1q unLo1 = pl) by reflexivity. clearbody pl.
      pose proof (PR2 unHi2 ltac:(lia)) as Ph. set (ph := rd32 a1q unHi2) in *. assert (Eph : rd32 a1q unHi2 = ph) by reflexivity. clearbody ph.
      wstep. wstep. rdptr AR1_2 OK2 unLo1. rewrite Epl. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO : store_ok s0segs mm (wa (A1 + 4 * unLo1)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * unLo1) 4 _ AR1_2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1_2 unLo1. rewrite (unsigned_lit ph) in AR1_2 by lia.
      pose proof (zb8_length (wr32 a1q unLo1 ph) ARR1_SIZE ltac:(lia)) as L1r.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * unHi2)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * unHi2) 4 _ AR1_2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1_2 unHi2. rewrite (unsigned_lit pl) in AR1_2 by lia.
      rewrite <- Eph, <- Epl in AR1_2.
      change (wr32 (wr32 a1q unLo1 (rd32 a1q unHi2)) unHi2 (rd32 a1q unLo1)) with (mswap a1q unLo1 unHi2) in AR1_2.
      set (a1s := mswap a1q unLo1 unHi2) in *.
      assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact OK2).
      assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
      wstep.
      (* [comment removed for export] *)
      wstep; if_cases Ke; zify_cond_z Ke.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (unLo1 + 1)%Z (unHi2 - 1)%Z ltLo1 gtHi2 a1s _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact A2OK| exact PRs| lia| exact AR1_2| exact AR2_2| assumption| assumption| assumption|].
        intros m' x4' x5' x6' x15' x26'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' V1 V2 V3.
        eapply (K m' x4' x5' x6' x15' x26'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia| lia].
      + (* [comment removed for export] *)
        wstep. wstep. wstep. wstep; if_cases Kg; zify_cond_z Kg; [| exfalso; lia].
        assert (EQ : mpart_loop f sz a2 d med (MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2) = MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2).
        { destruct f as [|f']; [reflexivity|]. rewrite mpart_loop_S.
          assert (E1 : mpart_lo (S sz) a2 d med (MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2) = MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2).
          { rewrite mpart_lo_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi2 - 1 <? unLo1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          cbv zeta. rewrite E1.
          assert (E2 : mpart_hi (S sz) a2 d med (MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2) = MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2).
          { rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi2 - 1 <? unLo1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          rewrite E2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi2 - 1 <? unLo1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact AR1_2| exact AR2_2| assumption| assumption| assumption| exact OKs| exact PRs| lia| lia| lia].
    - (* [comment removed for export] *)
      intros m2 z4 z5 z6 z16 z26. cbv zeta. intros AR1_2 AR2_2 MI2 MU2 WM2 OK2 PR2 U2 G2 C1 C2 C3.
      set (p2 := mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi)) in *.
      destruct p2 as [a1q unLo2 unHi2 ltLo2 gtHi2] eqn:EP2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unLo2 ltLo2.
      replace (unHi2 <? unLo1) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      eapply (K m2 z4 z5 z6 z16 z26); [exact AR1_2| exact AR2_2| exact MI2| exact MU2| exact WM2| exact OK2| exact PR2| lia| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
