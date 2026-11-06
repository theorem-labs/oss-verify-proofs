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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - A2)%Z.
  Notation W1 := [(A1, A1 + ARR1_SIZE)]%Z.
  (* [comment removed for export] *)

  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac sw_ptr AR1 j v :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of AR1 with u8arr ?segs mm ?A (zb8 ?a ?nn) =>
        let SO := fresh "SO" in
        assert (SO : store_ok segs mm (wa (A + 4 * j)) 4 = true)
          by (eapply (u8arr_storeN_ok segs mm A _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]);
        wstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?ad (le4 ?w)) _) =>
          let H := fresh "ARw" in
          pose proof (zb8_write4 segs mm A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1;
          rewrite unsigned_lit in AR1 by lia;
          lazymatch type of AR1 with u8arr _ _ _ (zb8 (wr32 _ _ ?x) _) => replace x with v in AR1 by lia end
        end; try clear SO end end.
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  Ltac key_left j :=
    try lazymatch goal with |- context [Z_to_bv 64 (?x + me_A1 X)] => replace (x + me_A1 X)%Z with (me_A1 X + 4 * j)%Z by lia end.

  (* [comment removed for export] *)
  Lemma B0_plo : forall (lo hi d med unHi gtHi : Z) (a2 : zarr)
      (x10 x13 x14 x15 x19 x20 x23 x25 x26 : word)
      (f : nat) (unLo ltLo : Z) (a1 : zarr) (x12 x18 x29 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < Z.of_nat f)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m ->
    munch W1 me m -> wmono b0segs me m ->
    shzW b0segs W1 me A1 (A1 + ARR1_SIZE) -> shzW b0segs W1 me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x11' x12' x18' x28' x29' x30' x31' : word), let p' := mpart_lo f a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr b0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m' ->
      munch W1 me m' -> wmono b0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unHi p' = unHi -> mp_gtHi p' = gtHi ->
      (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (unLo <= mp_unLo p' <= unHi + 1)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 (mp_ltLo p')) (me_sp X) (Z_to_bv 64 P)
                            x10 x11' x12' x13 x14 x15 (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 med)
                            x18' x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa287c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 (A1 + 4 * unLo)) x12 x13 x14 x15 (Z_to_bv 64 unLo) (Z_to_bv 64 med)
                          x18 x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB (Z_to_bv 64 (A1 + 4 * unLo)) x29 (Z_to_bv 64 unLo) x31)
                     F (Z_to_bv 64 0xa273c) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi d med unHi gtHi a2 x10 x13 x14 x15 x19 x20 x23 x25 x26.
    induction f as [|f IH]; [intros; lia|].
    intros unLo ltLo a1 x12 x18 x29 x31 me m Hlo Hlt Hun Hgt Hhi Hd Hmed A1OK A2OK PR Hf AR1 AR2 MI MU WM SH1 SH2 K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite mpart_lo_S in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
    replace (unHi <? unLo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv zeta in K.
    pose proof (PR unLo ltac:(lia)) as Pu. set (pu := rd32 a1 unLo) in *.
    assert (Epu : rd32 a1 unLo = pu) by reflexivity. clearbody pu.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK unLo. rewrite Epu.
    (* [comment removed for export] *)
    brun. rdblk AR2 A2OK (pu + d)%Z. unfold rd8 in K.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - (* [comment removed for export] *)
      replace (zget a2 (pu + d) - med =? 0) with true in K by (symmetry; apply Z.eqb_eq; lia).
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      pose proof (PR ltLo ltac:(lia)) as Pl. set (pl := rd32 a1 ltLo) in *. assert (Epl : rd32 a1 ltLo = pl) by reflexivity. clearbody pl.
      brun_to 0xa280c%Z. key_left ltLo.
      brun. rdptr AR1 A1OK ltLo. rewrite Epl.
      brun. sw_ptr AR1 unLo pl.
      pose proof (zb8_length (wr32 a1 unLo pl) ARR1_SIZE ltac:(lia)) as L1b.
      (* [comment removed for export] *)
      brun. sw_ptr AR1 ltLo pu.
      rewrite <- Epl, <- Epu in AR1.
      change (wr32 (wr32 a1 unLo (rd32 a1 ltLo)) ltLo (rd32 a1 unLo)) with (mswap a1 unLo ltLo) in AR1.
      set (a1s := mswap a1 unLo ltLo) in *.
      assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
      assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        brun_to 0xa273c%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (unLo + 1)%Z (ltLo + 1)%Z a1s _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact A2OK| exact PRs| lia| exact AR1| exact AR2| assumption| assumption| assumption| exact SH1| exact SH2|].
        intros m' x11' x12' x18' x28' x29' x30' x31'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2.
        eapply (K m' x11' x12' x18' x28' x29' x30' x31'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia].
      + (* [comment removed for export] *)
        brun_to 0xa287c%Z.
        assert (EQ : mpart_lo f a2 d med (MP a1s (unLo + 1) unHi (ltLo + 1) gtHi) = MP a1s (unLo + 1) unHi (ltLo + 1) gtHi).
        { destruct f as [|f']; [reflexivity|]. rewrite mpart_lo_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
          replace (unHi <? unLo + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact OKs| exact PRs| reflexivity| reflexivity| lia| lia].
    - replace (zget a2 (pu + d) - med =? 0) with false in K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kg; zify_cond_z Kg.
      + replace (0 <? zget a2 (pu + d) - med) with true in K by (symmetry; apply Z.ltb_lt; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
      + replace (0 <? zget a2 (pu + d) - med) with false in K by (symmetry; apply Z.ltb_ge; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        (* [comment removed for export] *)
        brun. if_cases Kc; zify_cond_z Kc.
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (IH (unLo + 1)%Z ltLo a1 _ _ _ _ me mm) end;
            [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| assumption| assumption| assumption| exact SH1| exact SH2| ].
          intros m' x11' x12' x18' x28' x29' x30' x31'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2.
          eapply (K m' x11' x12' x18' x28' x29' x30' x31'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia].
        * (* [comment removed for export] *)
          brun_to 0xa287c%Z.
          assert (EQ : mpart_lo f a2 d med (MP a1 (unLo + 1) unHi ltLo gtHi) = MP a1 (unLo + 1) unHi ltLo gtHi).
          { destruct f as [|f']; [reflexivity|]. rewrite mpart_lo_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
            replace (unHi <? unLo + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_phi : forall (lo hi d med unLo ltLo : Z) (a2 : zarr)
      (x10 x13 x14 x15 x19 x20 x23 x25 x26 : word)
      (f : nat) (unHi gtHi : Z) (a1 : zarr) (x12 x18 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < Z.of_nat f)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m ->
    munch W1 me m -> wmono b0segs me m ->
    shzW b0segs W1 me A1 (A1 + ARR1_SIZE) -> shzW b0segs W1 me A2 (A2 + ARR2_SIZE) ->
    (forall m' (SHh : Z) (x18' : word), let p' := mpart_hi f a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr b0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m' ->
      munch W1 me m' -> wmono b0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unLo p' = unLo -> mp_ltLo p' = ltLo ->
      (unLo <= mp_unHi p' <= unHi)%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      (zget a2 (rd32 (mp_a1 p') (mp_unHi p') + d) < med)%Z -> saddr (A1 + 4 * mp_unHi p') SHh ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                            x10 (Z_to_bv 64 (A1 + 4 * mp_unHi p')) (Z_to_bv 64 (zget a2 (rd32 (mp_a1 p') (mp_unHi p') + d))) x13 x14 x15 (Z_to_bv 64 unLo) (Z_to_bv 64 med)
                            x18' x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB
                            (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 (A1 + 4 * mp_unHi p')) (Z_to_bv 64 (rd32 (mp_a1 p') (mp_unHi p'))) (Z_to_bv 64 SHh))
                       F (Z_to_bv 64 0xa29d0) fc None m' (seg_rom b0segs))) ->
    (forall m' (x11' x12' x18' x28' x29' x30' x31' : word), let p' := mpart_hi f a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr b0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m' ->
      munch W1 me m' -> wmono b0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unLo p' = unLo -> mp_ltLo p' = ltLo ->
      (mp_unHi p' < unLo)%Z -> (unLo <= mp_unHi p' + 1)%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                            x10 x11' x12' x13 x14 x15 (Z_to_bv 64 unLo) (Z_to_bv 64 med)
                            x18' x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa2a6c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 (A1 + 4 * unHi)) x12 x13 x14 x15 (Z_to_bv 64 unLo) (Z_to_bv 64 med)
                          x18 x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB (Z_to_bv 64 unHi) (Z_to_bv 64 (A1 + 4 * unHi)) x30 x31)
                     F (Z_to_bv 64 0xa2894) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi d med unLo ltLo a2 x10 x13 x14 x15 x19 x20 x23 x25 x26.
    induction f as [|f IH]; [intros; lia|].
    intros unHi gtHi a1 x12 x18 x30 x31 me m Hlo Hlt Hun Hgt Hhi Hd Hmed A1OK A2OK PR Hf AR1 AR2 MI MU WM SH1 SH2 K1 K2.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite mpart_hi_S in K1, K2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1, K2.
    replace (unHi <? unLo) with false in K1, K2 by (symmetry; apply Z.ltb_ge; lia). cbv zeta in K1. cbv zeta in K2.
    pose proof (PR unHi ltac:(lia)) as Pu. set (pu := rd32 a1 unHi) in *.
    assert (Epu : rd32 a1 unHi = pu) by reflexivity. clearbody pu.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK unHi. rewrite Epu.
    (* [comment removed for export] *)
    brun. rdblk AR2 A2OK (pu + d)%Z. unfold rd8 in K1, K2.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - replace (zget a2 (pu + d) - med =? 0) with true in K1, K2 by (symmetry; apply Z.eqb_eq; lia).
      cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1, K2.
      pose proof (PR gtHi ltac:(lia)) as Pg. set (pg := rd32 a1 gtHi) in *. assert (Epg : rd32 a1 gtHi = pg) by reflexivity. clearbody pg.
      (* [comment removed for export] *)
      brun_to 0xa2964%Z. key_left gtHi.
      brun. rdptr AR1 A1OK gtHi. rewrite Epg.
      brun. sw_ptr AR1 unHi pg.
      pose proof (zb8_length (wr32 a1 unHi pg) ARR1_SIZE ltac:(lia)) as L1b.
      (* [comment removed for export] *)
      brun. sw_ptr AR1 gtHi pu.
      rewrite <- Epg, <- Epu in AR1.
      change (wr32 (wr32 a1 unHi (rd32 a1 gtHi)) gtHi (rd32 a1 unHi)) with (mswap a1 unHi gtHi) in AR1.
      set (a1s := mswap a1 unHi gtHi) in *.
      assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
      assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        brun_to 0xa2894%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (unHi - 1)%Z (gtHi - 1)%Z a1s _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact A2OK| exact PRs| lia| exact AR1| exact AR2| assumption| assumption| assumption| exact SH1| exact SH2| |].
        * intros m' SHh x18'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3 AS.
          eapply (K1 m' SHh x18'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| exact B3| exact AS].
        * intros m' x11' x12' x18' x28' x29' x30' x31'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3.
          eapply (K2 m' x11' x12' x18' x28' x29' x30' x31'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| lia].
      + (* [comment removed for export] *)
        brun_to 0xa2a6c%Z.
        assert (EQ : mpart_hi f a2 d med (MP a1s unLo (unHi - 1) ltLo (gtHi - 1)) = MP a1s unLo (unHi - 1) ltLo (gtHi - 1)).
        { destruct f as [|f']; [reflexivity|]. rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
          replace (unHi - 1 <? unLo) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        rewrite EQ in K2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K2.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K2 mm _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact OKs| exact PRs| reflexivity| reflexivity| lia| lia| lia].
    - replace (zget a2 (pu + d) - med =? 0) with false in K1, K2 by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kg; zify_cond_z Kg.
      + replace (zget a2 (pu + d) - med <? 0) with true in K1 by (symmetry; apply Z.ltb_lt; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1. rewrite <- Epu.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm ((A1 + 4 * unHi) / 8 + 2147450880)%Z _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia| rewrite Epu; lia| apply saddr_intro].
      + replace (zget a2 (pu + d) - med <? 0) with false in K1, K2 by (symmetry; apply Z.ltb_ge; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K1, K2.
        (* [comment removed for export] *)
        brun. if_cases Kc; zify_cond_z Kc.
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (IH (unHi - 1)%Z gtHi a1 _ _ _ _ me mm) end;
            [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| assumption| assumption| assumption| exact SH1| exact SH2| |].
          -- intros m' SHh x18'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3 AS.
             eapply (K1 m' SHh x18'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| exact B3| exact AS].
          -- intros m' x11' x12' x18' x28' x29' x30' x31'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2 B3.
             eapply (K2 m' x11' x12' x18' x28' x29' x30' x31'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia| lia].
        * (* [comment removed for export] *)
          brun_to 0xa2a6c%Z.
          assert (EQ : mpart_hi f a2 d med (MP a1 unLo (unHi - 1) ltLo gtHi) = MP a1 unLo (unHi - 1) ltLo gtHi).
          { destruct f as [|f']; [reflexivity|]. rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi].
            replace (unHi - 1 <? unLo) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          rewrite EQ in K2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K2.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K2 mm _ _ _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
