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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msG.
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

  (* [comment removed for export] *)
  Lemma B0_part : forall (lo hi d med : Z) (sz : nat) (a2 : zarr)
      (x10 x13 x14 x15 x19 x20 x23 x25 x26 : word)
      (f : nat) (unLo unHi ltLo gtHi : Z) (a1 : zarr) (x11 x12 x16 x18 x28 x29 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    (Z.of_nat sz = hi - lo + 1)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < 2 * Z.of_nat f)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m ->
    munch W1 me m -> wmono b0segs me m ->
    shzW b0segs W1 me A1 (A1 + ARR1_SIZE) -> shzW b0segs W1 me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x11' x12' x18' x28' x29' x30' x31' : word), let p' := mpart_loop f sz a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr b0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv b0segs m' ->
      munch W1 me m' -> wmono b0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) ->
      (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (mp_unHi p' < mp_unLo p')%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 (mp_ltLo p')) (me_sp X) (Z_to_bv 64 P)
                            x10 x11' x12' x13 x14 x15 (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 med)
                            x18' x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa2a6c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 med)
                          x18 x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28 x29 (Z_to_bv 64 unLo) x31)
                     F (Z_to_bv 64 0xa2728) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi d med sz a2 x10 x13 x14 x15 x19 x20 x23 x25 x26.
    induction f as [|f IH]; [intros; lia|].
    intros unLo unHi ltLo gtHi a1 x11 x12 x16 x18 x28 x29 x31 me m Hlo Hlt Hun Hgt Hhi Hd Hmed Hsz A1OK A2OK PR Hf AR1 AR2 MI MU WM SH1 SH2 K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite mpart_loop_S in K.
    (* [comment removed for export] *)
    brun_to 0xa273c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_plo X Y Q XOK XSEP YOK lo hi d med unHi gtHi a2 _ _ _ _ _ _ _ _ _ (S sz) unLo ltLo a1 _ _ _ _ me mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact SH1| exact SH2|].
    intros m1 y11 y12 y18 y28 y29 y30 y31. cbv zeta. intros AR1_1 AR2_1 MI1 MU1 WM1 OK1 PR1 U1 G1 B1 B2.
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
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
        [st_eq| exact AR1_1| exact AR2_1| exact MI1| exact MU1| exact WM1| exact OK1| exact PR1| lia| lia| lia]. }
    (* [comment removed for export] *)
    brun_to 0xa2894%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_phi X Y Q XOK XSEP YOK lo hi d med unLo1 ltLo1 a2 _ _ _ _ _ _ _ _ _ (S sz) unHi gtHi a1p _ _ _ _ me mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact OK1| exact A2OK| exact PR1| lia| exact AR1_1| exact AR2_1| exact MI1| exact MU1| exact WM1| exact SH1| exact SH2| |].
    - (* [comment removed for export] *)
      intros m2 SHh z18. cbv zeta. intros AR1_2 AR2_2 MI2 MU2 WM2 OK2 PR2 U2 G2 C1 C2 C3 ASH.
      set (p2 := mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi)) in *.
      destruct p2 as [a1q unLo2 unHi2 ltLo2 gtHi2] eqn:EP2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unLo2 ltLo2.
      replace (unHi2 <? unLo1) with false in K by (symmetry; apply Z.ltb_ge; lia).
      bz_params.
      pose proof (zb8_length a1q ARR1_SIZE ltac:(lia)) as L1q.
      pose proof (PR2 unLo1 ltac:(lia)) as Pl. set (pl := rd32 a1q unLo1) in *. assert (Epl : rd32 a1q unLo1 = pl) by reflexivity. clearbody pl.
      pose proof (PR2 unHi2 ltac:(lia)) as Ph. set (ph := rd32 a1q unHi2) in *. assert (Eph : rd32 a1q unHi2 = ph) by reflexivity. clearbody ph.
      brun. rdptr AR1_2 OK2 unLo1. rewrite Epl.
      (* [comment removed for export] *)
      sw_ptr AR1_2 unLo1 ph.
      pose proof (zb8_length (wr32 a1q unLo1 ph) ARR1_SIZE ltac:(lia)) as L1r.
      (* [comment removed for export] *)
      brun. sw_ptr AR1_2 unHi2 pl.
      rewrite <- Eph, <- Epl in AR1_2.
      change (wr32 (wr32 a1q unLo1 (rd32 a1q unHi2)) unHi2 (rd32 a1q unLo1)) with (mswap a1q unLo1 unHi2) in AR1_2.
      set (a1s := mswap a1q unLo1 unHi2) in *.
      assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact OK2).
      assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
      (* [comment removed for export] *)
      brun_to 0xa271c%Z.
      wstep; if_cases Ke; zify_cond_z Ke.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (unLo1 + 1)%Z (unHi2 - 1)%Z ltLo1 gtHi2 a1s _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact OKs| exact A2OK| exact PRs| lia| exact AR1_2| exact AR2_2| assumption| assumption| assumption| exact SH1| exact SH2|].
        intros m' x11' x12' x18' x28' x29' x30' x31'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' V1 V2 V3.
        eapply (K m' x11' x12' x18' x28' x29' x30' x31'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia| lia].
      + (* [comment removed for export] *)
        wstep. wstep. wstep; if_cases Kg; zify_cond_z Kg; [| exfalso; lia].
        assert (EQ : mpart_loop f sz a2 d med (MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2) = MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2).
        { destruct f as [|f']; [reflexivity|]. rewrite mpart_loop_S.
          assert (E1 : mpart_lo (S sz) a2 d med (MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2) = MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2).
          { rewrite mpart_lo_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi2 - 1 <? unLo1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          cbv zeta. rewrite E1.
          assert (E2 : mpart_hi (S sz) a2 d med (MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2) = MP a1s (unLo1 + 1) (unHi2 - 1) ltLo1 gtHi2).
          { rewrite mpart_hi_S. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi2 - 1 <? unLo1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          rewrite E2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]. replace (unHi2 - 1 <? unLo1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
          [st_eq| exact AR1_2| exact AR2_2| assumption| assumption| assumption| exact OKs| exact PRs| lia| lia| lia].
    - (* [comment removed for export] *)
      intros m2 z11 z12 z18 z28 z29 z30 z31. cbv zeta. intros AR1_2 AR2_2 MI2 MU2 WM2 OK2 PR2 U2 G2 C1 C2 C3.
      set (p2 := mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi)) in *.
      destruct p2 as [a1q unLo2 unHi2 ltLo2 gtHi2] eqn:EP2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unLo2 ltLo2.
      replace (unHi2 <? unLo1) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      eapply (K m2 z11 z12 z18 z28 z29 z30 z31); [exact AR1_2| exact AR2_2| exact MI2| exact MU2| exact WM2| exact OK2| exact PR2| lia| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
