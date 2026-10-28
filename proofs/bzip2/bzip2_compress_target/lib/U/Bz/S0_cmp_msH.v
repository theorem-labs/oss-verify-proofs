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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
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
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Local Ltac UKit.u_norm ::= rewrite ?zext32_id.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation NA2 := (18446744073709551615 - me_A2 X)%Z.

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
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  Ltac st_ptr AR1 j :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * j)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end;
    wstep; sw_ptr AR1 j.

  Section PART.
    Variables (lo hi d med : Z) (a2 : zarr) (xra x8 x10 x19 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word).
    Hypothesis Hlo : (0 <= lo)%Z. Hypothesis Hhi : (hi < n)%Z. Hypothesis Hd : (0 <= d <= 14)%Z. Hypothesis Hmed : (0 <= med < 256)%Z.
    Hypothesis A2OK : zbok a2.
    Notation RP t0 t1 t2 a1 a2r a4 a5 a6 a7 :=
      (mkR xra (Z_to_bv 64 p) gp tp t0 t1 t2 x8 (Z_to_bv 64 NA2) x10 a1 a2r (Z_to_bv 64 med) a4 a5 a6 a7
           (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 x22 x23 (Z_to_bv 64 d) x25 x26 x27 x28 x29 x30 x31).
    Notation MEMS a1 me m := (u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) /\ u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) /\ mem_inv s0segs m /\
                              munch [(A1, A1 + ARR1_SIZE)]%Z me m /\ wmono s0segs me m).

    Lemma U0_plo : forall (unHi gtHi : Z) (f : nat) (unLo ltLo : Z) (a1 : zarr) (t1 t2 : word) (me m : word -> option byte),
      (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z ->
      zbok a1 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < Z.of_nat f)%Z ->
      u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
      (forall m' (t0' t1' t2' a6' a7' : word), let p' := mpart_lo f a2 d med (MP a1 unLo unHi ltLo gtHi) in
        u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
        munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
        zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unHi p' = unHi -> mp_gtHi p' = gtHi ->
        (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (unLo <= mp_unLo p' <= unHi + 1)%Z ->
        evt s0segs Q (MS (RP t0' t1' t2' (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 (mp_ltLo p')) a6' a7')
                         F (Z_to_bv 64 0x211f0) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RP (Z_to_bv 64 (A1 + 4 * unLo)) t1 t2 (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo)
                           (Z_to_bv 64 unLo) (Z_to_bv 64 (A1 + 4 * unLo)))
                       F (Z_to_bv 64 0x21120) fc None m (seg_rom s0segs)).
    Proof using All.
      intros unHi gtHi. induction f as [|f IH]; [intros; lia|].
      intros unLo ltLo a1 t1 t2 me m Hlt Hun Hgt A1OK PR Hf AR1 AR2 MI MU WM K.
      msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
      bz_params.
      pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
      rewrite mpart_lo_S in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
      replace (unHi <? unLo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv zeta in K.
      pose proof (PR unLo ltac:(lia)) as Pu. set (pu := rd32 a1 unLo) in *.
      assert (Epu : rd32 a1 unLo = pu) by reflexivity. clearbody pu.
      urun_to 0x21140%Z.
      rdptr AR1 A1OK unLo. rewrite Epu.
      urun_to 0x2115c%Z.
      rdblk AR2 A2OK (pu + d)%Z. unfold rd8 in K.
      urun.
      if_cases Ke; zify_cond_z Ke.
      - replace (zget a2 (pu + d) - med =? 0) with true in K by (symmetry; apply Z.eqb_eq; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        pose proof (PR ltLo ltac:(lia)) as Pl. set (pl := rd32 a1 ltLo) in *. assert (Epl : rd32 a1 ltLo = pl) by reflexivity. clearbody pl.
        urun_to 0x211b4%Z.
        rdptr AR1 A1OK ltLo. rewrite Epl.
        st_ptr AR1 unLo. rewrite (unsigned_lit pl) in AR1 by lia.
        pose proof (zb8_length (wr32 a1 unLo pl) ARR1_SIZE ltac:(lia)) as L1b.
        urun_to 0x211c4%Z.
        st_ptr AR1 ltLo. rewrite (unsigned_lit pu) in AR1 by lia.
        rewrite <- Epl, <- Epu in AR1.
        change (wr32 (wr32 a1 unLo (rd32 a1 ltLo)) ltLo (rd32 a1 unLo)) with (mswap a1 unLo ltLo) in AR1.
        set (a1s := mswap a1 unLo ltLo) in *.
        assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
        assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
        urun.
        if_cases Kl; zify_cond_z Kl.
        + urun_to 0x21120%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (IH (unLo + 1)%Z (ltLo + 1)%Z a1s _ _ me mm) end;
            [st_eq| lia| lia| lia| exact OKs| exact PRs| lia| exact AR1| exact AR2| assumption| assumption| assumption|].
          intros m' t0' t1' t2' a6' a7'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2.
          eapply (K m' t0' t1' t2' a6' a7'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia].
        + urun_to 0x211f0%Z.
          assert (EQ : mpart_lo f a2 d med (MP a1s (unLo + 1) unHi (ltLo + 1) gtHi) = MP a1s (unLo + 1) unHi (ltLo + 1) gtHi)
            by (destruct f; [reflexivity| rewrite mpart_lo_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi];
                replace (unHi <? unLo + 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity]).
          rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact OKs| exact PRs| reflexivity| reflexivity| lia| lia].
      - replace (zget a2 (pu + d) - med =? 0) with false in K by (symmetry; apply Z.eqb_neq; lia).
        urun.
        if_cases Kg; zify_cond_z Kg.
        + replace (0 <? zget a2 (pu + d) - med) with true in K by (symmetry; apply Z.ltb_lt; lia).
          cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
          urun_to 0x211f0%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
        + replace (0 <? zget a2 (pu + d) - med) with false in K by (symmetry; apply Z.ltb_ge; lia).
          urun.
          if_cases Kl; zify_cond_z Kl.
          * urun_to 0x21120%Z.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (IH (unLo + 1)%Z ltLo a1 _ _ me mm) end;
              [st_eq| lia| lia| lia| exact A1OK| exact PR| lia| exact AR1| exact AR2| assumption| assumption| assumption|].
            intros m' t0' t1' t2' a6' a7'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' G' B1 B2.
            eapply (K m' t0' t1' t2' a6' a7'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact G'| lia| lia].
          * urun_to 0x211f0%Z.
            assert (EQ : mpart_lo f a2 d med (MP a1 (unLo + 1) unHi ltLo gtHi) = MP a1 (unLo + 1) unHi ltLo gtHi)
              by (destruct f; [reflexivity| rewrite mpart_lo_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi];
                  replace (unHi <? unLo + 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity]).
            rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
              [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
    Qed.


    Lemma U0_phi : forall (unLo ltLo : Z) (f : nat) (unHi gtHi : Z) (a1 : zarr) (a6 t2 : word) (me m : word -> option byte),
      (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z ->
      zbok a1 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < Z.of_nat f)%Z ->
      u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
      (forall m' (t2' : word), let p' := mpart_hi f a2 d med (MP a1 unLo unHi ltLo gtHi) in
        u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
        munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
        zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unLo p' = unLo -> mp_ltLo p' = ltLo ->
        (unLo <= mp_unHi p' <= unHi)%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
        evt s0segs Q (MS (RP (Z_to_bv 64 (A1 + 4 * mp_unHi p')) (Z_to_bv 64 (A1 + 4 * mp_unHi p')) t2' (Z_to_bv 64 unLo) (Z_to_bv 64 (mp_unHi p'))
                             (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 ltLo) (Z_to_bv 64 (rd32 (mp_a1 p') (mp_unHi p'))) (Z_to_bv 64 (mp_unHi p')))
                         F (Z_to_bv 64 0x212d0) fc None m' (seg_rom s0segs))) ->
      (forall m' (t0' t1' t2' a6' a7' : word), let p' := mpart_hi f a2 d med (MP a1 unLo unHi ltLo gtHi) in
        u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
        munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
        zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) -> mp_unLo p' = unLo -> mp_ltLo p' = ltLo ->
        (mp_unHi p' < unLo)%Z -> (unLo - 1 <= mp_unHi p')%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
        evt s0segs Q (MS (RP t0' t1' t2' (Z_to_bv 64 unLo) (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 ltLo) a6' a7')
                         F (Z_to_bv 64 0x21324) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RP (Z_to_bv 64 (A1 + 4 * unHi)) (Z_to_bv 64 (A1 + 4 * unHi)) t2 (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi)
                           (Z_to_bv 64 ltLo) a6 (Z_to_bv 64 unHi))
                       F (Z_to_bv 64 0x21208) fc None m (seg_rom s0segs)).
    Proof using All.
      intros unLo ltLo. induction f as [|f IH]; [intros; lia|].
      intros unHi gtHi a1 a6 t2 me m Hlt Hun Hgt A1OK PR Hf AR1 AR2 MI MU WM KB KX.
      msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
      bz_params.
      pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
      rewrite mpart_hi_S in KB, KX. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in KB, KX.
      replace (unHi <? unLo) with false in KB, KX by (symmetry; apply Z.ltb_ge; lia). cbv zeta in KB, KX.
      pose proof (PR unHi ltac:(lia)) as Pu. set (pu := rd32 a1 unHi) in *.
      assert (Epu : rd32 a1 unHi = pu) by reflexivity. clearbody pu.
      urun_to 0x21228%Z.
      rdptr AR1 A1OK unHi. rewrite Epu.
      urun_to 0x21244%Z.
      rdblk AR2 A2OK (pu + d)%Z. unfold rd8 in KB, KX.
      urun.
      if_cases Ke; zify_cond_z Ke.
      - replace (zget a2 (pu + d) - med =? 0) with true in KB, KX by (symmetry; apply Z.eqb_eq; lia).
        cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in KB, KX.
        pose proof (PR gtHi ltac:(lia)) as Pg. set (pg := rd32 a1 gtHi) in *. assert (Epg : rd32 a1 gtHi = pg) by reflexivity. clearbody pg.
        urun_to 0x2129c%Z.
        rdptr AR1 A1OK gtHi. rewrite Epg.
        st_ptr AR1 unHi. rewrite (unsigned_lit pg) in AR1 by lia.
        pose proof (zb8_length (wr32 a1 unHi pg) ARR1_SIZE ltac:(lia)) as L1b.
        urun_to 0x212ac%Z.
        st_ptr AR1 gtHi. rewrite (unsigned_lit pu) in AR1 by lia.
        rewrite <- Epg, <- Epu in AR1.
        change (wr32 (wr32 a1 unHi (rd32 a1 gtHi)) gtHi (rd32 a1 unHi)) with (mswap a1 unHi gtHi) in AR1.
        set (a1s := mswap a1 unHi gtHi) in *.
        assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact A1OK).
        assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
        urun.
        if_cases Kl; zify_cond_z Kl.
        + urun_to 0x21208%Z.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (IH (unHi - 1)%Z (gtHi - 1)%Z a1s _ _ me mm) end;
            [st_eq| lia| lia| lia| exact OKs| exact PRs| lia| exact AR1| exact AR2| assumption| assumption| assumption| |].
          * intros m' t2'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' L' B1 B2.
            eapply (KB m' t2'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact L'| lia| lia].
          * intros m' t0' t1' t2' a6' a7'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' L' B1 B2 B3.
            eapply (KX m' t0' t1' t2' a6' a7'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact L'| lia| lia| lia].
        + urun_to 0x21324%Z.
          assert (EQ : mpart_hi f a2 d med (MP a1s unLo (unHi - 1) ltLo (gtHi - 1)) = MP a1s unLo (unHi - 1) ltLo (gtHi - 1))
            by (destruct f; [reflexivity| rewrite mpart_hi_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi];
                replace (unHi - 1 <? unLo) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity]).
          rewrite EQ in KX. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in KX.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KX mm _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact OKs| exact PRs| reflexivity| reflexivity| lia| lia| lia].
      - replace (zget a2 (pu + d) - med =? 0) with false in KB, KX by (symmetry; apply Z.eqb_neq; lia).
        urun.
        if_cases Kg; zify_cond_z Kg.
        + replace (zget a2 (pu + d) - med <? 0) with true in KB, KX by (symmetry; apply Z.ltb_lt; lia).
          cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in KB, KX.
          rewrite Epu in KB.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KB mm _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia].
        + replace (zget a2 (pu + d) - med <? 0) with false in KB, KX by (symmetry; apply Z.ltb_ge; lia).
          urun.
          if_cases Kl; zify_cond_z Kl.
          * urun_to 0x21208%Z.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (IH (unHi - 1)%Z gtHi a1 _ _ me mm) end;
              [st_eq| lia| lia| lia| exact A1OK| exact PR| lia| exact AR1| exact AR2| assumption| assumption| assumption| |].
            -- intros m' t2'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' L' B1 B2.
               eapply (KB m' t2'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact L'| lia| lia].
            -- intros m' t0' t1' t2' a6' a7'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' U' L' B1 B2 B3.
               eapply (KX m' t0' t1' t2' a6' a7'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact U'| exact L'| lia| lia| lia].
          * urun_to 0x21324%Z.
            assert (EQ : mpart_hi f a2 d med (MP a1 unLo (unHi - 1) ltLo gtHi) = MP a1 unLo (unHi - 1) ltLo gtHi)
              by (destruct f; [reflexivity| rewrite mpart_hi_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi];
                  replace (unHi - 1 <? unLo) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity]).
            rewrite EQ in KX. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in KX.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KX mm _ _ _ _ _) end;
              [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| reflexivity| reflexivity| lia| lia| lia].
    Qed.


    Lemma U0_part_gen : forall (sz : nat) (f : nat) (unLo unHi ltLo gtHi : Z) (a1 : zarr) (t0 t1 t2 a1r a7 : word) (me m : word -> option byte),
      (lo <= ltLo <= unLo)%Z -> (unLo <= unHi + 2)%Z -> (unHi <= gtHi <= hi)%Z -> (Z.of_nat sz = hi - lo + 1)%Z ->
      zbok a1 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < 2 * Z.of_nat f)%Z ->
      u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
      (forall m' (t0' t1' t2' a6' a7' : word), let p' := mpart_loop f sz a2 d med (MP a1 unLo unHi ltLo gtHi) in
        u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
        munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
        zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) ->
        (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (mp_unHi p' < mp_unLo p')%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
        evt s0segs Q (MS (RP t0' t1' t2' (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 (mp_ltLo p')) a6' a7')
                         F (Z_to_bv 64 0x21324) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RP t0 t1 t2 a1r (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo) a7)
                       F (Z_to_bv 64 0x21100) fc None m (seg_rom s0segs)).
    Proof using All.
      intros sz. induction f as [|f IH].
      - intros unLo unHi ltLo gtHi a1 t0 t1 t2 a1r a7 me m Hlt Hun Hgt Hsz A1OK PR Hf AR1 AR2 MI MU WM K.
        msenv_open XOK. bz_params. cbn [mpart_loop] in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
        urun. if_cases K0; zify_cond_z K0; [exfalso; lia|].
        urun. if_cases K1; zify_cond_z K1; [|exfalso; lia].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| lia| lia| lia].
      - intros unLo unHi ltLo gtHi a1 t0 t1 t2 a1r a7 me m Hlt Hun Hgt Hsz A1OK PR Hf AR1 AR2 MI MU WM K.
        msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
        bz_params.
        pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
        rewrite mpart_loop_S in K. cbv zeta in K.
        urun. if_cases K0; zify_cond_z K0.
        + urun_to 0x21120%Z.
          enter_with (U0_plo unHi gtHi (S sz) unLo ltLo a1 _ _ me m);
            [st_eq| lia| lia| lia| exact A1OK| exact PR| lia| exact AR1| exact AR2| exact MI| exact MU| exact WM|].
          intros m1 y0 y1 y2 y6 y7. cbv zeta. intros AR1_1 AR2_1 MI1 MU1 WM1 OK1 PR1 U1 G1 B1 B2.
          set (p1 := mpart_lo (S sz) a2 d med (MP a1 unLo unHi ltLo gtHi)) in *.
          destruct p1 as [a1p unLo1 unHi1 ltLo1 gtHi1] eqn:EP1. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unHi1 gtHi1.
          pose proof (zb8_length a1p ARR1_SIZE ltac:(lia)) as L1p.
          urun. if_cases Kc; zify_cond_z Kc.
          * assert (EQ : mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi) = MP a1p unLo1 unHi ltLo1 gtHi)
              by (rewrite mpart_hi_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]; replace (unHi <? unLo1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
            rewrite EQ in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
            replace (unHi <? unLo1) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
              [st_eq| exact AR1_1| exact AR2_1| exact MI1| exact MU1| exact WM1| exact OK1| exact PR1| lia| lia| lia].
          * urun_to 0x21208%Z.
            enter_with (U0_phi unLo1 ltLo1 (S sz) unHi gtHi a1p _ _ me m1);
              [st_eq| lia| lia| lia| exact OK1| exact PR1| lia| exact AR1_1| exact AR2_1| exact MI1| exact MU1| exact WM1| |].
            -- intros m2 z2. cbv zeta. intros AR1_2 AR2_2 MI2 MU2 WM2 OK2 PR2 U2 L2' C1 C2.
               set (p2 := mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi)) in *.
               destruct p2 as [a1q unLo2 unHi2 ltLo2 gtHi2] eqn:EP2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unLo2 ltLo2.
               replace (unHi2 <? unLo1) with false in K by (symmetry; apply Z.ltb_ge; lia).
               pose proof (zb8_length a1q ARR1_SIZE ltac:(lia)) as L1q.
               pose proof (PR2 unLo1 ltac:(lia)) as Pl. set (pl := rd32 a1q unLo1) in *. assert (Epl : rd32 a1q unLo1 = pl) by reflexivity. clearbody pl.
               pose proof (PR2 unHi2 ltac:(lia)) as Ph. set (ph := rd32 a1q unHi2) in *. assert (Eph : rd32 a1q unHi2 = ph) by reflexivity. clearbody ph.
               urun_to 0x21300%Z.
               rdptr AR1_2 OK2 unLo1. rewrite Epl.
               st_ptr AR1_2 unLo1. rewrite (unsigned_lit ph) in AR1_2 by lia.
               pose proof (zb8_length (wr32 a1q unLo1 ph) ARR1_SIZE ltac:(lia)) as L1r.
               urun_to 0x2130c%Z.
               st_ptr AR1_2 unHi2. rewrite (unsigned_lit pl) in AR1_2 by lia.
               rewrite <- Eph, <- Epl in AR1_2.
               change (wr32 (wr32 a1q unLo1 (rd32 a1q unHi2)) unHi2 (rd32 a1q unLo1)) with (mswap a1q unLo1 unHi2) in AR1_2.
               set (a1s := mswap a1q unLo1 unHi2) in *.
               assert (OKs : zbok a1s) by (subst a1s; apply zbok_mswap; exact OK2).
               assert (PRs : pr n a1s 0 (n - 1)) by (subst a1s; apply pr_mswap; try assumption; lia).
               urun_to 0x21100%Z.
               lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
                 enter_with (IH (unLo1 + 1)%Z (unHi2 - 1)%Z ltLo1 gtHi2 a1s _ _ _ _ _ me mm) end;
                 [st_eq| lia| lia| lia| exact Hsz| exact OKs| exact PRs| lia| exact AR1_2| exact AR2_2| assumption| assumption| assumption|].
               intros m' t0' t1' t2' a6' a7'. cbv zeta. intros AR1' AR2' MI' MU' WM' OK' PR' V1 V2 V3.
               eapply (K m' t0' t1' t2' a6' a7'); [exact AR1'| exact AR2'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia| lia].
            -- intros m2 z0 z1 z2 z6 z7. cbv zeta. intros AR1_2 AR2_2 MI2 MU2 WM2 OK2 PR2 U2 L2' C1 C2 C3.
               set (p2 := mpart_hi (S sz) a2 d med (MP a1p unLo1 unHi ltLo1 gtHi)) in *.
               destruct p2 as [a1q unLo2 unHi2 ltLo2 gtHi2] eqn:EP2. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in *. subst unLo2 ltLo2.
               replace (unHi2 <? unLo1) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
               eapply (K m2 z0 z1 z2 z6 z7); [exact AR1_2| exact AR2_2| exact MI2| exact MU2| exact WM2| exact OK2| exact PR2| lia| lia| lia].
        + assert (EQ1 : mpart_lo (S sz) a2 d med (MP a1 unLo unHi ltLo gtHi) = MP a1 unLo unHi ltLo gtHi)
            by (rewrite mpart_lo_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]; replace (unHi <? unLo) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          rewrite EQ1 in K.
          assert (EQ2 : mpart_hi (S sz) a2 d med (MP a1 unLo unHi ltLo gtHi) = MP a1 unLo unHi ltLo gtHi)
            by (rewrite mpart_hi_S; cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi]; replace (unHi <? unLo) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          rewrite EQ2 in K. cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
          replace (unHi <? unLo) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [mp_a1 mp_unLo mp_unHi mp_ltLo mp_gtHi] in K.
          urun. if_cases K1; zify_cond_z K1; [|exfalso; lia].
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
            [st_eq| exact AR1| exact AR2| assumption| assumption| assumption| exact A1OK| exact PR| lia| lia| lia].
    Qed.

  End PART.

  Lemma S0_part : forall (lo hi d med : Z) (sz : nat) (a2 : zarr)
      (xra x8 x10 x19 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
      (f : nat) (unLo unHi ltLo gtHi : Z) (a1 : zarr) (t0 t1 t2 a1r a7 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z -> (0 <= med < 256)%Z ->
    (Z.of_nat sz = hi - lo + 1)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (unHi - unLo + 1 < 2 * Z.of_nat f)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (t0' t1' t2' a6' a7' : word), let p' := mpart_loop f sz a2 d med (MP a1 unLo unHi ltLo gtHi) in
      u8arr s0segs m' A1 (zb8 (mp_a1 p') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono s0segs me m' ->
      zbok (mp_a1 p') -> pr n (mp_a1 p') 0 (n - 1) ->
      (ltLo <= mp_ltLo p' <= mp_unLo p')%Z -> (mp_unHi p' < mp_unLo p')%Z -> (mp_unHi p' <= mp_gtHi p' <= gtHi)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp t0' t1' t2' x8 (Z_to_bv 64 NA2) x10
                            (Z_to_bv 64 (mp_unLo p')) (Z_to_bv 64 (mp_unHi p')) (Z_to_bv 64 med) (Z_to_bv 64 (mp_gtHi p')) (Z_to_bv 64 (mp_ltLo p')) a6' a7'
                            (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 x22 x23 (Z_to_bv 64 d) x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21324) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp t0 t1 t2 x8 (Z_to_bv 64 NA2) x10
                          a1r (Z_to_bv 64 unHi) (Z_to_bv 64 med) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo) a7
                          (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 x22 x23 (Z_to_bv 64 d) x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21100) fc None m (seg_rom s0segs)).
  Proof using XOK XSEP.
    intros lo hi d med sz a2 xra x8 x10 x19 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 f unLo unHi ltLo gtHi a1 t0 t1 t2 a1r a7 me m
      Hlo Hlt Hun Hgt Hhi Hd Hmed Hsz A1OK A2OK PR Hf AR1 AR2 MI MU WM K.
    exact (U0_part_gen lo hi d med a2 xra x8 x10 x19 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Hlo Hhi Hd Hmed A2OK
             sz f unLo unHi ltLo gtHi a1 t0 t1 t2 a1r a7 me m Hlt ltac:(lia) Hgt Hsz A1OK PR Hf AR1 AR2 MI MU WM K).
  Qed.

End S0MS.

End ACeilS1.
