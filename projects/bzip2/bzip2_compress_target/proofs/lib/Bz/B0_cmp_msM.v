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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
Import BzCSewC.BzCSewB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msW B0_cmp_msMa B0_cmp_msMb B0_cmp_msX B0_cmp_msMa B0_cmp_msMb.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Lemma sll32_srl30 : forall a, (a * 4294967296 / 1073741824 = a * 4)%Z.
Proof. intros a. replace (a * 4294967296)%Z with (a * 4 * 1073741824)%Z by lia. apply Z.div_mul. lia. Qed.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  (* [comment removed for export] *)
  Variables (w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w480 : word).
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  Notation cCM := (Z_to_bv 64 18446744073707454463).
  Notation NBD := (18446744073709551615 - am_BD Y)%Z.
  Notation W2 := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (P, P + 496); (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024)]%Z.
  Notation SQ2 i ss q416 q440 :=
    (mkSLQ (Z_to_bv 64 i) (Z_to_bv 64 ss) w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 q416 q440 w480).
  (* [comment removed for export] *)

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.

  (* [comment removed for export] *)
  Lemma B0_step2 : forall (i ss : Z) (a1 a2 ft bd cs ce : zarr) (w416 w440 : word)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x26 x28 : word) (me m : word -> option byte),
    let ci := ms_copy_init 256 cs ce ft ss 0 in let cs0 := fst ci in let ce0 := snd ci in
    let j0 := clearmask (zget ft (Z.shiftl ss 8)) in
    let rf := ms_copy_fwd (S (Z.to_nat n)) a1 cs0 a2 bd n ss j0 in let a1F := fst (fst rf) in let csF := snd (fst rf) in
    let j1 := (clearmask (zget ft (Z.shiftl (ss + 1) 8)) - 1)%Z in
    let rb := ms_copy_bwd (S (Z.to_nat n)) a1F ce0 a2 bd n ss j1 in let a1B := fst (fst rb) in let ceB := snd (fst rb) in
    let ftm := ms_mark 256 ft ss 0 in
    (0 <= i <= 255)%Z -> (0 <= ss < 256)%Z ->
    zget bd ss = 0%Z -> ftv ft ->
    (forall k, let '(r, jk) := ms_copy_fwd k a1 cs0 a2 bd n ss j0 in fwdF a2 bd n ss (fst r) (snd r) jk) ->
    (zget csF ss <= snd rf)%Z ->
    (forall k, let '(r, jk) := ms_copy_bwd k a1F ce0 a2 bd n ss j1 in bwdF a2 bd n ss (fst r) (snd r) jk) ->
    (snd rb <= zget ceB ss)%Z ->
    (zget csF ss - 1 = zget ceB ss \/ (zget csF ss = 0 /\ zget ceB ss = n - 1))%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m FT (zw32 ft 65537) ->
    u8arr b0segs m BD (zb8 bd 256) -> u32arr b0segs m CS (zw32 cs 256) -> u32arr b0segs m CE (zw32 ce 256) ->
    rw_cells b0segs m P (slm_cells X Y SHF SHn (SQ2 i ss w416 w440)) ->
    mem_inv b0segs m -> munch W2 me m -> wmono b0segs me m ->
    mviews X Y W2 me ->
    (forall (last : bool) m' (SHbd SH6 SH9 : Z) (y5 y6 y7 y13 y14 y15 y16 y17 y28 : word),
      last = (i =? 255)%Z -> saddr (BD + ss) SHbd -> saddr (FT + 1024 * ss) SH6 -> saddr (FT + 1024 * ss + 1024) SH9 ->
      zbok a1B -> pr n a1B 0 (n - 1) -> ftv ftm ->
      (forall c, 0 <= c < 256 -> 0 <= zget csF c <= n)%Z -> (forall c, 0 <= c < 256 -> -1 <= zget ceB c < n)%Z ->
      u8arr b0segs m' A1 (zb8 a1B ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ftm 65537) ->
      u8arr b0segs m' BD (zb8 (zset bd ss 1) 256) -> u32arr b0segs m' CS (zw32 csF 256) -> u32arr b0segs m' CE (zw32 ceB 256) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss)))) ->
      mem_inv b0segs m' -> munch W2 me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 i) (Z_to_bv 64 255) (Z_to_bv 64 (BD + ss)) y13 y14 y15 y16 y17
                            x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) (Z_to_bv 64 SH9) cCM (Z_to_bv 64 (4 * (256 * 256 + ss)))
                            (Z_to_bv 64 (FT + 1024 * ss + 1024)) (Z_to_bv 64 SH6) cSB y28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 (if last then 0xa4438 else 0xa4200)) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 32) x20 (Z_to_bv 64 33) x22 cCM (Z_to_bv 64 ss) (Z_to_bv 64 (ss * 256)) x26 cSB
                          x28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                     F (Z_to_bv 64 0xa3cd0) fc None m (seg_rom b0segs)).
  Proof.
    intros i ss a1 a2 ft bd cs ce w416 w440 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x26 x28 me m.
    intros ci cs0 ce0 j0 rf a1F csF j1 rb a1B ceB ftm Hi Hss BD0 FTV FWF FWfin BWF BWfin A1007 A1OK A2OK BDOK PR AR1 AR2 FTB BDB CSB CEB SLB MI MU WM MV K.
    msenv_open XOK. amenv_open YOK. bz_params. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_BD X Y YSX) as AS1b. pose proof (amsx_1_CS X Y YSX) as AS1c. pose proof (amsx_1_CE X Y YSX) as AS1e.
    pose proof (amsx_2_BD X Y YSX) as AS2b. pose proof (amsx_2_CS X Y YSX) as AS2c. pose proof (amsx_2_CE X Y YSX) as AS2e.
    pose proof (amsx_F_BD X Y YSX) as ASFb. pose proof (amsx_F_CS X Y YSX) as ASFc. pose proof (amsx_F_CE X Y YSX) as ASFe. box_ors.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    mviews_open MV. open_slb_in SLB.
    (* [comment removed for export] *)
    brun_to 0xa3cf4%Z.
    pose proof (saddr_intro (BD + ss)%Z) as ASBD. set (SHbd := ((BD + ss) / 8 + 2147450880)%Z) in *. clearbody SHbd.
    (* [comment removed for export] *)
    brun_to 0xa3d04%Z. rdblk BDB BDOK ss. rewrite BD0.
    (* [comment removed for export] *)
    brun_to 0xa3d50%Z. rewrite sll32_srl30.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
    enter_with (B0_cinit X Y SHF SHn Q XOK YOK YSX 256 0 ss ft cs ce (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mc);
      [st_eq| lia| lia| lia| exact FTV| exact FTB| exact CSB| exact CEB| exact SLB| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs); [exact SHFz| exact MU| sub_fp_solve| lia| lia]| eapply (shpW_sub b0segs); [exact SHFp| exact MU| sub_fp_solve| lia| lia]|].
    intros m1 z10 z16 z17. cbv zeta. intros FTB1 CS1 CE1 SLB1 MI1 MU1 WM1. fold ci in CS1, CE1. fold cs0 in CS1. fold ce0 in CE1.
    clear FTB CSB CEB SLB MI. transport_after_call b0segs mc m1 MU1 WM1. clear MU1 WM1. open_slb_in SLB1.
    pose proof (zw32_length cs0 256 ltac:(lia)) as Lcs0. pose proof (zw32_length ce0 256 ltac:(lia)) as Lce0.
    pose proof (FWF 0%nat) as F0. cbn [ms_copy_fwd fst snd] in F0. destruct F0 as [CSR _]. pose proof (CSR ss ltac:(lia)) as Css.
    pose proof (FTV (256 * ss)%Z ltac:(lia)) as Vs0.
    assert (Hj0 : j0 = clearmask (zget ft (256 * ss))) by (subst j0; rewrite shl8; reflexivity).
    pose proof (clearmask_bounds (zget ft (256 * ss)) ltac:(lia)) as J0r. rewrite <- Hj0 in J0r.
    (* [comment removed for export] *)
    brun.
    replace (CS + ss * 4)%Z with (CS + 4 * ss)%Z by lia. replace (FT + ss * 256 * 4)%Z with (FT + 1024 * ss)%Z by lia.
    pose proof (saddr_intro (FT + 1024 * ss)%Z) as AS6. set (SH6 := ((FT + 1024 * ss) / 8 + 2147450880)%Z) in *. clearbody SH6.
    pose proof (saddr_intro (CS + 4 * ss)%Z) as ASCS. set (SHcs := ((CS + 4 * ss) / 8 + 2147450880)%Z) in *. clearbody SHcs.
    rd32_at FTB1 (256 * ss)%Z.
    (* [comment removed for export] *)
    brun. rd32_at CS1 ss. wstep. rewrite land_CM64, <- Hj0 by lia.
    (* [comment removed for export] *)
    assert (JOINB : forall m' (SH9 : Z) (a1'' ce' : zarr) (jB : Z) (y5 y6 y7 y10 y11 y14 y15 y16 y17 y28 : word),
      saddr (FT + 1024 * ss + 1024) SH9 ->
      rb = (a1'', ce', jB) -> zbok a1'' -> pr n a1'' 0 (n - 1) ->
      (forall c, 0 <= c < 256 -> 0 <= zget csF c <= n)%Z -> (forall c, 0 <= c < 256 -> -1 <= zget ce' c < n)%Z ->
      u8arr b0segs m' A1 (zb8 a1'' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ft 65537) ->
      u8arr b0segs m' BD (zb8 bd 256) -> u32arr b0segs m' CS (zw32 csF 256) -> u32arr b0segs m' CE (zw32 ce' 256) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss)))) ->
      mem_inv b0segs m' -> munch W2 me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 (Z_to_bv 64 (zget ce' ss)) (Z_to_bv 64 (zget csF ss)) y14 y15 y16 y17
                            x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) (Z_to_bv 64 SH9) cCM (Z_to_bv 64 (ss * 4))
                            (Z_to_bv 64 (FT + 1024 * ss + 1024)) (Z_to_bv 64 SH6) cSB y28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 0xa4150) fc None m' (seg_rom b0segs))).
    { intros m' SH9 a1'' ce' jB y5 y6 y7 y10 y11 y14 y15 y16 y17 y28 AS9 Erb OK'' PR'' CSR' CER' AR1' AR2' FTB' BD' CS' CE' SLB' MI' MU' WM'.
      clear AR1 AR2 FTB1 BDB CS1 CE1 SLB1 MI1 MU WM. open_slb_in SLB'.
      assert (EceB : ceB = ce') by (subst ceB; rewrite Erb; reflexivity). rewrite EceB in A1007.
      pose proof (CSR' ss ltac:(lia)) as Cs1. pose proof (CER' ss ltac:(lia)) as Ce1.
      assert (EaB : a1B = a1'') by (subst a1B; rewrite Erb; reflexivity).
      pose proof (zb8_length a1'' ARR1_SIZE ltac:(lia)) as L1''. pose proof (zw32_length csF 256 ltac:(lia)) as LcsF. pose proof (zw32_length ce' 256 ltac:(lia)) as Lce'.
      (* [comment removed for export] *)
      assert (OKK : forall m'' (r10 r11 : word), m'' = m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            r10 r11 (Z_to_bv 64 (zget ce' ss)) (Z_to_bv 64 (zget csF ss)) y14 y15 y16 y17
                            x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) (Z_to_bv 64 SH9) cCM (Z_to_bv 64 (ss * 4))
                            (Z_to_bv 64 (FT + 1024 * ss + 1024)) (Z_to_bv 64 SH6) cSB y28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 0xa418c) fc None m'' (seg_rom b0segs))).
      { intros m'' r10 r11 ->.
        (* [comment removed for export] *)
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (B0_mark X Y SHF SHn Q XOK YOK 256 0 ss ft (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
          [st_eq| lia| lia| lia| exact FTV| exact FTB'| exact SLB'| exact MI'| apply munch_refl| apply wmono_refl
          | eapply (shzW_sub b0segs); [exact SHFz| exact MU'| sub_fp_solve| lia| lia]|].
        intros m2 v10 v12. cbv zeta. intros FTVm FTB2 SLB2 MI2 MU2 WM2. fold ftm in FTVm, FTB2.
        clear FTB' SLB' MI'. transport_after_call b0segs m' m2 MU2 WM2. clear MU2 WM2. open_slb_in SLB2.
        (* [comment removed for export] *)
        brun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (SOb : store_ok b0segs mm (wa (BD + ss)) 1 = true)
            by (eapply (u8arr_storeN_ok b0segs _ BD _ ss 1 _ BD'); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
          change bs with (le1 (Z_to_bv 64 1));
          pose proof (zb8_write1 b0segs mm BD bd 256 ss (Z_to_bv 64 1) BD' ltac:(lia)) as BDw end.
        clear BD'. store_done. rename BDw into BD'. change (wr8 bd ss (bv_unsigned (Z_to_bv 64 1))) with (zset bd ss 1) in BD'.
        (* [comment removed for export] *)
        wstep. wstep. wstep; if_cases Kl; zify_cond_z Kl.
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K true mm SHbd SH6 SH9 _ _ _ _ _ _ _ _ _) end;
            [st_eq| symmetry; apply Z.eqb_eq; lia| exact ASBD| exact AS6| exact AS9| rewrite EaB; exact OK''| rewrite EaB; exact PR''| exact FTVm| exact CSR'| rewrite EceB; exact CER'
            | rewrite EaB; exact AR1'| exact AR2'| exact FTB2| exact BD'| exact CS'| rewrite EceB; exact CE'| exact SLB2| exact MI2| exact MU'| exact WM'].
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K false mm SHbd SH6 SH9 _ _ _ _ _ _ _ _ _) end;
            [st_eq| symmetry; apply Z.eqb_neq; lia| exact ASBD| exact AS6| exact AS9| rewrite EaB; exact OK''| rewrite EaB; exact PR''| exact FTVm| exact CSR'| rewrite EceB; exact CER'
            | rewrite EaB; exact AR1'| exact AR2'| exact FTB2| exact BD'| exact CS'| rewrite EceB; exact CE'| exact SLB2| exact MI2| exact MU'| exact WM']. }
      (* [comment removed for export] *)
      brun. if_cases K7.
      { enter_with (OKK m' _ _); [st_eq| reflexivity]. }
      lazymatch type of K7 with ?c = false => first [apply bveqb_lit_false in K7 | idtac "K7?"] | _ => idtac end.
      wstep; if_cases K8; zify_cond_z K8.
      1:{ exfalso. destruct A1007 as [E7|[E7 _]]; [| lia]. apply K7. replace (zget csF ss + -1)%Z with (zget ce' ss) by lia. reflexivity. }
      wstep. wstep; if_cases K9.
      2:{ first [apply bveqb_lit_false in K9 | idtac "K9?"]. exfalso. destruct A1007 as [E7|[E7 E8]]; [lia|]. apply K9. rewrite E8. reflexivity. }
      enter_with (OKK m' _ _); [st_eq| reflexivity]. }
    (* [comment removed for export] *)
    assert (JOINF : forall m' (a1' cs' : zarr) (jF : Z) (y5 y6 y7 y10 y11 y12 y15 y16 y17 y28 : word),
      rf = (a1', cs', jF) -> zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> 0 <= zget cs' c <= n)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ft 65537) ->
      u8arr b0segs m' BD (zb8 bd 256) -> u32arr b0segs m' CS (zw32 cs' 256) -> u32arr b0segs m' CE (zw32 ce0 256) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss)))) ->
      mem_inv b0segs m' -> munch W2 me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 (Z_to_bv 64 (zget cs' ss)) (Z_to_bv 64 (ss * 4)) y15 y16 y17
                            x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) x22 cCM (Z_to_bv 64 (ss * 4))
                            (Z_to_bv 64 (ss * 256)) (Z_to_bv 64 SH6) cSB y28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 0xa3f9c) fc None m' (seg_rom b0segs))).
    { intros m' a1' cs' jF y5 y6 y7 y10 y11 y12 y15 y16 y17 y28 Erf OK' PR' CSR' AR1' AR2' FTB' BD' CS' CE' SLB' MI' MU' WM'.
      clear AR1 AR2 FTB1 BDB CS1 CE1 SLB1 MI1 MU WM. open_slb_in SLB'.
      assert (EaF : a1F = a1') by (subst a1F; rewrite Erf; reflexivity). assert (EcF : csF = cs') by (subst csF; rewrite Erf; reflexivity).
      pose proof (BWF 0%nat) as B0. cbn [ms_copy_bwd fst snd] in B0. destruct B0 as [CER _]. pose proof (CER ss ltac:(lia)) as Ces.
      pose proof (FTV (256 * ss + 256)%Z ltac:(lia)) as Vs1.
      assert (Hj1 : j1 = (clearmask (zget ft (256 * ss + 256)) - 1)%Z) by (subst j1; rewrite shl8; f_equal; f_equal; f_equal; lia).
      pose proof (clearmask_bounds (zget ft (256 * ss + 256)) ltac:(lia)) as J1r.
      pose proof (zb8_length a1' ARR1_SIZE ltac:(lia)) as L1'. pose proof (zw32_length cs' 256 ltac:(lia)) as Lcs'.
      (* [comment removed for export] *)
      brun_to 0xa3fb0%Z. ack_rd (FT + 1024 * ss + 1024)%Z 4%Z. ack_merge.
      pose proof (saddr_intro (FT + 1024 * ss + 1024)%Z) as AS9. set (SH9 := ((FT + 1024 * ss + 1024) / 8 + 2147450880)%Z) in *. clearbody SH9.
      (* [comment removed for export] *)
      brun.
      replace (CE + ss * 4)%Z with (CE + 4 * ss)%Z by lia.
      pose proof (saddr_intro (CE + 4 * ss)%Z) as ASCE. set (SHce := ((CE + 4 * ss) / 8 + 2147450880)%Z) in *. clearbody SHce.
      rd32_at FTB' (256 * ss + 256)%Z.
      (* [comment removed for export] *)
      brun. rd32_at CE' ss. wstep. rewrite land_CM64 by lia. wstep.
      replace (clearmask (zget ft (256 * ss + 256)) + -1)%Z with j1 by lia.
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        assert (Erb : rb = (a1', ce0, j1)) by (subst rb; rewrite EaF; apply ms_copy_bwd_stop; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINB mm SH9 a1' ce0 j1 _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AS9| exact Erb| exact OK'| exact PR'| rewrite EcF; exact CSR'| exact CER| exact AR1'| exact AR2'| exact FTB'| exact BD'| rewrite EcF; exact CS'| exact CE'
          | exact SLB'| exact MI'| exact MU'| exact WM'].
        rewrite EcF. reflexivity.
      - (* [comment removed for export] *)
        wstep. wstep. wstep. wstep.
        enter_with (B0_cbwd X Y SHF SHn Q XOK XSEP YOK YSX (S (Z.to_nat n)) j1 ss SHce a1' a2 bd ce0 (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss)))
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' m');
          [st_eq| lia| lia| exact ASCE| rewrite <- EaF; exact BWF| rewrite <- EaF; fold rb; subst ceB; destruct rb as [[? ?] ?]; exact BWfin
          | exact OK'| exact A2OK| exact BDOK| exact PR'| exact AR1'| exact AR2'| exact BD'| exact CE'| exact SLB'| exact MI'| apply munch_refl| apply wmono_refl
          | eapply (shzW_sub b0segs); [exact SH1| exact MU'| sub_fp_solve| lia| lia]| eapply (shzW_sub b0segs); [exact SH2| exact MU'| sub_fp_solve| lia| lia]
          | eapply (shzW_sub b0segs); [exact SHCE| exact MU'| sub_fp_solve| lia| lia]|].
        intros m2 a1'' ce' jB u5 u6 u7 u28 u17 Erb2 OK'' PR'' CER'' AR1'' AR2'' BD'' CE'' SLB'' MI2 MU2 WM2.
        clear AR1' AR2' BD' CE' SLB' MI'. transport_after_call b0segs m' m2 MU2 WM2. clear MU2 WM2.
        assert (Erb : rb = (a1'', ce', jB)) by (subst rb; rewrite EaF; exact Erb2).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINB mm SH9 a1'' ce' jB _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AS9| exact Erb| exact OK''| exact PR''| rewrite EcF; exact CSR'| exact CER''| exact AR1''| exact AR2''| exact FTB'| exact BD''| rewrite EcF; exact CS'| exact CE''
          | exact SLB''| exact MI2| exact MU'| exact WM'].
        rewrite EcF. reflexivity. }
    clear JOINB.
    (* [comment removed for export] *)
    wstep; if_cases Kf; zify_cond_z Kf.
    - (* [comment removed for export] *)
      assert (Erf : rf = (a1, cs0, j0)) by (subst rf; apply ms_copy_fwd_stop; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINF mm a1 cs0 j0 _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact Erf| exact A1OK| exact PR| exact CSR| exact AR1| exact AR2| exact FTB1| exact BDB| exact CS1| exact CE1| exact SLB1| exact MI1| exact MU| exact WM].
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      enter_with (B0_cfwd X Y SHF SHn Q XOK XSEP YOK YSX (S (Z.to_nat n)) j0 ss SHcs a1 a2 bd cs0 (SQ2 i ss (Z_to_bv 64 SHbd) (Z_to_bv 64 (BD + ss)))
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 m1);
        [st_eq| lia| lia| exact ASCS| exact FWF| fold rf; subst csF; destruct rf as [[? ?] ?]; exact FWfin
        | exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BDB| exact CS1| exact SLB1| exact MI1| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]| eapply (shzW_sub b0segs); [exact SH2| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub b0segs); [exact SHCS| exact MU| sub_fp_solve| lia| lia]|].
      intros m2 a1' cs' jF u5 u6 u7 u28 u12 Erf OK' PR' CSR' AR1' AR2' BD' CS' SLB' MI2 MU2 WM2.
      clear AR1 AR2 BDB CS1 SLB1 MI1. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINF mm a1' cs' jF _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact Erf| exact OK'| exact PR'| exact CSR'| exact AR1'| exact AR2'| exact FTB1| exact BD'| exact CS'| exact CE1| exact SLB'| exact MI2| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
