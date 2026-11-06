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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msI B0_cmp_msW B0_cmp_msF B0_cmp_fsW.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Ltac sx_norm_all := repeat match goal with |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_of_Z_signed v) by lia end.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id; demod; sx_norm_all.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  (* [comment removed for export] *)
  Variables (w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w328 w336 w344 w352 w480 : word).
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation NSLO := (18446744073709551615 - am_SLO Y)%Z.
  Notation W1 := [(A1, A1 + ARR1_SIZE)]%Z.
  Notation WST := [(P, P + 496); (P + 500, P + 536); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation SLJ q312 q392 q408 q416 q440 :=
    (slm_cells X Y SHF SHn (mkSLQ w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 q312 w328 w336 w344 w352 q392 q408 q416 q440 w480)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma B0_qswap1 : forall (lo hi ltLo unLo unHi gtHi : Z) (a1 : zarr) (w312 w392 w440 : word)
      (x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells b0segs m P (SLJ w312 w392 (Z_to_bv 64 hi) (Z_to_bv 64 lo) w440) -> mem_inv b0segs m ->
    munch W1 me m -> wmono b0segs me m ->
    shzW b0segs W1 me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x10' x11' x12' x17' x28' x29' x30' x31' : word),
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells b0segs m' P (SLJ w312 w392 (Z_to_bv 64 hi) (Z_to_bv 64 lo) w440) -> mem_inv b0segs m' ->
      munch W1 me m' -> wmono b0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13 x14 x15 (Z_to_bv 64 unLo) x17'
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa2cc4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + 4 * lo)) x11 x12 x13 x14 x15 (Z_to_bv 64 unLo) x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2b94) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi a1 w312 w392 w440 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgt Hhi A1OK PR AR1 SLB MI MU WM SH1 K.
    msenv_open XOK. amenv_open YOK. bz_params. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    assert (JOIN : forall (y11 y12 : word),
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A1 + 4 * lo)) y11 y12 x13 x14 x15 (Z_to_bv 64 unLo) (Z_to_bv 64 (mmin (ltLo - lo) (unLo - ltLo)))
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa2bc8) fc None m (seg_rom b0segs))).
    2:{ brun. if_cases Kc; zify_cond_z Kc.
        - enter_with (JOIN _ _). unfold mmin. replace (ltLo - lo <? unLo - ltLo) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep. enter_with (JOIN _ _). unfold mmin. replace (ltLo - lo <? unLo - ltLo) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    intros y11 y12.
    set (nn := mmin (ltLo - lo) (unLo - ltLo)) in *.
    assert (Hnn : (nn <= ltLo - lo /\ nn <= unLo - ltLo /\ (nn = ltLo - lo \/ nn = unLo - ltLo))%Z).
    { subst nn. unfold mmin. destruct (Z.ltb_spec (ltLo - lo) (unLo - ltLo)); lia. }
    clearbody nn.
    (* [comment removed for export] *)
    brun. if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - rewrite mvswap_S in K. replace (0 <? nn) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact SLB| exact MI| exact MU| exact WM| exact A1OK| exact PR].
    - (* [comment removed for export] *)
      brun_to 0xa2be8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (B0_vswap1 X Y SHF SHn Q XOK YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo hi (S (Z.to_nat nn)) nn lo (unLo - nn)%Z a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact SLB| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia] |].
      intros m' x29' x30' x31'. cbv zeta. intros AR1' SLB' MI' MU' WM' OK' PR'.
      clear AR1 SLB MI. lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU' WM' end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1'| exact SLB'| exact MI'| exact MU| exact WM| exact OK'| exact PR'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_qswap2 : forall (lo hi ltLo unLo unHi gtHi : Z) (a1 : zarr) (w312 w392 w440 : word)
      (x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> rw_cells b0segs m P (SLJ w312 w392 (Z_to_bv 64 hi) (Z_to_bv 64 lo) w440) -> mem_inv b0segs m ->
    munch W1 me m -> wmono b0segs me m ->
    shzW b0segs W1 me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x5' x6' x10' x11' x17' x28' x29' x30' : word),
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1' := mvswap (S (Z.to_nat mm)) a1 unLo (hi - mm + 1) mm in
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> rw_cells b0segs m' P (SLJ w312 w392 (Z_to_bv 64 hi) (Z_to_bv 64 lo) w440) -> mem_inv b0segs m' ->
      munch W1 me m' -> wmono b0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                            x10' x11' (Z_to_bv 64 (gtHi - unHi)) x13 x14 x15 (Z_to_bv 64 unLo) x17'
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28' x29' x30' x31)
                       F (Z_to_bv 64 0xa2e10) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 (Z_to_bv 64 unLo) x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2cc4) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi a1 w312 w392 w440 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgt Hhi A1OK PR AR1 SLB MI MU WM SH1 K.
    msenv_open XOK. amenv_open YOK. bz_params. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    assert (JOIN : forall (y10 y11 : word),
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (mmin (hi - gtHi) (gtHi - unHi))) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                            y10 y11 (Z_to_bv 64 (gtHi - unHi)) x13 x14 x15 (Z_to_bv 64 unLo) x17
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa2cf8) fc None m (seg_rom b0segs))).
    2:{ brun. if_cases Kc; zify_cond_z Kc.
        - enter_with (JOIN _ _). unfold mmin. replace (hi - gtHi <? gtHi - unHi) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep. enter_with (JOIN _ _). unfold mmin. replace (hi - gtHi <? gtHi - unHi) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    intros y10 y11.
    set (mm := mmin (hi - gtHi) (gtHi - unHi)) in *.
    assert (Hmm : (mm <= hi - gtHi /\ mm <= gtHi - unHi /\ (mm = hi - gtHi \/ mm = gtHi - unHi))%Z).
    { subst mm. unfold mmin. destruct (Z.ltb_spec (hi - gtHi) (gtHi - unHi)); lia. }
    clearbody mm.
    (* [comment removed for export] *)
    brun. if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - rewrite mvswap_S in K. replace (0 <? mm) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact SLB| exact MI| exact MU| exact WM| exact A1OK| exact PR].
    - (* [comment removed for export] *)
      brun_to 0xa2d34%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
        enter_with (B0_vswap2 X Y SHF SHn Q XOK YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo hi (S (Z.to_nat mm)) mm unLo (hi - mm + 1)%Z a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm0 mm0) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact SLB| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia] |].
      intros m' x11' x29' x30'. cbv zeta. intros AR1' SLB' MI' MU' WM' OK' PR'.
      clear AR1 SLB MI. lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU' WM' end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1'| exact SLB'| exact MI'| exact MU| exact WM| exact OK'| exact PR'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Ltac st_stk ARR idx v :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of ARR with u32arr _ _ ?BASE _ =>
        let SO := fresh "SO" in
        pose proof (u32arr_store_ok b0segs mm BASE _ idx _ ARR ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO;
        wstep; ovw_store ARR idx v (apply unsigned_lit_mod32); try clear SO end end.

  (* [comment removed for export] *)
  Lemma B0_push3 : forall (qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d SHl SHh SHd : Z) (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Z)
      (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (w312 w408 w416 : word)
      (x5 x6 x7 x10 x11 x12 x16 x17 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= qsp <= 97)%Z ->
    (forall v, In v [v0l; v0h; v0d; v1l; v1h; v1d; v2l; v2h; v2d] -> - 2147483648 <= v < 2147483648)%Z ->
    saddr (SLO + 4 * (qsp - 1)) SHl -> saddr (SHI + 4 * (qsp - 1)) SHh -> saddr (SD + 4 * (qsp - 1)) SHd ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr b0segs m SLO (ovw slo Jlo 100) -> u32arr b0segs m SHI (ovw shi Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLJ w312 (Z_to_bv 64 (SHI + 4 * (qsp - 1))) w408 w416 (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
    rw_cells b0segs m (P + 500) [C4 (Z_to_bv 64 c0); C4 (Z_to_bv 64 c1); C4 (Z_to_bv 64 c2); C4 (Z_to_bv 64 c3); C4 (Z_to_bv 64 c4); C4 (Z_to_bv 64 c5);
                                 C4 (Z_to_bv 64 c6); C4 (Z_to_bv 64 c7); C4 (Z_to_bv 64 c8)] ->
    (c0 = v0d /\ c1 = v1d /\ c2 = v2d /\ c3 = v0h /\ c4 = v1h /\ c5 = v2h /\ c6 = v0l /\ c7 = v1l /\ c8 = v2l)%Z ->
    mem_inv b0segs m -> munch WST me m -> wmono b0segs me m ->
    shzW b0segs WST me SLO (SLO + 400) -> shzW b0segs WST me SHI (SHI + 400) -> shzW b0segs WST me SD (SD + 400) ->
    (forall m',
      u32arr b0segs m' SLO (ovw (zset (zset (zset slo (qsp - 1) v0l) qsp v1l) (qsp + 1) v2l) Jlo 100) ->
      u32arr b0segs m' SHI (ovw (zset (zset (zset shi (qsp - 1) v0h) qsp v1h) (qsp + 1) v2h) Jhi 100) ->
      u32arr b0segs m' SD (ovw (zset (zset (zset sd (qsp - 1) v0d) qsp v1d) (qsp + 1) v2d) Jd 100) ->
      rw_cells b0segs m' P (SLJ (Z_to_bv 64 (qsp + 2)) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) w408 w416 (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
      rw_cells b0segs m' (P + 500) [C4 (Z_to_bv 64 c0); C4 (Z_to_bv 64 c1); C4 (Z_to_bv 64 c2); C4 (Z_to_bv 64 c3); C4 (Z_to_bv 64 c4); C4 (Z_to_bv 64 c5);
                                    C4 (Z_to_bv 64 c6); C4 (Z_to_bv 64 c7); C4 (Z_to_bv 64 c8)] ->
      mem_inv b0segs m' -> munch WST me m' -> wmono b0segs me m' ->
      bfree_at X Y Q 0xa38bc m') ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) x16 x17
                          x18 x19 x20 x21 x22 (Z_to_bv 64 NSLO) x24 (Z_to_bv 64 (SD + 4 * (qsp - 1))) (Z_to_bv 64 qsp) cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa3018) fc None m (seg_rom b0segs)).
  Proof.
    intros qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d SHl SHh SHd c0 c1 c2 c3 c4 c5 c6 c7 c8 slo shi sd Jlo Jhi Jd w312 w408 w416
           x5 x6 x7 x10 x11 x12 x16 x17 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 me m
           Hq HV ASl ASh ASd LJlo LJhi LJd SLOB SHIB SDB SLB NX EC MI MU WM SHZl SHZh SHZd K.
    destruct EC as (-> & -> & -> & -> & -> & -> & -> & -> & ->).
    msenv_open XOK. amenv_open YOK. open_slb_in SLB.
    assert (R0l := HV v0l ltac:(cbn; tauto)). assert (R0h := HV v0h ltac:(cbn; tauto)). assert (R0d := HV v0d ltac:(cbn; tauto)).
    assert (R1l := HV v1l ltac:(cbn; tauto)). assert (R1h := HV v1h ltac:(cbn; tauto)). assert (R1d := HV v1d ltac:(cbn; tauto)).
    assert (R2l := HV v2l ltac:(cbn; tauto)). assert (R2h := HV v2h ltac:(cbn; tauto)). assert (R2d := HV v2d ltac:(cbn; tauto)). clear HV.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    brun. st_stk SLOB (qsp - 1)%Z v0l.
    brun. st_stk SHIB (qsp - 1)%Z v0h.
    brun. st_stk SDB (qsp - 1)%Z v0d.
    (* [comment removed for export] *)
    brun. st_stk SLOB qsp v1l.
    brun. st_stk SHIB qsp v1h.
    brun. st_stk SDB qsp v1d.
    (* [comment removed for export] *)
    brun. st_stk SLOB (qsp + 1)%Z v2l.
    brun. st_stk SHIB (qsp + 1)%Z v2h.
    brun. st_stk SDB (qsp + 1)%Z v2d.
    (* [comment removed for export] *)
    brun_to 0xa38bc%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (K mm SLOB SHIB SDB SLB NX ltac:(assumption) ltac:(assumption) ltac:(assumption)) as KK end.
    unfold bfree_at in KK. enter_with KK. st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Ltac qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me v0l v0h v0d v1l v1h v1d v2l v2h v2d :=
    brun_to 0xa3018%Z;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_push3 qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d SHl SHh SHd _ _ _ _ _ _ _ _ _ slo shi sd Jlo Jhi Jd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| exact Hq| intros v Hv; cbn in Hv; lia| exact ASl| exact ASh| exact ASd| exact LJlo| exact LJhi| exact LJd| exact SLOB| exact SHIB| exact SDB| exact SLB| exact NX
      | repeat split; lia| exact MI| exact MU| exact WM| exact SHZl| exact SHZh| exact SHZd| ];
    let m' := fresh "m'" in
    intros m' SLO' SHI' SD' SLB' NX' MI' MU' WM';
    eapply (K m' _ _ _ _ _ _ _ _ _); [exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact MI'| exact MU'| exact WM'].

  (* [comment removed for export] *)
  Lemma B0_qnext : forall (lo hi d ltLo unLo gu qsp SHl SHh SHd : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (w312 : word) (nx : nxt)
      (x5 x6 x10 x11 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= hi + 1)%Z -> (0 <= gu <= hi + 1 - unLo)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 97)%Z ->
    saddr (SLO + 4 * (qsp - 1)) SHl -> saddr (SHI + 4 * (qsp - 1)) SHh -> saddr (SD + 4 * (qsp - 1)) SHd ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr b0segs m SLO (ovw slo Jlo 100) -> u32arr b0segs m SHI (ovw shi Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLJ w312 (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
    rw_cells b0segs m (P + 500) (nxt_cells nx) -> mem_inv b0segs m ->
    munch WST me m -> wmono b0segs me m ->
    shzW b0segs WST me SLO (SLO + 400) -> shzW b0segs WST me SHI (SHI + 400) -> shzW b0segs WST me SD (SD + 400) ->
    (forall m' (z0 z1 z2 z3 z4 z5 z6 z7 z8 : word),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - gu + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      u32arr b0segs m' SLO (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr b0segs m' SHI (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr b0segs m' SD (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      rw_cells b0segs m' P (SLJ (Z_to_bv 64 (qsp + 2)) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
      rw_cells b0segs m' (P + 500) (nxt_cells (mkNXT z0 z1 z2 z3 z4 z5 z6 z7 z8)) -> mem_inv b0segs m' -> munch WST me m' -> wmono b0segs me m' ->
      bfree_at X Y Q 0xa38bc m') ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          x10 x11 (Z_to_bv 64 gu) (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) (Z_to_bv 64 unLo) x17
                          x18 x19 x20 x21 x22 (Z_to_bv 64 NSLO) (Z_to_bv 64 d) (Z_to_bv 64 (SD + 4 * (qsp - 1))) (Z_to_bv 64 qsp) cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2e10) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi d ltLo unLo gu qsp SHl SHh SHd slo shi sd Jlo Jhi Jd w312 nx x5 x6 x10 x11 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgu Hhi Hd Hq ASl ASh ASd LJlo LJhi LJd SLOB SHIB SDB SLB NX MI MU WM SHZl SHZh SHZd K.
    msenv_open XOK. amenv_open YOK. bz_params. open_slb_in SLB. open_nx_in NX.
    cbv zeta in K.
    set (kn := (lo + unLo - ltLo - 1)%Z) in K. set (km := (hi - gu + 1)%Z) in K. unfold srt2 in K. cbv beta iota delta [nsz] in K.
    assert (Ekn : kn = (lo + unLo - ltLo - 1)%Z) by reflexivity. assert (Ekm : km = (hi - gu + 1)%Z) by reflexivity.
    (* [comment removed for export] *)
    brun_to 0xa2f44%Z. wstep; if_cases Kc1; zify_cond_z Kc1.
    - replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
      brun_to 0xa2f98%Z. wstep; if_cases Kc2; zify_cond_z Kc2.
      + replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        brun_to 0xa2ff8%Z. wstep; if_cases Kc3; zify_cond_z Kc3.
        * replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
        * replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
      + replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        brun_to 0xa2ff8%Z. wstep; if_cases Kc3; zify_cond_z Kc3.
        * replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z.
        * replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z.
    - replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
      brun_to 0xa2f98%Z. wstep; if_cases Kc2; zify_cond_z Kc2.
      + replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        brun_to 0xa2ff8%Z. wstep; if_cases Kc3; zify_cond_z Kc3.
        * replace (hi - km <? kn - lo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
        * replace (hi - km <? kn - lo) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
      + replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        brun_to 0xa2ff8%Z. wstep; if_cases Kc3; zify_cond_z Kc3.
        * replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z.
        * replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SLB NX MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd Hq qsp SHl SHh SHd slo shi sd Jlo Jhi Jd me (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
