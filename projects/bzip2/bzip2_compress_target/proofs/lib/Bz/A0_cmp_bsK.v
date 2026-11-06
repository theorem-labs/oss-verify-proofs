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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsS A0_cmp_msV A0_cmp_bsV A0_cmp_fsQ.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Lemma budget_q_magic_mod : ((Z.land (wf_clamp p_wf + -1) 255 * 171) mod 18446744073709551616 / 512 = budget_q)%Z.
Proof. pose proof wf_clamp_rng as W. rewrite land255_wf. rewrite Z.mod_small by lia. apply budget_q_magic. Qed.

Section A0BSK.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X. Hypothesis YOK : amenv_ok X Y.
  Hypothesis YSH : (2147450880 <= SHF)%Z. Hypothesis YSHh : (SHF + 652 <= me_lo X)%Z.
  Hypothesis YSHF : (am_FB Y + 5216 <= SHF \/ SHF + 652 <= am_FB Y)%Z.
  Hypothesis YSHE : (me_E X + 55768 <= SHF \/ SHF + 652 <= me_E X)%Z.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WP5 := [(P + 8, P + 16); (P + 248, P + 256); (P + 392, P + 416); (P + 436, P + 440); (SHF + 634, SHF + 652)]%Z.
  Ltac sbf3 := wstep; change (le1 (Z_to_bv 64 (-13))) with [f3b]; mem_after_store.

  Lemma A0_bs_P5 : forall (m : word -> option byte) (bs jbud : list byte) (v0 v8 : word)
      (v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 : word) (v384 v392 v400 v408 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m P [C8 v0; C8 v8] ->
    rw_cells a0segs m (P + 216) [C8 v216; C8 v224; C8 v232; C8 v240; C8 v248; C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312;
                                 C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376] ->
    rw_cells a0segs m (P + 384) [C8 v384; C8 v392; C8 v400; C8 v408] -> rw_cells a0segs m (P + 436) [CB 4 jbud] ->
    rw_cells a0segs m (SHF + 634) [CB 18 bs] ->
    rw_cells a0segs m (E + 40) [C8 (Z_to_bv 64 FT)] -> rw_cells a0segs m (E + 56) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] ->
    rw_cells a0segs m (E + 88) [C4 (Z_to_bv 64 WORKFACTOR)] -> rw_cells a0segs m (E + 108) [C4 (Z_to_bv 64 n)] -> rw_cells a0segs m (E + 656) [C4 (Z_to_bv 64 0)] ->
    mem_inv a0segs m -> shzW a0segs WP5 m E (E + 55768) ->
    (* [comment removed for export] *)
    (forall m' (SHn : Z) (y12 : word), (10000 <= n)%Z -> saddr (E + 108) SHn ->
       rw_cells a0segs m' P [C8 v0; C8 (Z_to_bv 64 (n * budget_q))] ->
       rw_cells a0segs m' (P + 216) [C8 v216; C8 v224; C8 v232; C8 v240; C8 (Z_to_bv 64 0); C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312;
                                     C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376] ->
       rw_cells a0segs m' (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] ->
       rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 (n * budget_q))] ->
       rw_cells a0segs m' (E + 40) [C8 (Z_to_bv 64 FT)] -> rw_cells a0segs m' (E + 56) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] ->
       rw_cells a0segs m' (E + 88) [C4 (Z_to_bv 64 WORKFACTOR)] -> rw_cells a0segs m' (E + 108) [C4 (Z_to_bv 64 n)] -> rw_cells a0segs m' (E + 656) [C4 (Z_to_bv 64 0)] ->
       mem_inv a0segs m' -> munch WP5 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x97be4) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 128) y12 (Z_to_bv 64 A1) x14 x15 x16 x17
                             (Z_to_bv 64 (E + 108)) cSB (Z_to_bv 64 n) x21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) x24 (Z_to_bv 64 E) (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 SHn) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x558c4) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (SHn : Z) (y10 y11 y12 : word), (n < 10000)%Z -> saddr (E + 108) SHn ->
       rw_cells a0segs m' P [C8 v0; C8 v8] ->
       rw_cells a0segs m' (P + 216) [C8 v216; C8 v224; C8 v232; C8 v240; C8 (Z_to_bv 64 0); C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312;
                                     C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376] ->
       rw_cells a0segs m' (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] ->
       rw_cells a0segs m' (P + 436) [CB 4 jbud] ->
       rw_cells a0segs m' (E + 40) [C8 (Z_to_bv 64 FT)] -> rw_cells a0segs m' (E + 56) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] ->
       rw_cells a0segs m' (E + 88) [C4 (Z_to_bv 64 WORKFACTOR)] -> rw_cells a0segs m' (E + 108) [C4 (Z_to_bv 64 n)] -> rw_cells a0segs m' (E + 656) [C4 (Z_to_bv 64 0)] ->
       mem_inv a0segs m' -> munch WP5 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             y10 y11 y12 (Z_to_bv 64 A1) x14 x15 x16 x17
                             (Z_to_bv 64 (E + 108)) cSB (Z_to_bv 64 n) x21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) x24 (Z_to_bv 64 E) (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 SHn) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x9a33c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 (Z_to_bv 64 SHF) x23 x24 (Z_to_bv 64 E) (Z_to_bv 64 (SHF + 178)) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97a88) fc None m (seg_rom a0segs)).
  Proof.
    intros m bs jbud v0 v8 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 v384 v392 v400 v408
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x27 x28 x29 x30 x31 C0 C216 C384 BUD RZ EFT EPB EWF ENB EVB MI SHE KB KS.
    msenv_open1 XOK. amenv_open YOK. bz_params. box_ors.
    pose proof (munch_refl WP5 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    destruct (rw_cells_CB_C1s a0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 18 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    (* [comment removed for export] *)
    wstep. wstep. do 18 sbf3. clear RZ.
    (* [comment removed for export] *)
    arun_to 0x97b28%Z.
    set (SHn := ((E + 108) / 8 + 2147450880)%Z). assert (ASN : saddr (E + 108) SHn) by reflexivity. clearbody SHn.
    (* [comment removed for export] *)
    arun_to 0x97b74%Z. wstep. lit_store.
    arun_to 0x97b80%Z.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z n) by lia. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (P + 384)%Z ?cs |- _ => idtac "C384 =" cs end end.
    wstep; if_cases Kn; zify_cond_z Kn.
    - (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z WORKFACTOR) by lia.
      (* [comment removed for export] *)
      eapply (evt_cut a0segs (fun ms' => ms' = _)).
      { wstep; if_true_z. wstep. wstep. if_cases Kwf; zify_cond_z Kwf.
        - apply evt_done. rewrite <- (wf_clamp_lt100 Kwf). reflexivity.
        - wstep. apply evt_done. rewrite (wf_clamp_ge100 Kwf). reflexivity. }
      intros ms' ->. pose proof (wf_clamp_rng) as WFR.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep.
      rewrite budget_q_magic_mod.
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (budget0_rng n ltac:(lia)) as BQR.
      wstep. wstep.
      wstep. wstep. wstep.
      enter_with (KB _ SHn _ ltac:(lia) ASN); [st_eq| exact C0| exact C216| exact C384| exact BUD| exact EFT| exact EPB| exact EWF| exact ENB| exact EVB| assumption| exact MU| exact WM].
    - (* [comment removed for export] *)
      wstep.
      enter_with (KS _ SHn _ _ _ ltac:(lia) ASN); [st_eq| exact C0| exact C216| exact C384| exact BUD| exact EFT| exact EPB| exact EWF| exact ENB| exact EVB| assumption| exact MU| exact WM].
  Qed.
End A0BSK.
End ACeilS1.
