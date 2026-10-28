(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Strategy 1000 [ms_ftab_zero].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section UFZ.
  Variables (FT P : Z) (Q : machine_state -> Prop).
  Variables (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HFT0 : (0 < FT)%Z. Hypothesis HFT4 : (FT mod 4 = 0)%Z. Hypothesis HFTP : (FT + 262148 <= P)%Z.
  Hypothesis HP : (P + 312 <= 2 ^ 64)%Z.
  Notation WF := [(FT, FT + 262148)]%Z.

  Tactic Notation "zw32_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.

  Lemma U_ftab_zero : forall (cnt : nat) (i : Z) (ft : zarr) (x13 x14 : word) (me m : word -> option byte),
    (Z.of_nat cnt = i + 1)%Z -> (0 <= i <= 65536)%Z -> (forall v, 0 <= zget ft v < 4294967296)%Z ->
    u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    rw_cells s0segs m (P + 304) [C8 (Z_to_bv 64 FT)] ->
    munch WF me m -> wmono s0segs me m ->
    (forall m' (x13' x14' : word), let ft' := ms_ftab_zero cnt ft i in
      (forall v, 0 <= zget ft' v < 4294967296)%Z ->
      u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' ->
      rw_cells s0segs m' (P + 304) [C8 (Z_to_bv 64 FT)] ->
      munch WF me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) x13' x14'
                            a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x20524) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) x13 x14
                          a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x204dc) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros i ft x13 x14 me m Hcnt Hi FTW FTB MI FR MU WM K.
    pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    cbn [ms_ftab_zero] in K.
    urun_to 0x2051c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ i _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v))
    | _ => idtac end.
    zw32_store_at FTB i 0%Z (reflexivity).
    assert (FTW1 : forall v, (0 <= zget (zset ft i 0) v < 4294967296)%Z) by (intros v; rewrite zget_zset; destruct (v =? i); [lia| apply FTW]).
    wstep; if_cases Kc.
    - apply negb_true_iff in Kc. apply bveqb_lit_false in Kc.
      assert (Hi1 : (1 <= i)%Z) by (clear -Kc Hi; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (i - 1)%Z (zset ft i 0) _ _ me mm) end;
        [st_eq| lia| lia| exact FTW1| exact FTB| exact MI| exact FR| exact MU| exact WM| exact K].
    - apply negb_false_iff in Kc. unfold bv_eqb in Kc. apply Z.eqb_eq in Kc. rewrite !Z_to_bv_unsigned in Kc.
      unfold bv_wrap, bv_modulus in Kc. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in Kc.
      assert (Hi0 : (i = 0)%Z) by (clear -Kc Hi; Z.div_mod_to_equations; lia).
      assert (cnt = 0%nat) as -> by lia. cbn [ms_ftab_zero] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact FTW1| exact FTB| exact MI| exact FR| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End UFZ.

End ACeilS1.
