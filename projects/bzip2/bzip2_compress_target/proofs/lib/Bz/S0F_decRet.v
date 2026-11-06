(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
Module S0_indexIntoF.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
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
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition S0_indexIntoF_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (indx : Z) (CF : Z) (ws : list word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (index_into_f indx (sv32 ws))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [] m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ u32arr s0segs m' CF ws.

Section P.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 x a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (CF : Z) (ws : list word).
  Hypothesis ARR : u32arr s0segs m CF ws.
  Hypothesis LEN : length ws = 257%nat.
  Hypothesis MI : mem_inv s0segs m.

  Notation indx := (bv_signed x).
  Notation POST := (S0_indexIntoF_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_signed x) CF ws m).
  (* [comment removed for export] *)
  Notation ST pc nb na x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x (Z_to_bv 64 CF) (Z_to_bv 64 nb) (Z_to_bv 64 na) (Z_to_bv 64 1) x15 x16 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Lemma S0_iif_loop : forall (k : nat) (nb na : Z) (x15 x16 : word),
    (na - nb = 2 ^ (Z.of_nat k))%Z -> (1 <= k)%nat -> (0 <= nb)%Z -> (na <= 256)%Z ->
    munch [] m m -> wmono s0segs m m ->
    index_into_f indx (sv32 ws) = fst (iif_loop (sv32 ws) indx nb na k) ->
    evt s0segs POST (ST 0x14528 nb na x15 x16).
  Proof.
    induction k as [|k IH]; intros nb na x15 x16 HK Hk NB NA MU WM RES; [lia|].
    pose proof (u32arr_bound s0segs m CF ws ARR) as CFB. rewrite LEN in CFB.
    assert (P2 : (0 < 2 ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in HK by lia.
    wstep. wstep. wstep. wstep.
    set (mid := ((nb + na) / 2)%Z) in *.
    assert (HM : (mid = nb + 2 ^ Z.of_nat k)%Z) by (subst mid; mlia).
    destruct (nth_error_ok ws mid 257 LEN ltac:(lia)) as [w NTH].
    pose proof (u32arr_read s0segs m CF ws mid w _ ARR NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    (* [comment removed for export] *)
    cbn [iif_loop] in RES. rewrite (zb_shiftr_div (nb + na) 1) in RES by lia. change (2^1)%Z with 2%Z in RES.
    fold mid in RES. rewrite (sv32_nth ws mid w NTH) in RES.
    pose proof (swrap32_range (bv_unsigned w)) as WR.
    wstep. if_cases K; zify_cond K; rewrite sx32_signed in K.
    - (* [comment removed for export] *)
      replace (bv_swrap 32 (bv_unsigned w) <=? indx)%Z with false in RES by (symmetry; apply Z.leb_gt; lia).
      replace (mid - nb)%Z with (2 ^ Z.of_nat k)%Z in RES by lia.
      wstep. wstep. wstep. if_cases K2; zify_cond K2.
      + replace (2 ^ Z.of_nat k =? 1)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia).
        apply (IH nb mid); try assumption; try lia. destruct k; [cbn in K2; lia| lia].
      + replace (2 ^ Z.of_nat k =? 1)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia).
        cbn [fst] in RES. wstep. wstep. rewrite <- RES. unfold S0_indexIntoF_post. finish.
    - (* [comment removed for export] *)
      replace (bv_swrap 32 (bv_unsigned w) <=? indx)%Z with true in RES by (symmetry; apply Z.leb_le; lia).
      replace (na - mid)%Z with (2 ^ Z.of_nat k)%Z in RES by lia.
      wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2.
      + replace (2 ^ Z.of_nat k =? 1)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia).
        apply (IH mid na); try assumption; try lia. destruct k; [cbn in K2; lia| lia].
      + replace (2 ^ Z.of_nat k =? 1)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia).
        cbn [fst] in RES. wstep. wstep. rewrite <- RES. unfold S0_indexIntoF_post. finish.
  Qed.

  Lemma S0_indexIntoF_walk : forall x11 x12 x13 x14 x15 x16,
    x11 = Z_to_bv 64 CF ->
    evt s0segs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1451c) fc None m (seg_rom s0segs)).
  Proof.
    intros until x16. intros ->.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    wstep. wstep. wstep.
    apply (S0_iif_loop 8); try assumption; try reflexivity; lia.
  Qed.
End P.

Lemma S0_indexIntoF_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (CF : Z) (ws : list word),
  u32arr s0segs m CF ws -> length ws = 257%nat -> mem_inv s0segs m ->
  a1 = Z_to_bv 64 CF ->
  evt s0segs (S0_indexIntoF_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_signed a0) CF ws m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1451c) fc None m (seg_rom s0segs)).
Proof. intros. eapply S0_indexIntoF_walk; eassumption. Qed.

End ACeilS1.
End S0_indexIntoF.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zb8_length_nat, ?zw32_length_nat, ?zh16_length_nat in *.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SasFastF RelLia.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition QF (A : act14) (r : dres) : machine_state -> Prop := FPOST14 DI_S0 A (dfin r).

(* [comment removed for export] *)
Definition S0F_RET (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt s0segs (Q (DRet rv L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) x20 x21 x22 x23 x24 x25 x26 x27
              (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d63c) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_RET_OK (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt s0segs (Q (DRet BZ_OK L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) x20 x21 x22 x23 x24 x25 x26 x27
              (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d638) (a_fc A) None m (seg_rom s0segs)).

(* [comment removed for export] *)
Definition S0F_RET_DATA (A : act14) (Q : dres -> machine_state -> Prop) : Prop :=
  forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (a_usp A + -320) ->
    munch (W14 DI_S0 (a_cx A) (a_usp A)) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt s0segs (Q (DRet BZ_DATA_ERROR L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_usp A + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (a_S A + 64036)) x9
              x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_S A)) x20 x21 x22 x23 x24 x25 x26 x27
              (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d6fc) (a_fc A) None m (seg_rom s0segs)).

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  Lemma S0F_dec_retc : forall (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
      (m : word -> option byte)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt s0segs (QF A (DRet rv L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) x20 x21 x22 x23 x24 x25 x26 x27
              (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d648) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros until pb. intros DM FR ST MU WM MI DP Hnb PO.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    open_dmemF DM. s2img.
    hide_all_but (SAV, FR).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S + 64036, S + 64144); (usp + -320, usp)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    do 30 wstep.
    (* [comment removed for export] *)
    apply (rw_cells_merge_firstn s0segs _ _ _ 11) in SAV. cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in SAV.
    apply (rw_cells_merge_mid s0segs _ _ _ 2 12) in SAV. cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in SAV.
    revive_all MUL WML AOK.
    do 15 wstep.
    release_frame FR ST (bv_unsigned (a_sp A)).
    lazymatch type of SAV with rw_cells _ ?mm _ [CB 44 ?j1; _; CB 60 ?j2] =>
      apply evt_done; unfold QF, FPOST14; cbn [dfin];
      do 14 eexists; exists mm, (jk_set_s J j1 j2)
    end.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [close_dmemF|].
    split; [exact ST|].
    split; [|exact PO].
    dpureF_solve DP.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_dec_ret4 : forall (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
      (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
      (m : word -> option byte)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z -> dpost14 (d_set_sv d L) ->
    evt s0segs (QF A (DRet rv L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 rv) x11 f184 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) x20 x21 x22 x23 x24 x25 x26 x27
              (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d640) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros until pb. intros DM FR ST MU WM MI DP Hnb PO.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
    wstep. wstep.
    enter_with S0F_dec_retc; [ st_eq | exact DM | exact FR | exact ST | exact MU | exact WM | exact MI | exact DP | exact Hnb | exact PO ].
  Qed.

  Lemma S0F_dec_ret : S0F_RET A (QF A).
  Proof.
    unfold S0F_RET. intros until pb. intros DM FR ST MU WM MI DP Hnb PO.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
    wstep.
    enter_with S0F_dec_ret4; [ st_eq | exact DM | exact FR | exact ST | exact MU | exact WM | exact MI | exact DP | exact Hnb | exact PO ].
  Qed.

  Lemma S0F_dec_ret_ok : S0F_RET_OK A (QF A).
  Proof.
    unfold S0F_RET_OK. intros until pb. intros DM FR ST MU WM MI DP Hnb PO.
    wstep.
    enter_with S0F_dec_ret; [ st_eq | exact DM | exact FR | exact ST | exact MU | exact WM | exact MI | exact DP | exact Hnb | exact PO ].
  Qed.

  Lemma S0F_dec_ret_data : S0F_RET_DATA A (QF A).
  Proof.
    unfold S0F_RET_DATA. intros until pb. intros DM FR ST MU WM MI DP Hnb PO.
    wstep. wstep.
    enter_with S0F_dec_ret; [ st_eq | exact DM | exact FR | exact ST | exact MU | exact WM | exact MI | exact DP | exact Hnb | exact PO ].
  Qed.
End R.

End ACeilS1.
