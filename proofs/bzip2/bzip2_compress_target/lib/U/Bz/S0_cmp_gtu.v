(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtuA UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
Local Ltac UKit.u_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0GTU.
  Variables (A2 qoff n Bud : Z) (a2z : zarr).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable me : word -> option byte.
  Hypothesis A2OK : zbok a2z.
  Hypothesis NB : (10000 <= n <= (NBLOCKMAX + 19))%Z.
  Hypothesis QO : (n + 34 <= qoff <= n + 35)%Z.
  Hypothesis QAL : ((A2 + qoff) mod 2 = 0)%Z.
  Hypothesis A2R : (0 < A2 /\ A2 + ARR2_SIZE <= alloc_ceiling)%Z.
  Hypothesis BUDR : (0 < Bud /\ Bud + 4 <= 18446744073709551616 /\ Bud mod 4 = 0)%Z.
  Hypothesis SEPB : (A2 + ARR2_SIZE <= Bud \/ Bud + 4 <= A2)%Z.

  Notation POST r := (gtU_post s0segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A2 Bud a2z r me).

  (* [comment removed for export] *)
  Ltac rd8_at AR2 idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (A2OK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac gtu_exit RES :=
    wstep; wstep; cbv beta iota zeta delta [rd8 qrd fst snd] in RES; subst; unfold gtU_post; cbn [fst snd]; finish; try reflexivity.

  (* [comment removed for export] *)
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Ltac pre_step AR2 RES i1 i2 t :=
    urun; rd8_at AR2 (i1 + t)%Z; urun; rd8_at AR2 (i2 + t)%Z; urun;
    let Kb := fresh "Kb" in
    if_cases Kb; zify_cond_z Kb;
    [ rewrite (gtu_pre_ne_t _ a2z i1 i2 t) in RES by exact Kb; gtu_exit RES
    | rewrite (gtu_pre_eq_t _ a2z i1 i2 t) in RES by exact Kb;
      let t' := eval vm_compute in (t + 1)%Z in
      replace (i1 + (t + 1))%Z with (i1 + t')%Z in RES by lia; replace (i2 + (t + 1))%Z with (i2 + t')%Z in RES by lia;
      clear Kb ].

  Lemma S0_gtu_entry : forall (i1 i2 budget : Z) (m : word -> option byte) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
    (0 <= i1 <= n + 14)%Z -> (0 <= i2 <= n + 14)%Z ->
    (-2147483648 <= snd (mainGtU i1 i2 a2z qoff n budget))%Z -> (budget < 2147483648)%Z ->
    u8arr s0segs m A2 (zb8 a2z ARR2_SIZE) -> rw_cells s0segs m Bud [C4 (Z_to_bv 64 budget)] -> mem_inv s0segs m ->
    munch [(Bud, Bud + 4)]%Z me m -> wmono s0segs me m ->
    evt s0segs (POST (mainGtU i1 i2 a2z qoff n budget))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i1) (Z_to_bv 64 i2) (Z_to_bv 64 A2) (Z_to_bv 64 (A2 + qoff)) (Z_to_bv 64 n) (Z_to_bv 64 Bud)
               a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x235ec) fc None m (seg_rom s0segs)).
  Proof.
    intros i1 i2 budget m t0 t1 t2 a6 a7 t3 t4 t5 t6 Hi1 Hi2 BMIN BMAX AR2 BUD MI MU WM.
    bz_params. pose proof alloc_ceiling_le as ACL.
    pose proof (zb8_length a2z ARR2_SIZE ltac:(lia)) as L2.
    remember (mainGtU i1 i2 a2z qoff n budget) as r eqn:RES.
    unfold mainGtU in RES.
    replace (gtu_pre 12 a2z i1 i2) with (gtu_pre 12 a2z (i1 + 0) (i2 + 0)) in RES by (f_equal; lia).
    (* [comment removed for export] *)
    pre_step AR2 RES i1 i2 0%Z.
    pre_step AR2 RES i1 i2 1%Z.
    pre_step AR2 RES i1 i2 2%Z.
    pre_step AR2 RES i1 i2 3%Z.
    pre_step AR2 RES i1 i2 4%Z.
    pre_step AR2 RES i1 i2 5%Z.
    pre_step AR2 RES i1 i2 6%Z.
    pre_step AR2 RES i1 i2 7%Z.
    pre_step AR2 RES i1 i2 8%Z.
    pre_step AR2 RES i1 i2 9%Z.
    pre_step AR2 RES i1 i2 10%Z.
    pre_step AR2 RES i1 i2 11%Z.
    cbn [gtu_pre] in RES.
    (* [comment removed for export] *)
    urun_to 0x2386c%Z.
    subst r. enter_with (S0_gtu_loop A2 qoff n Bud a2z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc me A2OK NB QO QAL A2R BUDR SEPB
                          (S (S (Z.to_nat ((n + 8) / 8)))) (i1 + 12)%Z (i2 + 12)%Z (n + 8)%Z budget m);
      [st_eq| lia| lia| lia| | exact BMIN| lia| exact AR2| exact BUD| exact MI| exact MU| exact WM].
    pose proof (Z.div_pos (n + 8) 8 ltac:(lia) ltac:(lia)). rewrite !Nat2Z.inj_succ, Z2Nat.id by lia. lia.
  Qed.
End S0GTU.

Theorem S0_mainGtU : gtU_spec S0C.
Proof.
  unfold gtU_spec. cbn [ci_segs ci_mainGtU S0C]. intros until a2z.
  intros -> -> -> -> -> -> AR2 BUD MI A2OK Hi1 Hi2 NB QO QAL A2lo A2hi Blo Bhi Bal SEPB BMIN BMAX.
  bz_ceil; bz_params; unfold CEIL, apart in *.
  eapply S0_gtu_entry; try eassumption; try lia.
  - apply munch_refl.
  - apply wmono_refl.
Qed.

End ACeilS1.
