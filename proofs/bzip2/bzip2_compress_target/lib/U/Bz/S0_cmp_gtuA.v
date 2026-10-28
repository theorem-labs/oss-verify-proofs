(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit UKit.
From Stdlib Require Lia. Unset Lia Cache.
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
  Ltac rd16_at AR2 idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read2 segs mm A a nn (qoff + 2 * idx) _ AR2 ltac:(lia) ltac:(lia) A2OK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "Qy" in pose proof (rd16_range a (qoff + 2 * idx) A2OK) as B;
      rewrite (zx16_lit (rd16 a (qoff + 2 * idx))) by lia
    end.

  (* [comment removed for export] *)
  Ltac gtu_exit RES :=
    wstep; wstep; cbv beta iota zeta delta [rd8 qrd fst snd] in RES; subst; unfold gtU_post; cbn [fst snd]; finish; try reflexivity.

  (* [comment removed for export] *)
  Ltac oct_step AR2 RES i1 i2 t :=
    urun; rd8_at AR2 (i1 + t)%Z; urun; rd8_at AR2 (i2 + t)%Z; urun;
    let Kb := fresh "Kb" in
    if_cases Kb; zify_cond_z Kb;
    [ rewrite (gtu_oct_bne_t _ a2z qoff i1 i2 t) in RES by exact Kb; gtu_exit RES
    | urun; rd16_at AR2 (i1 + t)%Z; urun; rd16_at AR2 (i2 + t)%Z; urun;
      let Kq := fresh "Kq" in
      if_cases Kq; zify_cond_z Kq;
      [ rewrite (gtu_oct_qne_t _ a2z qoff i1 i2 t) in RES by first [exact Kb | exact Kq]; gtu_exit RES
      | rewrite (gtu_oct_eq_t _ a2z qoff i1 i2 t) in RES by first [exact Kb | exact Kq];
        let t' := eval vm_compute in (t + 1)%Z in
        replace (i1 + (t + 1))%Z with (i1 + t')%Z in RES by lia; replace (i2 + (t + 1))%Z with (i2 + t')%Z in RES by lia;
        clear Kb Kq ] ].

  Lemma S0_gtu_loop : forall (f : nat) (i1 i2 k budget : Z) (m : word -> option byte) (t2 t3 t4 t5 t6 : word),
    (0 <= i1 <= n + 26)%Z -> (0 <= i2 <= n + 26)%Z -> (0 <= k <= n + 8)%Z -> (k / 8 + 2 <= Z.of_nat f)%Z ->
    (-2147483648 <= snd (gtu_loop f a2z qoff n i1 i2 k budget))%Z -> (budget < 2147483648)%Z ->
    u8arr s0segs m A2 (zb8 a2z ARR2_SIZE) -> rw_cells s0segs m Bud [C4 (Z_to_bv 64 budget)] -> mem_inv s0segs m ->
    munch [(Bud, Bud + 4)]%Z me m -> wmono s0segs me m ->
    evt s0segs (POST (gtu_loop f a2z qoff n i1 i2 k budget))
      (MS (mkR ra sp gp tp (Z_to_bv 64 i2) (Z_to_bv 64 k) t2 s0 s1 (Z_to_bv 64 (18446744073709551615 - (A2 + qoff))) (Z_to_bv 64 1)
               (Z_to_bv 64 A2) (Z_to_bv 64 (A2 + qoff)) (Z_to_bv 64 n) (Z_to_bv 64 Bud)
               (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 i1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2386c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros. exfalso. pose proof (Z.div_pos k 8). lia. }
    intros i1 i2 k budget m t2 t3 t4 t5 t6 Hi1 Hi2 Hk Hf BMIN BMAX AR2 BUD MI MU WM.
    bz_params. pose proof alloc_ceiling_le as ACL.
    pose proof (zb8_length a2z ARR2_SIZE ltac:(lia)) as L2.
    remember (gtu_loop (S f) a2z qoff n i1 i2 k budget) as r eqn:RES.
    rewrite gtu_loop_S in RES.
    replace (gtu_oct 8 a2z qoff i1 i2) with (gtu_oct 8 a2z qoff (i1 + 0) (i2 + 0)) in RES by (f_equal; lia).
    (* [comment removed for export] *)
    urun. rd8_at AR2 (i1 + 0)%Z. urun. rd8_at AR2 (i2 + 0)%Z. urun.
    if_cases Kb; zify_cond_z Kb.
    { rewrite (gtu_oct_bne_t _ a2z qoff i1 i2 0) in RES by exact Kb. gtu_exit RES. }
    urun. rd16_at AR2 (i1 + 0)%Z. urun. rd16_at AR2 (i2 + 0)%Z. urun.
    if_cases Kq; zify_cond_z Kq.
    { rewrite (gtu_oct_qne_t _ a2z qoff i1 i2 0) in RES by first [exact Kb | exact Kq]. gtu_exit RES. }
    rewrite (gtu_oct_eq_t _ a2z qoff i1 i2 0) in RES by first [exact Kb | exact Kq].
    replace (i1 + (0 + 1))%Z with (i1 + 1)%Z in RES by lia. replace (i2 + (0 + 1))%Z with (i2 + 1)%Z in RES by lia. clear Kb Kq.
    oct_step AR2 RES i1 i2 1%Z.
    oct_step AR2 RES i1 i2 2%Z.
    oct_step AR2 RES i1 i2 3%Z.
    oct_step AR2 RES i1 i2 4%Z.
    oct_step AR2 RES i1 i2 5%Z.
    oct_step AR2 RES i1 i2 6%Z.
    oct_step AR2 RES i1 i2 7%Z.
    cbn [gtu_oct] in RES.
    assert (BLO : (-2147483648 <= budget - 1)%Z).
    { destruct (0 <=? k - 8)%Z; [| subst r; cbn in BMIN; lia].
      pose proof (gtu_loop_budget_le f a2z qoff n (gwrap n (i1 + 8)) (gwrap n (i2 + 8)) (k - 8) (budget - 1)) as LE.
      rewrite <- RES in LE. lia. }
    (* [comment removed for export] *)
    urun_to 0x23b44%Z. wstep. rewrite (sx32_of_Z_signed budget) by lia.
    urun_to 0x23b50%Z.
    wstep. wstep. wstep. wstep. wstep. wstep. rewrite (gwrap_sub_flag n (i1 + 8)) by lia.
    wstep. wstep. wstep. wstep. rewrite (gwrap_sub_flag n (i2 + 8)) by lia.
    wstep. wstep.
    wstep; if_cases Kk; [apply bgez_taken in Kk; [|lia] | apply bgez_not_taken in Kk; [|lia]].
    - (* [comment removed for export] *)
      replace (0 <=? k - 8)%Z with true in RES by (symmetry; apply Z.leb_le; lia).
      pose proof (gwrap_ge n (i1 + 8)) as W1. pose proof (gwrap_lt n (i1 + 8)) as W1'.
      pose proof (gwrap_ge n (i2 + 8)) as W2. pose proof (gwrap_lt n (i2 + 8)) as W2'.
      subst r. enter_with (IH (gwrap n (i1 + 8)) (gwrap n (i2 + 8)) (k - 8)%Z (budget - 1)%Z);
        [st_eq| lia| lia| lia| lia| exact BMIN| lia| exact AR2| assumption| assumption| assumption| assumption].
    - (* [comment removed for export] *)
      replace (0 <=? k - 8)%Z with false in RES by (symmetry; apply Z.leb_gt; lia). subst r.
      wstep. wstep. unfold gtU_post. cbn [fst snd]. finish; try reflexivity.
  Qed.
End S0GTU.

End ACeilS1.
