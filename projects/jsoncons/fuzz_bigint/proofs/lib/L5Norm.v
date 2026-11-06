(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigClz L5Defs L5Kn
     L5Core L5CoreSpecs L5Words L5Reduce L5Shl L5MulM.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5Norm.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5NORM.
Import L5CS. Import L5W.
Module PAi := LibSegZ_nzAi. Module PAd := LibSegZ_nzAd. Module PB := LibSegZ_nzB. Module PN := LibSegZ_nzN. Module PD := LibSegZ_nzD.
Module PEi := LibSegZ_nzEi. Module PEd := LibSegZ_nzEd. Module PF := LibSegZ_nzF. Module PG := LibSegZ_nzG. Module PH := LibSegZ_nzH. Module PK := LibSegZ_nzK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition NORM : Z := 0x2246c.
Definition BLTZ : Z := 0x224cc. Definition CLZ0 : Z := 0x224d0. Definition CLZH : Z := 0x224d4. Definition CLZX : Z := 0x224e0.
Definition NEG : Z := 0x224e4. Definition STX : Z := 0x224e8. Definition AFTER1 : Z := 0x224f4. Definition AFTER2 : Z := 0x22500.
Definition E2 : Z := 0x22504. Definition BGEU : Z := 0x22528. Definition F : Z := 0x2252c. Definition AFTER3 : Z := 0x22538.
Definition AFTER4 : Z := 0x22544. Definition K : Z := 0x2254c. Definition RET : Z := 0x22574.
Definition FRAME : Z := 64.
(* [comment removed for export] *)
Definition NORM_SCR : Z := 64 + L5MULM.MULM_SCR.
Definition MAXW : Z := 18446744073709551615.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.

(* [comment removed for export] *)
Definition clz_of (w : Z) : Z := 63 - Z.log2 w.
Lemma clz_of_spec w : 1 <= w < 2 ^ 64 -> 0 <= clz_of w <= 63 /\ 2 ^ 63 <= w * 2 ^ clz_of w < 2 ^ 64.
Proof.
  intros Hw. unfold clz_of. pose proof (Z.log2_spec w ltac:(lia)) as [A B]. pose proof (Z.log2_nonneg w) as C.
  assert (D: Z.log2 w <= 63).
  { destruct (Z_lt_le_dec 63 (Z.log2 w)) as [X|X]; [|exact X]. exfalso.
    assert (2 ^ 64 <= 2 ^ Z.log2 w) by (apply Z.pow_le_mono_r; lia). lia. }
  split. lia.
  replace (2 ^ 63) with (2 ^ Z.log2 w * 2 ^ (63 - Z.log2 w)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  replace (2 ^ 64) with (2 ^ Z.succ (Z.log2 w) * 2 ^ (63 - Z.log2 w)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (Z.pow_pos_nonneg 2 (63 - Z.log2 w) ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma clz_of_unique w c : 1 <= w -> 0 <= c -> 2 ^ 63 <= w * 2 ^ c < 2 ^ 64 -> c = clz_of w.
Proof.
  intros Hw Hc [A B]. unfold clz_of.
  assert (E: Z.log2 (w * 2 ^ c) = 63).
  { apply Z.log2_unique. lia. split. exact A. replace (Z.succ 63) with 64 by lia. exact B. }
  rewrite Z.log2_mul_pow2 in E by lia. lia.
Qed.
(* [comment removed for export] *)
Definition second (nd : nat) (D : list Z) : bool := (2 <=? nd)%nat && (nth_w D (nd - 1) <? nth_w D (nd - 2)).
(* [comment removed for export] *)
Definition norm_words (ws : list Z) (c : Z) (sec : bool) : list Z :=
  let D := L5SHL.shl_result ws c in if sec then mulw_words (firstn (rlen D) D) MAXW else D.

(* [comment removed for export] *)
Definition blocks_of (g : growth) : list (Z * Z) := match g with Same => [] | Grown A cap => [(A, 8 * cap)] end.
Definition obj_after (M' : word -> option byte) (o : Z) (b : L5.bigobj) (rw : list Z) (g : growth) (st' : L5.bstore) : Prop :=
  let m := length rw in let n' := rlen rw in
  let fbg := match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end in
  let fb' := if Nat.eqb n' 0 then Z.land fbg 253 else fbg in
  words_ok rw /\ (n' <= m)%nat /\
  L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' m st') rw /\
  (match st' with L5.BDyn cap _ => Z.of_nat m <= cap | L5.BInl _ _ => (m <= 2)%nat end) /\
  match g with
  | Same => match L5.bo_st b, st' with
            | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
            | L5.BInl _ _, L5.BInl _ _ => True
            | _, _ => False end
  | Grown A cap => L5.bo_dyn b = false /\ cap = 8 /\ st' = L5.BDyn cap A
  end.
(* [comment removed for export] *)
Definition dyn_area (o : Z) (b : L5.bigobj) : list L5.range :=
  match L5.bo_st b with L5.BDyn cap q => [(q, 8 * cap)] | L5.BInl _ _ => [] end.
Definition norm_W (od on px : Z) (bd bn : L5.bigobj) : list L5.range :=
  [(od, 32); (on, 32); (px, 4)] ++ dyn_area od bd ++ dyn_area on bn.
(* [comment removed for export] *)
Definition credits (L : heap_layout) (cr : credit) (k : Z) : Prop :=
  k * hl_k_per_malloc L <= fst cr /\ k * (64 + hl_b_overhead L) <= snd cr.
Definition cnt (b : L5.bigobj) : Z := if L5.bo_dyn b then 0 else 1.
Fixpoint debits (L : heap_layout) (cr : credit) (bl : list (Z * Z)) : credit :=
  match bl with [] => cr | (A, n) :: bl' => debit L (debits L cr bl') n end.

Definition norm_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (od on px sp : Z) (bd bn : L5.bigobj) (wd wn : list Z) (c : Z) (gd gn : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  let nd := L5.bo_len bd in
  c = clz_of (nth_w wd (nd - 1)) /\ 0 <= c <= 63 /\ 2 ^ 63 <= nth_w wd (nd - 1) * 2 ^ c < 2 ^ 64 /\
  let D := L5SHL.shl_result wd c in
  let sec := second nd D in
  getr R' 10%bv = Z_to_bv 64 (if sec then 1 else 0) /\
  L5.u32_at RSEGS M' px c /\
  (exists std stn, obj_after M' od bd (norm_words wd c sec) gd std /\ obj_after M' on bn (norm_words wn c sec) gn stn) /\
  LB' = blocks_of gn ++ blocks_of gd ++ LB /\ cr' = debits L cr (blocks_of gn ++ blocks_of gd) /\
  (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M' A (8 * cap) end) /\
  (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M' A (8 * cap) end) /\
  L5C.hpres L LB sp NORM_SCR (norm_W od on px bd bn) M M' /\
  (* [comment removed for export] *)
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat \/ sec = true end) /\
  (match gn with Same => True | Grown _ _ => (3 <= length (L5SHL.shl_result wn c))%nat \/ sec = true end).

Definition norm_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (od on px sp r : Z) (bd bn : L5.bigobj) (wd wn : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 11%bv = Z_to_bv 64 od -> getr R 12%bv = Z_to_bv 64 on -> getr R 13%bv = Z_to_bv 64 px ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp NORM_SCR ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M od bd -> L5C.obj_limbs RSEGS M bd wd -> (1 <= L5.bo_len bd <= 290)%nat ->
    nth_w wd (L5.bo_len bd - 1) <> 0 -> ((2 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) < 2 ^ 63) ->
    L5.big_at RSEGS M on bn -> L5C.obj_limbs RSEGS M bn wn -> (1 <= L5.bo_len bn <= 290)%nat ->
    ((2 <= L5.bo_len bd)%nat -> (2 <= L5.bo_len bn)%nat /\ exists i, (i < L5.bo_len bn)%nat /\ nth_w wn i <> 0) ->
    od mod 8 = 0 -> on mod 8 = 0 -> sp <= od -> sp <= on -> od + 32 <= hl_sptop L -> on + 32 <= hl_sptop L -> apart od 32 on 32 ->
    L5.defined M od 32 -> L5.defined M on 32 ->
    px mod 4 = 0 -> sp <= px -> px + 4 <= hl_sptop L -> apart px 4 od 32 -> apart px 4 on 32 -> L5.defined M px 4 ->
    (forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bd) + 1 <= cap /\ apart px 4 q (8 * cap)) ->
    (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bn) + 1 <= cap /\ apart px 4 q (8 * cap)) ->
    (* [comment removed for export] *)
    (second (L5.bo_len bd) (L5SHL.shl_result wd (clz_of (nth_w wd (L5.bo_len bd - 1)))) = true ->
       (L5.bo_dyn bd = true -> Z.of_nat (L5.bo_len bd) + 2 <= L5.bo_cap bd) /\ (L5.bo_dyn bn = true -> Z.of_nat (L5.bo_len bn) + 2 <= L5.bo_cap bn)) ->
    (forall cd qd cn qn, L5.bo_st bd = L5.BDyn cd qd -> L5.bo_st bn = L5.BDyn cn qn -> apart qd (8 * cd) qn (8 * cn)) ->
    credits L cr (cnt bd + cnt bn) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (c : Z) (gd gn : growth) LB' cr',
        norm_post L LB cr M M' R R' od on px sp bd bn wd wn c gd gn LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R NORM M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_2243c fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x22574 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M 0x22574 W_22574 r F_22574 eq_refl D_22574 H1 Hr He). Qed.
Lemma rl0 : (0%bv : bv 5) = reg 0. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl22 : (22%bv : bv 5) = reg 22. Proof. apply bv_eq. reflexivity. Qed.
(* [comment removed for export] *)
Lemma br_22394 fx R M : msteps RSEGS (st fx R 0x224cc M) (st fx R (if branch_taken BC_LT (getr R (reg 10)) (getr R (reg 0)) then 0x224e4 else 0x224d0) M).
Proof. rewrite <- rl0, <- rl10. apply (@BDQ.br_site fx M R 0x224cc 0x224e4 (0x224cc%bv : word) _ BC_LT 10 0 _ eq_refl F_224cc eq_refl D_224cc). reflexivity. Qed.
(* [comment removed for export] *)
Lemma br_223c8 fx R M : msteps RSEGS (st fx R 0x22500 M) (st fx R (if branch_taken BC_EQ (getr R (reg 22)) (getr R (reg 0)) then 0x2254c else 0x22504) M).
Proof. rewrite <- rl0, <- rl22. apply (@BDQ.br_site fx M R 0x22500 0x2254c (0x22500%bv : word) _ BC_EQ 22 0 _ eq_refl F_22500 eq_refl D_22500). reflexivity. Qed.
(* [comment removed for export] *)
Lemma br_223f0 fx R M : msteps RSEGS (st fx R 0x22528 M) (st fx R (if branch_taken BC_GEU (getr R (reg 10)) (getr R (reg 11)) then 0x2254c else 0x2252c) M).
Proof. rewrite <- rl10, <- rl11. apply (@BDQ.br_site fx M R 0x22528 0x2254c (0x22528%bv : word) _ BC_GEU 10 11 _ eq_refl F_22528 eq_refl D_22528). reflexivity. Qed.
(* [comment removed for export] *)
Lemma li_22398 fx R M : msteps RSEGS (st fx R 0x224d0 M) (st fx (regupd R (reg 11) (Z_to_bv 64 0)) 0x224d4 M).
Proof.
  rewrite <- rl11. eapply mst_step; [reflexivity | eapply (step_addi RSEGS R _ M _ _ 11%bv 0%bv _ F_224d0 eq_refl D_224d0) |].
  cbn [bv_eqb getr].
  match goal with |- msteps _ (mkst ?r ?p _ _) _ => replace r with (regupd R 11%bv (Z_to_bv 64 0)) by reflexivity; replace p with (Z_to_bv 64 0x224d4 : word) by (apply bv_eq; reflexivity) end.
  apply mst_refl.
Qed.

Lemma word_self (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. apply BG.word_of_unsigned. reflexivity. Qed.
Lemma word_range (w : word) : 0 <= bv_unsigned w < 2 ^ 64. Proof. apply (BL.bvu_range w). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (j : nat) : Z := bv_unsigned (getr R (reg j)).
Definition VAL (R0 R : bvmap 5 word) (sp od on n fbd dd px w0 w1 c fbd2 dd2 : Z) (j : nat) : word :=
  match j with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 od | 34%nat => Z_to_bv 64 on | 35%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 fbd | 37%nat => Z_to_bv 64 dd
  | 38%nat => Z_to_bv 64 px | 40%nat => Z_to_bv 64 w0 | 41%nat => Z_to_bv 64 w1 | 42%nat => getr R (reg 1) | 43%nat => Z_to_bv 64 c
  | 44%nat => Z_to_bv 64 fbd2 | 45%nat => Z_to_bv 64 dd2
  | 48%nat => getr R0 (reg 1) | 49%nat => getr R0 (reg 8) | 50%nat => getr R0 (reg 9) | 51%nat => getr R0 (reg 18) | 52%nat => getr R0 (reg 19)
  | 53%nat => getr R0 (reg 20) | 54%nat => getr R0 (reg 21) | 55%nat => getr R0 (reg 22)
  | _ => getr R (reg j)
  end.
Definition VZ (R0 R : bvmap 5 word) (sp od on n fbd dd px w0 w1 c fbd2 dd2 : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp
  | 33%nat => od | 34%nat => on | 35%nat => n | 36%nat => fbd | 37%nat => dd
  | 38%nat => px | 40%nat => w0 | 41%nat => w1 | 42%nat => U R 1 | 43%nat => c
  | 44%nat => fbd2 | 45%nat => dd2
  | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | 51%nat => U R0 18 | 52%nat => U R0 19 | 53%nat => U R0 20 | 54%nat => U R0 21 | 55%nat => U R0 22
  | _ => U R j
  end.
Lemma VAL_VZ R0 R sp od on n fbd dd px w0 w1 c fbd2 dd2 :
  0 <= sp < 2 ^ 64 -> 0 <= od < 2 ^ 64 -> 0 <= on < 2 ^ 64 -> 0 <= n < 2 ^ 62 -> 0 <= fbd < 256 -> 0 <= dd < 2 ^ 64 -> 0 <= px < 2 ^ 64 ->
  0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= fbd2 < 256 -> 0 <= dd2 < 2 ^ 64 ->
  forall j, bv_unsigned (ev (Env (VAL R0 R sp od on n fbd dd px w0 w1 c fbd2 dd2) (fun _ => [])) j) = VZ R0 R sp od on n fbd dd px w0 w1 c fbd2 dd2 j.
Proof.
  intros until j. cbn [ev]. unfold VAL, VZ, U.
  repeat (lazymatch goal with
          | |- bv_unsigned (match j with _ => _ end) = _ => destruct j as [|j]
          | _ => fail end; try (apply BG.unsigned_lit; lia); try reflexivity).
  all: try (apply BG.unsigned_lit; lia); try reflexivity.
Qed.

(* [comment removed for export] *)
Definition saved (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\
  L5.u64_at RSEGS M (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M (sp - 40) (U R0 19) /\ L5.u64_at RSEGS M (sp - 48) (U R0 20) /\
  L5.u64_at RSEGS M (sp - 56) (U R0 21) /\ L5.u64_at RSEGS M (sp - 64) (U R0 22).
Definition spok (sp : Z) : Prop := sp mod 16 = 0 /\ 1048640 <= sp <= 140737488355328.
Definition at_ret (R0 R' : bvmap 5 word) (sp rv : Z) : Prop :=
  getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\
  getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\
  getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22) /\ getr R' (reg 10) = Z_to_bv 64 rv.
(* [comment removed for export] *)
Definition cs_pass : list nat := [3; 4; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition KSA : list nat := Eval vm_compute in (BG.kept_list 56 PAi.regs0 PAi.regs_out0).
Lemma KSAi_ok : BG.kept_ok 56 PAi.regs0 PAi.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAd_ok : BG.kept_ok 56 PAd.regs0 PAd.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Definition KSB : list nat := Eval vm_compute in (BG.kept_list 56 PB.regs0 PB.regs_out0).
Lemma KSB_ok : BG.kept_ok 56 PB.regs0 PB.regs_out0 KSB = true. Proof. vm_compute. reflexivity. Qed.
Definition KSN : list nat := Eval vm_compute in (BG.kept_list 56 PN.regs0 PN.regs_out0).
Lemma KSN_ok : BG.kept_ok 56 PN.regs0 PN.regs_out0 KSN = true. Proof. vm_compute. reflexivity. Qed.
Definition KSD : list nat := Eval vm_compute in (BG.kept_list 56 PD.regs0 PD.regs_out0).
Lemma KSD_ok : BG.kept_ok 56 PD.regs0 PD.regs_out0 KSD = true. Proof. vm_compute. reflexivity. Qed.
Definition KSE : list nat := Eval vm_compute in (BG.kept_list 56 PEd.regs0 PEd.regs_out0).
Lemma KSEd_ok : BG.kept_ok 56 PEd.regs0 PEd.regs_out0 KSE = true. Proof. vm_compute. reflexivity. Qed.
Definition KSEi : list nat := Eval vm_compute in (BG.kept_list 56 PEi.regs0 PEi.regs_out0).
Lemma KSEi_ok : BG.kept_ok 56 PEi.regs0 PEi.regs_out0 KSEi = true. Proof. vm_compute. reflexivity. Qed.
Definition KSF : list nat := Eval vm_compute in (BG.kept_list 56 PF.regs0 PF.regs_out0).
Lemma KSF_ok : BG.kept_ok 56 PF.regs0 PF.regs_out0 KSF = true. Proof. vm_compute. reflexivity. Qed.
Definition KSG : list nat := Eval vm_compute in (BG.kept_list 56 PG.regs0 PG.regs_out0).
Lemma KSG_ok : BG.kept_ok 56 PG.regs0 PG.regs_out0 KSG = true. Proof. vm_compute. reflexivity. Qed.
Definition KSH : list nat := Eval vm_compute in (BG.kept_list 56 PH.regs0 PH.regs_out0).
Lemma KSH_ok : BG.kept_ok 56 PH.regs0 PH.regs_out0 KSH = true. Proof. vm_compute. reflexivity. Qed.
Definition KSK : list nat := Eval vm_compute in (BG.kept_list 56 PK.regs0 PK.regs_out0).
Lemma KSK_ok : BG.kept_ok 56 PK.regs0 PK.regs_out0 KSK = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_bltz (R : bvmap 5 word) (sp od on px : Z) (nd : nat) (w0 dynb : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 on /\ getr R (reg 9) = Z_to_bv 64 od /\
  getr R (reg 10) = Z_to_bv 64 w0 /\ getr R (reg 11) = Z_to_bv 64 dynb /\ getr R (reg 18) = Z_to_bv 64 px /\
  getr R (reg 19) = Z_to_bv 64 (Z.of_nat nd) /\ getr R (reg 20) = Z_to_bv 64 (od + 16) /\
  getr R (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8) /\ getr R (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1).

Lemma nzAi_conc fx R M (sp od on px fbd w0 : Z) (nd : nat) :
  spok sp -> L5.writable RSEGS M (sp - 64) 64 -> apart (sp - 64) 64 od 32 ->
  1048576 <= od -> od + 32 <= 2 ^ 47 -> od mod 8 = 0 -> 0 <= on < 2 ^ 64 -> 0 <= px < 2 ^ 64 ->
  L5.u8_at RSEGS M od fbd -> 0 <= fbd < 256 -> Z.testbit fbd 0 = false -> L5.u64_at RSEGS M (od + 8) (Z.of_nat nd) -> (1 <= nd <= 2)%nat ->
  L5.u64_at RSEGS M (od + 16 + 8 * (Z.of_nat nd - 1)) w0 -> 0 <= w0 < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 od -> getr R (reg 12) = Z_to_bv 64 on -> getr R (reg 13) = Z_to_bv 64 px ->
  exists fx' R' M', msteps RSEGS (st fx R NORM M) (st fx' R' BLTZ M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_bltz R' sp od on px nd w0 0 /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 Hon Hpx O0 Hfb Hb0 O8n Hn TOP Hw0 H2 H11 H12 H13. unfold apart in *.
  set (Vf := VAL R R sp od on (Z.of_nat nd) fbd 0 px w0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp od on (Z.of_nat nd) fbd 0 px w0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PAi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAi.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PAi.kn0). { unfold know_ok, PAi.kn0. L5K.kn_all ZA. }
  destruct (PAi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PAi.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PAi.regs0 PAi.regs_out0 56 KSA KSAi_ok HR Hag Hregs j Hj). }
  split. { unfold at_bltz. repeat split; rewrite (BG.out_reg PAi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAi.regs_out0]; try reflexivity;
           first [L5K.wordE' ZA Hag | apply BG.word_of_unsigned; L5K.evalE' ZA Hag]. }
  change (SR.ps_cells PAi.ps0) with PAi.cells0 in Hcells. unfold PAi.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PAi.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

Lemma nzAd_conc fx R M (sp od on px fbd dd w0 : Z) (nd : nat) :
  spok sp -> L5.writable RSEGS M (sp - 64) 64 -> apart (sp - 64) 64 od 32 ->
  1048576 <= od -> od + 32 <= 2 ^ 47 -> od mod 8 = 0 -> 0 <= on < 2 ^ 64 -> 0 <= px < 2 ^ 64 ->
  L5.u8_at RSEGS M od fbd -> 0 <= fbd < 256 -> Z.testbit fbd 0 = true -> L5.u64_at RSEGS M (od + 8) (Z.of_nat nd) -> (1 <= nd <= 300)%nat ->
  L5.u64_at RSEGS M (od + 24) dd -> 4096 <= dd -> dd + 8 * Z.of_nat nd <= 2 ^ 47 -> dd mod 8 = 0 -> apart (sp - 64) 64 dd (8 * Z.of_nat nd) ->
  L5.u64_at RSEGS M (dd + 8 * Z.of_nat nd - 8) w0 -> 0 <= w0 < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 od -> getr R (reg 12) = Z_to_bv 64 on -> getr R (reg 13) = Z_to_bv 64 px ->
  exists fx' R' M', msteps RSEGS (st fx R NORM M) (st fx' R' BLTZ M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ at_bltz R' sp od on px nd w0 1 /\ saved M' sp R
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW Sap Olo Ohi O8 Hon Hpx O0 Hfb Hb0 O8n Hn O24 Dlo Dhi D8 Dap TOP Hw0 H2 H11 H12 H13. unfold apart in *.
  set (Vf := VAL R R sp od on (Z.of_nat nd) fbd dd px w0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R R sp od on (Z.of_nat nd) fbd dd px w0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PAd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAd.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PAd.kn0). { unfold know_ok, PAd.kn0. L5K.kn_all ZA. }
  destruct (PAd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PAd.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PAd.regs0 PAd.regs_out0 56 KSA KSAd_ok HR Hag Hregs j Hj). }
  split. { unfold at_bltz. repeat split; rewrite (BG.out_reg PAd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAd.regs_out0]; try reflexivity;
           first [L5K.wordE' ZA Hag | apply BG.word_of_unsigned; L5K.evalE' ZA Hag]. }
  change (SR.ps_cells PAd.ps0) with PAd.cells0 in Hcells. unfold PAd.cells0 in Hcells.
  split. { unfold saved, U. repeat split.
    all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PAd.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_shl1 (R : bvmap 5 word) (sp od px c : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER1 /\ getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 9) = Z_to_bv 64 od /\
  getr R (reg 10) = Z_to_bv 64 od /\ getr R (reg 11) = Z_to_bv 64 c /\ getr R (reg 18) = Z_to_bv 64 px.

Lemma nzB_conc fx (R0 R : bvmap 5 word) M (sp od px c : Z) :
  spok sp -> 1048576 <= px -> px + 4 <= 2 ^ 47 -> px mod 4 = 0 -> apart (sp - 64) 64 px 4 -> L5.writable RSEGS M px 4 ->
  0 <= od < 2 ^ 64 -> 0 <= c <= 63 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 9) = Z_to_bv 64 od -> getr R (reg 11) = Z_to_bv 64 c -> getr R (reg 18) = Z_to_bv 64 px ->
  exists fx' R' M', msteps RSEGS (st fx R CLZX M) (st fx' R' L5SHL.SHL M')
    /\ (forall x, In x KSB -> getr R' (reg x) = getr R (reg x)) /\ at_shl1 R' sp od px c /\ L5.u32_at RSEGS M' px c
    /\ (forall a : word, ~ (px <= bv_unsigned a < px + 4) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Plo Phi P4 Pap PW Hod Hc H2 H9 H11 H18. unfold apart in *.
  set (Vf := VAL R0 R sp od 0 0 0 0 px 0 0 c 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp od 0 0 0 0 px 0 0 c 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PB.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PB.kn0). { unfold know_ok, PB.kn0. L5K.kn_all ZA. }
  destruct (PB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PB.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PB.regs0 PB.regs_out0 56 KSB KSB_ok HR Hag Hregs j Hj). }
  split. { unfold at_shl1, AFTER1. repeat split; rewrite (BG.out_reg PB.regs_out0 E' R' _ Hregs) by lia; cbn [nth PB.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PB.ps0) with PB.cells0 in Hcells. unfold PB.cells0 in Hcells.
  split. { rewrite <- (Z.add_0_r px). eapply L5K.u32_of_KWord4; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PB.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

Lemma nzN_conc fx (R0 R : bvmap 5 word) M (sp od px : Z) :
  spok sp -> 1048576 <= px -> px + 4 <= 2 ^ 47 -> px mod 4 = 0 -> apart (sp - 64) 64 px 4 -> L5.writable RSEGS M px 4 ->
  0 <= od < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 9) = Z_to_bv 64 od -> getr R (reg 18) = Z_to_bv 64 px ->
  exists fx' R' M', msteps RSEGS (st fx R NEG M) (st fx' R' L5SHL.SHL M')
    /\ (forall x, In x KSN -> getr R' (reg x) = getr R (reg x)) /\ at_shl1 R' sp od px 0 /\ L5.u32_at RSEGS M' px 0
    /\ (forall a : word, ~ (px <= bv_unsigned a < px + 4) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Plo Phi P4 Pap PW Hod H2 H9 H18. unfold apart in *.
  set (Vf := VAL R0 R sp od 0 0 0 0 px 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp od 0 0 0 0 px 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PN.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PN.kn0). { unfold know_ok, PN.kn0. L5K.kn_all ZA. }
  destruct (PN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PN.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PN.regs0 PN.regs_out0 56 KSN KSN_ok HR Hag Hregs j Hj). }
  split. { unfold at_shl1, AFTER1. repeat split; rewrite (BG.out_reg PN.regs_out0 E' R' _ Hregs) by lia; cbn [nth PN.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  change (SR.ps_cells PN.ps0) with PN.cells0 in Hcells. unfold PN.cells0 in Hcells.
  split. { rewrite <- (Z.add_0_r px). eapply L5K.u32_of_KWord4; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
  split. { intros x Hx. apply Hfr. unfold PN.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_shl2 (R : bvmap 5 word) (sp on px c : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 AFTER2 /\ getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 on /\
  getr R (reg 10) = Z_to_bv 64 on /\ getr R (reg 11) = Z_to_bv 64 c /\ getr R (reg 18) = Z_to_bv 64 px.

Lemma nzD_conc fx (R0 R : bvmap 5 word) M (sp on px c : Z) :
  spok sp -> 1048576 <= px -> px + 4 <= 2 ^ 47 -> px mod 4 = 0 -> apart (sp - 64) 64 px 4 -> L5.u32_at RSEGS M px c -> 0 <= c <= 63 ->
  0 <= on < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on -> getr R (reg 18) = Z_to_bv 64 px ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER1 M) (st fx' R' L5SHL.SHL M')
    /\ (forall x, In x KSD -> getr R' (reg x) = getr R (reg x)) /\ at_shl2 R' sp on px c /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Plo Phi P4 Pap PX Hc Hon H2 H8 H18. unfold apart in *.
  set (Vf := VAL R0 R sp 0 on 0 0 0 px 0 0 c 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp 0 on 0 0 0 px 0 0 c 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PD.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PD.kn0). { unfold know_ok, PD.kn0. L5K.kn_all ZA. }
  destruct (PD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PD.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PD.regs0 PD.regs_out0 56 KSD KSD_ok HR Hag Hregs j Hj). }
  split. { unfold at_shl2, AFTER2. repeat split; rewrite (BG.out_reg PD.regs_out0 E' R' _ Hregs) by lia; cbn [nth PD.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_bgeu (R : bvmap 5 word) (sp od : Z) (w1 w0 : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 9) = Z_to_bv 64 od /\ getr R (reg 10) = Z_to_bv 64 w1 /\ getr R (reg 11) = Z_to_bv 64 w0.

Lemma nzEd_conc fx (R0 R : bvmap 5 word) M (sp od fbd2 dd2 w1 w0 : Z) (nd : nat) :
  spok sp -> apart (sp - 64) 64 od 32 -> 1048576 <= od -> od + 32 <= 2 ^ 47 -> od mod 8 = 0 ->
  L5.u8_at RSEGS M od fbd2 -> 0 <= fbd2 < 256 -> Z.testbit fbd2 0 = true -> L5.u64_at RSEGS M (od + 24) dd2 ->
  4096 <= dd2 -> dd2 + 8 * Z.of_nat nd <= 2 ^ 47 -> dd2 mod 8 = 0 -> (2 <= nd <= 300)%nat ->
  L5.u64_at RSEGS M (dd2 + 8 * Z.of_nat nd - 8) w1 -> L5.u64_at RSEGS M (dd2 + 8 * Z.of_nat nd - 16) w0 -> 0 <= w1 < 2 ^ 64 -> 0 <= w0 < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 9) = Z_to_bv 64 od -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nd) ->
  getr R (reg 20) = Z_to_bv 64 (od + 16) -> getr R (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1) ->
  exists fx' R' M', msteps RSEGS (st fx R E2 M) (st fx' R' BGEU M')
    /\ (forall x, In x KSE -> getr R' (reg x) = getr R (reg x)) /\ at_bgeu R' sp od w1 w0 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Sap Olo Ohi O8 O0 Hfb Hb0 O24 Dlo Dhi D8 Hn X1 X0 Hw1 Hw0 H2 H9 H19 H20 H21 H22. unfold apart in *.
  set (Vf := VAL R0 R sp od 0 (Z.of_nat nd) 0 0 0 w1 w0 0 fbd2 dd2). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp od 0 (Z.of_nat nd) 0 0 0 w1 w0 0 fbd2 dd2 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PEd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PEd.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PEd.kn0). { unfold know_ok, PEd.kn0. L5K.kn_all ZA. }
  destruct (PEd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PEd.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PEd.regs0 PEd.regs_out0 56 KSE KSEd_ok HR Hag Hregs j Hj). }
  split. { unfold at_bgeu. repeat split; rewrite (BG.out_reg PEd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PEd.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

Lemma nzEi_conc fx (R0 R : bvmap 5 word) M (sp od fbd2 w1 w0 : Z) :
  spok sp -> apart (sp - 64) 64 od 32 -> 1048576 <= od -> od + 32 <= 2 ^ 47 -> od mod 8 = 0 ->
  L5.u8_at RSEGS M od fbd2 -> 0 <= fbd2 < 256 -> Z.testbit fbd2 0 = false ->
  L5.u64_at RSEGS M (od + 24) w1 -> L5.u64_at RSEGS M (od + 16) w0 -> 0 <= w1 < 2 ^ 64 -> 0 <= w0 < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 9) = Z_to_bv 64 od -> getr R (reg 19) = Z_to_bv 64 2 ->
  getr R (reg 20) = Z_to_bv 64 (od + 16) -> getr R (reg 21) = Z_to_bv 64 8 -> getr R (reg 22) = Z_to_bv 64 1 ->
  exists fx' R' M', msteps RSEGS (st fx R E2 M) (st fx' R' BGEU M')
    /\ (forall x, In x KSEi -> getr R' (reg x) = getr R (reg x)) /\ at_bgeu R' sp od w1 w0 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Sap Olo Ohi O8 O0 Hfb Hb0 X1 X0 Hw1 Hw0 H2 H9 H19 H20 H21 H22. unfold apart in *.
  set (Vf := VAL R0 R sp od 0 2 0 0 0 w1 w0 0 fbd2 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp od 0 2 0 0 0 w1 w0 0 fbd2 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PEi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PEi.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PEi.kn0). { unfold know_ok, PEi.kn0. L5K.kn_all ZA. }
  destruct (PEi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PEi.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PEi.regs0 PEi.regs_out0 56 KSEi KSEi_ok HR Hag Hregs j Hj). }
  split. { unfold at_bgeu. repeat split; rewrite (BG.out_reg PEi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PEi.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_mul (R : bvmap 5 word) (sp o ra : Z) : Prop :=
  getr R (reg 1) = Z_to_bv 64 ra /\ getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 10) = Z_to_bv 64 o /\ getr R (reg 11) = Z_to_bv 64 MAXW.

Lemma nzF_conc fx (R0 R : bvmap 5 word) M (sp od : Z) :
  spok sp -> 0 <= od < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 9) = Z_to_bv 64 od ->
  exists fx' R' M', msteps RSEGS (st fx R F M) (st fx' R' L5MULM.MULM M')
    /\ (forall x, In x KSF -> getr R' (reg x) = getr R (reg x)) /\ at_mul R' sp od AFTER3 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Hod H2 H9.
  set (Vf := VAL R0 R sp od 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp od 0 0 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PF.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PF.kn0). { unfold know_ok, PF.kn0. L5K.kn_all ZA. }
  destruct (PF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PF.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PF.regs0 PF.regs_out0 56 KSF KSF_ok HR Hag Hregs j Hj). }
  split. { unfold at_mul, AFTER3, MAXW. repeat split; rewrite (BG.out_reg PF.regs_out0 E' R' _ Hregs) by lia; cbn [nth PF.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

Lemma nzG_conc fx (R0 R : bvmap 5 word) M (sp on : Z) :
  spok sp -> 0 <= on < 2 ^ 64 -> getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER3 M) (st fx' R' L5MULM.MULM M')
    /\ (forall x, In x KSG -> getr R' (reg x) = getr R (reg x)) /\ at_mul R' sp on AFTER4 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] Hon H2 H8.
  set (Vf := VAL R0 R sp 0 on 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp 0 on 0 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PG.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PG.kn0). { unfold know_ok, PG.kn0. L5K.kn_all ZA. }
  destruct (PG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PG.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PG.regs0 PG.regs_out0 56 KSG KSG_ok HR Hag Hregs j Hj). }
  split. { unfold at_mul, AFTER4, MAXW. repeat split; rewrite (BG.out_reg PG.regs_out0 E' R' _ Hregs) by lia; cbn [nth PG.regs_out0]; try reflexivity; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nzH_conc fx (R0 R : bvmap 5 word) M (sp : Z) :
  spok sp -> L5.writable RSEGS M (sp - 64) 64 -> saved M sp R0 -> getr R (reg 2) = Z_to_bv 64 (sp - 64) ->
  exists fx' R' M', msteps RSEGS (st fx R AFTER4 M) (st fx' R' RET M')
    /\ (forall x, In x KSH -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp 1 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV H2. pose proof SV as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). unfold U in *.
  set (Vf := VAL R0 R sp 0 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp 0 0 0 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PH.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PH.kn0). { unfold know_ok, PH.kn0. L5K.kn_all ZA. }
  destruct (PH.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PH.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PH.regs0 PH.regs_out0 56 KSH KSH_ok HR Hag Hregs j Hj). }
  split. { unfold at_ret. repeat split; rewrite (BG.out_reg PH.regs_out0 E' R' _ Hregs) by lia; cbn [nth PH.regs_out0 edenot];
           first [reflexivity | rewrite <- (proj1 Hag) by lia; reflexivity | L5K.wordE' ZA Hag]. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

Lemma nzK_conc fx (R0 R : bvmap 5 word) M (sp : Z) :
  spok sp -> L5.writable RSEGS M (sp - 64) 64 -> saved M sp R0 -> getr R (reg 2) = Z_to_bv 64 (sp - 64) ->
  exists fx' R' M', msteps RSEGS (st fx R K M) (st fx' R' RET M')
    /\ (forall x, In x KSK -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp 0 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV H2. pose proof SV as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). unfold U in *.
  set (Vf := VAL R0 R sp 0 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ R0 R sp 0 0 0 0 0 0 0 0 0 0 0 j) by (apply VAL_VZ; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PK.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PK.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PK.kn0). { unfold know_ok, PK.kn0. L5K.kn_all ZA. }
  destruct (PK.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PK.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PK.regs0 PK.regs_out0 56 KSK KSK_ok HR Hag Hregs j Hj). }
  split. { unfold at_ret. repeat split; rewrite (BG.out_reg PK.regs_out0 E' R' _ Hregs) by lia; cbn [nth PK.regs_out0 edenot];
           first [reflexivity | rewrite <- (proj1 Hag) by lia; reflexivity | L5K.wordE' ZA Hag]. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.
End SCFG_2.


End L5NORM.
