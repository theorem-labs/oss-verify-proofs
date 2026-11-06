(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells Step.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_free_kit BF_poison BF_popdefs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cstep := stepA; try first [if_true | if_false].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
(* [comment removed for export] *)
Ltac sub_fp_fast :=
  let xq := fresh "xq" in let Hq := fresh "Hq" in
  intros xq Hq; cbn [outside] in Hq |- *; decompose [and] Hq; clear Hq;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end.
Ltac munch_fold mc m' MUc :=
  match goal with H : munch ?W ?ma mc |- _ =>
    let H2 := fresh in
    assert (H2 : munch W ma m') by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc]; sub_fp_fast]);
    clear H; rename H2 into H end.
Ltac after_callF mc m' MUc WMc := munch_fold mc m' MUc; after_call mc m' MUc WMc.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_POP : Z := 0x37c04.
Definition A_POP_MMRET : Z := 0x37d24.     (* [comment removed for export] *)
Definition A_POP_MID : Z := 0x37d78.       (* [comment removed for export] *)
Definition A_POP_NAME : Z := 0x170bc.      (* [comment removed for export] *)

Section POP.
Variable P : acc -> Prop.
Variables (gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (SB c RI STAT req : Z).
Notation INST := 0xaaf58.
Notation RIc := (BF_popdefs.RIc c RI).
Notation RB := (SB + c * 4294967296).          (* [comment removed for export] *)

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 1536.
Hypothesis SPH : usp < 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HSBH : kHighMemBeg <= SB.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis HREQ : 1 <= req <= hint c.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition pop_frame (m : mem) (ra s0 s1 s2 s3 s4 s5 s6 : word) : Prop :=
  rw_cells bsegs m (usp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma req_size_small : req * class_size c <= 65536.
Proof. aceil.
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in HC; lia)) as [_ CS].
  unfold hint, max_cached_hint, kMaxNumCachedHint, kMaxBytesCached in HREQ.
  destruct (Z.eqb_spec (class_size c) 0) as [E|NE]; [lia|].
  assert (H1 : req <= Z.max 1 (Z.min 8 (1024 / class_size c))) by lia.
  destruct (Z_le_gt_dec (1024 / class_size c) 1) as [LE|GT].
  - assert (req <= 1) by lia. nia.
  - assert (R8 : req <= 1024 / class_size c) by lia.
    assert (req * class_size c <= (1024 / class_size c) * class_size c) by nia.
    pose proof (Z.mul_div_le 1024 (class_size c) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma pop_grow2 : forall (ra s6 t0 t1 t2 a1x a5 a6 a7 : word) (m : mem) (mtx nf mfa au mu na nfr : Z) (Q : machine_state -> Prop),
  mem_inv bsegs m ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m RIc (ri_cells mtx nf mfa au mu na nfr) ->
  0 <= au <= mu -> mu mod 4096 = 0 -> mu + 262144 <= 3758096384 -> mu < au + req * class_size c ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_POP_MMRET) (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT)
                          (Z_to_bv 64 INST) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 262144) (Z_to_bv 64 A_POP_NAME) (Z_to_bv 64 req) a5 a6 a7
                          (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 (class_size c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x6f978) fc None m (seg_rom bsegs)) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT) (Z_to_bv 64 INST) a1x (Z_to_bv 64 c)
                          (Z_to_bv 64 au) (Z_to_bv 64 req) a5 a6 a7 (Z_to_bv 64 RB) (Z_to_bv 64 (au + req * class_size c)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x37ca8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI INS RIC AUMU MUA MUR GROW K. unfold A_POP_MMRET, A_POP_NAME, ri_cells in *.
  pose proof HSB as (SB1 & SB2 & SB3). unfold kSpaceSize in SB3; aceil.
  unfold kLargestClassID in HC. pose proof req_size_small as RS. pose proof (proj2 (class_size_mod c ltac:(clear -CEILB HC; lia))) as CS.
  set (sz := class_size c) in *. clearbody sz.
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *.
  assert (HRIv : 0x603000 <= RIv /\ RIv + 128 <= 2^47) by (subst RIv; rewrite HRI; unfold kSpaceSize; clear -CEILB SB1 SB3 HC; lia).
  assert (RBR : 0 <= SB + c * 4294967296 /\ SB + c * 4294967296 + mu + 262144 <= 2^47) by (clear -CEILB SB1 SB3 HC MUR AUMU; nia).
  do 2 zstepA.        (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  rewrite (ZBridge.zb_lxor_ones mu) by (clear -CEILB AUMU MUR; lia).
  replace ((au + req * sz + (18446744073709551615 - mu)) mod 18446744073709551616) with (au + req * sz - mu - 1)
    by (clear -CEILB AUMU MUR GROW RS; Z.div_mod_to_equations; lia).
  change 18446744073709289472 with (2^64 - 2^18). rewrite land_align_down by (clear -CEILB AUMU MUR GROW RS; lia). change (2^18) with 262144.
  rewrite (Z.mod_small (au + req * sz - mu - 1) 262144) by (clear -CEILB AUMU GROW RS; lia). rewrite Z.sub_diag, Z.add_0_l.
  do 2 zstepA.        (* [comment removed for export] *)
  do 2 zstepA.        (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  zstepA. if_cases KX; zify_cond KX; [exfalso; revert KX; rewrite ?unsigned_lit by (clear -CEILB AUMU MUR; lia); clear -CEILB AUMU MUR; intros KX; lia|]. clear KX.  (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  cstep.              (* [comment removed for export] *)
  do 2 zstepA.        (* [comment removed for export] *)
  do 3 zstepA.        (* [comment removed for export] *)
  cstep.              (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (mu + (SB + c * 4294967296)) with (SB + c * 4294967296 + mu) by (clear; lia).
  exact K.
Qed.

(* [comment removed for export] *)
Lemma pop_grow1 : forall (ra s6 t0 t1 t2 a1x a5 a6 a7 : word) (m : mem) (mtx nf mfa au mu na nfr : Z) (Q : machine_state -> Prop),
  mem_inv bsegs m ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m RIc (ri_cells mtx nf mfa au mu na nfr) ->
  0 <= au <= mu -> mu mod 4096 = 0 -> mu + 262144 <= 3758096384 -> mu < au + req * class_size c ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_POP_MMRET) (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT)
                          (Z_to_bv 64 INST) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 262144) (Z_to_bv 64 A_POP_NAME) (Z_to_bv 64 req) a5 a6 a7
                          (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 (class_size c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x6f978) fc None m (seg_rom bsegs)) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT) (Z_to_bv 64 INST) a1x (Z_to_bv 64 c)
                          (Z_to_bv 64 au) (Z_to_bv 64 req) a5 a6 a7 (Z_to_bv 64 RB) (Z_to_bv 64 (au + req * class_size c)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x37ca4) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI INS RIC AUMU MUA MUR GROW K. unfold ri_cells in *.
  unfold kLargestClassID in HC. pose proof req_size_small as RS. pose proof (proj2 (class_size_mod c ltac:(clear -CEILB HC; lia))) as CS.
  pose proof HSB as (SB1 & SB2 & SB3). unfold kSpaceSize in SB3; aceil.
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  assert (HRIr : 0x603000 <= RIv /\ RIv + 128 <= 2^47) by (rewrite HRIv, HRI; unfold kSpaceSize; clear -CEILB SB1 SB3 HC; lia).
  zstepA; if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear -CEILB AUMU MUR; lia).
  - (* [comment removed for export] *)
    zstepA.           (* [comment removed for export] *)
    zstepA. if_cases KN; zify_cond KN;
      (let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 4294967295))) in change (bv_unsigned (sx32 (Z_to_bv 64 4294967295))) with v in KN);
      [| exfalso; clear -CEILB KN; lia].   (* [comment removed for export] *)
    zstepA. zstepA.   (* [comment removed for export] *)
    subst mu RIv. eapply pop_grow2; [exact MI| exact INS| exact RIC| exact AUMU| exact MUA| exact MUR| exact GROW| exact K].
  - subst RIv. eapply pop_grow2; [exact MI| exact INS| exact RIC| exact AUMU| exact MUA| exact MUR| exact GROW| exact K].
Qed.

(* [comment removed for export] *)
Lemma pop_size_big : forall (ra spw s0 s1 s2 s3 s4 s5 s6 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 : word) (m : mem) (Q : machine_state -> Prop),
  17 <= c <= 30 ->
  (forall (a3' a5' a6' : word),
     evtA bsegs P Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 c) a3' a4 a5' a6' a7 s2 s3 s4 (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x37c8c) fc None m (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x37c68) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros HCB K.
  assert (CASES : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by (clear -CEILB HCB; lia).
  clear HCB.
  repeat match type of CASES with
  | _ \/ _ => destruct CASES as [E|CASES]
  | _ => rename CASES into E
  end.
  all: rewrite E in K; rewrite E; do 9 zstepA; eapply K.
Qed.

(* [comment removed for export] *)
Lemma pop_pre : forall (ra s0 s1 s2 s3 s4 s5 s6 t0 t1 t2 a5 a6 a7 : word) (m : mem) (mtx nf mfa au mu na nfr : Z) (Q : machine_state -> Prop),
  stk bsegs m lo usp -> mem_inv bsegs m ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m RIc (ri_cells mtx nf mfa au mu na nfr) ->
  0 <= au <= mu -> mu mod 4096 = 0 -> mu + 262144 <= 3758096384 ->
  (* [comment removed for export] *)
  (forall m' (a5' a6' : word), au + req * class_size c <= mu ->
     mem_inv bsegs m' -> stk bsegs m' lo (usp - 64) -> munch [(usp - 64, usp)] m m' -> wmono bsegs m m' -> pop_frame m' ra s0 s1 s2 s3 s4 s5 s6 ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT) (Z_to_bv 64 INST) (Z_to_bv 64 (c * 4294967296)) (Z_to_bv 64 c)
                             (Z_to_bv 64 au) (Z_to_bv 64 req) a5' a6' a7 (Z_to_bv 64 RB) (Z_to_bv 64 (au + req * class_size c)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 A_POP_MID) fc None m' (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall m' (a5' a6' : word), mu < au + req * class_size c ->
     mem_inv bsegs m' -> stk bsegs m' lo (usp - 64) -> munch [(usp - 64, usp)] m m' -> wmono bsegs m m' -> pop_frame m' ra s0 s1 s2 s3 s4 s5 s6 ->
     evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_POP_MMRET) (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT)
                             (Z_to_bv 64 INST) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 262144) (Z_to_bv 64 A_POP_NAME) (Z_to_bv 64 req) a5' a6' a7
                             (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 (class_size c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x6f978) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 STAT) (Z_to_bv 64 c) (Z_to_bv 64 RIc) (Z_to_bv 64 req) a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_POP) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros SK MI INS RIC AUMU MUA MUR KNO KGR. unfold A_POP, A_POP_MID, pop_frame, ri_cells in *.
  pose proof LOC as LOC0. aceil. pose proof HSB as (SB1 & SB2 & SB3). unfold kSpaceSize in SB3; aceil.
  unfold kLargestClassID in HC. pose proof req_size_small as RS. pose proof (proj2 (class_size_mod c ltac:(clear -CEILB HC; lia))) as CS.
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  assert (HRIr : 0x603000 <= RIv /\ RIv + 128 <= 2^47) by (rewrite HRIv, HRI; unfold kSpaceSize; clear -CEILB SB1 SB3 HC; lia).
  assert (MU : munch [(usp - 64, usp)] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 64%nat SK.
  do 9 zstepA.        (* [comment removed for export] *)
  do 2 zstepA.        (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  do 2 zstepA.        (* [comment removed for export] *)
  rewrite !(Z.shiftl_mul_pow2 c 32) by (clear; lia). change (2^32) with 4294967296.
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear -CEILB HC; lia); clear -CEILB HC; lia|]. clear K0.   (* [comment removed for export] *)
  zstepA.             (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tail5 CS RS HC AUMU MUR :=
    zstepA; zstepA;   (* [comment removed for export] *)
    zstepA;           (* [comment removed for export] *)
    zstepA;           (* [comment removed for export] *)
    zstepA;           (* [comment removed for export] *)
    rewrite ?(Z.mul_comm (class_size c) req); rewrite ?(Z.mod_small (req * class_size c) 18446744073709551616) by (clear -CS RS HC; lia).
  zstepA; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear -CEILB HC; lia).
  - (* [comment removed for export] *)
    eapply pop_size_big; [clear -CEILB K1 HC; lia|]. intros a3' a5' a6'.
    tail5 CS RS HC AUMU MUR.
    zstepA; if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear -CEILB HC AUMU MUR RS HREQ CS; lia).
    + (* [comment removed for export] *)
      replace (usp + -64) with (usp - 64) by (clear; lia). subst RIv.
      eapply KNO; [clear -CEILB KB; lia| exact MI| exact SK| exact MU| exact WM| exact FR].
    + replace (usp + -64) with (usp - 64) by (clear; lia). subst RIv.
      eapply pop_grow1; [exact MI| | | exact AUMU| exact MUA| exact MUR| clear -CEILB KB; lia| eapply KGR; [clear -CEILB KB; lia| exact MI| exact SK| exact MU| exact WM| exact FR]].
      all: first [eassumption| eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; clear -CEILB HRIr LO LOC; lia]].
  - (* [comment removed for export] *)
    zstepA.           (* [comment removed for export] *)
    rewrite !(Z.shiftl_mul_pow2 c 5) by (clear; lia). change (2^5) with 32. rewrite ?(Z.mod_small (c * 32) 18446744073709551616) by (clear -CEILB HC; lia).
    replace (c * 32) with (class_size c) by (rewrite (BF_popdefs.class_size_small c) by (clear -CEILB K1 HC; lia); clear; lia).
    tail5 CS RS HC AUMU MUR.
    zstepA; if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear -CEILB HC AUMU MUR RS HREQ CS; lia).
    + replace (usp + -64) with (usp - 64) by (clear; lia). subst RIv.
      eapply pop_grow1; [exact MI| | | exact AUMU| exact MUA| exact MUR| clear -CEILB KB; lia| eapply KGR; [clear -CEILB KB; lia| exact MI| exact SK| exact MU| exact WM| exact FR]].
      all: first [eassumption| eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; clear -CEILB HRIr LO LOC; lia]].
    + (* [comment removed for export] *)
      zstepA.         (* [comment removed for export] *)
      replace (usp + -64) with (usp - 64) by (clear; lia). subst RIv.
      eapply KNO; [clear -CEILB KB; lia| exact MI| exact SK| exact MU| exact WM| exact FR].
Qed.

(* [comment removed for export] *)
Lemma pop_grow_ok : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word) (m : mem) (mtx nf mfa au mu na nfr : Z) (shj : list byte)
    (TSD CTX T nmaps nmapped cm : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word) (Q : machine_state -> Prop),
  mem_inv bsegs m -> stk bsegs m lo (usp - 64) -> pop_frame m ra s0 s1 s2 s3 s4 s5 s6 ->
  rw_cells bsegs m RIc (ri_cells mtx nf mfa au mu na nfr) ->
  0 <= au <= mu -> mu mod 4096 = 0 -> mu + 262144 <= 3758096384 -> 0 <= nmaps -> 0 <= nmapped -> 0 <= cm ->
  poison_globals m ->
  rw_cells bsegs m (kShadowBase + (RB + mu) / 8) [CB (Z.to_nat 32768) shj] ->
  (forall a k, kShadowBase + (RB + mu) / 8 <= a -> a + Z.of_nat k <= kShadowBase + (RB + mu) / 8 + 32768 -> P (Z_to_bv 64 a, k)) ->
  thread_cells m tp TSD CTX T -> 0xa5000 <= TSD -> TSD + 8 <= 0x603000 ->
  placed CTX 4096 -> placed_s T 4096 ->      (* [comment removed for export] *)
  0xa5000 + 88 <= bv_unsigned tp < 0x603000 -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->
  STAT = T + kThrCacheStats -> T mod 8 = 0 -> (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) -> (CTX + 160 <= SB \/ SB + kSpaceSize + 4096 <= CTX) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) -> (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  rw_cells bsegs m (T + 2872) [C8 (Z_to_bv 64 nmaps); C8 (Z_to_bv 64 nmapped)] ->
  rw_cells bsegs m (STAT + 24) [C8 (Z_to_bv 64 cm)] ->
  (forall m' (t0' t1' t2' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (usp - 64) ->
     munch [(usp - 1536, usp - 64); (kShadowBase + (RB + mu) / 8, kShadowBase + (RB + mu) / 8 + 32768); (T + 2872, T + 2888); (STAT + 24, STAT + 32); (RIc + 48, RIc + 56)] m m' ->
     wmono bsegs m m' -> pop_frame m' ra s0 s1 s2 s3 s4 s5 s6 ->
     rw_cells bsegs m' RIc (ri_cells mtx nf mfa au (mu + 262144) na nfr) ->
     poison_globals m' ->
     rw_cells bsegs m' (kShadowBase + (RB + mu) / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] ->
     thread_cells m' tp TSD CTX T ->
     rw_cells bsegs m' (T + 2872) [C8 (Z_to_bv 64 (nmaps + 1)); C8 (Z_to_bv 64 (nmapped + 262144))] ->
     rw_cells bsegs m' (STAT + 24) [C8 (Z_to_bv 64 (cm + 262144))] ->
     evtA bsegs P Q (MS (mkR (Z_to_bv 64 0x37d44) (Z_to_bv 64 (usp - 64)) gp tp t0' t1' t2' (Z_to_bv 64 RIc) (Z_to_bv 64 (STAT + 24)) (Z_to_bv 64 INST) a1' a2'
                             (Z_to_bv 64 au) a4' a5' a6' a7' (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 (mu + 262144)) (Z_to_bv 64 (class_size c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 A_POP_MID) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_POP_MMRET) (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 STAT)
                          (Z_to_bv 64 (RB + mu)) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 (RB + mu)) (Z_to_bv 64 (class_size c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_POP_MMRET) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI SK FR RIC AUMU MUA MUR HNM HNMD HCM PG SHJ PSH TC HT1 HT2 HCP HTPL HTP HTC HST T8 HTSB HCSB PCTX PT TST CST CONT.
  pose proof HREQ as HREQ_pin.   (* [comment removed for export] *)
  unfold ri_cells in RIC, CONT. unfold A_POP_MMRET, A_POP_MID, pop_frame in *.
  pose proof LOC as LOC0. pose proof HSB as (SB1 & SB2 & SB3). aceil. unfold kSpaceSize in SB3.
  pose proof HCP as HCP0. plopen HCP. rename HCPi into HC1. rename HCPc into HC2. rename HCPs into HC3.
  pose proof HTPL as HTPL0. plopen HTPL. rename HTPLi into HT0. rename HTPLc into HT4. rename HTPLg into HT3. rename HTPLs into HT5.
  unfold kLargestClassID in HC.
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  assert (HRIr : 0x603000 <= RIv /\ RIv + 128 <= 2^47) by (rewrite HRIv, HRI; unfold kSpaceSize; clear -CEILB SB1 SB3 HC; lia).
  rewrite HRI in HRIv. unfold kSpaceSize in HRIv, HTSB, HCSB.
  set (A := SB + c * 4294967296 + mu) in *. assert (HA : A = SB + c * 4294967296 + mu) by reflexivity. clearbody A.
  pose proof HSBH as SBH. rewrite kHighMemBeg_val in SBH.
  assert (HAr : 17594333495296 + 4294967296 <= A /\ A + 262144 <= 2^47) by (rewrite HA; clear -CEILB SBH SB3 HC AUMU MUR; nia).
  assert (A8 : A mod 8 = 0) by (rewrite HA; clear -CEILB SB2 MUA; Z.div_mod_to_equations; lia).
  assert (MU : munch [(usp - 1536, usp - 64); (kShadowBase + A / 8, kShadowBase + A / 8 + 32768); (T + 2872, T + 2888); (STAT + 24, STAT + 32); (RIv + 48, RIv + 56)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold kShadowBase in *. unfold kThrCacheStats in HST.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear -CEILB HAr; lia); clear -CEILB HAr; intros K0; lia|]. clear K0.   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; clear -CEILB K1; lia|].     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  pose proof PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply evtA_cut;
    [ eapply (poison_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A 262144 250 shj);
      [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; clear -CEILB LO; lia| rewrite unsigned_lit by lia; clear -CEILB SPH; lia| exact MI
      | exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
      | exact A8| reflexivity| clear; lia| clear -CEILB HAr; lia| rewrite HA; clear -CEILB SB3 HC AUMU MUR; lia| right; rewrite kHighMemBeg_val; clear -CEILB HAr; lia| clear; lia| left; clear; lia
      | change (262144 / 8) with 32768; exact SHJ
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT
      | change (262144 / 8) with 32768; unfold kShadowBase; exact PSH ]
    |].
  clear G1 G2 G3 G4 G5 G6 G7 SHJ.
  cbv beta. intros ms' POST. unfold poison_post in POST. destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MI' & SK' & SH' & PG').
  unfold kShadowBase in MUc, SH'. rewrite !unsigned_lit in MUc, SK' by lia. change (262144 / 8) with 32768 in MUc, SH'.
  clear MI SK. lazymatch type of MUc with munch _ ?mc _ => after_callF mc m' MUc WMc end. ret_pc_lit.
  rename MI' into MI. rename SK' into SK.
  destruct PG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  cstep.                          (* [comment removed for export] *)
  eapply evtA_cut;
    [ eapply (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; clear -CEILB LO; lia| rewrite unsigned_lit by lia; clear -CEILB SPH; lia| exact MI
      | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| clear -CEILB HT1; lia| exact HT2| clear -CEILB HC1; lia| exact HC2| clear -CEILB HT0 HT4; lia| clear -CEILB HTP; lia
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT| exact PCTX ]
    |].
  cbv beta. intros ms2 POST. unfold gcts_post in POST. destruct POST as (a1x & m2 & -> & MU2 & WM2 & MI2 & SK2).
  rewrite !unsigned_lit in MU2, SK2 by lia.
  clear MI SK. lazymatch type of MU2 with munch _ ?mc _ => after_callF mc m2 MU2 WM2 end. ret_pc_lit.
  rename MI2 into MI. rename SK2 into SK.
  (* [comment removed for export] *)
  clear HSB HSBH HRI AUMU MUA MUR HNM HNMD HCM PSH K1 HC3.   (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  cstep. cstep.                   (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  assert (AL8 : (STAT + 24) mod 8 = 0) by (rewrite HST; clear -CEILB T8; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  zstepA. zstepA.                 (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  subst A.
  eapply CONT; [exact MI| exact SK| exact MU| exact WM| exact FR| exact RIC| exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))| exact SH'
               | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact TST| exact CST].
Qed.
End POP.
End RC__1.
