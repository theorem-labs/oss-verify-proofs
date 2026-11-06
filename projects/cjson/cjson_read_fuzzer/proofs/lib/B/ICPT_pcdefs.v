(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg ICPT_pcleaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition APRINTF_COMMON : Z := 0x460b8.
Definition APC_STACK : Z := 2272.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lowsh_at (m : word -> option byte) : Prop :=
  forall a, SH AIMG_LO <= a < SH AIMG_HI -> rw_cells bsegs m a [C1 (zb (alowsh a))].


(* [comment removed for export] *)
Lemma lowsh_at_munch : forall W m m', lowsh_at m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => snd iv <= SH AIMG_LO \/ SH AIMG_HI <= fst iv) W -> lowsh_at m'.
Proof.
  intros W m m' L MU WM HW a Ha. eapply rw_cells_transport; [exact (L a Ha)| exact MU| exact WM|].
  cbn [cells_size csize Nat.add Z.of_nat]. clear MU WM L.
  induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [fst snd] in H1.
  cbn. split; [lia| apply IH; exact H2].
Qed.
Lemma lowsh_at_munch_stack : forall u v m m', lowsh_at m -> munch [(u, v)] m m' -> wmono bsegs m m' ->
  alloc_ceiling <= u -> lowsh_at m'.
Proof.
  intros u v m m' L MU WM Hu. eapply lowsh_at_munch; [exact L| exact MU| exact WM|].
  apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right.
  unfold SH, SHADOW_OFFSET, AIMG_HI, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.

Definition pcommon_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2272, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'   (* [comment removed for export] *)
    /\ stk bsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition pcommon_stmt (fa : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    mem_inv bsegs m -> shbase_cells m -> lowsh_at m ->
    stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + APC_STACK <= bv_unsigned sp ->
    a1 = Z_to_bv 64 fa ->
    evt bsegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zbs (l : list Z) : list byte := map (Z_to_bv 8) l.
Lemma tbl_flags : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x15329 [CB 7 (zbs [39; 45; 43; 32; 35; 48; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x15329 (zbs [39; 45; 43; 32; 35; 48; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_lenmod : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x1b33d [CB 6 (zbs [106; 122; 116; 76; 113; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x1b33d (zbs [106; 122; 116; 76; 113; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_cs : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x1413d [CB 5 (zbs [99; 67; 115; 83; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x1413d (zbs [99; 67; 115; 83; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_iconv : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x1c427 [CB 8 (zbs [100; 105; 111; 117; 120; 88; 110; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x1c427 (zbs [100; 105; 111; 117; 120; 88; 110; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_fconv : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x16379 [CB 9 (zbs [97; 65; 101; 69; 102; 70; 103; 71; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x16379 (zbs [97; 65; 101; 69; 102; 70; 103; 71; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_aa : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x10418 [CB 8 (zbs [170; 170; 170; 170; 170; 170; 170; 170])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x10418 (zbs [170; 170; 170; 170; 170; 170; 170; 170]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma fmt_d_bytes : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x21240 [CB 3 (zbs [37; 100; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x21240 (zbs [37; 100; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.

Lemma fmt_g15_bytes : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x21260 [CB 7 (zbs [37; 49; 46; 49; 53; 103; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x21260 (zbs [37; 49; 46; 49; 53; 103; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma fmt_g17_bytes : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x212a0 [CB 7 (zbs [37; 49; 46; 49; 55; 103; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x212a0 (zbs [37; 49; 46; 49; 55; 103; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma fmt_u04x_bytes : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x212e0 [CB 6 (zbs [117; 37; 48; 52; 120; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x212e0 (zbs [117; 37; 48; 52; 120; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_atoll : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x10328 [CB 8 (zbs [154; 153; 153; 153; 153; 153; 153; 25])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x10328 (zbs [154; 153; 153; 153; 153; 153; 153; 25]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.

Ltac glue H1 H2 := let X := fresh in pose proof (proj2 (rw_cells_app bsegs _ _ _ _) (conj H1 H2)) as X; clear H1 H2; rename X into H1; cbn [app cells_size csize Nat.add Z.of_nat] in H1.

(* [comment removed for export] *)
Lemma lowsh_c8e8 : forall m, lowsh_at m ->
  rw_cells bsegs m 0x7fffc244 [C1 (zb 5); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3); C1 (zb 249); C1 (zb 249); C1 (zb 249)].
Proof.
  intros m L.
  assert (G : forall k : nat, (k < 8)%nat -> rw_cells bsegs m (0x7fffc244 + Z.of_nat k) [C1 (zb (alowsh (0x7fffc244 + Z.of_nat k)))]).
  { intros k Hk. apply L. unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI. lia. }
  pose proof (G 0%nat ltac:(lia)) as G0. pose proof (G 1%nat ltac:(lia)) as G1. pose proof (G 2%nat ltac:(lia)) as G2. pose proof (G 3%nat ltac:(lia)) as G3.
  pose proof (G 4%nat ltac:(lia)) as G4. pose proof (G 5%nat ltac:(lia)) as G5. pose proof (G 6%nat ltac:(lia)) as G6. pose proof (G 7%nat ltac:(lia)) as G7.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in G0, G1, G2, G3, G4, G5, G6, G7.
  match type of G0 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G0 end.
  match type of G1 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G1 end.
  match type of G2 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G2 end.
  match type of G3 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G3 end.
  match type of G4 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G4 end.
  match type of G5 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G5 end.
  match type of G6 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G6 end.
  match type of G7 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G7 end.
  change 2147469559 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5)])) in G1. glue G0 G1.
  change 2147469560 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5); C1 (zb 249)])) in G2. glue G0 G2.
  change 2147469561 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5); C1 (zb 249); C1 (zb 249)])) in G3. glue G0 G3.
  change 2147469562 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5); C1 (zb 249); C1 (zb 249); C1 (zb 249)])) in G4. glue G0 G4.
  change 2147469563 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3)])) in G5. glue G0 G5.
  change 2147469564 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3); C1 (zb 249)])) in G6. glue G0 G6.
  change 2147469565 with (2147469558 + Z.of_nat (cells_size [C1 (zb 5); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3); C1 (zb 249); C1 (zb 249)])) in G7. glue G0 G7.
  exact G0.
Qed.

(* [comment removed for export] *)
Lemma lowsh_c8f0 : forall m, lowsh_at m ->
  rw_cells bsegs m 0x7fffc24c [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 4); C1 (zb 249); C1 (zb 249); C1 (zb 249)].
Proof.
  intros m L.
  assert (G : forall k : nat, (k < 8)%nat -> rw_cells bsegs m (0x7fffc24c + Z.of_nat k) [C1 (zb (alowsh (0x7fffc24c + Z.of_nat k)))]).
  { intros k Hk. apply L. unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI. lia. }
  pose proof (G 0%nat ltac:(lia)) as G0. pose proof (G 1%nat ltac:(lia)) as G1. pose proof (G 2%nat ltac:(lia)) as G2. pose proof (G 3%nat ltac:(lia)) as G3.
  pose proof (G 4%nat ltac:(lia)) as G4. pose proof (G 5%nat ltac:(lia)) as G5. pose proof (G 6%nat ltac:(lia)) as G6. pose proof (G 7%nat ltac:(lia)) as G7.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in G0, G1, G2, G3, G4, G5, G6, G7.
  match type of G0 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G0 end.
  match type of G1 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G1 end.
  match type of G2 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G2 end.
  match type of G3 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G3 end.
  match type of G4 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G4 end.
  match type of G5 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G5 end.
  match type of G6 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G6 end.
  match type of G7 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G7 end.
  change 2147469567 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7)])) in G1. glue G0 G1.
  change 2147469568 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249)])) in G2. glue G0 G2.
  change 2147469569 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249)])) in G3. glue G0 G3.
  change 2147469570 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249)])) in G4. glue G0 G4.
  change 2147469571 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 4)])) in G5. glue G0 G5.
  change 2147469572 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 4); C1 (zb 249)])) in G6. glue G0 G6.
  change 2147469573 with (2147469566 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 4); C1 (zb 249); C1 (zb 249)])) in G7. glue G0 G7.
  exact G0.
Qed.

(* [comment removed for export] *)
Lemma lowsh_c8f8 : forall m, lowsh_at m ->
  rw_cells bsegs m 0x7fffc254 [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3); C1 (zb 249); C1 (zb 249); C1 (zb 249)].
Proof.
  intros m L.
  assert (G : forall k : nat, (k < 8)%nat -> rw_cells bsegs m (0x7fffc254 + Z.of_nat k) [C1 (zb (alowsh (0x7fffc254 + Z.of_nat k)))]).
  { intros k Hk. apply L. unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI. lia. }
  pose proof (G 0%nat ltac:(lia)) as G0. pose proof (G 1%nat ltac:(lia)) as G1. pose proof (G 2%nat ltac:(lia)) as G2. pose proof (G 3%nat ltac:(lia)) as G3.
  pose proof (G 4%nat ltac:(lia)) as G4. pose proof (G 5%nat ltac:(lia)) as G5. pose proof (G 6%nat ltac:(lia)) as G6. pose proof (G 7%nat ltac:(lia)) as G7.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in G0, G1, G2, G3, G4, G5, G6, G7.
  match type of G0 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G0 end.
  match type of G1 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G1 end.
  match type of G2 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G2 end.
  match type of G3 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G3 end.
  match type of G4 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G4 end.
  match type of G5 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G5 end.
  match type of G6 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G6 end.
  match type of G7 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G7 end.
  change 2147469575 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7)])) in G1. glue G0 G1.
  change 2147469576 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249)])) in G2. glue G0 G2.
  change 2147469577 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249)])) in G3. glue G0 G3.
  change 2147469578 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249)])) in G4. glue G0 G4.
  change 2147469579 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3)])) in G5. glue G0 G5.
  change 2147469580 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3); C1 (zb 249)])) in G6. glue G0 G6.
  change 2147469581 with (2147469574 + Z.of_nat (cells_size [C1 (zb 7); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 3); C1 (zb 249); C1 (zb 249)])) in G7. glue G0 G7.
  exact G0.
Qed.

(* [comment removed for export] *)
Lemma lowsh_c900 : forall m, lowsh_at m ->
  rw_cells bsegs m 0x7fffc25c [C1 (zb 6); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 0); C1 (zb 0); C1 (zb 0); C1 (zb 0)].
Proof.
  intros m L.
  assert (G : forall k : nat, (k < 8)%nat -> rw_cells bsegs m (0x7fffc25c + Z.of_nat k) [C1 (zb (alowsh (0x7fffc25c + Z.of_nat k)))]).
  { intros k Hk. apply L. unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI. lia. }
  pose proof (G 0%nat ltac:(lia)) as G0. pose proof (G 1%nat ltac:(lia)) as G1. pose proof (G 2%nat ltac:(lia)) as G2. pose proof (G 3%nat ltac:(lia)) as G3.
  pose proof (G 4%nat ltac:(lia)) as G4. pose proof (G 5%nat ltac:(lia)) as G5. pose proof (G 6%nat ltac:(lia)) as G6. pose proof (G 7%nat ltac:(lia)) as G7.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in G0, G1, G2, G3, G4, G5, G6, G7.
  match type of G0 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G0 end.
  match type of G1 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G1 end.
  match type of G2 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G2 end.
  match type of G3 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G3 end.
  match type of G4 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G4 end.
  match type of G5 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G5 end.
  match type of G6 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G6 end.
  match type of G7 with rw_cells _ _ _ [C1 (zb ?v)] => let x := eval vm_compute in v in change v with x in G7 end.
  change 2147469583 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6)])) in G1. glue G0 G1.
  change 2147469584 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6); C1 (zb 249)])) in G2. glue G0 G2.
  change 2147469585 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6); C1 (zb 249); C1 (zb 249)])) in G3. glue G0 G3.
  change 2147469586 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6); C1 (zb 249); C1 (zb 249); C1 (zb 249)])) in G4. glue G0 G4.
  change 2147469587 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 0)])) in G5. glue G0 G5.
  change 2147469588 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 0); C1 (zb 0)])) in G6. glue G0 G6.
  change 2147469589 with (2147469582 + Z.of_nat (cells_size [C1 (zb 6); C1 (zb 249); C1 (zb 249); C1 (zb 249); C1 (zb 0); C1 (zb 0); C1 (zb 0)])) in G7. glue G0 G7.
  exact G0.
Qed.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac lit_cond Kc := revert Kc; rewrite ?unsigned_lit by lia; intros Kc; try rewrite !Z.mod_small in Kc by lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le1_lit : forall z, Z_to_le_bytes 1 z = [Z_to_bv 8 z].
Proof. intros z. reflexivity. Qed.
Lemma le1_lit2 : forall z, (0 <= z < 2^64)%Z -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_lit z)
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit2 z) by lia
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac fold_ldb :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [zext 64 (bv_extract 0 8 (le_bytes_to_word ?l))] =>
        let v := eval vm_compute in (bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word l)))) in
        replace (zext 64 (bv_extract 0 8 (le_bytes_to_word l))) with (Z_to_bv 64 v : word)
          by (apply bv_eq; vm_compute; reflexivity)
      end
  end.
(* [comment removed for export] *)
Ltac fix_sub := match goal with |- context [Z_to_bv 64 (bv_unsigned ?r - 4096)] => replace (bv_unsigned r - 4096) with (bv_unsigned r + -4096) by lia | _ => idtac end.
Ltac gs := zstep; try fold_ldb; try (fix_litstore; mem_after_store_opt); try fold_lits; try (if_lit); fix_sub.
Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.
(* [comment removed for export] *)
Ltac shw_read H :=
  lazymatch type of H with rw_cells _ ?mm ?A ?cs =>
    let RD := fresh "RD" in
    pose proof (bytes_at_ov_read bsegs mm A (cells_bytes cs) 0 8 (rw_cells_bytes_at' _ _ _ _ H) ltac:(cbn; lia)) as RD;
    cbn [cells_bytes cbytes app firstn skipn Z.of_nat] in RD; rewrite Z.add_0_r in RD
  end.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac gsto p := repeat (tryif at_pc p then fail else lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => gs end).
Ltac pc_is := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => idtac "PC" p | |- evt _ _ (MS _ _ ?p _ _ _ _) => idtac "PC?" p | |- ?G => idtac "NOGOAL-EVT" end.



End CeilWrap.
(* [comment removed for export] *)
Ltac glue H1 H2 := let X := fresh in pose proof (proj2 (rw_cells_app bsegs _ _ _ _) (conj H1 H2)) as X; clear H1 H2; rename X into H1; cbn [app cells_size csize Nat.add Z.of_nat] in H1.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac lit_cond Kc := revert Kc; rewrite ?unsigned_lit by lia; intros Kc; try rewrite !Z.mod_small in Kc by lia.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_lit z)
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit2 z) by lia
  | _ => idtac
  end.
Ltac fold_ldb :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [zext 64 (bv_extract 0 8 (le_bytes_to_word ?l))] =>
        let v := eval vm_compute in (bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word l)))) in
        replace (zext 64 (bv_extract 0 8 (le_bytes_to_word l))) with (Z_to_bv 64 v : word)
          by (apply bv_eq; vm_compute; reflexivity)
      end
  end.
Ltac fix_sub := match goal with |- context [Z_to_bv 64 (bv_unsigned ?r - 4096)] => replace (bv_unsigned r - 4096) with (bv_unsigned r + -4096) by lia | _ => idtac end.
Ltac gs := zstep; try fold_ldb; try (fix_litstore; mem_after_store_opt); try fold_lits; try (if_lit); fix_sub.
Ltac shw_read H :=
  lazymatch type of H with rw_cells _ ?mm ?A ?cs =>
    let RD := fresh "RD" in
    pose proof (bytes_at_ov_read bsegs mm A (cells_bytes cs) 0 8 (rw_cells_bytes_at' _ _ _ _ H) ltac:(cbn; lia)) as RD;
    cbn [cells_bytes cbytes app firstn skipn Z.of_nat] in RD; rewrite Z.add_0_r in RD
  end.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac gsto p := repeat (tryif at_pc p then fail else lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => gs end).
Ltac pc_is := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => idtac "PC" p | |- evt _ _ (MS _ _ ?p _ _ _ _) => idtac "PC?" p | |- ?G => idtac "NOGOAL-EVT" end.
