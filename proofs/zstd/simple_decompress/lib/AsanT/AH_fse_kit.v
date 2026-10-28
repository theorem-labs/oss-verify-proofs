(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface AKit FsKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FB5 F := (mkABlock (ABFake 5) F 2048).

(* [comment removed for export] *)
Definition SHF (F : Z) : Z := Z.shiftr F 3 + ASHOFF.
Lemma SHF_shad : forall F, SHF F = shad F.
Proof. intros F. unfold SHF, shad. lia. Qed.

Definition B00 : byte := Z_to_bv 8 0.
Definition B04 : byte := Z_to_bv 8 4.
Definition BF1 : byte := Z_to_bv 8 18446744073709551601.   (* [comment removed for export] *)
Definition BF2 : byte := Z_to_bv 8 18446744073709551602.   (* [comment removed for export] *)
Definition BF3 : byte := Z_to_bv 8 18446744073709551603.   (* [comment removed for export] *)
Definition BF8 : byte := Z_to_bv 8 18446744073709551608.   (* [comment removed for export] *)

Definition Z64 : list byte := repeat (Z_to_bv 8 0) 64.     (* [comment removed for export] *)
Definition F8S : list byte := repeat (Z_to_bv 8 248) 64.   (* [comment removed for export] *)
Definition Z32 : list byte := repeat (Z_to_bv 8 0) 32.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FSH0 : list cell :=
  [C1 B00; C1 B00; C1 B00; C1 B00; CB 64 Z64;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; CB 64 Z64;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; CB 64 Z64;
   C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; CB 32 Z32].

(* [comment removed for export] *)
Definition FSH (sd sn sr : list byte) (g220 g222 : byte) : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; CB 64 sd;
   C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; CB 64 sn;
   C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; CB 64 sr;
   C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 g220; C1 BF2; C1 g222; C1 BF3; CB 32 Z32].

Lemma FSH0_size : cells_size FSH0 = 256%nat. Proof. reflexivity. Qed.
Lemma FSH_size : forall sd sn sr g220 g222, cells_size (FSH sd sn sr g220 g222) = 256%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fsh0_of_words : forall m F,
  rw_cells bsegs m (shad F) (repeat (C8 (Z_to_bv 64 0)) 32) -> rw_cells bsegs m (SHF F) FSH0.
Proof.
  intros m F H. rewrite SHF_shad. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fsh_forget : forall m F cs, rw_cells bsegs m (SHF F) cs -> cells_size cs = 256%nat ->
  rw_cells bsegs m (shad F) [CB 256 (cells_bytes cs)].
Proof.
  intros m F cs H HSZ. rewrite <- SHF_shad. eapply rw_cells_recast; [exact H| | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | cbn; lia].
  cbn. split; [| exact I]. destruct H as [[W _] _]. rewrite cells_bytes_length by exact W. exact HSZ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_nth : forall m A cs k c,
  rw_cells bsegs m A cs -> nth_error cs k = Some c ->
  rw_cells bsegs m (A + Z.of_nat (cells_size (firstn k cs))) [c].
Proof.
  intros m A cs k c H E.
  rewrite <- (firstn_skipn k cs) in H. apply (proj1 (rw_cells_app _ _ _ _ _)) in H. destruct H as [_ H].
  rewrite (skipn_S_nth cs k c E) in H.
  change (c :: skipn (S k) cs) with ([c] ++ skipn (S k) cs) in H.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in H. exact (proj1 H).
Qed.

Lemma rw_cells_mid : forall m m' A cs k c c',
  rw_cells bsegs m A cs -> nth_error cs k = Some c -> csize c' = csize c ->
  munch [(A + Z.of_nat (cells_size (firstn k cs)), A + Z.of_nat (cells_size (firstn k cs)) + Z.of_nat (csize c))] m m' ->
  wmono bsegs m m' ->
  rw_cells bsegs m' (A + Z.of_nat (cells_size (firstn k cs))) [c'] ->
  rw_cells bsegs m' A (firstn k cs ++ c' :: skipn (S k) cs).
Proof.
  intros m m' A cs k c c' H E HSZ MU WM H'.
  pose proof (rw_cells_bound _ _ _ _ H) as BD.
  rewrite <- (firstn_skipn k cs) in H. apply (proj1 (rw_cells_app _ _ _ _ _)) in H. destruct H as [H1 H2].
  rewrite (skipn_S_nth cs k c E) in H2.
  change (c :: skipn (S k) cs) with ([c] ++ skipn (S k) cs) in H2.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in H2. destruct H2 as [_ H3]. cbn [cells_size] in H3. rewrite Nat.add_0_r in H3.
  rewrite <- (firstn_skipn k cs) in BD. rewrite cells_size_app in BD. rewrite (skipn_S_nth cs k c E) in BD.
  cbn [cells_size] in BD.
  apply (proj2 (rw_cells_app _ _ _ _ _)). split.
  - eapply rw_cells_transport; [exact H1| exact MU| exact WM|]. cbn [disjoint_from]. split; [lia| exact I].
  - change (c' :: skipn (S k) cs) with ([c'] ++ skipn (S k) cs). apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H'|].
    cbn [cells_size]. rewrite Nat.add_0_r, HSZ.
    eapply rw_cells_transport; [exact H3| exact MU| exact WM|]. cbn [disjoint_from]. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unp_zero_cb : forall m X k,
  X mod 8 = 0 -> 0 <= X -> X + 8 * Z.of_nat k <= KEND ->
  rw_cells bsegs m (shad X) [CB k (repeat (Z_to_bv 8 0) k)] ->
  unpoisoned m X (X + 8 * Z.of_nat k).
Proof.
  intros m X k X8 X0 XH [[_ (B0 & B1 & BR)] _].
  unfold KEND in *. split; [lia|]. split; [lia|]. intros G Hlt Hlo Hhi.
  assert (HG : X / 8 <= G < X / 8 + Z.of_nat k) by (Z.div_mod_to_equations; lia).
  specialize (BR (Z.to_nat (G - X / 8))). cbn [cells_bytes cbytes] in BR. rewrite app_nil_r, repeat_length in BR.
  rewrite nth_error_repeat in BR by lia.
  assert (EA : shad X + Z.of_nat (Z.to_nat (G - X / 8)) = ASHOFF + G) by (rewrite shad_div; lia).
  rewrite EA in BR. rewrite mrd_high in BR by (unfold ASHOFF; Z.div_mod_to_equations; lia).
  exists (Z_to_bv 8 0). split; [apply BR; lia| left; reflexivity].
Qed.

Lemma unp_partial_c1 : forall m X k,
  X mod 8 = 0 -> 0 <= X -> X + 8 <= KEND -> 1 <= k <= 7 ->
  rw_cells bsegs m (shad X) [C1 (Z_to_bv 8 k)] ->
  unpoisoned m X (X + k).
Proof.
  intros m X k X8 X0 XH K1 H. unfold KEND in *.
  pose proof (rw_C1_high m (shad X) _ H ltac:(rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia)) as RB.
  split; [lia|]. split; [lia|]. intros G Hlt Hlo Hhi.
  assert (HG : G = X / 8) by (Z.div_mod_to_equations; lia). subst G.
  exists (Z_to_bv 8 k). split.
  - rewrite <- RB. rewrite shad_div. reflexivity.
  - right. rewrite sval_lit by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SUAR5 : Z := 0xc7360.    (* [comment removed for export] *)
Definition ASUAR5 : Z := 0xcfd00.

Lemma fse_got_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m ->
  rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m 0xc7328 [C8 (Z_to_bv 64 0xc91b8)].
Proof.
  intros AI L RNG st LB m AH. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
  split.
  - eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xc7360 (le8 (Z_to_bv 64 0xcfd00)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
  - eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xc7328 (le8 (Z_to_bv 64 0xc91b8)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fse_rt_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m ->
  rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] /\ rt_inited m /\ rt_layout m.
Proof.
  intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact G].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cr_stack : forall CI LB SP A n, SP <= A -> A + n <= 2^47 -> aclient_range CI LB SP A n.
Proof. intros. left. left. split; assumption. Qed.

Lemma cr_block : forall CI LB SP A n b, In b LB -> ab_addr b <= A -> A + n <= ab_addr b + ab_size b -> aclient_range CI LB SP A n.
Proof. intros CI LB SP A n b Hb H1 H2. right. left. exists b. split; [exact Hb| split; assumption]. Qed.

Lemma cr_fshadow : forall CI LB SP F A n, In (FB5 F) LB -> F mod 8 = 0 -> 0 <= F ->
  SHF F <= A -> A + n <= SHF F + 256 -> 0 <= n -> aclient_range CI LB SP A n.
Proof.
  intros CI LB SP F A n Hb F8 F0 H1 H2 N0. right. right. right. right. exists 5, F, 2048. split; [exact Hb|].
  unfold SHF in *. rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_client : forall CI LB' sp' F a, In (FB5 F) LB' -> F mod 8 = 0 -> 0 <= F -> SHF F <= a < SHF F + 256 -> aclient_addr CI LB' sp' a.
Proof.
  intros CI LB' sp' F a HIN F8 F0 Ha. right; right; right. exists (F + 8 * (a - SHF F)). split.
  - right; right. exists 5, F, 2048. split; [exact HIN| lia].
  - unfold SHF in *. rewrite shad_div. rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZRB13 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma FZRB13_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  cells_size (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition FRA (x0 x8 x16 x24 x32 x40 x48 x56 : word) (j64 : list byte) (x80 : word) : list cell :=
  [C8 x0; C8 x8; C8 x16; C8 x24; C8 x32; C8 x40; C8 x48; C8 x56; CB 16 j64; C8 x80].
Lemma FRA_size : forall x0 x8 x16 x24 x32 x40 x48 x56 j64 x80, cells_size (FRA x0 x8 x16 x24 x32 x40 x48 x56 j64 x80) = 88%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_ldiff_distrF x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity. Qed.
Lemma land_alignF : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 ->
  Z.land x (Z.ldiff (Z.ones 64) (Z.ones k)) = x - x mod 2^k.
Proof.
  intros x k Hx Hk. rewrite land_ldiff_distrF. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.
Lemma land_m32F : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)). rewrite land_alignF by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spa_props5 : forall SP, SP mod 16 = 0 ->     (* [comment removed for export] *)
  let SPA := (SP - 224) - (SP - 224) mod 32 in
  SP - 240 <= SPA <= SP - 224 /\ SPA mod 32 = 0 /\ SPA + 120 <= SP - 104.
Proof. intros SP H SPA. subst SPA. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma page_round_up_geF : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof. intros x Hx. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma harness_topF : forall L SP, SP + ATRUN_DEPTH = al_sp0 L -> 0 <= SP -> SP + 16 <= al_top L < SP + 48 + 4096.   (* [comment removed for export] *)
Proof.
  intros L SP E H0. unfold al_top. rewrite <- E. unfold ATRUN_DEPTH. replace (SP + 208 - 160) with (SP + 48) by lia.
  pose proof (page_round_up_geF (SP + 48) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma fzrb13_saved : forall m SP (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  rw_cells bsegs m (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  bytes_at bsegs m (SP - 16) (le8 s0) /\ bytes_at bsegs m (SP - 8) (le8 ra).
Proof.
  intros until s11. intros [[_ B] _]. unfold FZRB13 in B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  do 11 (apply (proj1 (bytes_at_app _ _ _ _ _)) in B; destruct B as [_ B]; rewrite length_le8 in B).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [B1 B2]. rewrite length_le8 in B2.
  split.
  - replace (SP - 16) with (SP + -104 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact B1.
  - replace (SP - 8) with (SP + -104 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact B2.
Qed.

(* [comment removed for export] *)
Lemma harness_uchainF : forall m (top PC SP sp' zl : Z),
  bytes_at bsegs m (SP - 16) (le8 (Z_to_bv 64 zl)) -> bytes_at bsegs m (SP - 8) (le8 (Z_to_bv 64 ATRUN_RET)) ->
  0 <= zl < SP -> SP mod 8 = 0 -> sp' < SP -> PC <> ATRUN_RET -> SP + 16 <= top ->
  exists tr, uchain m top PC sp' SP UDEPTH tr /\ (tr = [] \/ tr = [ATRUN_RET]).
Proof.
  intros m top PC SP sp' zl B1 B2 HZ SP8 HS NE TOP.
  pose proof (bytes_at_bound _ _ _ _ B2) as BB. rewrite length_le8 in BB.
  destruct (Z_lt_le_dec SP (top - 16)) as [LT|GE].
  - exists [ATRUN_RET]. split; [| right; reflexivity].
    replace [ATRUN_RET] with ((if ATRUN_RET =? PC then [] else [ATRUN_RET]) ++ []) by (replace (ATRUN_RET =? PC) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply uc_step with (fp := zl); [exact HS| exact LT| exact SP8| unfold UDEPTH; lia| exact B1| exact B2| unfold ATRUN_RET; lia| lia|].
    apply uc_stop. lia.
  - exists []. split; [| left; reflexivity]. apply uc_stop. lia.
Qed.

(* [comment removed for export] *)
Lemma harness_trace_inF : forall (U : list (list Z)) PC RET tr,
  In [PC; RET; ATRUN_RET] U -> In [PC; RET] U -> (tr = [] \/ tr = [ATRUN_RET]) -> In (PC :: RET :: tr) U /\ (length tr <= 28)%nat.
Proof. intros U PC RET tr H3 H2 [-> | ->]; cbn; split; auto; lia. Qed.
End CANSEC2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FshUnp.
  Variables (m : amem) (F : Z).
  Hypothesis F2048 : F mod 2048 = 0.
  Hypothesis F0 : 0 <= F.
  Hypothesis FE : F + 2048 + 8 <= KEND.

  Lemma shad_frame_off : forall k, 0 <= k -> k mod 8 = 0 -> shad (F + k) = SHF F + k / 8.
  Proof. intros k Hk K8. rewrite <- SHF_shad. unfold SHF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.

  Lemma fsh_cell : forall cs k c, rw_cells bsegs m (SHF F) cs -> nth_error cs k = Some c ->
    rw_cells bsegs m (SHF F + Z.of_nat (cells_size (firstn k cs))) [c].
  Proof. intros cs k c H E. eapply rw_cells_nth; eassumption. Qed.

  Lemma fsh_unp_data : forall sn sr g1 g2, rw_cells bsegs m (SHF F) (FSH Z64 sn sr g1 g2) -> unpoisoned m (F + 32) (F + 544).
  Proof.
    intros sn sr g1 g2 H. pose proof (fsh_cell _ 4 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
    replace (F + 544) with (F + 32 + 8 * Z.of_nat 64) by lia. apply unp_zero_cb; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia|].
    rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (32 / 8) with 4. exact C.
  Qed.
  Lemma fsh_unp_nc : forall sd sr g1 g2, rw_cells bsegs m (SHF F) (FSH sd Z64 sr g1 g2) -> unpoisoned m (F + 608) (F + 1120).
  Proof.
    intros sd sr g1 g2 H. pose proof (fsh_cell _ 13 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
    replace (F + 1120) with (F + 608 + 8 * Z.of_nat 64) by lia. apply unp_zero_cb; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia|].
    rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (608 / 8) with 76. exact C.
  Qed.
  Lemma fsh_unp_rt : forall sd sn g1 g2, rw_cells bsegs m (SHF F) (FSH sd sn Z64 g1 g2) -> unpoisoned m (F + 1184) (F + 1696).
  Proof.
    intros sd sn g1 g2 H. pose proof (fsh_cell _ 22 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
    replace (F + 1696) with (F + 1184 + 8 * Z.of_nat 64) by lia. apply unp_zero_cb; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia|].
    rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (1184 / 8) with 148. exact C.
  Qed.
  Lemma fsh_unp_msv : forall sd sn sr g2, rw_cells bsegs m (SHF F) (FSH sd sn sr B04 g2) -> unpoisoned m (F + 1760) (F + 1764).
  Proof.
    intros sd sn sr g2 H. pose proof (fsh_cell _ 31 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
    replace (F + 1764) with (F + 1760 + 4) by lia. apply unp_partial_c1; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia| lia|].
    rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (1760 / 8) with 220. exact C.
  Qed.
  Lemma fsh_unp_tl : forall sd sn sr g1, rw_cells bsegs m (SHF F) (FSH sd sn sr g1 B04) -> unpoisoned m (F + 1776) (F + 1780).
  Proof.
    intros sd sn sr g1 H. pose proof (fsh_cell _ 33 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
    replace (F + 1780) with (F + 1776 + 4) by lia. apply unp_partial_c1; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia| lia|].
    rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (1776 / 8) with 222. exact C.
  Qed.
  (* [comment removed for export] *)
  Lemma fsh_wr : forall cs, rw_cells bsegs m (SHF F) cs -> cells_size cs = 256%nat -> wr_at bsegs m (shad F) 256.
  Proof. intros cs H S. rewrite <- SHF_shad. pose proof (proj2 H) as W. rewrite S in W. exact W. Qed.
End FshUnp.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Definition fse_rt (m : amem) : Prop :=
  rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rt_inited m /\ rt_layout m
  /\ rw_cells bsegs m 0xc7328 [C8 (Z_to_bv 64 0xc91b8)].

Lemma fse_rtall_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m -> fse_rt m.
Proof.
  intros AI L RNG st LB m AH. destruct (fse_rt_of_aheap AI L RNG st LB m AH) as (A & B & C & D & _ & F & G).
  destruct (fse_got_of_aheap AI L RNG st LB m AH) as [_ H].
  exact (conj A (conj B (conj C (conj D (conj F (conj G H)))))).
Qed.

Fixpoint above (lo : Z) (W : list (Z * Z)) : Prop :=
  match W with [] => True | (a, b) :: W' => lo <= a /\ above lo W' end.

Lemma disjoint_of_above : forall W A n, above (A + n) W -> 0 <= n -> disjoint_from W A n.
Proof. induction W as [|[a b] W IH]; intros A n H N; cbn in *; [exact I|]. destruct H as [H1 H2]. split; [lia| apply IH; assumption]. Qed.

Lemma fse_rt_munch : forall W m m', fse_rt m -> munch W m m' -> wmono bsegs m m' -> above AIMG_HI W -> fse_rt m'.
Proof.
  intros W m m' (A & B & C & D & E & F & G) MU WM AB.
  assert (T : forall X cs, rw_cells bsegs m X cs -> X + Z.of_nat (cells_size cs) <= AIMG_HI -> rw_cells bsegs m' X cs).
  { intros X cs H HX. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. apply disjoint_of_above; [| lia].
    clear - AB HX. induction W as [|[a b] W IH]; cbn in *; [exact I|]. destruct AB as [A1 A2]. split; [lia| apply IH; exact A2]. }
  unfold AIMG_HI in T.
  refine (conj (T _ _ A _) (conj (T _ _ B _) (conj (T _ _ C _) (conj (T _ _ D _) (conj (T _ _ E _) (conj (T _ _ F _) (T _ _ G _))))))); cbn; lia.
Qed.
End CANSEC3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma bytes_at_firstnF : forall m A bs n, bytes_at bsegs m A bs -> (n <= length bs)%nat -> bytes_at bsegs m A (firstn n bs).
Proof.
  intros m A bs n (H0 & H1 & HB) Hn. split; [exact H0|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [| lia]. apply HB. lia.
Qed.

Lemma u8arr_of_two_cb : forall m A n1 n2 b1 b2,
  rw_cells bsegs m A [CB n1 b1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 b2] -> u8arr bsegs m A (b1 ++ b2).
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H2' : rw_cells bsegs m (A + Z.of_nat (cells_size [CB n1 b1])) [CB n2 b2]) by (cbn [cells_size csize]; rewrite Nat.add_0_r; exact H2).
  pose proof (proj2 (rw_cells_app _ _ _ [CB n1 b1] [CB n2 b2]) (conj H1 H2')) as H.
  apply (u8arr_of_rw_cells bsegs m A (n1 + n2)). eapply rw_cells_recast; [exact H| | | ].
  - destruct H as [[[L1 [L2 _]] _] _]. cbn in L1, L2 |- *. split; [rewrite length_app; lia| exact I].
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
  - cbn [cells_size csize app]. lia.
Qed.
End CANSEC4.
