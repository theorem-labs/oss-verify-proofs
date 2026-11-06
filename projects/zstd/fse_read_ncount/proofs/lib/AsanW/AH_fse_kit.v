(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface AKit FsKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Definition SHF (F : Z) : Z := Z.shiftr F 3 + ASHOFF.
Lemma SHF_shad : forall F, SHF F = shad F.
Proof. intros F. unfold SHF, shad. Local Ltac2 Set LiaHints.tbl := fun () => "0010=25349389888.1000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition B00 : byte := Z_to_bv 8 0.
Definition B04 : byte := Z_to_bv 8 4.
Definition BF1 : byte := Z_to_bv 8 18446744073709551601.
Definition BF2 : byte := Z_to_bv 8 18446744073709551602.
Definition BF3 : byte := Z_to_bv 8 18446744073709551603.
Definition BF8 : byte := Z_to_bv 8 18446744073709551608.
Definition Z64 : list byte := repeat (Z_to_bv 8 0) 64.
Definition F8S : list byte := repeat (Z_to_bv 8 248) 64.
Definition Z32 : list byte := repeat (Z_to_bv 8 0) 32.
Definition FSH0 : list cell :=
[C1 B00; C1 B00; C1 B00; C1 B00; CB 64 Z64;
C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; CB 64 Z64;
C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; CB 64 Z64;
C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; CB 32 Z32].
Definition FSH (sd sn sr : list byte) (g220 g222 : byte) : list cell :=
[C1 BF1; C1 BF1; C1 BF1; C1 BF1; CB 64 sd;
C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; CB 64 sn;
C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; CB 64 sr;
C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 BF2; C1 g220; C1 BF2; C1 g222; C1 BF3; CB 32 Z32].
Lemma FSH_size : forall sd sn sr g220 g222, cells_size (FSH sd sn sr g220 g222) = 256%nat.
Proof. reflexivity. Qed.
Lemma fsh0_of_words : forall m F,
rw_cells asegs m (shad F) (repeat (C8 (Z_to_bv 64 0)) 32) -> rw_cells asegs m (SHF F) FSH0.
Proof.
intros m F H. rewrite SHF_shad. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.
Lemma fsh_forget : forall m F cs, rw_cells asegs m (SHF F) cs -> cells_size cs = 256%nat ->
rw_cells asegs m (shad F) [CB 256 (cells_bytes cs)].
Proof.
intros m F cs H HSZ. rewrite <- SHF_shad. Local Ltac2 Set LiaHints.tbl := fun () => "0010=33574678188.5000005S3HSZ".
eapply rw_cells_recast; [exact H| | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | cbn; lia].
cbn. split; [| exact I]. destruct H as [[W _] _]. rewrite cells_bytes_length by exact W. exact HSZ.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rw_cells_nth : forall m A cs k c,
rw_cells asegs m A cs -> nth_error cs k = Some c ->
rw_cells asegs m (A + Z.of_nat (cells_size (firstn k cs))) [c].
Proof.
intros m A cs k c H E.
rewrite <- (firstn_skipn k cs) in H. apply (proj1 (rw_cells_app _ _ _ _ _)) in H. destruct H as [_ H].
rewrite (skipn_S_nth cs k c E) in H.
change (c :: skipn (S k) cs) with ([c] ++ skipn (S k) cs) in H.
apply (proj1 (rw_cells_app _ _ _ _ _)) in H. exact (proj1 H).
Qed.
Lemma unp_zero_cb : forall m X k,
X mod 8 = 0 -> 0 <= X -> X + 8 * Z.of_nat k <= KEND ->
rw_cells asegs m (shad X) [CB k (repeat (Z_to_bv 8 0) k)] ->
unpoisoned m X (X + 8 * Z.of_nat k).
Proof.
intros m X k X8 X0 XH [[_ (B0 & B1 & BR)] _].
unfold KEND in *. Local Ltac2 Set LiaHints.tbl := fun () => "0070>25083104987.22432814955.14  48953274495.205093298943.9  54042031068.9 57065871760.1457066085530.1500000B00F00T00X00\00d00oS2X02XH3Hlo3Hhi2EAS2HGS2X83Hlo3Hhi1HS2XHS2X0S3Hlt2HGS3Hlt2HG2EA".
split; [lia|]. split; [lia|]. intros G Hlt Hlo Hhi.
assert (HG : X / 8 <= G < X / 8 + Z.of_nat k) by (Z.div_mod_to_equations; lia).
specialize (BR (Z.to_nat (G - X / 8))). cbn [cells_bytes cbytes] in BR. rewrite app_nil_r, repeat_length in BR.
rewrite nth_error_repeat in BR by lia.
assert (EA : shad X + Z.of_nat (Z.to_nat (G - X / 8)) = ASHOFF + G) by (rewrite shad_div; lia).
rewrite EA in BR. rewrite mrd_high in BR by (unfold ASHOFF; Z.div_mod_to_equations; lia).
exists (Z_to_bv 8 0). split; [apply BR; lia| left; reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma unp_partial_c1 : forall m X k,
X mod 8 = 0 -> 0 <= X -> X + 8 <= KEND -> 1 <= k <= 7 ->
rw_cells asegs m (shad X) [C1 (Z_to_bv 8 k)] ->
unpoisoned m X (X + k).
Proof.
intros m X k X8 X0 XH K1 H. unfold KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>11070027575.9 11646664446.1222303322924.1524889733320.1954041770956.9 57170504600.2000000700;00E00O00S00eS2XH2K1S2K1S2X82X02H0S2X82K12H0S2X0S2X82K13Hlo3Hhi2H0".
pose proof (rw_C1_high m (shad X) _ H ltac:(rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia)) as RB.
split; [lia|]. split; [lia|]. intros G Hlt Hlo Hhi.
assert (HG : G = X / 8) by (Z.div_mod_to_equations; lia). subst G.
exists (Z_to_bv 8 k). split.
- rewrite <- RB. rewrite shad_div. reflexivity.
- right. rewrite sval_lit by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma fse_got_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m ->
rw_cells asegs m 0x997d8 [C8 (Z_to_bv 64 0xa2480)] /\ rw_cells asegs m 0x997a0 [C8 (Z_to_bv 64 0x9b5e8)].
Proof.
intros AI L RNG st LB m AH. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
split.
- eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0x997d8 (le8 (Z_to_bv 64 0xa2480)));
[ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
| vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
- eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0x997a0 (le8 (Z_to_bv 64 0x9b5e8)));
[ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
| vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.
#[using="Type"] Lemma fse_rt_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m ->
rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rw_cells asegs m 0xa2480 [C4 (Z_to_bv 64 1)] /\ rt_inited m /\ rt_layout m.
Proof.
intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact G].
Qed.
#[using="Type"] Lemma cr_stack : forall CI LB SP A n, SP <= A -> A + n <= 2^47 -> aclient_range CI LB SP A n.
Proof. intros. left. left. split; assumption. Qed.
#[using="Type"] Lemma cr_block : forall CI LB SP A n b, In b LB -> ab_addr b <= A -> A + n <= ab_addr b + ab_size b -> aclient_range CI LB SP A n.
Proof. intros CI LB SP A n b Hb H1 H2. right. left. exists b. split; [exact Hb| split; assumption]. Qed.
#[using="Type"] Lemma cr_fshadow : forall CI LB SP F A n, In (FB5 F) LB -> F mod 8 = 0 -> 0 <= F ->
SHF F <= A -> A + n <= SHF F + 256 -> 0 <= n -> aclient_range CI LB SP A n.
Proof.
intros CI LB SP F A n Hb F8 F0 H1 H2 N0. right. right. right. right. exists 5, F, 2048. split; [exact Hb|].
unfold SHF in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020>29784498910.1331706470327.2000000100=SS2F82H12H21H".
rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Definition FZRB13 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma FZRB13_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
cells_size (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. reflexivity. Qed.
Definition FRA (x0 x8 x16 x24 x32 x40 x48 x56 : word) (j64 : list byte) (x80 : word) : list cell :=
[C8 x0; C8 x8; C8 x16; C8 x24; C8 x32; C8 x40; C8 x48; C8 x56; CB 16 j64; C8 x80].
Lemma land_ldiff_distrF x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity. Qed.
Lemma land_alignF : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 ->
Z.land x (Z.ldiff (Z.ones 64) (Z.ones k)) = x - x mod 2^k.
Proof.
intros x k Hx Hk. rewrite land_ldiff_distrF. Local Ltac2 Set LiaHints.tbl := fun () => "0050=33449776729.433918904998.535497642355.451794599906.45744834927.4 00000400700800<00@S2HkS1HSS2HkS2Hx".
rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_m32F : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)). rewrite land_alignF by lia. reflexivity. Qed.
Lemma spa_props5 : forall SP, SP mod 16 = 0 ->
let SPA := (SP - 192) - (SP - 192) mod 32 in
SP - 208 <= SPA <= SP - 192 /\ SPA mod 32 = 0 /\ SPA + 88 <= SP - 104.
Proof. intros SP H SPA. subst SPA. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>29960295359.2300000CS1H2H02H12H52H63H10".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma page_round_up_geF : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof. intros x Hx. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.
#[using="Type"] Lemma harness_topF : forall L SP, SP + ATRUN_DEPTH = al_sp0 L -> 0 <= SP -> SP + 16 <= al_top L < SP + 48 + 4096.
Proof.
intros L SP E H0. unfold al_top. rewrite <- E. unfold ATRUN_DEPTH. Local Ltac2 Set LiaHints.tbl := fun () => "0030=18689963921.559055300873.5754485203.6  000004005008S2H0SS1H".
replace (SP + 208 - 160) with (SP + 48) by lia.
pose proof (page_round_up_geF (SP + 48) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fzrb13_saved : forall m SP (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
rw_cells asegs m (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
bytes_at asegs m (SP - 16) (le8 s0) /\ bytes_at asegs m (SP - 8) (le8 ra).
Proof.
intros until s11. intros [[_ B] _]. unfold FZRB13 in B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
do 11 (apply (proj1 (bytes_at_app _ _ _ _ _)) in B; destruct B as [_ B]; rewrite length_le8 in B).
apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [B1 B2]. rewrite length_le8 in B2.
split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0020>17406515338.1868068303114.18000001002SS".
replace (SP - 16) with (SP + -104 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact B1.
- replace (SP - 8) with (SP + -104 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact B2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma harness_uchainF : forall m (top PC SP sp' zl : Z),
bytes_at asegs m (SP - 16) (le8 (Z_to_bv 64 zl)) -> bytes_at asegs m (SP - 8) (le8 (Z_to_bv 64 ATRUN_RET)) ->
0 <= zl < SP -> SP mod 8 = 0 -> sp' < SP -> PC <> ATRUN_RET -> SP + 16 <= top ->
exists tr, uchain m top PC sp' SP UDEPTH tr /\ (tr = [] \/ tr = [ATRUN_RET]).
Proof.
intros m top PC SP sp' zl B1 B2 HZ SP8 HS NE TOP.
pose proof (bytes_at_bound _ _ _ _ B2) as BB. rewrite length_le8 in BB.
destruct (Z_lt_le_dec SP (top - 16)) as [LT|GE].
- exists [ATRUN_RET]. split; [| right; reflexivity].
Local Ltac2 Set LiaHints.tbl := fun () => "0060>15624047542.1626115181345.1627820268249.1630226979373.1646311404395.165680958410.16 00000700>00E00I00P00TS2HZ2BBS2HZ2BBS2NE2BBS2BBS2BB2GES2BB".
replace [ATRUN_RET] with ((if ATRUN_RET =? PC then [] else [ATRUN_RET]) ++ []) by (replace (ATRUN_RET =? PC) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
eapply uc_step with (fp := zl); [exact HS| exact LT| exact SP8| unfold UDEPTH; lia| exact B1| exact B2| unfold ATRUN_RET; lia| lia|].
apply uc_stop. lia.
- exists []. split; [| left; reflexivity]. apply uc_stop. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma harness_trace_inF : forall (U : list (list Z)) PC RET tr,
In [PC; RET; ATRUN_RET] U -> In [PC; RET] U -> (tr = [] \/ tr = [ATRUN_RET]) -> In (PC :: RET :: tr) U /\ (length tr <= 28)%nat.
Proof. intros U PC RET tr H3 H2 [-> | ->]; cbn; split; auto; lia. Qed.
End CANSEC2.
Section FshUnp.
Variables (m : amem) (F : Z).
Hypothesis F2048 : F mod 2048 = 0.
Hypothesis F0 : 0 <= F.
Hypothesis FE : F + 2048 + 8 <= KEND.
#[using="F2048 F0"] Lemma shad_frame_off : forall k, 0 <= k -> k mod 8 = 0 -> shad (F + k) = SHF F + k / 8.
Proof. intros k Hk K8. rewrite <- SHF_shad. unfold SHF. Local Ltac2 Set LiaHints.tbl := fun () => "0020>20966566545.3629784418006.8 00000L00SS5F20482K81H2H02H42H52H93H14S2F02Hk".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fsh_cell : forall cs k c, rw_cells asegs m (SHF F) cs -> nth_error cs k = Some c ->
rw_cells asegs m (SHF F + Z.of_nat (cells_size (firstn k cs))) [c].
Proof. intros cs k c H E. eapply rw_cells_nth; eassumption. Qed.
#[using="F2048 F0 FE"] Lemma fsh_unp_data : forall sn sr g1 g2, rw_cells asegs m (SHF F) (FSH Z64 sn sr g1 g2) -> unpoisoned m (F + 32) (F + 544).
Proof.
intros sn sr g1 g2 H. pose proof (fsh_cell _ 4 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>29277661002.1131527535260.1144021377819.1160942217710.1160998424697.1166151427713.2500000700;00?00C00G00WS2F02FES2F0S2F0S2F0S2F0S5F20482H02H12H5".
replace (F + 544) with (F + 32 + 8 * Z.of_nat 64) by lia. apply unp_zero_cb; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia|].
rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (32 / 8) with 4. exact C.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="F2048 F0 FE"] Lemma fsh_unp_nc : forall sd sr g1 g2, rw_cells asegs m (SHF F) (FSH sd Z64 sr g1 g2) -> unpoisoned m (F + 608) (F + 1120).
Proof.
intros sd sr g1 g2 H. pose proof (fsh_cell _ 13 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>39866934766.1143527870108.1153857049418.1160912168731.1164696539257.1166151427713.2500000400800?00C00G00WS2F0S2F0S2F02FES2F0S2F0S5F20482H02H12H5".
replace (F + 1120) with (F + 608 + 8 * Z.of_nat 64) by lia. apply unp_zero_cb; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia|].
rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (608 / 8) with 76. exact C.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="F2048 F0 FE"] Lemma fsh_unp_rt : forall sd sn g1 g2, rw_cells asegs m (SHF F) (FSH sd sn Z64 g1 g2) -> unpoisoned m (F + 1184) (F + 1696).
Proof.
intros sd sn g1 g2 H. pose proof (fsh_cell _ 22 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>10241893147.1113300128412.1146099943242.1163678339193.1166151427713.258276220398.11 00000400800?00C00S00WS2F0S2F0S2F02FES2F0S5F20482H02H12H5S2F0".
replace (F + 1696) with (F + 1184 + 8 * Z.of_nat 64) by lia. apply unp_zero_cb; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia|].
rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (1184 / 8) with 148. exact C.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="F2048 F0 FE"] Lemma fsh_unp_msv : forall sd sn sr g2, rw_cells asegs m (SHF F) (FSH sd sn sr B04 g2) -> unpoisoned m (F + 1760) (F + 1764).
Proof.
intros sd sn sr g2 H. pose proof (fsh_cell _ 31 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>10686471326.1118598602162.1125298218652.1127132684059.1155928933870.1156698953477.1166151427713.2500000400800<00@00D00K00[S2F0S2F0S2F0S2F0S2F0S2F02FES5F20482H02H12H5".
replace (F + 1764) with (F + 1760 + 4) by lia. apply unp_partial_c1; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia| lia|].
rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (1760 / 8) with 220. exact C.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="F2048 F0 FE"] Lemma fsh_unp_tl : forall sd sn sr g1, rw_cells asegs m (SHF F) (FSH sd sn sr g1 B04) -> unpoisoned m (F + 1776) (F + 1780).
Proof.
intros sd sn sr g1 H. pose proof (fsh_cell _ 33 _ H eq_refl) as C. cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>18598602162.1133138673822.1152725816732.1156422069253.115643279899.11 66151427713.2567965348078.1100000400800<00C00G00W00[S2F0S2F0S2F0S2F02FES2F0S5F20482H02H12H5S2F0".
replace (F + 1780) with (F + 1776 + 4) by lia. apply unp_partial_c1; [Z.div_mod_to_equations; lia| lia| unfold KEND in *; lia| lia|].
rewrite shad_frame_off by (try lia; Z.div_mod_to_equations; lia). change (1776 / 8) with 222. exact C.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fsh_wr : forall cs, rw_cells asegs m (SHF F) cs -> cells_size cs = 256%nat -> wr_at asegs m (shad F) 256.
Proof. intros cs H S. rewrite <- SHF_shad. pose proof (proj2 H) as W. rewrite S in W. exact W. Qed.
End FshUnp.
Section CANSEC3. Context {rc : runConstT}.
Definition fse_rt (m : amem) : Prop :=
rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rt_inited m /\ rt_layout m
/\ rw_cells asegs m 0x997a0 [C8 (Z_to_bv 64 0x9b5e8)].
#[using="Type"] Lemma fse_rtall_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m -> fse_rt m.
Proof.
intros AI L RNG st LB m AH. destruct (fse_rt_of_aheap AI L RNG st LB m AH) as (A & B & C & D & _ & F & G).
destruct (fse_got_of_aheap AI L RNG st LB m AH) as [_ H].
exact (conj A (conj B (conj C (conj D (conj F (conj G H)))))).
Qed.
Fixpoint above (lo : Z) (W : list (Z * Z)) : Prop :=
match W with [] => True | (a, b) :: W' => lo <= a /\ above lo W' end.
#[using="Type"] Lemma disjoint_of_above : forall W A n, above (A + n) W -> 0 <= n -> disjoint_from W A n.
Proof. induction W as [|[a b] W IH]; intros A n H N; cbn in *; [exact I|]. destruct H as [H1 H2]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30162186735.10000004S2H1".
split; [lia| apply IH; assumption]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fse_rt_munch : forall W m m', fse_rt m -> munch W m m' -> wmono asegs m m' -> above AIMG_HI W -> fse_rt m'.
Proof.
intros W m m' (A & B & C & D & E & F & G) MU WM AB.
assert (T : forall X cs, rw_cells asegs m X cs -> X + Z.of_nat (cells_size cs) <= AIMG_HI -> rw_cells asegs m' X cs).
{ intros X cs H HX. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. Local Ltac2 Set LiaHints.tbl := fun () => "0090>20452227590.9 35768368014.1542928432270.154670299534.15 56354406158.1557045487118.1561085553934.1565248414094.1567996735521.1800000700800900:00;00<00=00>00?S2A12HXSSSSSSSS".
apply disjoint_of_above; [| lia].
clear - AB HX. induction W as [|[a b] W IH]; cbn in *; [exact I|]. destruct AB as [A1 A2]. split; [lia| apply IH; exact A2]. }
unfold AIMG_HI in T.
refine (conj (T _ _ A _) (conj (T _ _ B _) (conj (T _ _ C _) (conj (T _ _ D _) (conj (T _ _ E _) (conj (T _ _ F _) (T _ _ G _))))))); cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC3.
Section CANSEC4. Context {rc : runConstT}.
#[using="Type"] Lemma bytes_at_firstnF : forall m A bs n, bytes_at asegs m A bs -> (n <= length bs)%nat -> bytes_at asegs m A (firstn n bs).
Proof.
intros m A bs n (H0 & H1 & HB) Hn. split; [exact H0|]. Local Ltac2 Set LiaHints.tbl := fun () => "0030>13024375603.121312062801.9  9241913293.12 00000900@00IS2Hn2Hi1HS2H12HnS2Hn2Hi1H".
split; [rewrite length_firstn; lia|].
intros i Hi. rewrite length_firstn in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [| lia]. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma u8arr_of_two_cb : forall m A n1 n2 b1 b2,
rw_cells asegs m A [CB n1 b1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 b2] -> u8arr asegs m A (b1 ++ b2).
Proof.
intros m A n1 n2 b1 b2 H1 H2.
assert (H2' : rw_cells asegs m (A + Z.of_nat (cells_size [CB n1 b1])) [CB n2 b2]) by (cbn [cells_size csize]; rewrite Nat.add_0_r; exact H2).
pose proof (proj2 (rw_cells_app _ _ _ [CB n1 b1] [CB n2 b2]) (conj H1 H2')) as H.
apply (u8arr_of_rw_cells asegs m A (n1 + n2)). eapply rw_cells_recast; [exact H| | | ].
- destruct H as [[[L1 [L2 _]] _] _]. cbn in L1, L2 |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0020>2888287004.12 41065774016.11000007008S2L12L2S".
split; [rewrite length_app; lia| exact I].
- cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
- cbn [cells_size csize app]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC4.
