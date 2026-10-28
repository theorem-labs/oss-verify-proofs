(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require FpReal ExpfModelB ExpfTablesB.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptExecB
  DitherLib DitherLoop LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap2 V2LeptExpf V2LeptKernCreateS V2LeptKernCreateS1 V2LeptKernDestroyS
  V2LeptKgauSegs V2LeptBl3_iface V2LeptKvals V2LeptKobjLib V2LeptUb.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomK LeptRoomBL LeptRop2Arith LeptRgbLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KgauW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition kgw_cell (i j : Z) : Z :=
  ExpfModelB.gauss_cell ExpfTablesB.DEN_GAUSS_D FpReal.p_one_s ((i - 20) * (i - 20) + (j - 20) * (j - 20)).

(* [comment removed for export] *)
Definition GI (M : word -> option byte) (kel arr : Z) (rows : Z -> Z) : Prop :=
  rdn SEGS M (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) /\
  rdn SEGS M (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) /\
  rdn SEGS M (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) /\
  (forall i, (0 <= i < 41)%Z -> rdn SEGS M (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) /\
  korg M kel 20 20.

Definition GV (M : word -> option byte) (rows : Z -> Z) (n : Z) : Prop :=
  forall i j, (0 <= i < n)%Z -> (0 <= j < 41)%Z -> rdn SEGS M (Z_to_bv 64 (rows i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (kgw_cell i j)).

(* [comment removed for export] *)
Definition GG (C : lctx) (A A1 : AS) (s kel arr : Z) (rows : Z -> Z) : Prop :=
  (4096 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ (kel mod 16 = 0)%Z /\ live A1 (Z_to_bv 64 kel) = Some 24%Z /\
  (4096 <= arr)%Z /\ (arr + 328 <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ live A1 (Z_to_bv 64 arr) = Some 328%Z /\
  (forall i, (0 <= i < 41)%Z -> (4096 <= rows i)%Z /\ (rows i + 164 <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\
     live A1 (Z_to_bv 64 (rows i)) = Some 164%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
     (rows i + 164 <= kel \/ kel + 24 <= rows i)%Z /\ (rows i + 164 <= arr \/ arr + 328 <= rows i)%Z) /\
  (forall i i', (0 <= i < 41)%Z -> (0 <= i' < 41)%Z -> i <> i' -> (rows i + 164 <= rows i' \/ rows i' + 164 <= rows i)%Z) /\
  sub_live A A1 /\ (alloc_top (c_vm C) + 8192 <= s - 128)%Z.

Lemma kgw_ag_keep : forall (L : list reg) regs regs' (r : reg) (v : word),
  regs_agree (fun x => In x L) regs regs' -> existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = false ->
  getr regs r = v -> getr regs' r = v.
Proof.
  intros L regs regs' r v AG E H. rewrite AG; [exact H|]. intros Hin.
  assert (T : existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) L = true).
  { apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.
Lemma kgw_ag_comp : forall (L1 L2 L : list reg) r1 r2 r3,
  regs_agree (fun x => In x L1) r1 r2 -> regs_agree (fun x => In x L2) r2 r3 ->
  forallb (fun x => existsb (fun y => Z.eqb (bv_unsigned y) (bv_unsigned x)) L) (L1 ++ L2) = true ->
  regs_agree (fun x => In x L) r1 r3.
Proof.
  intros L1 L2 L r1 r2 r3 A1 A2 B r Hr. rewrite forallb_forall in B.
  assert (IN : forall x, In x (L1 ++ L2) -> In x L).
  { intros x Hx. specialize (B x Hx). apply existsb_exists in B. destruct B as (y & Hy & E).
    apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hy. }
  rewrite A2, A1; [reflexivity | |].
  - intros Hin. apply Hr, IN, in_or_app. left. exact Hin.
  - intros Hin. apply Hr, IN, in_or_app. right. exact Hin.
Qed.
Ltac kgk AG := apply (kgw_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity |].
Ltac kgc A1 A2 := eapply kgw_ag_comp; [exact A1 | exact A2 | vm_compute; reflexivity].
Ltac kgin := cbn [In]; repeat first [left; reflexivity | right].
Ltac kglen := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac kgwsw CK := repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | kglen]).

Lemma kgw_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Lemma kgw_kvals : forall m rows, GV m rows 41 -> kvals m 41 41 rows kgw_cell.
Proof.
  intros m rows G i j Hi Hj. split; [exact (G i j Hi Hj) |].
  unfold kgw_cell. apply ExpfTablesB.bil_gauss_FB.
  pose proof (Z.square_nonneg (i - 20)) as Q1. pose proof (Z.square_nonneg (j - 20)) as Q2.
  assert (Q3 : (0 <= (20 - (i - 20)) * (20 + (i - 20)))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Q4 : (0 <= (20 - (j - 20)) * (20 + (j - 20)))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  nia.
Qed.

Lemma kgw_centre : kgw_cell 20 20 = FpReal.p_one_s.
Proof. unfold kgw_cell. exact ExpfTablesB.bil_gauss_centre. Qed.

Lemma kgw_kern_mem : forall C A A' m m' kel arr h w rows, kern C A A' m kel arr h w rows ->
  rdn SEGS m' (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
  rdn SEGS m' (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
  rdn SEGS m' (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
  (forall i, (0 <= i < h)%Z -> rdn SEGS m' (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) ->
  kern C A A' m' kel arr h w rows.
Proof.
  intros C A A' m m' kel arr h w rows K R1 R2 R3 R4.
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & _ & _ & _ & K10 & K11 & K12 & K13 & K14 & K15 & K16 & KR & KD & KL).
  refine (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj R1 (conj R2 (conj R3
          (conj K10 (conj K11 (conj K12 (conj K13 (conj K14 (conj K15 (conj K16 (conj _ (conj KD KL)))))))))))))))))).
  intros i Hi. destruct (KR i Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (R4 i Hi))))))))).
Qed.

Lemma GI_rinv : forall M M' kel arr rows ri lo, GI M kel arr rows -> rinv [(ri, 164%Z); (lo, 16%Z)] M M' ->
  (4096 <= kel)%Z -> (kel + 24 <= lo)%Z -> (4096 <= arr)%Z -> (arr + 328 <= lo)%Z -> (lo + 16 <= 2 ^ 64)%Z ->
  (ri + 164 <= kel \/ kel + 24 <= ri)%Z -> (ri + 164 <= arr \/ arr + 328 <= ri)%Z ->
  GI M' kel arr rows.
Proof.
  intros M M' kel arr rows ri lo (R1 & R2 & R3 & R4 & K1 & K2) RI Hk Hkl Ha Hal Hl D1 D2.
  assert (T : forall (a : Z) (n : nat), (0 <= a)%Z -> (a + Z.of_nat n <= lo)%Z -> (a + Z.of_nat n <= ri \/ ri + 164 <= a)%Z ->
     rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n).
  { intros a n Ha0 Hal' Hr. apply (rinv_rdn SEGS _ M M' a n RI); [lia | lia |].
    intros r Hr'. cbn [In] in Hr'. destruct Hr' as [<- | [<- | []]]; cbn [fst snd]; lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R1.
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R2.
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R3.
  - intros i Hi. rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (R4 i Hi).
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact K1.
  - rewrite T by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact K2.
Qed.

Lemma GV_rinv : forall M M' rows n ri lo, GV M rows n -> rinv [(ri, 164%Z); (lo, 16%Z)] M M' -> (lo + 16 <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < n)%Z -> (0 <= rows i)%Z /\ (rows i + 164 <= lo)%Z /\ (rows i + 164 <= ri \/ ri + 164 <= rows i)%Z) ->
  GV M' rows n.
Proof.
  intros M M' rows n ri lo G RI Hl D i j Hi Hj. destruct (D i Hi) as (D0 & D1 & D2).
  rewrite (rinv_rdn SEGS _ M M' (rows i + 4 * j) 4 RI); [exact (G i j Hi Hj) | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
  intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma GV_step : forall M rows i, GV M rows i ->
  (forall jj, (0 <= jj < 41)%Z -> rdn SEGS M (Z_to_bv 64 (rows i + 4 * jj)) 4 = Some (Z_to_le_bytes 4 (kgw_cell i jj))) ->
  GV M rows (i + 1).
Proof.
  intros M rows i G V i' j Hi' Hj. destruct (Z.eq_dec i' i) as [-> | N]; [exact (V j Hj) | apply G; lia].
Qed.

Lemma kgw_fs_not : forall r : reg, In (u r) fs_list -> r <> 14%bv /\ r <> 15%bv.
Proof.
  intros r H. unfold fs_list in H. cbn [In] in H.
  split; intro E; subst r; vm_compute in H; lia.
Qed.

Definition GREGS : list reg := [1; 2; 10; 11; 12; 13; 14; 19; 20; 24; 25]%bv.

(* [comment removed for export] *)
Lemma kg_rows : forall (k : nat) (i : Z) fr0 fr cs r R3 M C A A1 md vm1 (s : Z) m (ret : word) r0 f0 kel arr rows (S : TSet),
  Cok C -> (s <= c_top C)%Z -> (c_top C - LSTK <= s - 128)%Z -> (s <= 2 ^ 47)%Z -> (0 <= i < 41)%Z -> Z.of_nat k = (41 - i)%Z ->
  GG C A A1 s kel arr rows -> frm_zero cs ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C A s m M -> cellsZ M (frameg s ret r0 f0) -> GI M kel arr rows -> GV M rows i ->
  getr r 2 = Z_to_bv 64 (s - 112) -> getr r 19 = Z_to_bv 64 i -> regs_agree (fun x => In x GREGS) R3 r ->
  getr R3 8 = Z_to_bv 64 20 -> getr R3 9 = Z_to_bv 64 20 -> getr R3 18 = Z_to_bv 64 kel -> getr R3 21 = Z_to_bv 64 40 ->
  getr R3 22 = Z_to_bv 64 41 -> getr R3 23 = Z_to_bv 64 (-20) ->
  reg_get fr0 8 = nan_box (Z_to_bv 32 FpReal.p_one_s) -> reg_get fr0 9 = Z_to_bv 64 ExpfTablesB.DEN_GAUSS_D ->
  (forall x : reg, In (u x) fs_list -> reg_get fr x = reg_get fr0 x) ->
  (forall fr' cs' M' r', W C A1 M' (with_vmmaps vm1 md) -> POSTM C A s m M' -> cellsZ M' (frameg s ret r0 f0) ->
     GI M' kel arr rows -> GV M' rows 41 -> frm_zero cs' -> (forall x : reg, In (u x) fs_list -> reg_get fr' x = reg_get fr0 x) ->
     getr r' 2 = Z_to_bv 64 (s - 112) -> regs_agree (fun x => In x GREGS) R3 r' ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r' (0x39258 : word) M' al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r (0x39158 : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [| k IH]; intros i fr0 fr cs r R3 M C A A1 md vm1 s m ret r0 f0 kel arr rows S CK Hsc Hlo H47 Hi Hk GGi Hz HWM PM CF GIM GVM
    S2 S19 AGr R38 R39 R318 R321 R322 R323 F08 F09 FS POST'; [lia|].
  pose proof GGi as (Gk & Gk2 & Gk16 & LAk & Ga & Ga2 & Ga16 & LAa & GR & GD & SL & Gtop).
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS.
  pose proof HWM as [_ WPM _ _ _ _ _ _ _ _ _]. pose proof WPM as [MHM MLM _].
  destruct (GR i Hi) as (Gr & Gr2 & Gr16 & LAr & LAr0 & L0r & Drk & Dra).
  pose proof GIM as (Ch & Cw & Ca & Crows & Kor).
  destruct (kg_OH al_rom (mkFP fr cs) r M i Hi ltac:(kgk AGr; exact R38) ltac:(kgk AGr; exact R39) S19 ltac:(kgk AGr; exact R323))
    as (r1 & MOH & G120 & G124 & G125 & AGOH).
  eapply rz_msteps; [exact MHM | exact MLM | exact MOH |].
  assert (SOKr : store_ok SEGS M (Z_to_bv 64 (rows i)) 164 = true).
  { apply (kgw_sok_blk C A1 M (with_vmmaps vm1 md) (Z_to_bv 64 (rows i)) 164); [exact CK | exact HWM | exact LAr | | |]; rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (SOKs : store_ok SEGS M (Z_to_bv 64 (s - 128)) 16 = true).
  { apply (W_sok_win C A1 M (with_vmmaps vm1 md)); [exact CK | exact HWM | lia | cbn; lia]. }
  eapply rz_reach; [exact WPM | |].
  { apply (kg_inner al_rom s kel arr i (rows i) M ltac:(repeat split; lia)
             ltac:(split; [apply al16_mod8; exact Gk16 | split; [apply al16_mod8; exact Ga16 | apply al16_mod4; exact Gr16]])
             SOKr SOKs Ch Cw Ca (Crows i Hi)
             ltac:(intros j Hj; apply (W_ro C A1 M (with_vmmaps vm1 md) (Z_to_bv 64 j) HWM); unfold inZ; rewrite u_Z2bv by lia; cbn; lia)
             ltac:(intros j Hj; apply (W_ro C A1 M (with_vmmaps vm1 md) (Z_to_bv 64 j) HWM); unfold inZ; rewrite u_Z2bv by lia; cbn; lia)
             41%nat fr r1 fr cs r1 M 0 ltac:(reflexivity) ltac:(lia) Hz (rinv_refl _ _)
             ltac:(kgk AGOH; exact S2) G120 G125 G124 ltac:(kgk AGOH; kgk AGr; exact R318) ltac:(kgk AGOH; kgk AGr; exact R322)
             ltac:(kgk AGOH; exact S19) ltac:(rewrite (FS 8%bv ltac:(vm_compute; left; reflexivity)); exact F08)
             ltac:(rewrite (FS 9%bv ltac:(vm_compute; right; left; reflexivity)); exact F09)
             (regs_agree_refl _ _) (fun x _ => eq_refl)). }
  intros fin (fr' & cs' & r2 & M' & -> & Hz' & RI & RI2 & S2' & AGI & FSI & VAL).
  assert (LR : local_regions C A1 A (s - 112) (R_Kg s (rows i))).
  { unfold local_regions, R_Kg. constructor.
    - right. exists (Z_to_bv 64 (rows i)), 164%Z. rewrite u_Z2bv by lia. cbn [fst snd]. repeat split; try assumption; lia.
    - constructor; [left; cbn [fst snd]; lia | constructor]. }
  destruct (rinv_WP2 C A A1 M (with_vmmaps vm1 md) M' (R_Kg s (rows i)) (s - 112) CK HWM SL ltac:(lia) RI LR) as (W' & PMr).
  assert (PM' : POSTM C A s m M') by (eapply POSTM_trans; [exact PM | apply (POSTM_mono C A (s - 112) s); [lia | exact PMr]]).
  assert (CF' : cellsZ M' (frameg s ret r0 f0)).
  { apply (cellsZ_frm C (s - 112) M M'); [exact CK | exact (proj1 PMr) | lia | | exact CF].
    eapply Forall_impl; [| apply frameg_bounds; lia]. intros av Hav. cbn beta in Hav |- *. lia. }
  assert (GI' : GI M' kel arr rows) by (apply (GI_rinv M M' kel arr rows (rows i) (s - 128) GIM RI); lia).
  assert (GV' : GV M' rows (i + 1)).
  { apply GV_step.
    - apply (GV_rinv M M' rows i (rows i) (s - 128) GVM RI ltac:(lia)). intros i' Hi'.
      destruct (GR i' ltac:(lia)) as (Gr' & Gr2' & _). destruct (GD i' i ltac:(lia) Hi ltac:(lia)) as [X | X]; lia.
    - intros jj Hjj. exact (VAL jj ltac:(lia)). }
  assert (FS' : forall x : reg, In (u x) fs_list -> reg_get fr' x = reg_get fr0 x) by (intros x Hx; rewrite (FSI x Hx); exact (FS x Hx)).
  assert (AG12 : regs_agree (fun x => In x GREGS) R3 r2).
  { assert (AGa : regs_agree (fun x => In x GREGS) R3 r1) by (kgc AGr AGOH). kgc AGa AGI. }
  pose proof W' as [_ WP' _ _ _ _ _ _ _ _ _]. pose proof WP' as [MH' ML' _].
  destruct (Z.eq_dec (i + 1) 41) as [Last | NotLast].
  - destruct (kg_ON al_rom (mkFP fr' cs') true r2 M' i Hi Last ltac:(kgk AGI; kgk AGOH; exact S19) ltac:(kgk AGI; kgk AGOH; kgk AGr; exact R321))
      as (r3 & MON & G319 & AGON).
    eapply rz_msteps; [exact MH' | exact ML' | exact MON |].
    apply (POST' fr' cs' M' r3 W' PM' CF' GI' ltac:(rewrite <- Last; exact GV') Hz' FS' ltac:(kgk AGON; exact S2') ltac:(kgc AG12 AGON)).
  - destruct (kg_ON al_rom (mkFP fr' cs') false r2 M' i Hi ltac:(change (i + 1 < 41)%Z; lia) ltac:(kgk AGI; kgk AGOH; exact S19) ltac:(kgk AGI; kgk AGOH; kgk AGr; exact R321))
      as (r3 & MON & G319 & AGON).
    eapply rz_msteps; [exact MH' | exact ML' | exact MON |].
    apply (IH (i + 1)%Z fr0 fr' cs' r3 R3 M' C A A1 md vm1 s m ret r0 f0 kel arr rows S CK Hsc Hlo H47 ltac:(lia) ltac:(lia) GGi Hz' W' PM' CF' GI' GV'
             ltac:(kgk AGON; exact S2') G319 ltac:(kgc AG12 AGON) R38 R39 R318 R321 R322 R323 F08 F09 FS' POST').
Qed.

(* [comment removed for export] *)
Theorem makeGaussianKernel_W : makeGaussianKernel_contract.
Proof.
  intros fr cs C A m md regs s ret S CK HW Hz H2 Hs16 Hstk Hsc H1 Hret H4 H10 H11 Hfa0 Hfa1 kR bR AR HkR HbR POST.
  replace (Z_to_bv 64 PC_makeGaussianKernel) with (0x390ac : word) by (apply bv_eq; reflexivity).
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS. unfold KER_STACK, LSF in Hstk.
  assert (IMG : (0 <= alloc_top (c_vm C))%Z) by (pose proof Cimg as X; cbn in X; lia).
  pose proof HW as [WI WP _ _ _ _ _ _ _ _ _]. pose proof WP as [MH ML _].
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  destruct (kg_A al_rom fr cs regs m s ret ltac:(lia) ltac:(lia) SOKf H2 H1 H10 H11 Hfa0 Hfa1)
    as (fr1 & R1 & M1 & FO1 & F18 & F19 & S1 & G11 & G1a & G1b & G18 & G19 & G121 & G122 & AG1).
  set (m1 := FRG m s ret regs fr) in *.
  assert (W1 : W C A m1 md) by (unfold m1, FRG; kgwsw CK; exact HW).
  assert (PM1 : POSTM C A s m m1).
  { apply (POSTM_range C A m md m1 (s - 104) s s CK HW); [ | lia | lia | lia].
    intros a Ha. unfold m1. apply FRG_out; lia. }
  assert (CF1 : cellsZ m1 (frameg s ret regs fr)) by (unfold m1; apply frameg_init; lia).
  eapply rz_msteps; [exact MH | exact ML | exact M1 |].
  apply (kernelCreate_S1_W (fx := mkFP fr1 cs) C A m1 md R1 (s - 112)%Z 41 41 (Z_to_bv 64 0x3911c) S kR bR CK W1 S1
           ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) G11 ltac:(red; apply bv_eq; reflexivity)
           ltac:(kgk AG1; exact H4) G1a G1b ltac:(lia) ltac:(lia) ltac:(lia) AR HkR HbR).
  intros A1 m2 vm1 R2 W2 CK2 PM2 (kel & arr & rows & G2k & KN) AR1.
  replace (Z_to_bv 64 0x3911c) with (0x3911c : word) by (apply bv_eq; reflexivity).
  pose proof KN as (Kk1 & Kk2 & Kk16 & LA1k & LAk & L0k & Rh & Rw & Ra & Ka1 & Ka2 & Ka16 & Kne & LA1a & LAa & L0a & KROWS & KDIST & KFR).
  pose proof W2 as [_ WP2 _ _ _ _ _ _ _ _ _]. pose proof WP2 as [MH2 ML2 _].
  assert (SLA : sub_live A A1) by (exact (kern_sub_live _ _ _ _ _ _ _ _ _ KN)).
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 kel) 24 CK W2 LA1k ltac:(lia)) as BRk. rewrite u_Z2bv in BRk by lia.
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 arr) (8 * 41) CK W2 LA1a ltac:(lia)) as BRa. rewrite u_Z2bv in BRa by lia.
  assert (SOKk : store_ok SEGS m2 (Z_to_bv 64 (kel + 8)) 8 = true).
  { apply (kgw_sok_blk C A1 m2 (with_vmmaps vm1 md) (Z_to_bv 64 kel) 24); [exact CK | exact W2 | exact LA1k | | |]; rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct (kg_B al_rom fr1 cs R2 m2 kel ltac:(lia) ltac:(lia) ltac:(apply al16_mod8; exact Kk16) Hz SOKk F19 G2k
              ltac:(rewrite (cs_kept_get _ _ 8%bv CK2) by (right; right; right; left; reflexivity); exact G18)
              ltac:(rewrite (cs_kept_get _ _ 9%bv CK2) by (right; right; right; right; left; reflexivity); exact G19)
              ltac:(rewrite (cs_kept_get _ _ 22%bv CK2) by (right; right; right; right; right; vm_compute; split; discriminate); exact G122))
    as (fr2 & cs2 & R3 & M3 & Hz2 & FO2 & F29 & G318 & G319 & G322 & G323 & AG3).
  set (m2b := wbytes m2 (Z_to_bv 64 (kel + 8)) (word_to_le_bytes 4 (Z_to_bv 64 20))) in *.
  set (m3 := wbytes m2b (Z_to_bv 64 (kel + 12)) (word_to_le_bytes 4 (Z_to_bv 64 20))) in *.
  assert (W2b : W C A1 m2b (with_vmmaps vm1 md)).
  { unfold m2b. apply (W_store_blk C A1 m2 _ (Z_to_bv 64 kel) _ 24); [exact CK | exact W2 | exact LA1k | exact L0k | rewrite !u_Z2bv by lia; lia | kglen]. }
  assert (W3 : W C A1 m3 (with_vmmaps vm1 md)).
  { unfold m3. apply (W_store_blk C A1 m2b _ (Z_to_bv 64 kel) _ 24); [exact CK | exact W2b | exact LA1k | exact L0k | rewrite !u_Z2bv by lia; lia | kglen]. }
  assert (PM3 : POSTM C A (s - 112) m2 m3).
  { eapply POSTM_trans.
    - unfold m2b. apply (POSTM_blk C A A1 m2 _ (Z_to_bv 64 kel) (Z_to_bv 64 (kel + 8)) 24 (word_to_le_bytes 4 (Z_to_bv 64 20)) (s - 112) CK W2 LA1k LAk SLA);
        [rewrite !u_Z2bv by lia; lia | kglen].
    - unfold m3. apply (POSTM_blk C A A1 m2b _ (Z_to_bv 64 kel) (Z_to_bv 64 (kel + 12)) 24 (word_to_le_bytes 4 (Z_to_bv 64 20)) (s - 112) CK W2b LA1k LAk SLA);
        [rewrite !u_Z2bv by lia; lia | kglen]. }
  assert (PMm3 : POSTM C A s m m3).
  { eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [apply (POSTM_mono C A (s - 112) s); [lia | exact PM2] |].
    apply (POSTM_mono C A (s - 112) s); [lia | exact PM3]. }
  assert (CF3 : cellsZ m3 (frameg s ret regs fr)).
  { apply (cellsZ_frm C (s - 112) m1 m3); [exact CK | exact (FRM_trans _ _ _ _ _ (proj1 PM2) (proj1 PM3)) | lia | | exact CF1].
    eapply Forall_impl; [| apply frameg_bounds; lia]. intros av Hav. cbn beta in Hav |- *. lia. }
  assert (DKA : (arr + 328 <= kel \/ kel + 24 <= arr)%Z).
  { destruct (live_apart C A1 m2 _ (Z_to_bv 64 arr) (Z_to_bv 64 kel) (8 * 41) 24 CK W2 LA1a LA1k
                (zbv_ne arr kel ltac:(lia) ltac:(lia) (fun E => Kne (eq_sym E))) ltac:(lia) ltac:(lia)) as [X | X];
      rewrite !u_Z2bv in X by lia; lia. }
  assert (GI3 : GI m3 kel arr rows).
  { unfold m3, m2b. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - rewrite !rdn_wbytes_out_Z by kglen. exact Rh.
    - rewrite !rdn_wbytes_out_Z by kglen. exact Rw.
    - rewrite !rdn_wbytes_out_Z by kglen. exact Ra.
    - intros i Hi. destruct (KROWS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & Ri).
      rewrite !rdn_wbytes_out_Z by kglen. exact Ri.
    - rewrite rdn_wbytes_out_Z by kglen. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia.
    - apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (GGi : GG C A A1 s kel arr rows).
  { unfold GG. split; [lia |]. split; [exact Kk2 |]. split; [exact Kk16 |]. split; [exact LA1k |]. split; [lia |]. split; [lia |].
    split; [exact Ka16 |]. split; [exact LA1a |]. split; [| split; [| split; [exact SLA | lia]]].
    - intros i Hi. destruct (KROWS i Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _).
      pose proof (blk_range C A1 m2 _ (Z_to_bv 64 (rows i)) (4 * 41) CK W2 X6 ltac:(lia)) as BRr. rewrite u_Z2bv in BRr by lia.
      split; [lia |]. split; [lia |]. split; [exact X3 |]. split; [exact X6 |]. split; [exact X7 |]. split; [exact X8 |]. split.
      + destruct (live_apart C A1 m2 _ (Z_to_bv 64 (rows i)) (Z_to_bv 64 kel) (4 * 41) 24 CK W2 X6 LA1k
                    (zbv_ne (rows i) kel ltac:(lia) ltac:(lia) X5) ltac:(lia) ltac:(lia)) as [X | X]; rewrite !u_Z2bv in X by lia; lia.
      + destruct (live_apart C A1 m2 _ (Z_to_bv 64 (rows i)) (Z_to_bv 64 arr) (4 * 41) (8 * 41) CK W2 X6 LA1a
                    (zbv_ne (rows i) arr ltac:(lia) ltac:(lia) X4) ltac:(lia) ltac:(lia)) as [X | X]; rewrite !u_Z2bv in X by lia; lia.
    - intros i i' Hi Hi' Hne. destruct (KROWS i Hi) as (X1 & X2 & _ & _ & _ & X6 & _). destruct (KROWS i' Hi') as (Y1 & Y2 & _ & _ & _ & Y6 & _).
      destruct (live_apart C A1 m2 _ (Z_to_bv 64 (rows i)) (Z_to_bv 64 (rows i')) (4 * 41) (4 * 41) CK W2 X6 Y6
                  (zbv_ne (rows i) (rows i') ltac:(lia) ltac:(lia) (KDIST i i' Hi Hi' Hne)) ltac:(lia) ltac:(lia)) as [X | X];
        rewrite !u_Z2bv in X by lia; lia. }
  eapply rz_msteps; [exact MH2 | exact ML2 | exact M3 |].
  apply (kg_rows 41%nat 0 fr2 fr2 cs2 R3 R3 m3 C A A1 md vm1 s m ret regs fr kel arr rows S CK Hsc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
           GGi Hz2 W3 PMm3 CF3 GI3 ltac:(intros i j Hi; exfalso; lia)
           ltac:(kgk AG3; rewrite (cs_kept_get _ _ 2%bv CK2) by (left; reflexivity); exact S1) G319 (regs_agree_refl _ _)
           ltac:(kgk AG3; rewrite (cs_kept_get _ _ 8%bv CK2) by (right; right; right; left; reflexivity); exact G18)
           ltac:(kgk AG3; rewrite (cs_kept_get _ _ 9%bv CK2) by (right; right; right; right; left; reflexivity); exact G19)
           G318
           ltac:(kgk AG3; rewrite (cs_kept_get _ _ 21%bv CK2) by (right; right; right; right; right; vm_compute; split; discriminate); exact G121)
           G322 G323
           ltac:(rewrite FO2 by (intro E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate); exact F18) F29 (fun x _ => eq_refl)).
  intros frL csL ML1 rL WL PML CFL GIL GVL HzL FSL SL2 AGL.
  destruct (kg_E al_rom fr frL csL rL regs ML1 s kel ret ltac:(lia) ltac:(lia) Hret CFL SL2 ltac:(kgk AGL; exact G318))
    as (RE & ME & SE2 & SE1 & SE10 & KE & AGE).
  pose proof WL as [_ WPL _ _ _ _ _ _ _ _ _]. pose proof WPL as [MHL MLL _].
  eapply rz_msteps; [exact MHL | exact MLL | exact ME |].
  assert (K3 : getr RE 3%bv = getr regs 3%bv).
  { kgk AGE. kgk AGL. kgk AG3. rewrite (cs_kept_get _ _ 3%bv CK2) by (right; left; reflexivity). kgk AG1. reflexivity. }
  assert (K4 : getr RE 4%bv = getr regs 4%bv).
  { kgk AGE. kgk AGL. kgk AG3. rewrite (cs_kept_get _ _ 4%bv CK2) by (right; right; left; reflexivity). kgk AG1. reflexivity. }
  assert (K26 : getr RE 26%bv = getr regs 26%bv).
  { kgk AGE. kgk AGL. kgk AG3. rewrite (cs_kept_get _ _ 26%bv CK2) by (right; right; right; right; right; vm_compute; split; discriminate). kgk AG1. reflexivity. }
  assert (K27 : getr RE 27%bv = getr regs 27%bv).
  { kgk AGE. kgk AGL. kgk AG3. rewrite (cs_kept_get _ _ 27%bv CK2) by (right; right; right; right; right; vm_compute; split; discriminate). kgk AG1. reflexivity. }
  assert (CKF : cs_kept regs RE).
  { apply cs_kept_intro; [rewrite SE2, H2; reflexivity | exact K3 | exact K4 | | | | | | | | | | | exact K26 | exact K27]; apply KE; kgin. }
  assert (FSF : forall r : reg, In (u r) fs_list -> reg_get (bvmap_set 9 (reg_get fr 9) (bvmap_set 8 (reg_get fr 8) frL)) r = reg_get fr r).
  { intros r Hr. destruct (kgw_fs_not r Hr) as (N14 & N15).
    destruct (Z.eq_dec (u r) 9) as [E9 | N9].
    { assert (r = 9%bv) as -> by (apply bv_eq; rewrite E9; reflexivity). apply fpv_get_same. }
    rewrite fpv_get_other by (intro E; subst r; apply N9; reflexivity).
    destruct (Z.eq_dec (u r) 8) as [E8 | N8].
    { assert (r = 8%bv) as -> by (apply bv_eq; rewrite E8; reflexivity). apply fpv_get_same. }
    rewrite fpv_get_other by (intro E; subst r; apply N8; reflexivity).
    rewrite (FSL r Hr), (FO2 r ltac:(intro E; subst r; apply N9; reflexivity) N14 N15).
    exact (FO1 r ltac:(intro E; subst r; apply N8; reflexivity) ltac:(intro E; subst r; apply N9; reflexivity)). }
  apply (POST _ csL A1 ML1 vm1 RE WL HzL CKF PML).
  - exists kel, arr, rows. destruct GIL as (L1 & L2 & L3 & L4 & L5).
    refine (conj SE10 (conj (kgw_kern_mem C A A1 m2 ML1 kel arr 41 41 rows KN L1 L2 L3 L4) (conj L5 _))).
    exists kgw_cell. exact (conj (kgw_kvals ML1 rows GVL) kgw_centre).
  - exact FSF.
  - exact AR1.
Qed.

End KgauW.
