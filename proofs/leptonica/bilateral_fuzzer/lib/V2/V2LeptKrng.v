(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap2 V2LeptExpf V2LeptKernCreateS V2LeptKernCreateS1 V2LeptKernDestroyS V2LeptKernLeaf
  V2LeptKrngSegs V2LeptBl3_iface V2LeptKvals V2LeptKobjLib V2LeptUb V2LeptKgau.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomK LeptRoomBL LeptRop2Arith LeptRgbLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KrngW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition krw_cell (i j : Z) : Z := ExpfModelB.bil_cell ExpfTablesB.DEN_RANGE1 j.

Ltac krk AG := apply (kgw_ag_keep _ _ _ _ _ AG); [vm_compute; reflexivity |].
Ltac krin := cbn [In]; repeat first [left; reflexivity | right].
Ltac krlen := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac krwsw CK := repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | krlen]).
Ltac krn := rewrite ?u_Z2bv by lia; try change (Z.of_nat 1024) with 1024%Z; try change (Z.of_nat 16) with 16%Z;
  try change (Z.of_nat 8) with 8%Z; try change (Z.of_nat 4) with 4%Z; lia.
Ltac krcs := first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
                   | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
                   | right; right; right; right; right; vm_compute; split; discriminate ].
Ltac krch AGE AGL AG5 CK4 AG3 CK2 AG1 :=
  krk AGE; krk AGL; krk AG5; rewrite (cs_kept_get _ _ _ CK4) by krcs; krk AG3; rewrite (cs_kept_get _ _ _ CK2) by krcs; krk AG1; reflexivity.

Lemma krw_kvals : forall m row (rows : Z -> Z), rows 0%Z = row ->
  (forall jj, (0 <= jj < 256)%Z -> rdn SEGS m (Z_to_bv 64 (row + 4 * jj)) 4 = Some (Z_to_le_bytes 4 (ExpfModelB.bil_cell ExpfTablesB.DEN_RANGE1 jj))) ->
  kvals m 1 256 rows krw_cell.
Proof.
  intros m row rows E V i j Hi Hj. assert (i = 0%Z) as -> by lia. rewrite E. unfold krw_cell.
  split; [exact (V j Hj) | apply ExpfTablesB.bil_range1_FB; exact Hj].
Qed.

Lemma krw_centre : krw_cell 0 0 = FpReal.p_one_s.
Proof. unfold krw_cell. exact ExpfTablesB.bil_range1_centre. Qed.

Lemma krw_out : forall (m m' : word -> option byte) (lo hi a : Z) (n : nat), (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z -> (a + Z.of_nat n <= lo \/ hi <= a)%Z ->
  rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros m m' lo hi a n OUT Ha Han D. apply rdn_ext.
  - rewrite u_Z2bv by lia. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT. lia.
Qed.

Lemma krw_rinv : forall (M M' : word -> option byte) (s row a : Z) (n : nat), rinv (R_Kr s row) M M' ->
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> (a + Z.of_nat n <= row \/ row + 1024 <= a)%Z -> (a + Z.of_nat n <= s - 64 \/ s - 48 <= a)%Z ->
  rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n.
Proof.
  intros M M' s row a n RI Ha Han D1 D2. apply (rinv_rdn SEGS _ M M' a n RI Ha Han).
  intros r Hr. unfold R_Kr in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd]; lia.
Qed.

Theorem makeRangeKernel_W : makeRangeKernel_contract.
Proof.
  intros fr cs C A m md regs s ret S CK HW Hz H2 Hs16 Hstk Hsc H1 Hret H4 Hfa0 kR bR AR HkR HbR POST.
  replace (Z_to_bv 64 PC_makeRangeKernel) with (0x3b5c4 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS. unfold KER_STACK, LSF in Hstk.
  assert (IMG : (0 <= alloc_top (c_vm C))%Z) by (pose proof Cimg as X; cbn in X; lia).
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (GTOP : (alloc_top (c_vm C) + 8192 <= s - 64)%Z) by lia.
  pose proof HW as [WI WP _ _ _ _ _ _ _ _ _]. pose proof WP as [MH MLo _].
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  destruct (kr_A al_rom fr cs regs m s ret ltac:(lia) ltac:(lia) SOKf H2 H1 Hfa0)
    as (fr1 & cs1 & R1 & M1 & FZ1 & FO1 & F18 & S1 & G1a & G110 & G111 & G118 & AG1).
  set (m1 := FRR m s ret regs fr) in *.
  assert (W1 : W C A m1 md) by (unfold m1, FRR; krwsw CK; exact HW).
  assert (PM1 : POSTM C A s m m1).
  { apply (POSTM_range C A m md m1 (s - 40) s s CK HW); [ | lia | lia | lia].
    intros a Ha. unfold m1. apply FRR_out; lia. }
  assert (CF1 : cellsZ m1 (framer s ret regs fr)) by (unfold m1; apply framer_init; lia).
  eapply rz_msteps; [exact MH | exact MLo | exact M1 |].
  apply (kernelCreate_S1_W (fx := mkFP fr1 cs1) C A m1 md R1 (s - 48)%Z 256 1 (Z_to_bv 64 0x3b5fc) S kR bR CK W1 S1
           ltac:(rewrite Zminus_mod, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) G1a ltac:(red; apply bv_eq; reflexivity)
           ltac:(krk AG1; exact H4) G110 G111 ltac:(lia) ltac:(lia) ltac:(lia) AR HkR HbR).
  intros A1 m2 vm1 R2 W2 CK2 PM2 (kel & arr & rows & G2k & KN) AR1.
  replace (Z_to_bv 64 0x3b5fc) with (0x3b5fc : word) by (apply bv_eq; reflexivity).
  pose proof KN as (Kk1 & Kk2 & Kk16 & LA1k & LAk & L0k & Rh & Rw & Ra & Ka1 & Ka2 & Ka16 & Kne & LA1a & LAa & L0a & KROWS & KDIST & KFR).
  pose proof W2 as [_ WP2 _ _ _ _ _ _ _ _ _]. pose proof WP2 as [MH2 ML2 _].
  assert (SLA : sub_live A A1) by (exact (kern_sub_live _ _ _ _ _ _ _ _ _ KN)).
  destruct (KROWS 0%Z ltac:(lia)) as (Kr1 & Kr2 & Kr16 & Kra & Krk & LA1r & LAr & L0r & Rr).
  replace (arr + 8 * 0)%Z with arr in Rr by lia.
  set (row := rows 0%Z) in *.
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 kel) 24 CK W2 LA1k ltac:(lia)) as BRk. rewrite u_Z2bv in BRk by lia.
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 arr) (8 * 1) CK W2 LA1a ltac:(lia)) as BRa. rewrite u_Z2bv in BRa by lia.
  pose proof (blk_range C A1 m2 _ (Z_to_bv 64 row) (4 * 256) CK W2 LA1r ltac:(lia)) as BRr. rewrite u_Z2bv in BRr by lia.
  assert (DKA : (arr + 8 <= kel \/ kel + 24 <= arr)%Z).
  { destruct (live_apart C A1 m2 _ (Z_to_bv 64 arr) (Z_to_bv 64 kel) (8 * 1) 24 CK W2 LA1a LA1k
                (zbv_ne arr kel ltac:(lia) ltac:(lia) (fun E => Kne (eq_sym E))) ltac:(lia) ltac:(lia)) as [X | X];
      rewrite !u_Z2bv in X by lia; lia. }
  assert (DRK : (row + 1024 <= kel \/ kel + 24 <= row)%Z).
  { destruct (live_apart C A1 m2 _ (Z_to_bv 64 row) (Z_to_bv 64 kel) (4 * 256) 24 CK W2 LA1r LA1k
                (zbv_ne row kel ltac:(lia) ltac:(lia) Krk) ltac:(lia) ltac:(lia)) as [X | X];
      rewrite !u_Z2bv in X by lia; lia. }
  assert (DRA : (row + 1024 <= arr \/ arr + 8 <= row)%Z).
  { destruct (live_apart C A1 m2 _ (Z_to_bv 64 row) (Z_to_bv 64 arr) (4 * 256) (8 * 1) CK W2 LA1r LA1a
                (zbv_ne row arr ltac:(lia) ltac:(lia) Kra) ltac:(lia) ltac:(lia)) as [X | X];
      rewrite !u_Z2bv in X by lia; lia. }
  destruct (kr_B al_rom fr1 cs1 R2 m2 kel ltac:(lia) (FZ1 Hz) G2k F18)
    as (fr2 & cs2 & R3 & M3 & Hz2 & FO2 & F28 & G38 & G310 & G311 & G312 & G31 & AG3).
  eapply rz_msteps; [exact MH2 | exact ML2 | exact M3 |].
  replace (0x38a54 : word) with (Z_to_bv 64 PC_kernelSetOrigin) by (apply bv_eq; reflexivity).
  apply (kernelSetOrigin_W (mkFP fr2 cs2) C A A1 m2 (with_vmmaps vm1 md) R3 (s - 48) kel 0 0 (Z_to_bv 64 0x3b620) S CK W2 SLA
           ltac:(krk AG3; rewrite (cs_kept_get _ _ _ CK2) by krcs; exact S1) ltac:(lia) ltac:(lia)
           G31 ltac:(red; apply bv_eq; reflexivity) G310 G311 G312 ltac:(lia) ltac:(lia) ltac:(lia) LA1k LAk L0k).
  intros m3 R4 W3 CK4 PM3 OUT3 Ry Rx G410.
  replace (Z_to_bv 64 0x3b620) with (0x3b620 : word) by (apply bv_eq; reflexivity).
  destruct (kr_C al_rom (mkFP fr2 cs2) R4 m3) as (R5 & M5 & G59 & AG5).
  pose proof W3 as [_ WP3 _ _ _ _ _ _ _ _ _]. pose proof WP3 as [MH3 ML3 _].
  eapply rz_msteps; [exact MH3 | exact ML3 | exact M5 |].
  assert (SOKr : store_ok SEGS m3 (Z_to_bv 64 row) 1024 = true).
  { apply (kgw_sok_blk C A1 m3 (with_vmmaps vm1 md) (Z_to_bv 64 row) (4 * 256)); [exact CK | exact W3 | exact LA1r | krn | krn | krn]. }
  assert (SOKs : store_ok SEGS m3 (Z_to_bv 64 (s - 64)) 16 = true).
  { apply (W_sok_win C A1 m3 (with_vmmaps vm1 md)); [exact CK | exact W3 | lia | cbn; lia]. }
  assert (Ch3 : rdn SEGS m3 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
  { rewrite (krw_out m2 m3 (kel + 8) (kel + 16) kel 4 OUT3) by krn. exact Rh. }
  assert (Cw3 : rdn SEGS m3 (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 256))).
  { rewrite (krw_out m2 m3 (kel + 8) (kel + 16) (kel + 4) 4 OUT3) by krn. exact Rw. }
  assert (Ca3 : rdn SEGS m3 (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr))).
  { rewrite (krw_out m2 m3 (kel + 8) (kel + 16) (kel + 16) 8 OUT3) by krn. exact Ra. }
  assert (Cr3 : rdn SEGS m3 (Z_to_bv 64 arr) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 row))).
  { rewrite (krw_out m2 m3 (kel + 8) (kel + 16) arr 8 OUT3) by krn. exact Rr. }
  eapply rz_reach; [exact WP3 | |].
  { apply (kr_loop al_rom s kel arr row m3 ltac:(repeat split; lia)
             ltac:(split; [apply al16_mod8; exact Kk16 | split; [apply al16_mod8; exact Ka16 | apply al16_mod4; exact Kr16]])
             SOKr SOKs Ch3 Cw3 Ca3 Cr3
             ltac:(intros j Hj; apply (W_ro C A1 m3 (with_vmmaps vm1 md) (Z_to_bv 64 j) W3); unfold inZ; rewrite u_Z2bv by lia; cbn; lia)
             ltac:(intros j Hj; apply (W_ro C A1 m3 (with_vmmaps vm1 md) (Z_to_bv 64 j) W3); unfold inZ; rewrite u_Z2bv by lia; cbn; lia)
             256%nat fr2 R5 fr2 cs2 R5 m3 0 ltac:(reflexivity) ltac:(lia) Hz2 (rinv_refl _ _)
             ltac:(krk AG5; rewrite (cs_kept_get _ _ _ CK4) by krcs; krk AG3; rewrite (cs_kept_get _ _ _ CK2) by krcs; exact S1)
             G59
             ltac:(krk AG5; rewrite (cs_kept_get _ _ _ CK4) by krcs; exact G38)
             ltac:(krk AG5; rewrite (cs_kept_get _ _ _ CK4) by krcs; krk AG3; rewrite (cs_kept_get _ _ _ CK2) by krcs; exact G118)
             F28 (regs_agree_refl _ _) (fun x _ => eq_refl)). }
  intros fin (frL & csL & RL & ML & -> & HzL & RIL & _ & SL2 & SL8 & AGL & FSL & VAL).
  assert (LR : local_regions C A1 A (s - 48) (R_Kr s row)).
  { unfold local_regions, R_Kr. constructor.
    - right. exists (Z_to_bv 64 row), 1024%Z. rewrite u_Z2bv by lia. cbn [fst snd]. repeat split; try assumption; lia.
    - constructor; [left; cbn [fst snd]; lia | constructor]. }
  destruct (rinv_WP2 C A A1 m3 (with_vmmaps vm1 md) ML (R_Kr s row) (s - 48) CK W3 SLA ltac:(lia) RIL LR) as (WL & PMr).
  assert (PML : POSTM C A s m ML).
  { eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [apply (POSTM_mono C A (s - 48) s); [lia | exact PM2] |].
    eapply POSTM_trans; [apply (POSTM_mono C A (s - 48) s); [lia | exact PM3] |].
    apply (POSTM_mono C A (s - 48) s); [lia | exact PMr]. }
  assert (CFL : cellsZ ML (framer s ret regs fr)).
  { apply (cellsZ_frm C (s - 48) m1 ML); [exact CK | | lia | | exact CF1].
    - exact (FRM_trans _ _ _ _ _ (FRM_trans _ _ _ _ _ (proj1 PM2) (proj1 PM3)) (proj1 PMr)).
    - eapply Forall_impl; [| apply framer_bounds; lia]. intros av Hav. cbn beta in Hav |- *. lia. }
  destruct (kr_E al_rom fr frL csL RL regs ML s kel ret ltac:(lia) ltac:(lia) Hret CFL SL2 SL8)
    as (RE & ME & SE2 & SE1 & SE10 & KE & AGE).
  pose proof WL as [_ WPL _ _ _ _ _ _ _ _ _]. pose proof WPL as [MHL MLL _].
  eapply rz_msteps; [exact MHL | exact MLL | exact ME |].
  assert (CKF : cs_kept regs RE).
  { apply cs_kept_intro; [rewrite SE2, H2; reflexivity | | | apply KE; krin | apply KE; krin | apply KE; krin | | | | | | | | | ];
      krch AGE AGL AG5 CK4 AG3 CK2 AG1. }
  assert (FSF : forall r : reg, In (u r) fs_list -> reg_get (bvmap_set 8 (reg_get fr 8) frL) r = reg_get fr r).
  { intros r Hr. destruct (kgw_fs_not r Hr) as (N14 & N15).
    destruct (Z.eq_dec (u r) 8) as [E8 | N8].
    { assert (r = 8%bv) as -> by (apply bv_eq; rewrite E8; reflexivity). apply fpv_get_same. }
    rewrite fpv_get_other by (intro E; subst r; apply N8; reflexivity).
    rewrite (FSL r Hr), (FO2 r ltac:(intro E; subst r; apply N8; reflexivity) N14 N15).
    exact (FO1 r ltac:(intro E; subst r; apply N8; reflexivity) N15). }
  apply (POST _ csL A1 ML vm1 RE WL HzL CKF PML).
  - exists kel, arr, rows. split; [exact SE10 |]. split.
    + apply (kgw_kern_mem C A A1 m2 ML kel arr 1 256 rows KN).
      * rewrite (krw_rinv m3 ML s row kel 4 RIL) by krn. exact Ch3.
      * rewrite (krw_rinv m3 ML s row (kel + 4) 4 RIL) by krn. exact Cw3.
      * rewrite (krw_rinv m3 ML s row (kel + 16) 8 RIL) by krn. exact Ca3.
      * intros i Hi. assert (i = 0%Z) as -> by lia. replace (arr + 8 * 0)%Z with arr by lia.
        rewrite (krw_rinv m3 ML s row arr 8 RIL) by krn. exact Cr3.
    + split.
      * unfold korg. split.
        -- rewrite (krw_rinv m3 ML s row (kel + 8) 4 RIL) by krn. rewrite Ry, w2b4_Z by lia. reflexivity.
        -- rewrite (krw_rinv m3 ML s row (kel + 12) 4 RIL) by krn. rewrite Rx, w2b4_Z by lia. reflexivity.
      * exists krw_cell. split; [| exact krw_centre].
        apply (krw_kvals ML row rows eq_refl). intros jj Hjj. exact (VAL jj ltac:(lia)).
  - exact FSF.
  - exact AR1.
Qed.

End KrngW.
