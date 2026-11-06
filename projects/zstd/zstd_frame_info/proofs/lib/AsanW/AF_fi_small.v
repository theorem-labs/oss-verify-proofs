(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem Mem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_chk3.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
(* [comment removed for export] *)
Ltac gfact CK := let C := fresh in destruct CK as [C|C]; [left; exact C| right; lia].

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition FHTAB : list Z := [0;0;0;0;0;0;0;0; 1;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0;
                              0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0;
                              0;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0; 8;0;0;0;0;0;0;0]%Z.
#[using="Type"] Lemma fhtab_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AFI_DIDTAB (map (Z_to_bv 8) FHTAB).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AFI_DIDTAB. Local Ltac2 Set LiaHints.tbl := fun () => "0020=1121359246.3 36321585685.3000001002SS".
lia. } { cbn. unfold AFI_DIDTAB. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fhtab_read : forall m k, mem_inv asegs m -> 0 <= k < 12 ->
  ov_read_bytes asegs m (wa (AFI_DIDTAB + 8 * k)) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTAB))).
Proof.
  intros m k MI Hk.
  rewrite (bytes_at_read asegs m AFI_DIDTAB (map (Z_to_bv 8) FHTAB) (8 * k) 8 (fhtab_bytes m MI)); [| lia| cbn; lia].
  f_equal. rewrite <- List.firstn_map, <- List.skipn_map. reflexivity.
Qed.
#[using="Type"] Lemma zrange_all : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, 0 <= c < Z.of_nat n -> P c = true.
Proof.
  intros P n H c Hc. apply (proj1 (forallb_forall _ _) H). apply in_map_iff. exists (Z.to_nat c). Local Ltac2 Set LiaHints.tbl := fun () => "0020=25492742081.629765743970.6000004008S2HcS2Hc".
split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shr6_cases : forall c, 0 <= c < 256 -> 0 <= Z.shiftr c 6 <= 3.
Proof. intros c Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0020=29535697342.363967162203.3000004005S2HcS".
rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma tabsh_eq1 : forall k, 0 <= k <= 3 ->
  Z.shiftr (Z.land (134464 + Z.shiftl k 3) 18446744073709551615) 3 + 2147450880 = 2147467688 + k.
Proof.
  intros k Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0040=29784460291.335497642355.351882110075.356337469475.3000001002003007SSSS2Hk".
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma tabsh_eq2 : forall j, 0 <= j <= 3 ->
  Z.shiftr (Z.land (134528 + Z.shiftl j 3) 18446744073709551615) 3 + 2147450880 = 2147467696 + j.
Proof.
  intros j Hj. Local Ltac2 Set LiaHints.tbl := fun () => "0040=11561786841.329784461188.335497642740.39066961828.3 000001002003007SSSS2Hj".
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
(* [comment removed for export] *)
Hypothesis GCI : In (0x20d40, 0x20dc0)%Z CI.

(* [comment removed for export] *)
Definition leafA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) (a1' a2' a3' a4' a5' : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo SPV
    /\ magree asegs (aclient_addr CI LB SPV) m m'
    /\ AHEAP AI L RNG st LB m'.

Definition leafA_stmt (pc : Z) (minlen : Z) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  gshA m ->
  stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - 16 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv asegs m ->
  rng RNG lo (SPV - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
  evtF asegs RNG (leafA_post L RNG ra SPV gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc st LB lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Definition isframeA_stmt : Prop := leafA_stmt AFI_ISFRAME 4.
Definition fhsizeA_stmt : Prop := leafA_stmt AFI_FHSIZE 5.

(* [comment removed for export] *)
#[using="Type"] Lemma leaf_closeA : forall L RNG st LB SPV lo m m',
  AHEAP AI L RNG st LB m -> (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP + 4096 <= lo -> lo <= SPV - 16 -> SPV + 16 < al_top L ->
  munch [(SPV - 16, SPV)] m m' -> wmono asegs m m' ->
  magree asegs (aclient_addr CI LB SPV) m m' /\ AHEAP AI L RNG st LB m'.
Proof.
  intros L RNG st LB SPV lo m m' AH LBH BOT LO SPT MU WM.
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0. pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  split.
  - eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. Local Ltac2 Set LiaHints.tbl := fun () => "0020>24592922879.2736090134378.3000000L00`S3BOT2LO3SPT3ATR3LY13LY33LY4S3BOT2LO3ATR3LY13LY4".
exact (stack_not_client CI LB SPV (SPV - 16) a HCI HCI0 LBH ltac:(lia) Hr Ha).
  - eapply (AI_frame AI); [exact AH| exact MU| exact WM|]. constructor; [| constructor]. left; left. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem isframeA : isframeA_stmt.
Proof.
  unfold isframeA_stmt, leafA_stmt, AFI_ISFRAME.
  intros until lo. intros AH LBH BUF NB HC GS ST BOT LO SPT SP16 MI RSTK RI RIS -> ->.
  pose proof atop_range as ATR. pose proof (buf_atA_bound _ _ _ BUF) as BB. pose proof (proj2 BUF) as PLR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC. destruct RTC as (_ & GOT & _ & _ & SHB & _).
  pose proof (munch_refl [(SPV - 16, SPV)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01:0?10644847640.10410644847646.10110995101159.99 11003117282.10711091121410.74 11091121410.76 11093218566.12112108886724.88 14202172478.10614204193981.10214722623428.66 14937404945.12114937404951.12314937404951.12414948324753.10916077671799.70 16166233773.94 16790439781.99 17072957965.10917075049779.70 18599469035.75 2027029998.75  21921679679.10021922154557.105246216824.89   26187303326.12326842599285.12128465183341.10228913119921.12228913119927.12328913119927.12428922925361.10929786660475.84 29792256216.10229792256217.10629792256221.11129794353371.12329794353373.1212979471401.108 2979471401.69  29932669512.12130982594487.75 32241090838.70 32377744366.75 35128789679.90 35497698861.1093970684375.111 43895326353.12243895326353.75 43895326353.77 43978883656.95 44429395365.11145054632369.12245221239098.75 46544363475.12147378304819.12348153790514.95 49418115928.68 50507204723.90 51625734065.12352709134728.11154111686574.12356311178883.12356570282913.12359311024115.72 61448148287.10761450317119.10364297306694.10264305420614.94 64405586220.10664405586221.1027067733018.75  7886379226.106 7886379227.102 00000700>00[01801<01@01H01\01c01j01n01o02002102202602=02D02L02P02Q02]02d02k03C03]03^03c03h03m04204704804=04B04G04L04Q04V04W05105205505A05F05K05L05Q05R05S05X05Y05^05b05c05d05k05l06306406N06h06i06j07007707>07[08808`09H09L09M09NS1K3R1bS1K3R1bS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS2LOS2LOS2LO3R1bS3Bk23BOT2LO3ATR3R1cS1K3R1bS1K3R1bS2LOFFFFS2NBS3R1b1HS3R1b1HS2LO3R1bS2LOSS3BOT2LO3ATRS1K3R1bS1K3R1bS3Bk23BOT2LO3ATR3R1b3R1cS3Bk13Bk23BOT2LO3ATR1K3R1bFS3R1bS3R1bS3R1bS3R1bS3R1bSS3R1bS3R1bS3R1bS3R1bS3R1bS3R1bSS3Bk13Bk23BOT2LO3ATR1K3R1bSS1KS3BOT2LO3ATRS3R1bS3R1bFS3R1bSSS3R1bFS3R1bS2HBFFS1K3R1bSS1K3R1bFS3Bk13Bk23BOT2LO3ATR1K3R1bS3Bk13Bk23BOT2LO3ATR1K3R1bFFS2Z01KS1K3R1bS1K3R1bS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk13Bk23BOT2LO4SP163ATR2BB1K2HN2R43R1bS3Bk13Bk23BOT2LO4SP163ATR2BB1K2HN2R43R1bS2HBFF".
carve_frame 16%nat ST.
  zstep. zstep.                                   (* [comment removed for export] *)
  zstep.                                          (* [comment removed for export] *)
  zstep. bcase K.                                 (* [comment removed for export] *)
  - (* [comment removed for export] *)
    assert (NZ : 0 < zlen bl) by lia.
    pose proof (hcoverA_unpoisoned AI L RNG st LB m S (zlen bl) AH HC NZ) as UNP.
    destruct HC as [Z0|(p & BA & BN & Hbk & Bk1 & Bk2)]; [exfalso; lia|].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hbk) as (HN & (R1 & R2 & R3 & R4) & RGA & RGS & _).
    unfold shlen in RGS. rewrite Z.shiftr_div_pow2 in RGS by lia. change (2^3) with 8 in RGS.
    pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
    lazymatch goal with H : munch _ m ?m1 |- _ => rename H into MU1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (UNP1 : unpoisoned m1 S (S + zlen bl)) by
        (eapply unpoisoned_munch; [exact UNP| exact MU1|]; rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from]; split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| exact I]);
      assert (PL1 : bytes_at asegs m1 S (map (Z_to_bv 8) bl)) by
        (refine (proj1 (buf_atA_frame m m1 S bl _ BUF MU1 _)); cbn [disjoint_from]; split; [lia| exact I])
    end.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) S UNP1 ltac:(lia) ltac:(lia)) as (b0 & RD0 & CK0 & SR0).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_7fee0; [gfact CK0| exact SR0| lia| assumption|]. intros y1.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) (S + 3) UNP1 ltac:(lia) ltac:(lia)) as (b3 & RD3 & CK3 & SR3).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_7fef4; [gfact CK3| exact SR3| lia| assumption|]. intros y2.
    (* [comment removed for export] *)
    lazymatch type of PL1 with bytes_at _ ?m1 _ _ =>
      pose proof (buf_readA m1 S bl 1 (conj PL1 PLR) ltac:(lia)) as RB1;
      pose proof (buf_readA m1 S bl 0 (conj PL1 PLR) ltac:(lia)) as RB0; replace (wa (S + 0)) with (wa S) in RB0 by (unfold wa; f_equal; lia);
      pose proof (buf_readA m1 S bl 2 (conj PL1 PLR) ltac:(lia)) as RB2;
      pose proof (buf_readA m1 S bl 3 (conj PL1 PLR) ltac:(lia)) as RB3;
      destruct (buf_nthA m1 S bl 0 (conj PL1 PLR) ltac:(lia)) as [_ V0]; destruct (buf_nthA m1 S bl 1 (conj PL1 PLR) ltac:(lia)) as [_ V1];
      destruct (buf_nthA m1 S bl 2 (conj PL1 PLR) ltac:(lia)) as [_ V2]; destruct (buf_nthA m1 S bl 3 (conj PL1 PLR) ltac:(lia)) as [_ V3]
    end.
    do 4 zstep.                                   (* [comment removed for export] *)
    do 8 zstep.                                   (* [comment removed for export] *)
    zstep. bcase K1.
    + (* [comment removed for export] *)
      do 4 zstep.                                 (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
      lazymatch goal with M : munch _ m ?mf, W : wmono asegs m ?mf, MI9 : mem_inv asegs ?mf, ST9 : stk asegs ?mf lo _ |- _ =>
        destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
        apply evtF_done; unfold leafA_post; do 6 eexists; exists mf;
        split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
    + (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
      lazymatch goal with M : munch _ m ?mf, W : wmono asegs m ?mf, MI9 : mem_inv asegs ?mf, ST9 : stk asegs ?mf lo _ |- _ =>
        destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
        apply evtF_done; unfold leafA_post; do 6 eexists; exists mf;
        split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
  - (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    lazymatch goal with M : munch _ m ?mf, W : wmono asegs m ?mf, MI9 : mem_inv asegs ?mf, ST9 : stk asegs ?mf lo _ |- _ =>
      destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
      apply evtF_done; unfold leafA_post; do 6 eexists; exists mf;
      split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gshA_rd0 : forall m a, gshA m -> (0x7fffc1a8 <= a < 0x7fffc1ac \/ 0x7fffc1b0 <= a < 0x7fffc1b4) ->
  ov_read_bytes asegs m (wa a) 1 = Some [Z_to_bv 8 0].
Proof. intros m a G Ha. apply ov_read1_of_byte; [lia| lia|]. apply gshA_zero; [exact G| exact Ha]. Qed.

#[using="Type"] Theorem fhsizeA : fhsizeA_stmt.
Proof.
  unfold fhsizeA_stmt, leafA_stmt, AFI_FHSIZE.
  intros until lo. intros AH LBH BUF NB HC GS ST BOT LO SPT SP16 MI RSTK RI RIS -> ->.
  pose proof atop_range as ATR. pose proof (buf_atA_bound _ _ _ BUF) as BB. pose proof (proj2 BUF) as PLR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC. destruct RTC as (_ & GOT & _ & _ & SHB & _).
  pose proof (munch_refl [(SPV - 16, SPV)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01R0?11091121408.78 11091121410.74 11093218565.12311123667595.12211447730086.16212108886724.88 12152703750.10314722623428.66 16077671799.70 16800856201.10316806931334.96 17071248012.11017075049779.70 17363013250.11917516378361.10618599469035.75 2027029998.75  23626598166.12023633870206.10624283024576.11524350674608.12424350674610.12224350674615.125246216824.89   25125709391.11025390136860.11027478224098.92 29324322046.12229668508888.12229784416347.10629786643421.10929786659052.10829786659053.10729786660475.84 29792256214.11529792256215.11929792256217.10329792256217.11029792256220.10329794353374.1222979471401.109 2979471401.69  30982594487.75 32241090838.70 32377744366.75 34060037199.10738114971390.120387403923.115  39198604721.11541415761994.10041854394848.11943895326353.12443895326353.75 43895326353.79 45069577529.98 45071062462.97 45221239098.75 48056024553.12248873807278.11549418115928.68 51304911647.10251304927515.10453508216720.12453782341950.11054801773241.10355336861633.11155336861647.11155338958788.12455338958789.11955338958790.11655707291957.10956328625397.11357018324616.10357018324617.10557684357432.92 59308628433.1  59308628566.1  59311024115.72 59536694175.11961982324945.11963718803940.10763956215694.12263958312838.11563958312839.11963958312841.11063958312841.11164090604862.90 64405586220.10366490185364.10368246084393.10868246099992.10968632855797.96 7067733018.75  7672346518.122 7886379226.103 8573091283.102 9010595361.110 9074758901.115 00000400800@00A00B00V00W00[00_01<01Y01a01e01f01k01l02802902A02I02N02S02X03003803903@03E03N03S03X03]03b03c03h03m04204704<04A04F04G04H04K04W04\04]04^04_04d04e04j04k04l05305:05>05?05@05A05I05Q05V05W06106906A06I06Q06Y06^06_06d06i06n07207607<07=07F07N07S07X07]07b07g08708_08`09309F09M09Q09R09S09[09\09]S2LOS2LOS2LO3R1bFFS3Bk23BOT2LO3ATR3R1cFS2LOS2NBS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS2LO3R1bS2LOFS3R1bSS3BOT2LO3ATRFS3R1b2L3S3R1b2L6S3R1bS3R1bS3R1bS3Bk23BOT2LO3ATR3R1b3R1cS3R1b2L3FS1K3R1bS3R1bS3R1b3SB2S3R1bS3R1bS3R1bS3R1bSS3R1bS3R1bS3R1bS3R1bS3R1bS3R1bS3R1bSSS1KS3BOT2LO3ATRS3R1bFFFS3R1bFS3R1bSSS1K3R1bS1K3R1bS2HBFFSS3R1b2L3S3R1b2L6S3R1bFS3Bk13Bk23BOT2LO3ATR1K3R1bS3R1b2V4S3R1b2V4S3R1b2V4S3R1b2V4S3R1b2V4S3R1bFS3R1bS3R1bS3R1bS2K2S2K3S2Z01KFS3R1b3SB1S3R1b2L6S3R1bS3R1bS3R1bS3R1bS3R1bS3BOT2LO3ATR3R1bS3Bk13Bk23BOT2LO4SP163ATR2BB1K2HN2R43R1bFS3BOT2LO3ATR3R1b2L3S3BOT2LO3ATR3R1b2L6S3R1b1HS2HBFFS3R1b2V4FF".
carve_frame 16%nat ST.
  zstep. zstep.                                   (* [comment removed for export] *)
  zstep.                                          (* [comment removed for export] *)
  zstep. bcase K.                                 (* [comment removed for export] *)
  - (* [comment removed for export] *)
    assert (NZ : 0 < zlen bl) by lia.
    pose proof (hcoverA_unpoisoned AI L RNG st LB m S (zlen bl) AH HC NZ) as UNP.
    destruct HC as [Z0|(p & BA & BN & Hbk & Bk1 & Bk2)]; [exfalso; lia|].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hbk) as (HN & (R1 & R2 & R3 & R4) & RGA & RGS & _).
    unfold shlen in RGS. rewrite Z.shiftr_div_pow2 in RGS by lia. change (2^3) with 8 in RGS.
    pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
    lazymatch goal with H : munch _ m ?m1 |- _ => rename H into MU1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (UNP1 : unpoisoned m1 S (S + zlen bl)) by
        (eapply unpoisoned_munch; [exact UNP| exact MU1|]; rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from]; split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| exact I]);
      assert (PL1 : bytes_at asegs m1 S (map (Z_to_bv 8) bl)) by
        (refine (proj1 (buf_atA_frame m m1 S bl _ BUF MU1 _)); cbn [disjoint_from]; split; [lia| exact I]);
      assert (GS1 : gshA m1) by
        (unfold harness_invA, GSH_ADDR in *; eapply rw_cells_transport; [exact GS| exact MU1| eassumption| cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]]);
      assert (MI1 : mem_inv asegs m1) by assumption
    end.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) (S + 4) UNP1 ltac:(lia) ltac:(lia)) as (b4 & RD4 & CK4 & SR4).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_7ffbc; [gfact CK4| exact SR4| lia| assumption|]. intros y1.
    (* [comment removed for export] *)
    lazymatch type of PL1 with bytes_at _ ?m1 _ _ =>
      pose proof (buf_readA m1 S bl 4 (conj PL1 PLR) ltac:(lia)) as RB4; destruct (buf_nthA m1 S bl 4 (conj PL1 PLR) ltac:(lia)) as [_ V4] end.
    zstep.                                        (* [comment removed for export] *)
    cbv beta. rewrite (byte_litA _ V4).
    set (c := Znth 4 bl) in *.
    assert (L3 : 0 <= Z.land c 3 <= 3).
    { assert (E : Z.land c 3 = c mod 4) by exact (Z.land_ones c 2 ltac:(lia)). rewrite E. pose proof (Z.mod_pos_bound c 4). lia. }
    pose proof (shr6_cases c V4) as L6.
    zstep. zstep. zstep. zstep. zstep.            (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    rewrite (tabsh_eq1 (Z.land c 3) L3).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (gshA_rd0 m1 (2147467688 + Z.land c 3) GS1 ltac:(lia)) as RS1 end.
    zstep.                                        (* [comment removed for export] *)
    cbv beta. rewrite (byte_litA 0) by lia.
    zstep. bcase K2; [exfalso; clear - K2; lia|]. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.            (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    rewrite (tabsh_eq2 (Z.shiftr c 6) L6).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (gshA_rd0 m1 (2147467696 + Z.shiftr c 6) GS1 ltac:(lia)) as RS2 end.
    zstep.                                        (* [comment removed for export] *)
    cbv beta. rewrite (byte_litA 0) by lia.
    zstep. bcase K3; [exfalso; clear - K3; lia|]. (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (RDA : ov_read_bytes asegs m1 (wa (134464 + Z.shiftl (Z.land c 3) 3)) 8
                    = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * Z.land c 3)) FHTAB))))
        by (replace (134464 + Z.shiftl (Z.land c 3) 3) with (AFI_DIDTAB + 8 * Z.land c 3)
              by (unfold AFI_DIDTAB; rewrite Z.shiftl_mul_pow2 by lia; lia);
            apply fhtab_read; [exact MI1| lia]);
      assert (RDB : ov_read_bytes asegs m1 (wa (134528 + Z.shiftl (Z.shiftr c 6) 3)) 8
                    = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * (8 + Z.shiftr c 6))) FHTAB))))
        by (replace (134528 + Z.shiftl (Z.shiftr c 6) 3) with (AFI_DIDTAB + 8 * (8 + Z.shiftr c 6))
              by (unfold AFI_DIDTAB; rewrite Z.shiftl_mul_pow2 by lia; lia);
            apply fhtab_read; [exact MI1| lia])
    end.
    (* [comment removed for export] *)
    assert (SB1 : 0 <= Z.shiftl (Z.land c 3) 3 <= 24) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
    assert (SB2 : 0 <= Z.shiftl (Z.shiftr c 6) 3 <= 24) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
    zstep. zstep.                                 (* [comment removed for export] *)
    do 9 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    lazymatch goal with M : munch _ m ?mf, W : wmono asegs m ?mf, MI9 : mem_inv asegs ?mf, ST9 : stk asegs ?mf lo _ |- _ =>
      destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
      apply evtF_done; unfold leafA_post; do 6 eexists; exists mf;
      split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
  - (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    lazymatch goal with M : munch _ m ?mf, W : wmono asegs m ?mf, MI9 : mem_inv asegs ?mf, ST9 : stk asegs ?mf lo _ |- _ =>
      destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
      apply evtF_done; unfold leafA_post; do 6 eexists; exists mf;
      split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Stmts.
End CANSEC1.
