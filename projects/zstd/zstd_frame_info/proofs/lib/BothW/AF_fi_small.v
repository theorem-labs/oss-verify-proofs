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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_chk AF_fi_chk3.
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
Ltac brr := first [if_true | if_false].
(* [comment removed for export] *)
Ltac guard_false :=
  first [ brr
        | let G := fresh "G" in if_cases G; zify_cond G;
          [ exfalso; first [ lia | rewrite ?unsigned_lit in G by lia; lia | rewrite ?unsigned_lit_wrap in G; rewrite ?Z.mod_small in G by lia; lia ]
          | clear G ] ].
(* [comment removed for export] *)
Lemma lxor_m1S : forall x, Z.lxor x (-1) = - x - 1.
Proof.
  intros x. Local Ltac2 Set LiaHints.tbl := fun () => "0020=10351595562.357579945479.1000004005S2HiS".
replace (- x - 1) with (Z.lnot x) by (unfold Z.lnot; lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.lnot_spec, Z.bits_m1 by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac lnot_of X := try rewrite (zb_lxor_ones X) by lia; try rewrite (lxor_m1S X).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition FHTAB : list Z := [0;0;0;0;0;0;0;0; 1;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0;
                              0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0;
                              0;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0; 8;0;0;0;0;0;0;0]%Z.
#[using="Type"] Lemma fhtab_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m AFI_DIDTAB (map (Z_to_bv 8) FHTAB).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AFI_DIDTAB. Local Ltac2 Set LiaHints.tbl := fun () => "0020=1121359246.3 36321585685.3000001002SS".
lia. } { cbn. unfold AFI_DIDTAB. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fhtab_read : forall m k, mem_inv bsegs m -> 0 <= k < 12 ->
  ov_read_bytes bsegs m (wa (AFI_DIDTAB + 8 * k)) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTAB))).
Proof.
  intros m k MI Hk.
  rewrite (bytes_at_read bsegs m AFI_DIDTAB (map (Z_to_bv 8) FHTAB) (8 * k) 8 (fhtab_bytes m MI)); [| lia| cbn; lia].
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

(* [comment removed for export] *)
#[using="Type"] Lemma tabsh_eq1b : forall k, 0 <= k <= 3 -> Z.shiftr (134464 + Z.shiftl k 3) 3 + 2147450880 = 2147467688 + k.
Proof. intros k Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784460291.351882110075.3000001002SS".
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma tabsh_eq2b : forall j, 0 <= j <= 3 -> Z.shiftr (134528 + Z.shiftl j 3) 3 + 2147450880 = 2147467696 + j.
Proof. intros j Hj. Local Ltac2 Set LiaHints.tbl := fun () => "0020=11561786841.329784461188.3000001002SS".
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

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
  fun ms' => exists (r : Z) (a1' a2' a3' a4' a5' a6' : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ magree bsegs (aclient_addr CI LB SPV) m m'
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
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - 16 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m ->
  rng RNG lo (SPV - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
  evtF bsegs RNG (leafA_post L RNG ra SPV gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc st LB lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

Definition isframeA_stmt : Prop := leafA_stmt AFI_ISFRAME 4.
Definition fhsizeA_stmt : Prop := leafA_stmt AFI_FHSIZE 5.

(* [comment removed for export] *)
#[using="Type"] Lemma leaf_closeA : forall L RNG st LB SPV lo m m',
  AHEAP AI L RNG st LB m -> (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP + 4096 <= lo -> lo <= SPV - 16 -> SPV + 16 < al_top L ->
  munch [(SPV - 16, SPV)] m m' -> wmono bsegs m m' ->
  magree bsegs (aclient_addr CI LB SPV) m m' /\ AHEAP AI L RNG st LB m'.
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
  pose proof (munch_refl [(SPV - 16, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01>0?10644847640.10410644847646.10110995101159.99 11003117282.10711091121410.74 11091121410.76 11093218566.12112108886724.88 14159447534.75 14202172478.10614204193981.10214722623428.66 14937404945.12114937404951.12314937404951.12414948324753.10916077671799.70 16166233773.94 16790439781.99 17072957965.10917075049779.70 18599469035.75 21207494953.90 21921679679.10021922154557.105246216824.89   26187303326.12326842599285.12128465183341.10228913119921.12228913119927.12328913119927.12428922925361.10929786660475.84 29792256216.10229792256217.10629792256221.11129794353371.12329794353373.1212979471401.108 2979471401.69  29932669512.12130982594487.75 32241090838.70 35128789679.90 35497698861.1093970684375.111 40488864061.90 43895326353.12243895326353.75 43895326353.77 43978883656.95 44429395365.11145054632369.12245221239098.75 46544363475.12147378304819.12348153790514.95 49418115928.68 5012112366.75  50507204723.90 51625734065.12352709134728.11154111686574.12356311178883.12356570282913.12359311024115.72 59314988138.91 61448148287.10761450317119.10364297306694.10264301028607.91 64305420614.94 64405586220.10664405586221.1027067733018.75  7886379226.106 7886379227.102 00000700>00[01801<01@01H01\01h01o02602:02;02<02=02>02B02I02P02X02\02]02^02e02l03D03^03_03d03i03n04304804904>04C04H04M04R04W04X05205305605;05@05A05B05G05H05I05N05O05T05X05Y05Z05a05b05n06506606P06j06k06l07207L07S07Z08708T09109Y0:A0:E0:F0:GS1K3R1bS1K3R1bS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS2LOS2LOS2LO3R1bS3Bk23BOT2LO3ATR3R1cS3BOT2LO3ATRS1K3R1bS1K3R1bS2LOFFFFS2NBS3R1b1HS3R1b1HS2LO3R1bS2LOSFS1K3R1bS1K3R1bS3Bk23BOT2LO3ATR3R1b3R1cS3Bk13Bk23BOT2LO3ATR1K3R1bFS3R1bS3R1bS3R1bS3R1bS3R1bSS3R1bS3R1bS3R1bS3R1bS3R1bS3R1bSS3Bk13Bk23BOT2LO3ATR1K3R1bSS1KS3R1bS3R1bFFS3R1bSSS3R1bFS3R1bS2HBFFS1K3R1bSS3BOT2LO3ATRS1K3R1bFS3Bk13Bk23BOT2LO3ATR1K3R1bS3Bk13Bk23BOT2LO3ATR1K3R1bFFS2Z01KS3Bk13BOT2LO3ATR3R1a3R1b1GS1K3R1bS1K3R1bS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk13Bk23BOT2LO4SP163ATR2BB1K2HN2R43R1bS3Bk13Bk23BOT2LO4SP163ATR2BB1K2HN2R43R1bS2HBFF".
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
      assert (PL1 : bytes_at bsegs m1 S (map (Z_to_bv 8) bl)) by
        (refine (proj1 (buf_atA_frame m m1 S bl _ BUF MU1 _)); cbn [disjoint_from]; split; [lia| exact I])
    end.
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) S UNP1 ltac:(lia) ltac:(lia)) as (b0 & RD0 & CK0 & SR0).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_7fef0; [gfact CK0| exact SR0| lia| assumption|]. intros y1.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) (S + 3) UNP1 ltac:(lia) ltac:(lia)) as (b3 & RD3 & CK3 & SR3).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_7ff04; [gfact CK3| exact SR3| lia| assumption|]. intros y2.
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
      lazymatch goal with M : munch _ m ?mf, W : wmono bsegs m ?mf, MI9 : mem_inv bsegs ?mf, ST9 : stk bsegs ?mf lo _ |- _ =>
        destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
        apply evtF_done; unfold leafA_post; do 7 eexists; exists mf;
        split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
    + (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
      lazymatch goal with M : munch _ m ?mf, W : wmono bsegs m ?mf, MI9 : mem_inv bsegs ?mf, ST9 : stk bsegs ?mf lo _ |- _ =>
        destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
        apply evtF_done; unfold leafA_post; do 7 eexists; exists mf;
        split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
  - (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    lazymatch goal with M : munch _ m ?mf, W : wmono bsegs m ?mf, MI9 : mem_inv bsegs ?mf, ST9 : stk bsegs ?mf lo _ |- _ =>
      destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
      apply evtF_done; unfold leafA_post; do 7 eexists; exists mf;
      split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gshA_rd0 : forall m a, gshA m -> (0x7fffc1a8 <= a < 0x7fffc1ac \/ 0x7fffc1b0 <= a < 0x7fffc1b4) ->
  ov_read_bytes bsegs m (wa a) 1 = Some [Z_to_bv 8 0].
Proof. intros m a G Ha. apply ov_read1_of_byte; [lia| lia|]. apply gshA_zero; [exact G| exact Ha]. Qed.

#[using="Type"] Theorem fhsizeA : fhsizeA_stmt.
Proof.
  unfold fhsizeA_stmt, leafA_stmt, AFI_FHSIZE.
  intros until lo. intros AH LBH BUF NB HC GS ST BOT LO SPT SP16 MI RSTK RI RIS -> ->.
  pose proof atop_range as ATR. pose proof (buf_atA_bound _ _ _ BUF) as BB. pose proof (proj2 BUF) as PLR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC. destruct RTC as (_ & GOT & _ & _ & SHB & _).
  pose proof (munch_refl [(SPV - 16, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01Z0?11091121408.78 11091121410.74 11093218564.12411125764736.12111447730086.16112108886724.88 12152703750.10313721871836.92 14159447534.75 14722623428.66 16077671799.70 16800856201.10316802407995.93 16806931334.96 17071264188.11017075049779.70 17363013261.11817516378361.10818599469035.75 20324874701.10423626598166.11923633870206.10824283024591.11424350674608.12424350674609.123246216824.89   25125709391.11225390136860.11227478224098.92 29324322045.12329666411731.12129784416347.10829784531416.10229786643421.10329786659053.10929786660475.84 29792256213.12129792256216.11829792256217.10329792256217.11229792256217.11429792256220.1032979471401.109 2979471401.69  30982594487.75 31683733039.10432241090838.70 34060037199.10936395935771.10537530820045.10438114971390.119387403932.114  39198604734.11441415761994.10041854394863.11843895326353.12543895326353.75 43895326353.79 45069577529.98 45071062462.97 45221239098.75 48058121698.12148873807265.11449418115928.68 5012112366.75  51304927515.10651307161883.10453508216720.12453782341950.11254801773241.10355336861645.11555336861645.11955336861646.11455338958789.12355707291957.11156328625397.11557018324616.10557018324617.10757684357432.92 5782850095.104 59308628433.1  59308628566.1  59311024115.72 59314988138.10559314988138.93 59536694160.11861944093278.92 61982324958.11863718803940.10963958312837.12163958312838.11463958312840.11863958312841.11263958312841.11464090604862.90 64405586220.10366490185364.10368246099992.10368248609309.10268632855797.96 7067733018.75  7674443677.121 7886379226.103 8573091283.102 9010595361.112 9074758901.117 00000400800@00A00B00V00W00X00d00h00l01I01f02C02K02O02P02U02V02W02X02`02h02m03203J03R03S03Z03_03h03m04204704<04=04B04G04L04Q04V04[04`04a04b04c04f04k05805905:05;05<05A05B05G05H05I05P05W05[05\05]05^05j06206:06?06@06Z06b06j07207:07?07H07M07R07W07X07\07`07f08508O08P08Q08Z08b08g08l09109609;09K0:30:40:G0:Z0:a0:e0:f0:g0:o0;00;9S2LOS2LOS2LO3R1bFFS3Bk23BOT2LO3ATR3R1cFFS3BOT2LO3ATRS2LOS2NBS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS3Bk23BOT2LO3ATR2BB1K3R1b3R1cS2LO3R1bS2LOFS3R1bSFFS3R1b2L3S3R1b2L6S3R1bS3R1bS3Bk23BOT2LO3ATR3R1b3R1cS3R1b2L3FS1K3R1bS3R1bS3R1b3SB2S3R1bS3R1bS3R1bS3R1bSS3R1bS3R1bS3R1bS3R1bS3R1bS3R1bS3R1bSSFS1KS3R1bS3R1b3SB13SB2FFFFS3R1bFS3R1bSSS1K3R1bS1K3R1bS2HBFFSS3BOT2LO3ATRS3R1b2L6S3R1b2L3S3R1bFS3Bk13Bk23BOT2LO3ATR1K3R1bS3R1b2V4S3R1b2V4S3R1b2V4S3R1b2V4S3R1bS3R1b3SB1S3R1bS3R1bS3R1bFS2K2S2K3S2Z01KS3R1b3SB11G3SB2S3Bk13BOT2LO3ATR3R1a3R1b1GFFS3R1b3SB1S3R1b2L6S3R1bS3R1bS3R1bS3R1bS3R1bS3BOT2LO3ATR3R1bS3Bk13Bk23BOT2LO4SP163ATR2BB1K2HN2R43R1bFS3BOT2LO3ATR3R1b2L6S3BOT2LO3ATR3R1b2L3S3R1b1HS2HBFFS3R1b2V4FS3R1b3SB2".
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
      assert (PL1 : bytes_at bsegs m1 S (map (Z_to_bv 8) bl)) by
        (refine (proj1 (buf_atA_frame m m1 S bl _ BUF MU1 _)); cbn [disjoint_from]; split; [lia| exact I]);
      assert (GS1 : gshA m1) by
        (unfold harness_invA, GSH_ADDR in *; eapply rw_cells_transport; [exact GS| exact MU1| eassumption| cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]]);
      assert (MI1 : mem_inv bsegs m1) by assumption
    end.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) (S + 4) UNP1 ltac:(lia) ltac:(lia)) as (b4 & RD4 & CK4 & SR4).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_7ffd8; [gfact CK4| exact SR4| lia| assumption|]. intros y1.
    (* [comment removed for export] *)
    lazymatch type of PL1 with bytes_at _ ?m1 _ _ =>
      pose proof (buf_readA m1 S bl 4 (conj PL1 PLR) ltac:(lia)) as RB4; destruct (buf_nthA m1 S bl 4 (conj PL1 PLR) ltac:(lia)) as [_ V4] end.
    zstep.                                        (* [comment removed for export] *)
    cbv beta. rewrite (byte_litA _ V4).
    set (c := Znth 4 bl) in *.
    assert (L3 : 0 <= Z.land c 3 <= 3).
    { assert (E : Z.land c 3 = c mod 4) by exact (Z.land_ones c 2 ltac:(lia)). rewrite E. pose proof (Z.mod_pos_bound c 4). lia. }
    pose proof (shr6_cases c V4) as L6.
    assert (SB1 : 0 <= Z.shiftl (Z.land c 3) 3 <= 24) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
    assert (SB2 : 0 <= Z.shiftl (Z.shiftr c 6) 3 <= 24) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. lnot_of 134464.                        (* [comment removed for export] *)
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. lnot_of 134528.                        (* [comment removed for export] *)
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    first [rewrite (tabsh_eq1b (Z.land c 3) L3) | rewrite (tabsh_eq1 (Z.land c 3) L3)].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (gshA_rd0 m1 (2147467688 + Z.land c 3) GS1 ltac:(lia)) as RS1 end.
    zstep.                                        (* [comment removed for export] *)
    cbv beta. rewrite (byte_litA 0) by lia.
    zstep. bcase K2; [exfalso; clear - K2; lia|]. (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    first [rewrite (tabsh_eq2b (Z.shiftr c 6) L6) | rewrite (tabsh_eq2 (Z.shiftr c 6) L6)].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (gshA_rd0 m1 (2147467696 + Z.shiftr c 6) GS1 ltac:(lia)) as RS2 end.
    zstep.                                        (* [comment removed for export] *)
    cbv beta. rewrite (byte_litA 0) by lia.
    zstep. bcase K3; [exfalso; clear - K3; lia|]. (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (RDA : ov_read_bytes bsegs m1 (wa (134464 + Z.shiftl (Z.land c 3) 3)) 8
                    = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * Z.land c 3)) FHTAB))))
        by (replace (134464 + Z.shiftl (Z.land c 3) 3) with (AFI_DIDTAB + 8 * Z.land c 3)
              by (unfold AFI_DIDTAB; rewrite Z.shiftl_mul_pow2 by lia; lia);
            apply fhtab_read; [exact MI1| lia]);
      assert (RDB : ov_read_bytes bsegs m1 (wa (134528 + Z.shiftl (Z.shiftr c 6) 3)) 8
                    = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * (8 + Z.shiftr c 6))) FHTAB))))
        by (replace (134528 + Z.shiftl (Z.shiftr c 6) 3) with (AFI_DIDTAB + 8 * (8 + Z.shiftr c 6))
              by (unfold AFI_DIDTAB; rewrite Z.shiftl_mul_pow2 by lia; lia);
            apply fhtab_read; [exact MI1| lia])
    end.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    do 8 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    lazymatch goal with M : munch _ m ?mf, W : wmono bsegs m ?mf, MI9 : mem_inv bsegs ?mf, ST9 : stk bsegs ?mf lo _ |- _ =>
      destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
      apply evtF_done; unfold leafA_post; do 7 eexists; exists mf;
      split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
  - (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    lazymatch goal with M : munch _ m ?mf, W : wmono bsegs m ?mf, MI9 : mem_inv bsegs ?mf, ST9 : stk bsegs ?mf lo _ |- _ =>
      destruct (leaf_closeA L RNG st LB SPV lo m mf AH LBH BOT LO SPT M W) as [MG9 AH9];
      apply evtF_done; unfold leafA_post; do 7 eexists; exists mf;
      split; [reflexivity|]; split; [exact MI9|]; split; [exact ST9|]; split; [exact MG9| exact AH9] end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Stmts.
End CANSEC1.
