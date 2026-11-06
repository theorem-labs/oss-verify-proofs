(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_gfha_iface AF_fi_gfcs.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM1 : stack_malloc_1_stmtk AI fflag rng_fs 1.
Hypothesis GFHA : gfhaA_stmt AI rng_fs.
Hypothesis GIMG : In (0x20d40, 0x20dc0)%Z CI.      (* [comment removed for export] *)
Notation FB1 F := (mkABlock (ABFake 1) F 128).

(* [comment removed for export] *)
Definition gfcsA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ magree bsegs (aclient_addr CI LB SPV) m m'
    /\ AHEAP AI L RNG st LB m'.

Definition gfcsA_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (lo : Z),
  AHEAP AI L RNG st LB m ->
  fake_lek 1 1 LB -> fake_lek 0 0 LB ->                                  (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  gshA m ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - GFCS_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
  evtF bsegs RNG (gfcsA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFI_GFCS) fc None m (seg_rom bsegs)).

#[using="fflag FFLAG FREL SM1 GFHA GIMG"] Theorem gfcsA : gfcsA_stmt.
Proof.
  unfold gfcsA_stmt.
  intros L RNG ra SPV gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB S bl lo
         AH LE1 LE0 LBH BUF NB HC GSH ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS -> ->.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  unfold GFCS_STACK_A, AFI_STACK in LO.
  pose proof (spa_propsA SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & _ & _ & SHB & SUA & _).
  destruct (gfcs_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { Local Ltac2 Set LiaHints.tbl := fun () => "01S0?10067494706.13410286866424.88 1387335774.83  14434989683.13814434989683.19515860008408.19016218619486.13417283174833.13417294153783.88 17616073063.12717991086127.83 17997379594.12217997708812.17619628012706.12220118477938.12720133380586.13420146148781.13820146148781.19520667538767.13321445010926.11921455905371.88 23948144866.13025188966468.88 26492779925.13627858218883.13427860477445.88 28573892092.13928573892092.14028748943648.83 29452337932.13429782628086.13429784460045.17229786411515.13329788559449.18829788740059.13029928407609.13829928407609.19429928407609.19529928407609.19631122784805.13432293822159.13334131708783.17634132036969.12234134132044.83 34891932807.13835487970017.17635498130626.83 36339653704.18836354315754.13338007979531.13438168430774.15838738239746.19039473256951.13439609733482.92 39831286831.13140575443708.1344221554310.134 44518355164.19648557391637.13348567891639.18849141910660.11949747972711.1335033780125.172 50950165260.13850950165260.19450950165260.19550950167453.17350950167453.17450950167824.17252026834029.13452101693566.17252101693566.17352101693566.17452101693566.17552101693566.17652101693566.17752551281388.13852551281388.19556170235708.83 56184917785.12256185112863.17657716256011.14159148144883.12659308585216.13659827697002.13460595102003.13861139289837.13463183223768.13163868847056.13168200134232.1347780033100.190 7979291495.128 8378946369.175 8378946369.176 8378946369.177 9314899696.125 9608221839.130 9608221839.193 9690333146.134 00000600W00e01T02C02L02U03203K03P03U03^03g03h04:04@05105b05g06@06Y06k07007U08608S09;09c09d09m0:20::0:?0:D0:I0:f0;C0;`0<=0<F0<K0<S0<[0<_0=<0==0=>0=C0=H0=M0=R0=[0=a0>:0>?0>D0>I0>Q0>W0>]0>^0?C0?L0?T0?\0?d0?l0@40@<0@B0A50A=0AE0Ai0BM0C10C60C;0C@0CI0CR0D80DJ0Dm0E30ES0E\0Ea0Ef0Ek0F40F;0Fc0G80GM0G_0Gi0H30H:S4F128S3BOT2LO3SPT3ATR3LY13LY33LY44SPABS3SPT3LY34SPABS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323FHb2HrS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323FHb2HrS3FHb3GHaS3FHa3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPABS3FHbS3BOTS3BOT3FHbS3BOT3FHbFS3SPT3LY34SPAB3FHbS4F128S3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA324F1283FHbS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA324F1283FHbS3FHbS3BOT2LO3SPT3ATR3LY34SPABS3BOT2LO3SPT3ATR3LY34SPABS3ATR4F1283FHa3FHcS3BOTS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS3BOT2LO3SPT3ATR3LY13LY44SPAB3FHbS3BOT2LO3SPT3ATR3LY13LY44SPABS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxFS3FHb3FHdS3FHbS3FHb2HaS3FHbS3FHbS3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3FHb3FHdS3FHbS2LO3FHbS2LO3FHbS2LOS3BOT2LO3ATR3LY13LY44SPAB3FHbFFS3FHbS3FHbS3FHbS3FHbS3FHb3GHdS4F128S3BOT2LO3ATR3LY13LY44SPABS3FHbS3FHbS3FHbS3FHb2HrS4F128S4F128SS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3FHbS4F1282HaS3FHb2HrS3FHb2HrS3FHb2HrS3FHb2HaS3FHb2HaS3FHb2HaS4F128S3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323FHb3AVS2HaS3FHb2HaS3FHb2HaS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS3FHbS3FHbS3SPTS3SPT3FHbS3SPT3FHbS2D12D23BOT2LO3ATR3LY13LY44SPAB3FHb2HaS3SPT3LY34SPAB3FHbS2Z03BOT2LO3ATR3LY13LY44SPAB3FHb2HaS4F128S3BOT2LO3ATR3LY13LY44SPAB3FHb2HrS3FHa3FHbS3FHbS3FHbS3FHbS3FHb3GHaS3FHb1DS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3FHb2HaS3SPT3LY34SPAB3FHb2HaS3SPT3LY34SPAB3FHb2HaS3SPT3LY34SPAB3FHbS4SPAB3FHbS4SPAB3FHbS5SPA32".
eapply (gfcs_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| unfold KEND; lia| unfold AFI_STACK; lia| lia]. }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear GOT SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (MG1 : magree bsegs (aclient_addr CI LB SPV) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SPV (SPV - 112) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  clear MU1 WM1.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof SM1 as SMC. unfold stack_malloc_1_stmtk, sm_stmtk in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPAz SPV)) by lia;
      first [exact AH1| exact LE1| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F128 & FH & FC & FFC2 & SHF2 & RFF & RSFF).
  rewrite ?(unsigned_lit (SPAz SPV)) in ST2, HPR2 by lia.
  retlitA.
  change (Z.to_nat (128 - 32)) with 96%nat in FFC2. change (128 / 8) with 16 in RSFF.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  assert (NFB : ~ In (FB1 FF) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
  assert (FFD : forall b, In b LB -> FF + 128 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB1 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. lia. }
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  assert (MG2 : magree bsegs (aclient_addr CI LB SPV) m m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
  clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1.
  (* [comment removed for export] *)
  destruct (gfcs_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply (gfcs_hdr gp tp s2 s5 s7 s8 s9 s10 s11 FR fc SPV lo); first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F128
                       | exact RFF| exact RSFF| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac].
  intros m3 j16 MU3 WM3 MI3 FRA3 FFC3 SHF3. cbv beta.
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  pose proof (app_vs_shadow FF 128 (Z.shiftr FF 3 + 2147450880) 16 FH (proj1 BSF) (proj2 BSF)) as AVS.
  assert (AH3 : AHEAP AI L RNG st (FB1 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB1 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 1, FF, 128; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
  assert (LBH3 : forall b, In b (FB1 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
  assert (MG3 : magree bsegs (aclient_addr CI LB SPV) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)|].
    split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha);
            rewrite ESH; lia| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk bsegs m3 lo (SPAz SPV))
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk bsegs m3 (SPAz SPV + 24) (SPV + -72))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  clear MG2 FRB2 FRA2 STG2 ST2 MI2 AH2 FFC2 SHF2 GPC2.
  (* [comment removed for export] *)
  unfold GFHDR in FFC3.
  change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1ae1d); C8 (Z_to_bv 64 0x80bfc); CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 FF))])
    with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1ae1d); C8 (Z_to_bv 64 0x80bfc)] ++ [CB 96 junk] ++ [C8 (Z_to_bv 64 (fflag L 1 FF))]) in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FJ3 FF1203]. cbn [cells_size csize Nat.add] in FF1203.
  replace (FF + Z.of_nat 24 + Z.of_nat 96) with (FF + 120) in FF1203 by lia. replace (FF + Z.of_nat 24) with (FF + 24) in FJ3 by lia.
  apply (rw_cells_split_CB bsegs m3 _ [] 96 junk [] [8; 48; 40]%nat) in FJ3; [| reflexivity]. cbn [app mk_CB_cells] in FJ3.
  lazymatch type of FJ3 with rw_cells _ _ _ [?c0; ?c1; ?c2] =>
    apply (proj1 (rw_cells_appA _ m3 _ [c0] [c1; c2])) in FJ3; destruct FJ3 as [FJa FZ3]; cbn [cells_size csize Nat.add] in FZ3;
    apply (proj1 (rw_cells_appA _ m3 _ [c1] [c2])) in FZ3; destruct FZ3 as [FZ3 FJb]; cbn [cells_size csize Nat.add] in FJb end.
  replace (FF + 24 + Z.of_nat 8) with (FF + 32) in FZ3, FJb by lia. replace (FF + 32 + Z.of_nat 48) with (FF + 80) in FJb by lia.
  (* [comment removed for export] *)
  assert (SHZ3 : rw_cells bsegs m3 (Z.shiftr (FF + 32) 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 6)).
  { unfold GFSH1 in SHF3.
    lazymatch type of SHF3 with rw_cells _ _ _ [?a0'; ?a1'; ?a2'; ?a3'; ?b0; ?b1; ?b2; ?b3; ?b4; ?b5; ?c0; ?c1; ?c2; ?c3; ?c4; ?c5] =>
      change [a0'; a1'; a2'; a3'; b0; b1; b2; b3; b4; b5; c0; c1; c2; c3; c4; c5]
        with ([a0'; a1'; a2'; a3'] ++ [b0; b1; b2; b3; b4; b5] ++ [c0; c1; c2; c3; c4; c5]) in SHF3 end.
    pose proof (proj1 (rw_cells_appA _ _ _ _ _) SHF3) as [_ X]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X.
    replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact X|].
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof GFHA as G. unfold gfhaA_stmt, gfhaA_stmt_at in G.
    eapply (G L RNG (Z_to_bv 64 0x80d28) (SPAz SPV)) with (lo := lo) (S := S) (bl := bl) (ZF := FF + 32); clear G.
    - exact AH3.
    - apply fake_lek_push; [intros F' n' E; discriminate E| exact LE0].
    - exact LBH3.
    - split; [| exact PLR]. eapply bytes_at_magree; [exact MG3| exact PL|]. rewrite length_map. intros a Ha.
      destruct HC as [Z0|(p & D & N & Hb & D1 & D2)]; [exfalso; lia|]. apply (cl_block CI LB SPV (HB p D N) a Hb). cbn. lia.
    - exact NB.
    - apply hcoverA_cons_fake. exact HC.
    - exact FZ3.
    - split.
      + exists 1, FF, 128. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact FH| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
      + replace (FF + 32 + 48) with ((FF + 32) + 8 * Z.of_nat 6) by lia. apply (c1z_cells_unpoisoned 6 m3 (FF + 32) SHZ3); [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia|].
        unfold KEND in *. lia.
    - OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - exists 1, FF, 128. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. split; [reflexivity|].
      split; [lia|]. split; [unfold KEND in *; lia|]. change (128 / 8) with 16. split; [rewrite ESH; exact (proj2 SHF3)| exact RSFF].
    - eapply gshA_mg; [exact MG3| intros a Ha; exact (gsh_client CI LB SPV a GIMG Ha)| exact GSH].
    - exact STL3.
    - exact BOT.
    - unfold AFI_STACK. lia.
    - lia.
    - OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - exact MI3.
    - exact TP.
    - exact RSTK.
    - exact RI.
    - exact RIS.
    - exact RFS.
    - eapply rng_sub'; [exact RFF| lia].
    - eapply rng_sub'; [exact RSFF|]. rewrite !shad_div. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  cbv beta. intros ms' PO. unfold gfhaA_post in PO.
  destruct PO as (r & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & zj1 & hb & zj2 & m4
                  & -> & MI4 & ST4 & MG4 & AH4 & ZFH4 & _).
  retlitA.
  (* [comment removed for export] *)
  destruct (FFLAG _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (FLC4 & RG & GH & GC & GBL & GCI).
  pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
  assert (CLF : forall a, FF <= a < FF + 128 -> ~ (FF + 32 <= a < FF + 32 + 48) -> aclient_addr CI (FB1 FF :: LB) (SPAz SPV) a /\ ~ (FF + 32 <= a < FF + 32 + 48)).
  { intros a Ha Hn. split; [| exact Hn]. apply (cl_block CI (FB1 FF :: LB) (SPAz SPV) (FB1 FF) a ltac:(left; reflexivity)). cbn. lia. }
  assert (SHF4 : rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) GFSH1).
  { eapply rw_cells_magree; [exact MG4| exact SHF3|]. cbn [cells_size csize Nat.add GFSH1 length]. intros a Ha. split; [| lia].
    right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    right; right. exists 1, FF, 128. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (FF04 : rw_cells bsegs m4 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1ae1d); C8 (Z_to_bv 64 0x80bfc)]).
  { eapply rw_cells_magree; [exact MG4| exact FF03|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLF; lia. }
  assert (FF1204 : rw_cells bsegs m4 (FF + 120) [C8 (Z_to_bv 64 (fflag L 1 FF))]).
  { eapply rw_cells_magree; [exact MG4| exact FF1203|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLF; lia. }
  assert (FRB4 : rw_cells bsegs m4 (SPV + -72) (GFRB ra s0 s1 s2 s3 s4 s5 s6 s7)).
  { eapply rw_cells_magree; [exact MG4| exact FRB3|]. cbn [cells_size csize Nat.add GFRB length]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  assert (FRA4 : rw_cells bsegs m4 (SPAz SPV) [CB 16 j16; C8 (Z_to_bv 64 FF)]).
  { eapply rw_cells_magree; [exact MG4| exact FRA3|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  assert (STG4 : stk bsegs m4 (SPAz SPV + 24) (SPV + -72)).
  { eapply stk_magree; [exact MG4| exact STG3|]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gfcs_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact SHF4| exact FF04| exact FF1204| exact FLC4| exact ZFH4| exact FRB4| exact FRA4| exact ST4| exact STG4| exact MI4
            | exact FH| exact FC| exact F128| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16| exact RI
            | rewrite ESH; exact RSFF | eapply rng_sub'; [exact RSTK| lia]| unfold KEND; lia | unfold AFI_STACK; lia | lia]. }
  cbv beta. intros ms' (y10 & y11' & mp & m5 & -> & MU5 & WM5 & MIp & MU6 & WM6 & MI5 & ST5 & FLC5).
  assert (AHp : AHEAP AI L RNG st (FB1 FF :: LB) mp).
  { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|].
    constructor; [| constructor; [| constructor]]; cbn.
    - right; right. right; right. exists 1, FF, 128. split; [left; reflexivity|].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - right; left. exists (FB1 FF). split; [left; reflexivity| cbn; lia]. }
  pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
  assert (AH5 : AHEAP AI L RNG st LB m5).
  { eapply aheap_eqA; [exact AHr|].
    apply (mem_eq_singleA mp m5 (fflag L 1 FF) (Z_to_bv 8 0)); [lia| lia| exact MU6| apply byte_of_c1A; [exact FLC5| lia]]. }
  apply evtF_done. unfold gfcsA_post. do 15 eexists. exists m5. split; [reflexivity|].
  split; [exact MI5|]. split; [exact ST5|].
  split.
  { assert (MG4' : magree bsegs (aclient_addr CI LB SPV) m m4).
    { eapply magree_trans; [exact MG3|]. eapply magree_mono; [exact MG4|]. intros a Ha. split.
      - eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia].
      - intros Hr. exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha). }
    assert (MGp : magree bsegs (aclient_addr CI LB SPV) m mp).
    { eapply magree_munch_step; [exact MG4'| exact MU5| exact WM5|].
      intros a Ha. cbn.
      split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia|].
      split; [intros Hr; exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
    eapply magree_munch_step; [exact MGp| exact MU6| exact WM6|].
    intros a Ha. cbn. split; [| exact I].
    intros Hr. refine (app_not_client CI LB SPV (fflag L 1 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
    intros b Hb. exact (GBL b (or_intror Hb)). }
  exact AH5.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
End CANSEC1.
