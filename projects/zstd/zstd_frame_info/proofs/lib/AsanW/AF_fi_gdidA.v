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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit AF_fi_gfha_iface AF_fi_mem AF_fi_gdid.
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
Definition gdidA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo SPV
    /\ magree asegs (aclient_addr CI LB SPV) m m'
    /\ AHEAP AI L RNG st LB m'.

Definition gdidA_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (lo : Z),
  AHEAP AI L RNG st LB m ->
  fake_lek 1 1 LB -> fake_lek 0 0 LB ->                                  (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  gshA m ->
  stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - GDID_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
  evtF asegs RNG (gdidA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFI_GDID) fc None m (seg_rom asegs)).

#[using="fflag FFLAG FREL SM1 GFHA GIMG"] Theorem gdidA : gdidA_stmt.
Proof.
  unfold gdidA_stmt.
  intros L RNG ra SPV gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB S bl lo
         AH LE1 LE0 LBH BUF NB HC GSH ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS -> ->.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  unfold GDID_STACK_A, AFI_STACK in LO.
  pose proof (spa_propsA SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & _ & _ & SHB & SUA & _).
  destruct (gdid_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { Local Ltac2 Set LiaHints.tbl := fun () => "0270?10067494706.15010286866424.88 11146609067.1621387335774.83  14434989683.13814434989683.21214982483438.14215860008408.20716218570462.14016218619486.15017283174833.15017294153783.88 17616073063.12717991086127.83 17997379594.12217997708812.19219318355690.16619628012706.12220118477938.12720133380586.15020146148781.13820146148781.21220667538767.13321443191518.14221445010926.11921455905371.88 21698460598.17423948144866.130244068018.142  24947289248.14225073799015.16625073808999.16825073988583.17025075715559.16425077993063.16725188966468.88 26432200358.14226492779925.13627480679381.16527858218883.15027860477445.88 28292029762.16628573892092.13928573892092.14028748943648.83 29452337932.15029782628086.13429784460045.18829786411515.13329788559449.20529788740059.13029790838294.17029928407609.13829928407609.16629928407609.21129928407609.21229928407609.21330283386102.14231122784805.15031123292837.14032293822159.13334131708783.19234132036969.12234134132044.83 34891932807.13835487970017.19235498130626.83 36339653704.20536354315754.13337383091378.14137769055268.16238006044424.14238007979531.15038738239746.20739473256951.15039473502583.14039609733482.92 39831286831.13140573185023.14240575443708.15041179479428.11942155345985.1424221046278.140 4221554310.150 44518355164.21347002488684.17147052170701.14248557391637.13348567891639.2054865552455.162 49747972711.1335033780125.188 50950165260.13850950165260.16650950165260.21150950165260.21250950167453.18950950167453.19050950167824.18852026834029.13452101693566.18852101693566.18952101693566.19052101693566.19152101693566.19252101693566.19352551281388.13852551281388.21256170235708.83 56182786461.14256184917785.12256185112863.19257013917709.14257716256011.15759148144883.12659308585216.15259827697002.15060335326791.14260595102003.13861139289837.15062278675126.14263183223768.13163868847056.13168200134232.15068202463067.1426871395124.142 7780033100.207 7979291495.128 8378946369.191 8378946369.192 8378946369.193 9314899696.125 9608221839.130 9608221839.210 9690333146.150 00000600W00\00j01Y02H02I02R02[02d03A03Z03_03d03m04604V04W04i04o05`06Q06V07307L07e07j08<08Y08Z09;09\0::0:W0;80;=0;>0;c0<D0<e0=B0=_0>G0>o0?00?90?>0?F0?K0?P0?U0?Z0@70@T0A10AN0Ak0Bd0Bm0C60C;0CC0CK0CO0Cl0Cm0Cn0D30D80D>0Dc0Dh0Dm0E60E<0EB0E[0E`0Ee0Ej0Ek0FH0FM0FR0FZ0G>0GC0GI0GO0GT0H90HB0HJ0HR0HZ0Hb0Hj0I20I:0I@0J30J;0JC0Jg0KK0Ko0L40L90L>0L_0Lh0M10M60M\0Mn0NQ0NW0O80OX0Oa0PB0PG0PL0PQ0PV0P[0Pd0Pk0QS0Qh0R=0RO0RY0Rc0RjS4F128S3BOT2LO3SPT3ATR3LY13LY33LY44SPABS3FHbS3SPT3LY34SPABS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323FHb2HrS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323FHb2HrFS3FHb3GHaS3FHa3FHbS3FHa3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPABS3FHbS3BOTS3BOT3FHbS3BOT3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHb2HrFS3SPT3LY34SPAB3FHbS4F128S3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA324F1283FHbS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA324F1283FHbS3FHbS3BOT2LO3SPT3ATR3LY34SPAB3FHbS3BOT2LO3SPT3ATR3LY34SPABS3BOT2LO3SPT3ATR3LY34SPABS3FHbS3ATR4F1283FHa3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHbFS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHcS3BOT2LO3ATR4SPAB4F1283FHc3AVSS3BOT2LO3ATR4SPAB3FHb3BSF3AVSS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHcS3BOTFS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHcS3BOT2LO3SPT3ATR3LY13LY44SPAB3FHbS3BOT2LO3SPT3ATR3LY13LY44SPABS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxFS3FHb3FHdS3FHbS3FHb2HaS3FHbS3FHbS3FHbS3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA324F1283FHa3FHb3FHdS3FHb3FHdS3FHb3FHdS3FHbS2LO3FHbS2LO3FHbS2LOS3BOT2LO3ATR3LY13LY44SPAB3FHbFFS3FHbS3FHbS4F128S3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3FHbS3FHbS3FHbS3FHb3GHdS4F128S4F128S3BOT2LO3ATR3LY13LY44SPABS3FHbS3FHbS3FHbSS3BOT2LO3ATR3LY13LY44SPAB3FHbS3FHbS3FHbS3FHb2HrS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HxS3FHbS4F128S4F128S3FHbS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3FHbS4F1282HaS3FHb2HrS3FHb2HrS3FHb2HrS3FHb2HrS3FHb2HaS3FHb2HaS3FHb2HaS4F128S3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323FHb3AVS2HaS3FHb2HaS3FHb2HaS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc2HaS3FHbS3FHbS3SPTS3BOT2LO3SPT3ATR3LY13LY44SPAB3FHbS3SPT3FHbS3SPT3FHbS3FHbS2D12D23BOT2LO3ATR3LY13LY44SPAB3FHb2HaS3SPT3LY34SPAB3FHbS2Z03BOT2LO3ATR3LY13LY44SPAB3FHb2HaS4F128S3BOT2LO3ATR3LY13LY44SPAB3FHb3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHb2HrS3FHa3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHcS3FHbS3FHbS3FHbS3FHbS3FHbS3FHb3GHaS3FHb1DS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3FHb2HaS3SPT3LY34SPAB3FHb2HaS3SPT3LY34SPAB3FHb2HaS3SPT3LY34SPAB3FHbS4SPAB3FHbS4SPAB3FHbS5SPA32".
eapply (gdid_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| unfold KEND; lia| unfold AFI_STACK; lia| lia]. }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear GOT SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (MG1 : magree asegs (aclient_addr CI LB SPV) m m1).
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
  assert (MG2 : magree asegs (aclient_addr CI LB SPV) m m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
  clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1.
  (* [comment removed for export] *)
  destruct (gdid_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply (gdid_hdr gp tp s2 s5 s7 s8 s9 s10 s11 FR fc SPV lo); first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F128
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
  assert (MG3 : magree asegs (aclient_addr CI LB SPV) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)|].
    split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha);
            rewrite ESH; lia| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk asegs m3 lo (SPAz SPV))
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk asegs m3 (SPAz SPV + 24) (SPV + -72))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  clear MG2 FRB2 FRA2 STG2 ST2 MI2 AH2 FFC2 SHF2 GPC2.
  (* [comment removed for export] *)
  unfold GFHDR in FFC3.
  change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x14767); C8 (Z_to_bv 64 0x81b3c); CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 FF))])
    with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x14767); C8 (Z_to_bv 64 0x81b3c)] ++ [CB 96 junk] ++ [C8 (Z_to_bv 64 (fflag L 1 FF))]) in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FJ3 FF1203]. cbn [cells_size csize Nat.add] in FF1203.
  replace (FF + Z.of_nat 24 + Z.of_nat 96) with (FF + 120) in FF1203 by lia. replace (FF + Z.of_nat 24) with (FF + 24) in FJ3 by lia.
  apply (rw_cells_split_CB asegs m3 _ [] 96 junk [] [8; 48; 40]%nat) in FJ3; [| reflexivity]. cbn [app mk_CB_cells] in FJ3.
  lazymatch type of FJ3 with rw_cells _ _ _ [?c0; ?c1; ?c2] =>
    apply (proj1 (rw_cells_appA _ m3 _ [c0] [c1; c2])) in FJ3; destruct FJ3 as [FJa FZ3]; cbn [cells_size csize Nat.add] in FZ3;
    apply (proj1 (rw_cells_appA _ m3 _ [c1] [c2])) in FZ3; destruct FZ3 as [FZ3 FJb]; cbn [cells_size csize Nat.add] in FJb end.
  replace (FF + 24 + Z.of_nat 8) with (FF + 32) in FZ3, FJb by lia. replace (FF + 32 + Z.of_nat 48) with (FF + 80) in FJb by lia.
  (* [comment removed for export] *)
  assert (SHZ3 : rw_cells asegs m3 (Z.shiftr (FF + 32) 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 6)).
  { unfold GFSH1 in SHF3.
    lazymatch type of SHF3 with rw_cells _ _ _ [?a0'; ?a1'; ?a2'; ?a3'; ?b0; ?b1; ?b2; ?b3; ?b4; ?b5; ?c0; ?c1; ?c2; ?c3; ?c4; ?c5] =>
      change [a0'; a1'; a2'; a3'; b0; b1; b2; b3; b4; b5; c0; c1; c2; c3; c4; c5]
        with ([a0'; a1'; a2'; a3'] ++ [b0; b1; b2; b3; b4; b5] ++ [c0; c1; c2; c3; c4; c5]) in SHF3 end.
    pose proof (proj1 (rw_cells_appA _ _ _ _ _) SHF3) as [_ X]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X.
    replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact X|].
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC3. unfold artcells in RTC3.
  destruct RTC3 as (_ & GOT3 & RIC3 & REAL3 & SHB3 & _ & INI3 & LAY3 & _).
  assert (UNZ3 : unpoisoned m3 (FF + 32) (FF + 32 + 48)).
  { replace (FF + 32 + 48) with ((FF + 32) + 8 * Z.of_nat 6) by lia.
    apply (c1z_cells_unpoisoned 6 m3 (FF + 32) SHZ3); [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| unfold KEND in *; lia]. }
  assert (ESH16 : shad (FF + 128) - shad FF = 16) by (rewrite !shad_div; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  eapply evtF_cut.
  { eapply (amemset_specZ (FF + 32) 48 0 (SPAz SPV) RNG) with (lo := lo) (RLO2 := FF) (RHI2 := FF + 128);
      first [ exact MI3 | exact STL3 | exact GOT3 | exact RIC3 | exact SHB3 | exact INI3 | exact LAY3 | exact REAL3 | exact FZ3 | exact UNZ3 | exact RI
            | reflexivity
            | rewrite ESH16; rewrite ESH; exact (proj2 SHF3)
            | rewrite ESH16; exact RSFF
            | eapply rng_sub'; [exact RSTK| lia]
            | eapply rng_sub'; [exact RFF| lia]
            | apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]
            | unfold KHIGH; lia | unfold KEND in *; lia | lia ]. }
  cbv beta. intros ms' PO. unfold amemsetZ_post in PO.
  destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m3' & -> & MU3' & WM3' & MI3' & STL3' & FZ3').
  retlitA. change (Z.to_nat 48) with 48%nat in FZ3'.
  assert (AH3' : AHEAP AI L RNG st (FB1 FF :: LB) m3').
  { eapply (AI_frame AI); [exact AH3| exact MU3'| exact WM3'|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB1 FF); split; [left; reflexivity| cbn; lia]| constructor]. }
  assert (MG3x : magree asegs (aclient_addr CI LB SPV) m m3').
  { eapply magree_munch_step; [exact MG3| exact MU3'| exact WM3'|]. intros a Ha. cbn.
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV - 2208) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU3' WM3' ltac:(cbn [disjoint_from cells_size csize Nat.add GFSH1 length]; lia)) as SHF3x.
  pose proof (rw_cells_transport _ _ _ _ _ _ FF03 MU3' WM3' ltac:(cbn; lia)) as FF03x.
  pose proof (rw_cells_transport _ _ _ _ _ _ FF1203 MU3' WM3' ltac:(cbn; lia)) as FF1203x.
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU3' WM3' ltac:(cbn; lia)) as FRB3x.
  pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU3' WM3' ltac:(cbn; lia)) as FRA3x.
  assert (STG3x : stk asegs m3' (SPAz SPV + 24) (SPV + -72))
    by (eapply stk_transport; [exact STG3| exact MU3'| exact WM3'| intros x Hx; cbn; lia]).
  assert (SHZ3x : rw_cells asegs m3' (Z.shiftr (FF + 32) 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 6)).
  { eapply rw_cells_transport; [exact SHZ3| exact MU3'| exact WM3'|]. cbn [disjoint_from cells_size csize Nat.add repeat length].
    rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_div_pow2 in AVS by lia. change (2^3) with 8 in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  clear MU3' WM3' SHF3 FF03 FF1203 FRB3 FRA3 STG3 STL3 SHZ3 MI3 AH3 MG3 UNZ3 GOT3 RIC3 REAL3 SHB3 INI3 LAY3 FZ3.
  rename m3 into m3o. rename m3' into m3. rename SHF3x into SHF3. rename FF03x into FF03. rename FF1203x into FF1203. rename FRB3x into FRB3.
  rename FRA3x into FRA3. rename STG3x into STG3. rename STL3' into STL3. rename SHZ3x into SHZ3. rename MI3' into MI3. rename AH3' into AH3.
  rename MG3x into MG3. rename FZ3' into FZ3.
  (* [comment removed for export] *)
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply (gdid_call gp tp s8 s9 s10 s11 FR fc SPV RNG); [exact MI3|].
  cbv beta.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof GFHA as G. unfold gfhaA_stmt, gfhaA_stmt_at in G.
    eapply (G L RNG (Z_to_bv 64 0x81c78) (SPAz SPV)) with (lo := lo) (S := S) (bl := bl) (ZF := FF + 32); clear G.
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
  assert (SHF4 : rw_cells asegs m4 (Z.shiftr FF 3 + 2147450880) GFSH1).
  { eapply rw_cells_magree; [exact MG4| exact SHF3|]. cbn [cells_size csize Nat.add GFSH1 length]. intros a Ha. split; [| lia].
    right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    right; right. exists 1, FF, 128. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (FF04 : rw_cells asegs m4 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x14767); C8 (Z_to_bv 64 0x81b3c)]).
  { eapply rw_cells_magree; [exact MG4| exact FF03|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLF; lia. }
  assert (FF1204 : rw_cells asegs m4 (FF + 120) [C8 (Z_to_bv 64 (fflag L 1 FF))]).
  { eapply rw_cells_magree; [exact MG4| exact FF1203|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLF; lia. }
  assert (FRB4 : rw_cells asegs m4 (SPV + -72) (GFRB ra s0 s1 s2 s3 s4 s5 s6 s7)).
  { eapply rw_cells_magree; [exact MG4| exact FRB3|]. cbn [cells_size csize Nat.add GFRB length]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  assert (FRA4 : rw_cells asegs m4 (SPAz SPV) [CB 16 j16; C8 (Z_to_bv 64 FF)]).
  { eapply rw_cells_magree; [exact MG4| exact FRA3|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  assert (STG4 : stk asegs m4 (SPAz SPV + 24) (SPV + -72)).
  { eapply stk_magree; [exact MG4| exact STG3|]. intros a Ha. split; [apply cl_stack; lia| lia]. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gdid_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact SHF4| exact FF04| exact FF1204| exact FLC4| exact ZFH4| exact FRB4| exact FRA4| exact ST4| exact STG4| exact MI4
            | exact FH| exact FC| exact F128| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16| exact RI
            | rewrite ESH; exact RSFF | eapply rng_sub'; [exact RSTK| lia]| unfold KEND; lia | unfold AFI_STACK; lia | lia]. }
  cbv beta. intros ms' (y10 & y11' & y12' & mp & m5 & -> & MU5 & WM5 & MIp & MU6 & WM6 & MI5 & ST5 & FLC5).
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
  apply evtF_done. unfold gdidA_post. do 15 eexists. exists m5. split; [reflexivity|].
  split; [exact MI5|]. split; [exact ST5|].
  split.
  { assert (MG4' : magree asegs (aclient_addr CI LB SPV) m m4).
    { eapply magree_trans; [exact MG3|]. eapply magree_mono; [exact MG4|]. intros a Ha. split.
      - eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia].
      - intros Hr. exact (app_not_client CI LB SPV FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha). }
    assert (MGp : magree asegs (aclient_addr CI LB SPV) m mp).
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
