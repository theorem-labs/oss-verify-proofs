(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AHarness_iface AH_fi_iface AF_fi_kit
     AF_fi_gfha_iface AF_fi_mem AF_fi_chk AF_fi_gfhaC AF_fi_gfhaM AF_fi_gfhaQM.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
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
Hypothesis SM0 : stack_malloc_0_stmtk AI fflag rng_fs 0.
Hypothesis GIMG : In (0x20d40, 0x20dc0)%Z CI.      (* [comment removed for export] *)
Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
#[using="Type"] Lemma c1k_unpoisonedR : forall m A k j, rw_cells bsegs m (Z.shiftr A 3 + 2147450880) [C1 (Z_to_bv 8 k)] -> A mod 8 = 0 ->
  0 <= A -> 1 <= k <= 7 -> 0 <= j <= k -> A + 8 <= 2^47 -> unpoisoned m A (A + j).
Proof.
  intros m A k j H A8 A0 K7 Jk AH. Local Ltac2 Set LiaHints.tbl := fun () => "0080>11644555580.2115978983042.2124889733967.2124931955585.1829784466269.2138005288389.2245622865929.2161051933055.1800000700>00H00L00P00`00d011S2A02K7S2A02H1S2A82K72JkS2A0S2A0S2A82K72Jk2H12H2S2A0S2A02K72Jk2AH".
split; [lia|]. split; [lia|]. intros G H0 H1 H2.
  assert (EG : G = A / 8) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). subst G.
  exists (Z_to_bv 8 k). split.
  - unfold ASHOFF. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
    replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
    apply (byte_of_c1A m _ _ H). OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - right. rewrite (sval_lit k) by lia. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="FFLAG FREL"] Lemma gfha_closeA : forall (L : alayout) (RNG : footprint) (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (ZF nn lo FF : Z) (bz : ablock)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word) (mx : amem) (r : Z)
    (h0 h1 h2 : word) (j24 j1 hb j2 : list byte),
  AHEAP AI L RNG st (FB0 FF :: LB) mx ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  In bz LB -> ab_addr bz <= ZF -> ZF + 48 <= ab_addr bz + ab_size bz ->
  magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (ZF <= a < ZF + 48)) m mx ->
  rw_cells bsegs mx ZF [CB 24 j1; CB 4 hb; CB 20 j2] ->
  (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= nn /\ h <= 18) ->
  rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) GSH1 ->
  rw_cells bsegs mx FF [C8 h0; C8 h1; C8 h2] -> rw_cells bsegs mx (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs mx (SPV + -96) (GFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  rw_cells bsegs mx (SPAz SPV) [CB 24 j24; C8 (Z_to_bv 64 FF)] ->
  stk bsegs mx lo (SPAz SPV) -> stk bsegs mx (SPAz SPV + 32) (SPV + -96) -> mem_inv bsegs mx ->
  ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  SPV mod 16 = 0 -> SPV <= KEND -> lo <= SPV - AFI_STACK -> ATOP <= lo -> rng RNG lo (SPV - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (gfhaA_post AI L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB ZF nn lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x25 x26 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 0x80204) fc None mx (seg_rom bsegs)).
Proof.
  intros until j2. intros AHx LBH FFD BZ BZ1 BZ2 MGx ZFx RH SHFx FF0x FF56x FRBx FRAx STLx STGx MIx FH FC F64 RFF RSFF SP16 SPT LO BOT RSTK RI.
  pose proof atop_range as ATR. pose proof (spa_propsA SPV SP16) as (SPAB & SPA32 & _). unfold AFI_STACK in LO. unfold KEND in SPT.
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  Local Ltac2 Set LiaHints.tbl := fun () => "00F0?12995153056.12214434989683.14314950692319.10417991089884.12220146148781.14322116257864.13323585441644.13529786476646.10429788559449.13329928407609.14329928407609.14432775280396.14334342398647.13335497641708.14356170236367.12258685776440.14462277708727.13763848739242.12263868783922.10365466962616.1356786299319.138 9264669894.135 00000800[00l01501Y01^01g01l02102F02[02c03:03?03D03L04B04C04H04Q05C05LS2LO3FHbS4SP162LO3BOT3ATR4SPAB5SPA323FHb2HrS3F643ATR3FHa3FHcS3BOT3FHbS3F644SP162LO3BOT3ATR4SPAB5SPA323FHbS3FHbS3FHb3GHaS3FHbS3FHbS2LO3BOT3ATR4SPAB3FHbS2LO3BOT3ATR4SPAB3FHbS3FHb2HrS3BZ13BZ23F643BZF2GF2GZS3FHbS3FHbS3FHb2HrS3BZ13BZ24SP162LO3BOT3ATR4SPAB5SPA323FHb3BZF2GF2GZ3AVZFS3FHbS3FHb3GHaS3BZ13BZ24SP162LO3BOT3ATR4SPAB5SPA323FHb3BZF2GF2GZS3FHb3GHd".
assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (LBH bz BZ) as BZH. pose proof (ablk_lin _ _ BZH) as (BZa & BZb & BZc & BZd).
  pose proof (FFD bz BZ) as BZF.
  (* [comment removed for export] *)
  destruct (FFLAG _ _ _ _ _ _ _ _ AHx ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & _).
  pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
  pose proof (GBL bz ltac:(right; exact BZ)) as GZ.
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
  (* [comment removed for export] *)
  change [C8 h0; C8 h1; C8 h2] with ([C8 h0] ++ [C8 h1; C8 h2]) in FF0x.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FF0x. destruct FF0x as [FF0x _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gfha_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact SHFx| exact FF0x| exact FF56x| exact FLC| exact FRBx| exact FRAx| exact STLx| exact STGx| exact MIx
            | exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16| exact RI
            | rewrite ESH; exact RSFF | eapply rng_sub'; [exact RSTK| lia]| unfold KEND; lia | unfold AFI_STACK; lia | lia]. }
  cbv beta. intros ms' (y11 & mp & m5 & -> & MU5 & WM5 & MIp & MU6 & WM6 & MI5 & ST5 & FLC5).
  assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
  { eapply (AI_frame AI); [exact AHx| exact MU5| exact WM5|].
    constructor; [| constructor; [| constructor]]; cbn.
    - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia]. }
  pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
  assert (AH5 : AHEAP AI L RNG st LB m5).
  { eapply aheap_eqA; [exact AHr|].
    apply (mem_eq_singleA mp m5 (fflag L 0 FF) (Z_to_bv 8 0)); [lia| lia| exact MU6| apply byte_of_c1A; [exact FLC5| lia]]. }
  (* [comment removed for export] *)
  pose proof (app_vs_shadow (ab_addr bz) (ab_size bz) (Z.shiftr FF 3 + 2147450880) 8 BZH (proj1 BSF) (proj2 BSF)) as AVZ.
  pose proof (rw_cells_transport _ _ _ _ _ _ ZFx MU5 WM5 ltac:(cbn; lia)) as ZFp.
  pose proof (rw_cells_transport _ _ _ _ _ _ ZFp MU6 WM6 ltac:(cbn; lia)) as ZF5.
  apply evtF_done. unfold gfhaA_post.
  exists r. do 14 eexists. exists j1, hb, j2, m5. split; [reflexivity|].
  split; [exact MI5|]. split; [exact ST5|].
  split.
  { assert (MGp : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (ZF <= a < ZF + 48)) m mp).
    { eapply magree_munch_step; [exact MGx| exact MU5| exact WM5|].
      intros a [Ha Hn]. cbn.
      split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia|].
      split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
    eapply magree_munch_step; [exact MGp| exact MU6| exact WM6|].
    intros a [Ha Hn]. cbn. split; [| exact I].
    intros Hr. refine (app_not_client CI LB SPV (fflag L 0 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
    intros b Hb. exact (GBL b (or_intror Hb)). }
  split; [exact AH5|]. split; [exact ZF5| exact RH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
#[using="Type"] Lemma gfha_mcA : forall (L : alayout) (RNG : footprint) (SPV : Z) (rax gp tp x5 x6 x7 w8 w9 x13 x14 x15 x16 x17 : word)
    (w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 x28 x29 x30 x31 : word)
    (FR : bvmap 5 word) (fc : bv 32) (my : amem) (st : astate) (LB : list ablock) (S : Z) (bl : list Z) (lo FF : Z) (junk : list byte),
  AHEAP AI L RNG st (FB0 FF :: LB) my ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  buf_atA my S bl -> 0 < zlen bl <= 4 -> hcoverA LB S (zlen bl) ->
  rw_cells bsegs my (FF + 32) [CB (Z.to_nat (zlen bl)) junk] ->
  rw_cells bsegs my (Z.shiftr FF 3 + 2147450880) GSH4 ->
  stk bsegs my lo (SPAz SPV) -> mem_inv bsegs my ->
  ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  SPV mod 16 = 0 -> SPV <= KEND -> lo <= SPV - AFI_STACK -> ATOP + 4096 <= lo -> rng RNG lo (SPV - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (amemcpyZ_post rax gp tp w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 FR fc (SPAz SPV) (FF + 32) S (zlen bl) lo (map (Z_to_bv 8) bl) my)
    (MS (mkR rax (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 w8 w9 (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) x13 x14 x15 x16 x17
             w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 x28 x29 x30 x31)
        FR (Z_to_bv 64 AFI_AMEMCPY) fc None my (seg_rom bsegs)).
Proof.
  intros until junk. intros AHy LBH FFD BUF N4 HC DST SHF STL MI FH FC F64 RFF RSFF SP16 SPT LO BOT RSTK RI.
  pose proof atop_range as ATR. pose proof (spa_propsA SPV SP16) as (SPAB & SPA32 & _). unfold AFI_STACK in LO. unfold KEND in SPT.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
  Local Ltac2 Set LiaHints.tbl := fun () => "00Y0?12276715276.12412526909642.12416208281459.1231687324411.124 18433882437.12418599045935.12321455547488.12429339012372.11229782628086.12330496432114.12432245432605.12139466883290.12339523246479.78 39859484460.12440577606977.12442150856447.12445774878830.12446466591077.12447033583531.12448777321687.12348940630193.12450564126210.12452026834029.12352453071094.12455207473259.12355799688878.12456170497827.12459310612856.88 59372074086.12459842441943.12461149708624.12462651565374.12462857623715.12463683149453.12463868783905.77 65846594447.12466342778342.12466716936361.1127358684419.124 7730146453.124 9730883920.124 00000[01`02102F03203?03`03l04904I04Y04^04c05K05X06506F06V07E07V07[08g08l08m09=0:00:B0:M0:]0:n0;?0;P0;Q0<?0<D0<Q0=C0=P0=`0>00>_S2LO3BOT3ATR4SPAB3FHb2HN2A43R1a3R1b3HL23HL5S3F644SP162LO3BOT3ATR4SPAB5SPA323FHa3FHb2HN2A22A43R1a3R1b3HL23HL43HL5S3FHa3FHb3R1b3HL5S3Bk13Bk23FHb3R1b3HL5S3Bk22LO3BOT3ATR4SPAB3FHb2A43R1b3R1c3HL23HL5S3FHb3R1b3HL5S3SPT2LO3BOT3ATR4SPAB3FHb3R1b3HL5S3FHb2HN3R1bS3FHb3R1b3HL5S2N43FHb3R1b3HL5S2N43FHb3R1b3HL5S3F64S3F64S2LO3BOT3ATR4SPAB3FHb2A43R1b3R1c3HL53HL6S3FHb3R1b3HL5S2LO3BOT3ATR4SPAB3FHb3R1b3HL5S3FHb3R1b3HL33HL5S2N43FHb3R1b3HL5S2LO3BOT3ATR4SPAB3FHb2HN2A43R1a3R1b3HL23HL43HL5S3FHb3FHd3R1b3HL5S3FHdS2N43Bk13Bk24SP162LO3BOT3ATR4SPAB5SPA323FHb3FHu2HN2A22A43R1b3HL23HL43HL53BKFS3F64FS2N43FHb3R1b3HL5S3Bk12LO3BOT3ATR4SPAB3FHb2HN2A43R1a3R1b3HL13HL23HL5S4SPAB3FHb3R1b3HL5S2N42Z03FHbS2N43FHb3R1b3HL5S3F643FHb3R1b3HL5S3FHa3FHb3R1b3HL5S3Bk13FHb3R1b3HL5FS2N42LO3BOT3ATR4SPAB3FHb2HN2A43R1a3R1b3HL23HL5S3FHbS3FHb3R1b3HL5S2N42LO3BOT3ATR4SPAB3FHb3FHc2HN2A43R1a3R1b3HL23HL5S3FHb3R1a3R1bS2N43FHb3R1b3HL5S2N43FHb3R1b3HL5S3Bk23FHb3R1b3HL52LO3BOT3ATR4SPAB2HN2A43R1a3HL2".
assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (ESH8 : shad (FF + 64) - shad FF = 8) by (rewrite !shad_div; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AHy) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  destruct HC as [Z0|(p & BA & BN & Hbk & Bk1 & Bk2)]; [exfalso; lia|].
  destruct (AI_block AI _ _ _ _ _ _ _ _ AHy ltac:(right; exact Hbk)) as (HN & (R1 & R2 & R3 & R4) & RGA & RGS & _ & _ & _ & (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6)).
  pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
  destruct (block_hullR RNG my BA BN RLO RHI ltac:(lia) A1 A2 A3 A4 ltac:(lia) A5 A6) as (HR1 & HW1 & HL1 & HL2 & HL3 & HL4 & HL5 & HL6).
  pose proof (FFD _ Hbk) as BKF. cbn [ab_addr ab_size] in BKF.
  assert (US : unpoisoned my S (S + zlen bl)).
  { eapply hcoverA_unpoisoned; [exact AHy| right; exists p, BA, BN; split; [right; exact Hbk| split; [exact Bk1| exact Bk2]]| lia]. }
  (* [comment removed for export] *)
  assert (UD : unpoisoned my (FF + 32) (FF + 32 + zlen bl)).
  { unfold GSH4 in SHF.
    lazymatch type of SHF with rw_cells _ _ _ [?a0'; ?a1'; ?a2'; ?a3'; ?b4; ?c5; ?c6; ?c7] =>
      change [a0'; a1'; a2'; a3'; b4; c5; c6; c7] with ([a0'; a1'; a2'; a3'] ++ [b4] ++ [c5; c6; c7]) in SHF end.
    pose proof (proj1 (rw_cells_appA _ _ _ _ _) SHF) as [_ X]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X.
    apply (c1k_unpoisonedR my (FF + 32) 4 (zlen bl)); [| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| lia| lia| unfold KEND in *; lia].
    replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact X|].
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  pose proof (proj2 SHF) as WSH. cbn [cells_size csize Nat.add GSH4 length] in WSH.
  eapply (amemcpy_specZ (FF + 32) S (zlen bl) (SPAz SPV) RNG) with (lo := lo) (RLO1 := hull_loR BA) (RHI1 := hull_hiR BA BN) (RLO2 := FF) (RHI2 := FF + 64);
    [ exact MI | lia | exact STL | lia | unfold KHIGH; lia
    | exact GOT | exact RIC | exact SHB | exact INI | exact LAY | exact REAL
    | exact PL | rewrite length_map; lia | exact DST
    | lia | lia | lia
    | apply ablk_app_blk; [eapply ablk_sub; [exact R1| lia| lia]| lia]
    | apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]
    | exact US | exact UD | lia
    | repeat split; try lia; unfold KEND in *; lia
    | repeat split; try lia; unfold KEND in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
    | exact HW1 | rewrite ESH8; rewrite ESH; exact WSH
    | exact RI | eapply rng_sub'; [exact RSTK| lia] | eapply rng_sub'; [exact RGA| lia] | eapply rng_sub'; [exact RFF| lia]
    | exact HR1 | rewrite ESH8; exact RSFF
    | reflexivity | reflexivity | reflexivity ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="fflag FFLAG FREL SM0 GIMG"] Theorem gfhaA : gfhaA_stmt AI rng_fs.
Proof.
  unfold gfhaA_stmt, gfhaA_stmt_at.
  intros L RNG ra SPV gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB S bl ZF lo zj
         AH LE0 LBH BUF NB HC ZFC FCZ ZA SHZ GSH ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS RZF RSZF FMT -> -> ->.
  cbv beta in FMT. subst a3.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  unfold AFI_STACK in LO.
  pose proof (spa_propsA SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  (* [comment removed for export] *)
  destruct (fcellA_block _ _ _ _ FCZ) as (bz & BZ & BZ1 & BZ2).
  pose proof (LBH bz BZ) as BZH. pose proof (ablk_lin _ _ BZH) as (BZa & BZb & BZc & BZd). unfold AIMG_HI in BZa.
  Local Ltac2 Set LiaHints.tbl := fun () => "03]0?11801222823.18611801222825.20711801225127.18411801225129.20511803468327.18311803468329.20412993055350.13712993104880.16112993104882.17812993383539.24012995103219.17512995103229.19212995150419.97 12995219153.15312995333105.15012995333106.19012995333116.21113618615237.17214034762132.18914434989683.15414434989683.16814434989683.18514434989683.20614961409122.14515947691432.18216073608672.14616242798658.18616242798658.20316584884374.18916787775571.2011687374407.200 17148843337.18917294153783.10217345421797.14617991072641.19217991072655.17517991086127.97 17991154861.15317991301504.21117991301517.15017991301518.19017997379594.13717997708815.24018069523012.22218071525072.22218630334354.20019072016889.15919072016891.17619318355690.21419613120295.17519613120297.19219613265925.15319628012706.13720146148781.15420146148781.16820146148781.18520146148781.20620667538766.15920928615732.19920928615738.18221445010926.13321445438301.18921455905371.10222126696933.14922706556809.18922706556809.19022706556809.21022706556809.21122706556809.24022706556809.24123709141382.15424359320740.16024359320742.17724359320743.17624359320745.193246310705.189  24663435111.14225069433766.20125069433768.18425069433771.16625069433771.21125073798310.20625073798312.18925073798315.21525073798955.21425075896102.20525075896104.18825075906086.20225075906088.18525075906091.16725075906091.21225075906214.20325075906216.18625188966468.10225191180225.17825191180227.16126492779925.15227150168169.21927478582164.20427478582170.18727478761753.21327860477445.10228212502475.18928292029762.21428573892092.15528573892092.15628748943648.97 29760227832.10229786411508.14929786561494.20229786561496.18129786661642.16529786692826.20029788740059.14529790658906.16429928407609.15429928407609.16829928407609.18529928407609.18629928407609.20329928407609.20630772171805.15930772171807.17632163684933.20032230998831.21732243240206.14832775280396.15432775280396.16832775280396.18532775280396.18632775280396.20334327554358.18134327554360.20234327667482.14934340295604.16434891932807.15435084363323.24035084607928.16135084607930.17835094962612.21135094962617.15035094962618.19035095177243.97 35497641708.15435497641708.16835497641708.18535497641708.20637138285618.92 37779223993.20938161657970.14038326578485.18242006895035.19942153132482.18942878255082.18642878255082.20342989664339.1474461571599.149 4461575656.149 45416970812.18945643317633.21946352729980.18948875598066.18949747972712.14955200825157.17855200825159.16156170235708.97 56170548883.21156170548893.19056170548894.15056184835741.17856184835743.16156184917785.13756184995870.18956185112860.24057015865742.18957052433661.16257052433661.17957052433661.22257481071351.20657481071353.18557628700040.17057628700040.17157628700040.19257628700040.20957628700040.21857749819890.14257802544315.16859148144883.14159219390989.20959221620017.23159308583409.14959308583409.19159308583409.21059308583542.14959359724890.16459361524823.19959361524825.18259372355544.18159731800039.14259897630646.20159946373524.23459948476564.23659948477204.23759961234452.23360268869778.23560595102003.1546064129253.150 6064129254.190 6064129256.211 6066078567.240 6066457189.189 60683506292.19460683506298.17762993084019.20163625389838.18963848742745.97 63868847056.14664305157740.1466453983753.201 65119321526.20966460724116.17766460724122.1946799435120.201 68213739677.15168213739677.16968213739677.19168213739677.2126873637559.189 822107497.189  822580331.240  837145572.211  837145577.150  837145578.190  8511854442.106 9608221839.145 9692325712.201 9795755140.133 00000900B00o01P02=02^02f02n03603F03N03V03Z03b03j04204:05`06106k07e08_09Y0:60:S0:[0;@0;e0=40=i0>>0>O0?00?10?:0?C0?H0?Q0?Z0?c0?l0@50@F0AO0C=0C>0Cf0DN0E>0E?0E@0EA0EB0F=0G80H30Hn0I30I`0JM0Jf0KK0Kd0Ki0LY0MI0Mm0NQ0OA0P10Pa0QI0R10RY0SA0Sn0T50Ta0UM0V:0Vg0WS0X?0Y]0[Z0\F0]20]^0^J0_70_d0a20b@0bE0bN0bW0cD0d30d\0eE0gB0gg0h80he0iU0jE0jF0jo0k40k90k>0kG0kT0kY0k^0lC0lh0mM0n20nW0o<0od10L10l11<11D11L11T11\12G13213K13d14=14V15;15e16?16Y17317M17g18=18B18G18L18Q18R19G19a19f19k1:P1;81;`1<L1<Q1<V1<c1=31=@1=Q1>>1>F1>N1>S1>\1>e1>n1?71?@1?I1@:1@K1@X1@`1@h1A81AA1AJ1B:1Bj1CY1DH1E81ER1FF1F`1G51GJ1GR1GZ1Gb1Gm1H21H:1HB1HG1HL1II1J61K`1M>1Mk1OU1P=1PF1PO1PX1Pi1Q:1Qb1RJ1S?1Sl1Sm1T21TZ1V<1VI1W11WY1Wi1X11X=1XE1XM1XZ1Xk1Y<1YE1YN1YW1Z81ZB1ZR1ZSS3FHb3AVSS3FHb3AVSS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSF3BZ13BZa3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSFS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSF3BZ13BZa3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSFS2LO3FHbS2LO3FHbS2LO3FHbS2LO3FHb3R1b3SZ5S2LO3FHbS2LO3FHbS2LOS2LO3FHbS2LO3FHbS2LO3FHbS2LO3FHbS3Bk13Bk22Z12Z22ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3FHa3FHb3BZF3BSF3AVS3AVZ2HN3R1b1DS3FHb3R1b3SZ13SZ5S2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3FHb2HrS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3FHb2HrS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3FHb2HrS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3FHb2HrS3ATR3BZ13BZ23BZc3F643FHa3FHcS3BZ13BZ23BZF3AVS3AVZ3SZ33SZ4S2NB3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3FHb3R1b3SZ13SZ23SZ33SZ43SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ13SZ23SZ5S3Bk13Bk23FHb3R1b3SZ5S3FHb3R1b3SZ33SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZaFS3BOT3FHbS3BOT3FHbS3BOTS3BOT3FHbS3BOT3FHbS3BOT3FHbS3BOT3FHbS3BOT3FHbS3BOT3FHb3R1b3SZ5S2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23FHb2HN3R1b3SZ52Ha3BZuS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3FHa3FHb3BZF3BSF3AVS3AVZ2HN3R1b4SEPZ3SZ13SZ23SZ43SZ52HaFS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b3SZ52HrFFFFS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3F643FHbS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3F643FHbS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3F643FHbS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZa3F643FHbS3FHbS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3BZ13BZa3FHbS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3BZ13BZa3FHbS3BOT2LO3SPT3ATR3LY34SPABS3BOT2LO3SPT3ATR3LY34SPAB3FHb3R1b3SZ5S3BOT2LO3SPT3ATR3LY34SPABS3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSF2Hx3BZ13BZa3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSF2Hx3BZ13BZa3FHcS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3FHb3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ52HxS3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ52HxS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3BI13BI22HaS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b3SZ5S3FHb1DS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSFS3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23FHb3BZF3BSF3AVS3AVZ2HN3R1b3SZ13SZ23SZ43SZ5S3Bk22ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3BZc3F643FHa3FHb3FHc3BZF3BSF3AVS3AVZ2Hn2HN3R1b3R1c3SZ13SZ23SZ43SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSFS3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ5S2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3FHb3BZF3BSF3AVS3AVZ2HnS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3FHb3BZF3BSF3AVS3AVZ2HnS3BOTS3BOT3FHbS3BOT3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSFS3Bk22ZA3BOT2LO3ATR4SPAB3BZ23FHc3BSF2Hn3R1c3BZuS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHcS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHcS3Bk22ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3BZc3F643FHa3FHb3FHc3BZF3BSF3AVS3AVZ2Hn2HN3R1b3R1c3SZ13SZ23SZ43SZ5S3BOT2LO3SPT3ATR3LY13LY44SPAB3BZ13BZaS3FHb3R1b3SZ53SZ6S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b3SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSF2HxFS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3BZ13BZaS3FHbS3FHbS3FHbS3FHb3R1bS3FHb3R1b3SZ5S3FHbS3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3Bk13Bk23BZ13BZ23BZF3AVS3AVZ2R4S3FHb2Hn3R1b3SZ5S3FHb2HnS3FHb2HrS3FHb2HrS3FHb2HrS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2Hn2HrS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2Hn2HrS3BZ13BZ23F643BZF3AVS3AVZS3BZ13BZ23F643BZF3AVS3AVZS3BZ13BZ23F643BZF3AVS3AVZS3BZ13BZ23F643BZF3AVS3AVZS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHbS3SPT3LY34SPAB3BZ13BZa3FHb3R1b3SZ13SZ23SZ5S3SPT3LY34SPAB3BZ13BZa3FHbS3SPT3LY34SPAB3BZ13BZa3FHbS3SPT3LY34SPAB3BZ13BZa3FHbS3SPT3LY34SPAB3BZ13BZa3FHbS3SPT3LY34SPAB3BZ13BZa3FHbS3SPT3LY34SPAB3BZ13BZaS3FHbS3FHbS3FHbS3FHbSS3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3BZ13BZa3FHb3R1b3SZ5S3SPT3LY34SPAB3BZ13BZa3FHbS3FHbS3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHb3R1b3SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HrS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HrS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZ23BZa3FHb2HaS3FHbS3FHbS3FHb3R1b3SZ5S2ZA3BZ13BZ23BZuS3FHb3R1b3SZ5S3FHb3R1b3SZ23SZ5S3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3BZ13BZa3FHbS3FHb2HnS3FHb2HnS3SPTS3SPT3FHbS3SPT3FHbS3SPT3FHbS3SPT3FHbS3SPT3FHbS3SPT3FHbS3BOT2LO3SPT3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b3SZ5S3SPT3FHb3R1b3SZ5S3FHb3R1b3SZ5S3FHb2HaS3FHb2HaS3FHb3R1b3SZ52HaS3FHb3AVSS3FHb3AVSS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2Hn2HxS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3FHc2Hn2HxS3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ52HxS3SPT3LY34SPAB3BZ13BZa3FHbS3Bk13Bk23BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b2HaS3SPT3LY34SPAB3BZ13BZa3FHbS3BZ13BZ23FHb3R1b3SZ5S3BZ13BZ23FHb3R1b3SZ5S3FHb2HRS3FHb2HRS3FHb2HRS2Z03FHb2HnS3FHbS3FHb2HnS3FHb2HnS3FHbS3FHbS3Bk23BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b3R1c3SZ13SZ23SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ5S2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3F643FHa3FHb3BZF3BSF3AVS3AVZ2HN3R1b3SZ13SZ23SZ43SZ5S2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23FHb3BZF3BSF3AVS3AVZ2HN3R1b3SZ13SZ23SZ43SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ5S2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23BZa3F643FHa3FHb3BZF3BSF3AVS3AVZ2HN3R1b3SZ13SZ23SZ43SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HrS3BZ13FHbS3BZ13FHbS3BZ13FHbS3BZ13FHb3R1b3SZ5S3BZ13FHb3R1b3SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb3R1b3SZ13SZ23SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ23BZc3FHb3R1b3SZ5FS3FHbS3BOT2LO3ATR3LY13LY44SPAB2BB3BZ13BZa3FHbS2ZA3BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323BZ13BZ23FHb3BZF3BSF3AVS3AVZ2HN3R1b3SZ13SZ23SZ43SZ53BZuS3FHb3R1b3SZ5S3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZa3FHb2HnS3FHb2Hn3R1b3SZ5S3FHb2HaS3FHb3R1b2HaS3FHb2HaS3FHb2HaS3FHb3R1b3SZ5S3BZ23FHb3R1b3SZ5S3BZ23FHb3R1b3SZ5S3BZ23FHbS3BZ23FHbS3BZ23FHbS3BOT2LO3ATR3LY13LY44SPAB3BZ13BZaS4SPAB3FHbS3FHb2HS3R1b3SZ5S".
assert (ESHZ : shad ZF = Z.shiftr ZF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & _ & _ & SHB & SUA & _).
  destruct (gfha_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gfha_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| unfold KEND; lia| unfold AFI_STACK; lia| lia]. }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear GOT SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (MG1 : magree bsegs (aclient_addr CI LB SPV) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SPV (SPV - 144) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  clear MU1 WM1.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof SM0 as SMC. unfold stack_malloc_0_stmtk, sm_stmtk in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPAz SPV)) by lia;
      first [exact AH1| exact LE0| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF).
  rewrite ?(unsigned_lit (SPAz SPV)) in ST2, HPR2 by lia.
  retlitA.
  change (Z.to_nat (64 - 32)) with 32%nat in FFC2. change (64 / 8) with 8 in RSFF. cbn [repeat] in SHF2.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  assert (NFB : ~ In (FB0 FF) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
  assert (FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB0 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. lia. }
  pose proof (FFD bz BZ) as BZF.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  assert (MG2 : magree bsegs (aclient_addr CI LB SPV) m m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
  clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1.
  (* [comment removed for export] *)
  destruct (gfha_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply gfha_hdr with (lo := lo);
    first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F64
          | exact RFF| exact RSFF| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac].
  intros m3 j24 MU3 WM3 MI3 FRA3 FFC3 SHF3. cbv beta.
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  pose proof (app_vs_shadow FF 64 (Z.shiftr FF 3 + 2147450880) 8 FH (proj1 BSF) (proj2 BSF)) as AVS.
  pose proof (app_vs_shadow (ab_addr bz) (ab_size bz) (Z.shiftr FF 3 + 2147450880) 8 BZH (proj1 BSF) (proj2 BSF)) as AVZ.
  assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
  assert (LBH3 : forall b, In b (FB0 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
  assert (MG3 : magree bsegs (aclient_addr CI LB SPV) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)|].
    split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha);
            rewrite ESH; lia| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk bsegs m3 lo (SPAz SPV))
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk bsegs m3 (SPAz SPV + 32) (SPV + -96))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  clear MG2 FRB2 FRA2 STG2 ST2 MI2 AH2 FFC2 SHF2 GPC2.
  (* [comment removed for export] *)
  assert (CLZ : forall a, ZF <= a < ZF + 48 -> aclient_addr CI LB SPV a).
  { intros a Ha. apply (cl_block CI LB SPV bz a BZ). lia. }
  (* [comment removed for export] *)
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply gfha_disp; first [exact MI3| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold KEND; lia | unfold AFI_STACK; lia | lia | idtac].
  { (* [comment removed for export] *)
    intros r Hr.
    unfold GHDR in FFC3.
    change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800d8); CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 FF))])
      with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800d8)] ++ [CB 32 junk] ++ [C8 (Z_to_bv 64 (fflag L 0 FF))]) in FFC3.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [_ FF563]. cbn [cells_size csize Nat.add] in FF563.
    replace (FF + Z.of_nat 24 + Z.of_nat 32) with (FF + 56) in FF563 by lia.
    assert (ZF3 : rw_cells bsegs m3 ZF [CB 48 zj]).
    { eapply rw_cells_magree; [exact MG3| exact ZFC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLZ. lia. }
    apply (rw_cells_split_CB bsegs _ _ [] 48 zj [] [24; 4; 20]%nat) in ZF3; [| reflexivity]. cbn [app mk_CB_cells] in ZF3.
    eapply gfha_closeA with (bz := bz);
      [ exact AH3 | exact LBH | exact FFD | exact BZ | lia | lia
      | eapply magree_mono; [exact MG3| intros a [Ha _]; exact Ha]
      | exact ZF3
      | intros HR; exfalso; destruct Hr as [[-> _]|[-> _]]; vm_compute in HR; lia
      | exact SHF3 | exact FF03 | exact FF563 | exact FRB3 | exact FRA3 | exact STL3 | exact STG3 | exact MI3
      | exact FH | exact FC | exact F64 | exact RFF | exact RSFF | exact SP16
      | unfold KEND; lia | unfold AFI_STACK; lia | lia
      | eapply rng_sub'; [exact RSTK| lia] | exact RI ]. }
  { (* [comment removed for export] *)
    intros Hn HS.
    assert (BLK : exists b, In b LB /\ ab_addr b <= S /\ S + zlen bl <= ab_addr b + ab_size b) by (apply hcoverA_block; [exact HC| lia]).
    destruct BLK as (bi & BI & BI1 & BI2).
    assert (CLS : forall a, S <= a < S + zlen bl -> aclient_addr CI LB SPV a).
    { intros a Ha. apply (cl_block CI LB SPV bi a BI). lia. }
    (* [comment removed for export] *)
    eapply evtF_cut; [| intros ms' Hms; exact Hms].
    eapply gfha_sm1 with (lo := lo);
      first [exact SHF3| exact FFC3| exact MI3| exact FH| exact FC| exact F64| exact RFF| exact RSFF
            | exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac].
    intros m4 hw j8 j20 MU4 WM4 MI4 SHF4 FF04 FF244 FF564. cbv beta.
    assert (AH4 : AHEAP AI L RNG st (FB0 FF :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|].
      constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                    change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]|].
      constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]| constructor]. }
    assert (MG4 : magree bsegs (aclient_addr CI LB SPV) m m4).
    { eapply magree_munch_step; [exact MG3| exact MU4| exact WM4|]. intros a Ha. cbn.
      split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia|].
      split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 ltac:(cbn; lia)) as FRB4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU4 WM4 ltac:(cbn; lia)) as FRA4.
    assert (STL4 : stk bsegs m4 lo (SPAz SPV)) by (eapply stk_transport; [exact STL3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    assert (STG4 : stk bsegs m4 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    clear MU4 WM4 FRB3 FRA3 STL3 STG3 SHF3 FFC3 MI3 AH3 MG3.
    (* [comment removed for export] *)
    change [CB 8 j8; C4 hw; CB 20 j20] with ([CB 8 j8] ++ [C4 hw] ++ [CB 20 j20]) in FF244.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FF244. destruct FF244 as [_ HB4]. cbn [cells_size csize Nat.add] in HB4.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in HB4. destruct HB4 as [HB4 _]. cbn [cells_size csize Nat.add] in HB4.
    replace (FF + 24 + Z.of_nat 8) with (FF + 32) in HB4 by lia.
    eapply rw_cells_recast with (cs' := [CB (Z.to_nat (zlen bl)) (firstn (Z.to_nat (zlen bl)) (le4 hw)); CB (4 - Z.to_nat (zlen bl))%nat (skipn (Z.to_nat (zlen bl)) (le4 hw))]) in HB4;
      [| cbn [cells_wf cell_wf]; rewrite length_firstn, length_skipn, length_le4; repeat split; lia
       | cbn [cells_bytes cbytes]; rewrite ?app_nil_r, firstn_skipn; reflexivity
       | cbn [cells_size csize]; lia ].
    lazymatch type of HB4 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in HB4 end.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in HB4. destruct HB4 as [DST4 RST4]. cbn [cells_size csize] in RST4.
    match type of RST4 with rw_cells _ _ ?a _ => replace a with (FF + 32 + zlen bl) in RST4 by lia end.
    assert (BUF4 : buf_atA m4 S bl).
    { split; [| exact PLR]. eapply bytes_at_magree; [exact MG4| exact PL|]. rewrite length_map. intros a Ha. apply CLS. lia. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply gfha_mcA;
        [ exact AH4 | exact LBH | exact FFD | exact BUF4 | lia | exact HC | exact DST4 | exact SHF4 | exact STL4 | exact MI4
        | exact FH | exact FC | exact F64 | exact RFF | exact RSFF | exact SP16 | unfold KEND; lia | unfold AFI_STACK; lia | lia
        | eapply rng_sub'; [exact RSTK| lia] | exact RI ]. }
    cbv beta. intros ms' PO. unfold amemcpyZ_post in PO.
    destruct PO as (w5 & w6 & w7 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & w28 & w29 & w30 & w31 & m5 & -> & MU5 & WM5 & MI5 & STL5 & DST5 & SRC5).
    retlitA.
    assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
    { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]| constructor]. }
    assert (MG5 : magree bsegs (aclient_addr CI LB SPV) m m5).
    { eapply magree_munch_step; [exact MG4| exact MU5| exact WM5|]. intros a Ha. cbn.
      split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
      split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB4 MU5 WM5 ltac:(cbn; lia)) as FRB5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA4 MU5 WM5 ltac:(cbn; lia)) as FRA5.
    pose proof (rw_cells_transport _ _ _ _ _ _ SHF4 MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add GSH4 length]; lia)) as SHF5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF04 MU5 WM5 ltac:(cbn; lia)) as FF05.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF564 MU5 WM5 ltac:(cbn; lia)) as FF565.
    pose proof (rw_cells_transport _ _ _ _ _ _ RST4 MU5 WM5 ltac:(cbn; lia)) as RST5.
    assert (STG5 : stk bsegs m5 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG4| exact MU5| exact WM5| intros x Hx; left; cbn; lia]).
    clear MU5 WM5 FRB4 FRA4 SHF4 FF04 FF564 RST4 DST4 STG4 STL4 MI4 AH4 MG4 BUF4.
    (* [comment removed for export] *)
    assert (HB5 : rw_cells bsegs m5 (FF + 32) ([CB (Z.to_nat (zlen bl)) (map (Z_to_bv 8) bl)] ++ [CB (4 - Z.to_nat (zlen bl))%nat (skipn (Z.to_nat (zlen bl)) (le4 hw))])).
    { apply (proj2 (rw_cells_appA _ _ _ _ _)). split; [exact DST5|]. cbn [cells_size csize].
      match goal with |- rw_cells _ _ ?a _ => replace a with (FF + 32 + zlen bl) by lia end. exact RST5. }
    eapply rw_cells_recast with (cs' := [CB 4 (map (Z_to_bv 8) bl ++ skipn (Z.to_nat (zlen bl)) (le4 hw))]) in HB5;
      [| cbn [cells_wf cell_wf]; rewrite length_app, length_map, length_skipn, length_le4; split; [lia| exact I]
       | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity
       | cbn [cells_size csize app]; lia ].
    clear DST5 RST5.
    (* [comment removed for export] *)
    eapply evtF_cut; [| intros ms' Hms; exact Hms].
    eapply gfha_sm2 with (lo := lo);
      first [exact SHF5| exact HB5| exact MI5| exact FH| exact FC| exact F64| exact RFF| exact RSFF
            | exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac| idtac].
    + (* [comment removed for export] *)
      intros m6 MU6 WM6 MI6 SHF6 HB6.
      assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
      { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|].
        constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                      change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
      assert (MG6 : magree bsegs (aclient_addr CI LB SPV) m m6).
      { eapply magree_munch_step; [exact MG5| exact MU6| exact WM6|]. intros a Ha. cbn.
        split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia| exact I]. }
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB5 MU6 WM6 ltac:(cbn; lia)) as FRB6.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRA5 MU6 WM6 ltac:(cbn; lia)) as FRA6.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF05 MU6 WM6 ltac:(cbn; lia)) as FF06.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF565 MU6 WM6 ltac:(cbn; lia)) as FF566.
      assert (STL6 : stk bsegs m6 lo (SPAz SPV)) by (eapply stk_transport; [exact STL5| exact MU6| exact WM6| intros x Hx; left; cbn; lia]).
      assert (STG6 : stk bsegs m6 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG5| exact MU6| exact WM6| intros x Hx; left; cbn; lia]).
      assert (ZF6 : rw_cells bsegs m6 ZF [CB 48 zj]).
      { eapply rw_cells_magree; [exact MG6| exact ZFC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLZ. lia. }
      apply (rw_cells_split_CB bsegs _ _ [] 48 zj [] [24; 4; 20]%nat) in ZF6; [| reflexivity]. cbn [app mk_CB_cells] in ZF6.
      eapply gfha_closeA with (bz := bz);
        [ exact AH6 | exact LBH | exact FFD | exact BZ | lia | lia
        | eapply magree_mono; [exact MG6| intros a [Ha _]; exact Ha]
        | exact ZF6
        | intros HR; exfalso; vm_compute in HR; lia
        | exact SHF6 | exact FF06 | exact FF566 | exact FRB6 | exact FRA6 | exact STL6 | exact STG6 | exact MI6
        | exact FH | exact FC | exact F64 | exact RFF | exact RSFF | exact SP16
        | unfold KEND; lia | unfold AFI_STACK; lia | lia
        | eapply rng_sub'; [exact RSTK| lia] | exact RI ].
    + (* [comment removed for export] *)
      intros m6 MU6 WM6 MI6 SHF6 HB6.
      assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
      { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|].
        constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]| constructor]. }
      assert (MG6 : magree bsegs (aclient_addr CI LB SPV) m m6).
      { eapply magree_munch_step; [exact MG5| exact MU6| exact WM6|]. intros a Ha. cbn.
        split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB5 MU6 WM6 ltac:(cbn; lia)) as FRB6.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRA5 MU6 WM6 ltac:(cbn; lia)) as FRA6.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF05 MU6 WM6 ltac:(cbn; lia)) as FF06.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF565 MU6 WM6 ltac:(cbn; lia)) as FF566.
      assert (STL6 : stk bsegs m6 lo (SPAz SPV)) by (eapply stk_transport; [exact STL5| exact MU6| exact WM6| intros x Hx; left; cbn; lia]).
      assert (STG6 : stk bsegs m6 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG5| exact MU6| exact WM6| intros x Hx; left; cbn; lia]).
      clear MU6 WM6 FRB5 FRA5 FF05 FF565 STL5 STG5 SHF5 HB5 MI5 AH5 MG5.
      eapply rw_cells_recast with (cs' := [CB (Z.to_nat (zlen bl)) (firstn (Z.to_nat (zlen bl)) (le4 (Z_to_bv 64 0x184d2a50)));
                                             CB (4 - Z.to_nat (zlen bl))%nat (skipn (Z.to_nat (zlen bl)) (le4 (Z_to_bv 64 0x184d2a50)))]) in HB6;
        [| cbn [cells_wf cell_wf]; rewrite length_firstn, length_skipn, length_le4; repeat split; lia
         | cbn [cells_bytes cbytes]; rewrite ?app_nil_r, firstn_skipn; reflexivity
         | cbn [cells_size csize]; lia ].
      lazymatch type of HB6 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in HB6 end.
      apply (proj1 (rw_cells_appA _ _ _ _ _)) in HB6. destruct HB6 as [DST6 RST6]. cbn [cells_size csize] in RST6.
      match type of RST6 with rw_cells _ _ ?a _ => replace a with (FF + 32 + zlen bl) in RST6 by lia end.
      assert (BUF6 : buf_atA m6 S bl).
      { split; [| exact PLR]. eapply bytes_at_magree; [exact MG6| exact PL|]. rewrite length_map. intros a Ha. apply CLS. lia. }
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply gfha_mcA;
        [ exact AH6 | exact LBH | exact FFD | exact BUF6 | lia | exact HC | exact DST6 | exact SHF6 | exact STL6 | exact MI6
        | exact FH | exact FC | exact F64 | exact RFF | exact RSFF | exact SP16 | unfold KEND; lia | unfold AFI_STACK; lia | lia
        | eapply rng_sub'; [exact RSTK| lia] | exact RI ]. }
      cbv beta. intros ms' PO. unfold amemcpyZ_post in PO.
      destruct PO as (v5 & v6 & v7 & b1' & b2' & b3' & b4' & b5' & b6' & b7' & v28 & v29 & v30 & v31 & m7 & -> & MU7 & WM7 & MI7 & STL7 & DST7 & SRC7).
      retlitA.
      assert (AH7 : AHEAP AI L RNG st (FB0 FF :: LB) m7).
      { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|].
        constructor; [cbn; left; left; lia|].
        constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]| constructor]. }
      assert (MG7 : magree bsegs (aclient_addr CI LB SPV) m m7).
      { eapply magree_munch_step; [exact MG6| exact MU7| exact WM7|]. intros a Ha. cbn.
        split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
        split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB6 MU7 WM7 ltac:(cbn; lia)) as FRB7.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRA6 MU7 WM7 ltac:(cbn; lia)) as FRA7.
      pose proof (rw_cells_transport _ _ _ _ _ _ SHF6 MU7 WM7 ltac:(cbn [disjoint_from cells_size csize Nat.add GSH4 length]; lia)) as SHF7.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF06 MU7 WM7 ltac:(cbn; lia)) as FF07.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF566 MU7 WM7 ltac:(cbn; lia)) as FF567.
      pose proof (rw_cells_transport _ _ _ _ _ _ RST6 MU7 WM7 ltac:(cbn; lia)) as RST7.
      assert (STG7 : stk bsegs m7 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG6| exact MU7| exact WM7| intros x Hx; left; cbn; lia]).
      clear MU7 WM7 FRB6 FRA6 SHF6 FF06 FF566 RST6 DST6 STG6 STL6 MI6 AH6 MG6 BUF6.
      assert (HB7 : rw_cells bsegs m7 (FF + 32) ([CB (Z.to_nat (zlen bl)) (map (Z_to_bv 8) bl)]
                                                ++ [CB (4 - Z.to_nat (zlen bl))%nat (skipn (Z.to_nat (zlen bl)) (le4 (Z_to_bv 64 0x184d2a50)))])).
      { apply (proj2 (rw_cells_appA _ _ _ _ _)). split; [exact DST7|]. cbn [cells_size csize].
        match goal with |- rw_cells _ _ ?a _ => replace a with (FF + 32 + zlen bl) by lia end. exact RST7. }
      eapply rw_cells_recast with (cs' := [CB 4 (map (Z_to_bv 8) bl ++ skipn (Z.to_nat (zlen bl)) (le4 (Z_to_bv 64 0x184d2a50)))]) in HB7;
        [| cbn [cells_wf cell_wf]; rewrite length_app, length_map, length_skipn, length_le4; split; [lia| exact I]
         | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity
         | cbn [cells_size csize app]; lia ].
      clear DST7 RST7.
      (* [comment removed for export] *)
      eapply evtF_cut; [| intros ms' Hms; exact Hms].
      eapply gfha_sm3 with (lo := lo);
        first [exact SHF7| exact HB7| exact MI7| exact FH| exact FC| exact F64| exact RFF| exact RSFF
              | exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia] | unfold AFI_STACK; lia | unfold KEND; lia | lia | idtac].
      intros m8 r8 x10' x11' Hr8 MU8 WM8 MI8 SHF8 HB8.
      assert (AH8 : AHEAP AI L RNG st (FB0 FF :: LB) m8).
      { eapply (AI_frame AI); [exact AH7| exact MU8| exact WM8|].
        constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                      change (2 ^ 3) with 8; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
      assert (MG8 : magree bsegs (aclient_addr CI LB SPV) m m8).
      { eapply magree_munch_step; [exact MG7| exact MU8| exact WM8|]. intros a Ha. cbn.
        split; [intros Hr; refine (shadow_not_clientN CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _ Ha); rewrite ESH; lia| exact I]. }
      pose proof (rw_cells_transport _ _ _ _ _ _ FRB7 MU8 WM8 ltac:(cbn; lia)) as FRB8.
      pose proof (rw_cells_transport _ _ _ _ _ _ FRA7 MU8 WM8 ltac:(cbn; lia)) as FRA8.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF07 MU8 WM8 ltac:(cbn; lia)) as FF08.
      pose proof (rw_cells_transport _ _ _ _ _ _ FF567 MU8 WM8 ltac:(cbn; lia)) as FF568.
      assert (STL8 : stk bsegs m8 lo (SPAz SPV)) by (eapply stk_transport; [exact STL7| exact MU8| exact WM8| intros x Hx; left; cbn; lia]).
      assert (STG8 : stk bsegs m8 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG7| exact MU8| exact WM8| intros x Hx; left; cbn; lia]).
      assert (ZF8 : rw_cells bsegs m8 ZF [CB 48 zj]).
      { eapply rw_cells_magree; [exact MG8| exact ZFC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLZ. lia. }
      apply (rw_cells_split_CB bsegs _ _ [] 48 zj [] [24; 4; 20]%nat) in ZF8; [| reflexivity]. cbn [app mk_CB_cells] in ZF8.
      eapply gfha_closeA with (bz := bz);
        [ exact AH8 | exact LBH | exact FFD | exact BZ | lia | lia
        | eapply magree_mono; [exact MG8| intros a [Ha _]; exact Ha]
        | exact ZF8
        | intros HR; exfalso; destruct Hr8 as [-> | ->]; vm_compute in HR; lia
        | exact SHF8 | exact FF08 | exact FF568 | exact FRB8 | exact FRA8 | exact STL8 | exact STG8 | exact MI8
        | exact FH | exact FC | exact F64 | exact RFF | exact RSFF | exact SP16
        | unfold KEND; lia | unfold AFI_STACK; lia | lia
        | eapply rng_sub'; [exact RSTK| lia] | exact RI ]. }
  { (* [comment removed for export] *)
    intros Hn HS.
    unfold GHDR in FFC3.
    change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800d8); CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 FF))])
      with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800d8)] ++ [CB 32 junk] ++ [C8 (Z_to_bv 64 (fflag L 0 FF))]) in FFC3.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [_ FF563]. cbn [cells_size csize Nat.add] in FF563.
    replace (FF + Z.of_nat 24 + Z.of_nat 32) with (FF + 56) in FF563 by lia.
    (* [comment removed for export] *)
    destruct HC as [Z0|(p & BA & BN & Hbk & Bk1 & Bk2)]; [exfalso; lia|].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hbk) as (HN & (R1 & R2 & R3 & R4) & RGA & RGS & _).
    pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
    unfold shlen in RGS. rewrite Z.shiftr_div_pow2 in RGS by lia. change (2^3) with 8 in RGS.
    assert (SEPZ : S + zlen bl <= ZF \/ ZF + 48 <= S).
    { destruct FCZ as [(cls & FA0 & FN0 & Hfz & Z1 & Z2 & _) _].
      assert (NE : HB p BA BN <> mkABlock (ABFake cls) FA0 FN0) by (intros E; discriminate E).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH Hbk Hfz NE) as D. cbn in D. lia. }
    assert (CLS : forall a, S <= a < S + zlen bl -> aclient_addr CI LB SPV a).
    { intros a Ha. apply (cl_block CI LB SPV (HB p BA BN) a Hbk). cbn. lia. }
    (* [comment removed for export] *)
    assert (ZF3 : rw_cells bsegs m3 ZF [CB 48 zj]).
    { eapply rw_cells_magree; [exact MG3| exact ZFC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply CLZ. lia. }
    assert (FCZ3 : fcellA m3 LB ZF 48) by (eapply fcellA_mg; [exact MG3| intros a' Ha'; apply cl_shadow; right; right; exact Ha'| exact FCZ]).
    pose proof (proj2 FCZ3) as UNZ3.
    assert (SHZ3 : shullA RNG m3 LB ZF 48) by (eapply shullA_mg; [exact MG3| intros a' Ha'; apply cl_shadow; right; right; exact Ha'| exact SHZ]).
    destruct SHZ3 as (clsz & FA & FN & HFz & SZ1 & SZ2 & SZ3 & SZ4 & SZ5 & SZ6 & WRZ & RGZ).
    assert (ESHF : shad (FA + FN) - shad FA = FN / 8) by (rewrite !shad_div; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    (* [comment removed for export] *)
    pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC3. unfold artcells in RTC3.
    destruct RTC3 as (_ & GOT3 & RIC3 & REAL3 & SHB3 & _ & INI3 & LAY3 & _).
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU0. pose proof (wmono_refl bsegs m3) as WM0.
    unfold AFI_AMEMSET in *.
    zstep. zstep. zstep. zstep. zstep.
    clear MU0 WM0.
    eapply evtF_cut.
    { eapply (amemset_specZ ZF 48 0 (SPAz SPV) RNG) with (lo := lo) (RLO2 := FA) (RHI2 := FA + FN);
        [ exact MI3 | lia | exact STL3 | lia | unfold KHIGH; lia
        | exact GOT3 | exact RIC3 | exact SHB3 | exact INI3 | exact LAY3 | exact REAL3
        | exact ZF3 | lia
        | apply ablk_app_blk; [eapply ablk_sub; [exact BZH| lia| lia]| lia]
        | exact UNZ3 | lia | lia
        | repeat split; try lia; unfold KEND in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
        | rewrite ESHF; exact WRZ
        | exact RI | eapply rng_sub'; [exact RSTK| lia] | exact RZF | rewrite ESHF; exact RGZ
        | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros ms' PO. unfold amemsetZ_post in PO.
    destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m4 & -> & MU4 & WM4 & MI4 & STL4 & ZF4).
    retlitA. change (Z.to_nat 48) with 48%nat in ZF4.
    assert (AH4 : AHEAP AI L RNG st (FB0 FF :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|].
      constructor; [cbn; left; left; lia|].
      constructor; [cbn; right; left; exists bz; split; [right; exact BZ| cbn; lia]| constructor]. }
    assert (MG4 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (ZF <= a < ZF + 48)) m m4).
    { eapply magree_munch_step; [eapply magree_mono; [exact MG3| intros a [Ha _]; exact Ha]| exact MU4| exact WM4|].
      intros a [Ha Hz]. cbn. split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV - 2208) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
      split; [intros Hr; exact (Hz Hr)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 ltac:(cbn; lia)) as FRB4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU4 WM4 ltac:(cbn; lia)) as FRA4.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF03 MU4 WM4 ltac:(cbn; lia)) as FF034.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF563 MU4 WM4 ltac:(cbn; lia)) as FF564.
    pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add GSH1 length]; lia)) as SHF4.
    assert (STG4 : stk bsegs m4 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
    assert (USRC4 : unpoisoned m4 S (S + zlen bl)).
    { eapply hcoverA_unpoisoned; [exact AH4| apply hcoverA_cons_fake; right; exists p, BA, BN; split; [exact Hbk| split; [exact Bk1| exact Bk2]]| lia]. }
    assert (UZF4 : unpoisoned m4 ZF (ZF + 48)).
    { eapply unpoisoned_munch; [exact UNZ3| exact MU4|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
      pose proof BZH as BZu. unfold ablk, AIMG_HI, KLS in BZu. repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (GS4 : GSC m4).
    { apply gsc_of_gshA. eapply gshA_mg; [exact MG4| | exact GSH]. intros a Ha. split; [exact (gsh_client CI LB SPV a GIMG Ha)|].
      pose proof BZH as BZu. unfold ablk, AIMG_HI, KLS in BZu. lia. }
    assert (PL4 : bytes_at bsegs m4 S (map (Z_to_bv 8) bl)).
    { eapply bytes_at_magree; [exact MG4| exact PL|]. rewrite length_map. intros a Ha. split; [apply CLS; lia| lia]. }
    clear MU4 WM4 FRB3 FRA3 FF03 FF563 SHF3 STG3 STL3 MI3 AH3 MG3 ZF3 FCZ3 UNZ3 GOT3 RIC3 REAL3 SHB3 INI3 LAY3.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply gfha_mainA;
        first [ exact PLR | exact NB | exact ZA | exact SEPZ | exact USRC4 | exact UZF4 | exact RI | exact RIS | exact RZF | exact ZF4 | exact PL4 | exact GS4 | exact MI4
              | apply munch_refl | apply wmono_refl
              | rewrite <- ESHZ; exact RSZF
              | eapply rng_sub'; [exact RGA| lia]
              | rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; eapply rng_sub'; [exact RGS|]; rewrite shad_div; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
              | pose proof BZH as BZu; unfold ablk, KLS in BZu; unfold AIMG_HI, KLS, KHIGH in *; repeat split; lia
              | lia ]. }
    cbv beta. intros ms' PO. unfold QX in PO.
    destruct PO as (r & y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 & y21 & y22 & y25 & y26 & y28 & y29 & y30 & y31
                    & m5 & j1' & hb & j2' & -> & MU5 & WM5 & MI5 & ZF5 & RH).
    assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
    { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|].
      constructor; [cbn; right; left; exists bz; split; [right; exact BZ| cbn; lia]| constructor]. }
    assert (MG5 : magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (ZF <= a < ZF + 48)) m m5).
    { eapply magree_munch_step; [exact MG4| exact MU5| exact WM5|]. intros a [Ha Hz]. cbn. split; [intros Hr; exact (Hz Hr)| exact I]. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FRB4 MU5 WM5 ltac:(cbn; lia)) as FRB5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA4 MU5 WM5 ltac:(cbn; lia)) as FRA5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF034 MU5 WM5 ltac:(cbn; lia)) as FF035.
    pose proof (rw_cells_transport _ _ _ _ _ _ FF564 MU5 WM5 ltac:(cbn; lia)) as FF565.
    pose proof (rw_cells_transport _ _ _ _ _ _ SHF4 MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add GSH1 length]; lia)) as SHF5.
    assert (STL5 : stk bsegs m5 lo (SPAz SPV)) by (eapply stk_transport; [exact STL4| exact MU5| exact WM5| intros x Hx; left; cbn; lia]).
    assert (STG5 : stk bsegs m5 (SPAz SPV + 32) (SPV + -96)) by (eapply stk_transport; [exact STG4| exact MU5| exact WM5| intros x Hx; left; cbn; lia]).
    eapply gfha_closeA with (bz := bz);
      [ exact AH5 | exact LBH | exact FFD | exact BZ | lia | lia
      | exact MG5
      | exact ZF5
      | exact RH
      | exact SHF5 | exact FF035 | exact FF565 | exact FRB5 | exact FRA5 | exact STL5 | exact STG5 | exact MI5
      | exact FH | exact FC | exact F64 | exact RFF | exact RSFF | exact SP16
      | unfold KEND; lia | unfold AFI_STACK; lia | lia
      | eapply rng_sub'; [exact RSTK| lia] | exact RI ]. }
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="fflag FFLAG FREL SM0 GIMG"] Theorem gfhA : gfhA_stmt AI rng_fs.
Proof.
  unfold gfhA_stmt, gfhaA_stmt_at.
  intros L RNG ra SPV gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB S bl ZF lo zj
         AH LE0 LBH BUF NB HC ZFC FCZ ZA SHZ GSH ST BOT LO SPT SP16 MI TP RSTK RI RIS RFS RZF RSZF _ -> -> ->.
  unfold AFI_GFH.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep.
  pose proof gfhaA as G. unfold gfhaA_stmt, gfhaA_stmt_at, AFI_GFHA in G.
  eapply G; first [eassumption | reflexivity].
Qed.
End Asm.
End CANSEC1.
