(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem Mem Frame.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree AsanCtrl AsanEmbed Relim Gap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface Stdio_kit AHarness_iface AH_fi_iface AF_fi_kit
     AF_fi_gfha_iface AF_fi_ffsi_iface AF_fi_gfcs AF_fi_gfcsA AF_fi_gds AF_fi_gdsA AF_fi_gdid AF_fi_gdidA AF_fi_fdsA AF_fi_wrap AF_fi_small AF_fi_ffsi.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.

Section CANSEC1. Context {rc : runConstT}.
Definition LGOT_SUAR_F : Z := 0x98e90.

#[using="Type"] Lemma ltoi_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m LGOT_SUAR_F [C8 (Z_to_bv 64 0xa0e80)].
Proof.
  intros m R. unfold LGOT_SUAR_F. apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
Qed.
#[using="Type"] Lemma shadow16_c1sL : forall m s, rw_cells asegs m s (repeat (C8 (Z_to_bv 64 0)) 2) -> rw_cells asegs m s (repeat (C1 (Z_to_bv 8 0)) 16).
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma page_round_up_geL : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof. intros x Hx. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.
#[using="Type"] Lemma harness_topL : forall L SP, SP + ATRUN_DEPTH = al_sp0 L -> 0 <= SP -> SP + 48 <= al_top L < SP + 48 + 4096.
Proof.
  intros L SP E H0. unfold al_top. rewrite <- E. unfold ATRUN_DEPTH. Local Ltac2 Set LiaHints.tbl := fun () => "0030=18689963921.531329099219.659055300873.5000004007008S2H0S1HS".
replace (SP + 208 - 160) with (SP + 48) by lia.
  pose proof (page_round_up_geL (SP + 48) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rclean_mg : forall (P : Z -> Prop) m m' r,
  rclean m r -> magree asegs P m m' -> (forall s, shad (r_rlo r) <= s < shad (r_rhi r) -> 0 <= s < 2^64 /\ P s) -> rclean m' r.
Proof.
  intros P m m' r [(U & HU & W & AB) LT] MG HP. pose proof HU as (H1 & H2 & H3 & H4 & H5 & H6).
  split; [| exact LT]. split; [| split; [exact HU| split; [| exact AB]]].
  - eapply unpoisoned_agree; [exact U|]. intros s Hs.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>27076589246.2052792927696.2000000=00AS2H12H22H42HsS2Ha".
assert (X : shad (r_rlo r) <= s < shad (r_rhi r)) by (rewrite !shad_div in Hs |- *; unfold ASHOFF, KEND in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    destruct (HP s X) as [R Ps]. exact (proj1 (MG s R Ps)).
  - eapply wr_at_magree; [exact MG| exact W|]. intros a Ha. exact (proj2 (HP a ltac:(lia))).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_nil_any : forall (m m' : amem) S, bytes_at asegs m S [] -> bytes_at asegs m' S [].
Proof. intros m m' S (A & B & _). split; [exact A|]. split; [exact B|]. intros i Hi. cbn in Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0010=20742173918.8000004S2Hi".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma sel_mask : forall n D, 0 <= n -> 0 <= D < 2^64 ->
  Z.land (Z.land (Z.b2z (n <? 1) + -1) 18446744073709551615) D = (if n =? 0 then 0 else D).
Proof.
  intros n D Hn HD. destruct (n <? 1) eqn:E.
  - apply Z.ltb_lt in E. Local Ltac2 Set LiaHints.tbl := fun () => "0040=15334045905.627200643409.635495369753.68555327013.6 00000600900:00>S2Hn1ES1ESS2HD".
replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn. reflexivity.
  - apply Z.ltb_ge in E. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.land (Z.b2z false + -1) 18446744073709551615) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Notation f1c := (C1 (Z_to_bv 8 18446744073709551601)).
Notation f3c := (C1 (Z_to_bv 8 18446744073709551603)).
Notation f5c := (C1 (Z_to_bv 8 18446744073709551605)).
Notation f8c := (C1 (Z_to_bv 8 18446744073709551608)).
Notation z1c := (C1 (Z_to_bv 8 0)).
Definition LSH1 : list cell := [f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f3c; f3c; f3c; f3c; f3c; f3c].
Definition LSH5 : list cell := [f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c].
Definition LHDR : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x18743); C8 (Z_to_bv 64 0x7fc30)].
Ltac neglit z := lazymatch z with
  | -8 => replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity)
  | -11 => replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity)
  | -13 => replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity)
  | -15 => replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity)
  end.
Ltac sok0 base :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SH : rw_cells asegs mx base _ |- _ =>
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - AHARNESS_STACK.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition SPAh : Z := (SP - 96) - (SP - 96) mod 32.
  #[using="rc SP16"] Lemma spah_props : SP - 127 <= SPAh <= SP - 96 /\ SPAh mod 32 = 0 /\ (SP + -96) - (SP + -96) mod 2^5 = SPAh.
  Proof. unfold SPAh. change (2^5) with 32. Local Ltac2 Set LiaHints.tbl := fun () => "0010>57856635280.27000006S4SP16".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Definition LRB : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="rc SP16 SPT LOS LOC RSTK RI"] Lemma ltoi_pro : forall (t0 t1 t2 aD aN a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m ->
    rt_got m -> rt_shbase m -> rw_cells asegs m LGOT_SUAR_F [C8 (Z_to_bv 64 0xa0e80)] -> rw_cells asegs m 0xa0e80 [C4 (Z_to_bv 64 1)] ->
    evtF asegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x7fc94) (Z_to_bv 64 SPAh) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAh)
                     (Z_to_bv 64 128) (Z_to_bv 64 0xa0e78) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 aN s4 aD (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 AFI_SM1) fc None m' (seg_rom asegs)
        /\ munch [(SP - 128, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SP + -72) LRB /\ rw_cells asegs m' SPAh [CB 24 jA]
        /\ stk asegs m' lo SPAh /\ stk asegs m' (SPAh + 24) (SP + -72))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 aD aN a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFI_LTOI) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold LGOT_SUAR_F, AFI_LTOI, AFI_SM1 in *.
    unfold KEND in SPT. unfold AHARNESS_STACK in LOS. pose proof atop_range as ATR.
    pose proof spah_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 128, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "01f0>10047693422.6810287669065.6510287669065.6710287669065.6810287669065.6910382188910.6710626301228.6811637578185.6812269574729.691340665966.69 13641502813.6613868696777.6716200917870.6816380822931.6816408089748.6116622434386.6516622434386.6817373439945.6718074052718.6918871287511.6719750732782.672027029998.67 21004494112.6821656933230.6722044444371.6022664810540.672342125148.67 23470587095.6824289051761.6724630998586.6824830162102.6025240764910.6725259836654.6828686091948.6829514832494.6830196181434.6731058586091.613106977902.69 31731548819.6531748837718.6131755616852.6532377744366.6732651489978.6932735658066.6532735658066.6832840430244.5833501386478.6833680001082.6734697030444.6735010564462.6835842749143.6836550167516.6736627825777.6736828693371.6337204754348.6737286305386.6038303833303.6739219183342.6839302203090.5642322675313.6742450266737.6942467221968.5842831019478.6542831019478.6843086963927.694359095406.68 43872218225.6843872227804.6745003960666.6445221239098.6745393521777.6145713281902.684600809644.69 46024206162.6546024206162.6846051971694.6846356275438.674641771485.66 4643668681.67 46595340782.6746647744021.6546787521756.6747219577582.6747402546926.6849893969737.6751106262638.6951781592413.6651865665239.6754068232029.6654077074143.6856064834414.68563227834.68  56416742103.6856485352777.6857745675194.685853766638.67 58680421489.6758866340206.67589448407.67  59308628179.6259743357778.6559743357778.6860492306926.6761066828181.6861279679916.6861479303406.6762140770976.6562947167693.6564311933975.616652598510.67 67309361708.6767706252913.6868237603789.68698988910.67  8583720762.67 9155751918.67 9453015665.68 9843327049.68 00000B00C00D00E00F00X00\00]00^01001501601H01I01N01`02202302E02F02X02j02n03@03R03V03[03\03]03b03c04504G04K04]04b04c05505605G05X05j05o06A06S06T06f06k06o07A07B07G07H07I07M07N07O07a07f07g07h07m08208708808J08K08P08U08Z08l09>09B09T09f0:80:J0:O0:P0:b0:c0:h0;:0;L0;M0;_0;d0;e0;j0;o0<A0<F0<G0<H0<M0<_0<`0=20=30=70=I0=[0=m0=n0>20>D0>H0>I0>J0>\0>`0>a0>b0?40?90?K0?L0?MS3LOS3LOC3ATR4SPABSSSSS3LOS3LOC3ATR4SPABS2HBSSS3LOS3LOC3ATR4SPABS3LOSSS3LOS3LOC3ATR4SPABSS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOSSSS3SPTSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3SPTSS3LOS3LOC3ATR4SPABSS3SPT3LOS3LOC3ATRS3SPT3LOS3LOC3ATRS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3SPTS2HBS3LOS3LOC3ATR4SPABSS3LOSSSS2HBSSS3LOS3LOC3ATR4SPABS3LOSSSS3LOSS3SPTS3SPTSS3LOS3LOC3ATR4SPABSS3LOSS3LOSS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSSS3LOS3LOC3ATR4SPABSS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOSSS3LOSS3LOSS3LOS3LOC3ATR4SPABS3SPTSSS3SPTS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSS2K0S3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS2HBS3LOS3LOC3ATR4SPABS2HBSSS3LOS3LOC3ATR4SPABS2HBSSS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABSS".
carve_frame 72%nat ST. carve_frame 24%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 9 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    lazymatch goal with H : rw_cells _ _ (SP + -96) _ |- _ => release_frame H ST (SP + -72) end.
    destruct (stk_split asegs _ lo (SPAh + 24) (SP + -72) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPAh + 24) 24 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 24) with 24 in STL, FRA. replace (SPAh + 24 - 24) with SPAh in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [lazymatch goal with H : rw_cells _ _ (SP + -72) _ |- _ => exact H end|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="lo SP16 LOS LOC RSTK"] Lemma ltoi_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 aD aN x28 x29 x30 x31 : word) m (FF FLG : Z)
      (j0 j1 j2 : word) (junk : list byte) (jA : list byte) (Q : machine_state -> Prop),
    rw_cells asegs m SPAh [CB 24 jA] ->
    rw_cells asegs m FF [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells asegs m (shad FF) (repeat (C8 (Z_to_bv 64 0)) 2) ->
    mem_inv asegs m ->
    ablk FF (FF + 128) -> FF + 128 <= ATOP -> FF mod 128 = 0 ->
    rng RNG FF 128 -> rng RNG (shad FF) 16 ->
    (forall m' j16,
        munch [(SPAh + 16, SPAh + 24); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 16)] m m' ->
        wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' SPAh [CB 16 j16; C8 (Z_to_bv 64 FF)] ->
        rw_cells asegs m' FF (LHDR ++ [CB 96 junk; C8 (Z_to_bv 64 FLG)]) -> rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) LSH1 ->
        Q (MS (mkR (Z_to_bv 64 0x7fc94) (Z_to_bv 64 SPAh) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAh)
                   (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x18743) (Z_to_bv 64 0x7fc30) x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) aN (Z_to_bv 64 (FF + 32)) aD (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) s8 s9 s10 s11 x28 x29 x30 x31)
              FR (Z_to_bv 64 0x7fd30) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR (Z_to_bv 64 0x7fc94) (Z_to_bv 64 SPAh) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAh)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               s2 aN s4 aD (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x7fc94) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros FRA FFC SHF MI FH FC F128 RF RSF K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AHARNESS_STACK in LOS.
    pose proof spah_props as (SPAB & SPA32 & _).
    apply shadow16_c1sL in SHF. cbn [repeat] in SHF. Local Ltac2 Set LiaHints.tbl := fun () => "01d0>10191062042.8510299541350.8310841825258.8311603250610.8313557852353.8514866570234.8315341314694.8316753464773.851702481864.82 17941155254.8518138708044.8318343703478.8318369228174.8319218568712.8219570126950.8320139715884.8220200392866.8320749162842.8320874077976.8221525666008.8222724917048.8223098415148.832353938568.82 23716884570.8323950473669.6 24200872257.8224686014778.8225220040706.8325334232912.8525418808852.8526494647592.8226494647592.8326494647592.852673550442.82 27238062074.832818573085.85 29181457478.8329786411260.6 30460132882.8330906104780.8331153539003.8131880746886.8431930091218.823342490946.83 34098841190.8234252541850.8234501900210.8334597926842.8334910133892.8235301401292.8336737505306.8237123351842.8338154183177.8138389508810.8239178121190.8339656437418.8240194833727.8241044649514.8341091132398.8341615107788.834173552739.85 42200342570.8342452747910.8242643832943.8542831019478.83441253466.84  44417097546.83449256530.73  45221239098.8245508725130.8345585588076.8345982589382.834606400646.83 46378729034.8346901542423.8547946365538.8348211285674.8348639348472.8249943447116.8350050922987.8150524051526.8351816630506.8352107682714.8353156436688.8253309796028.7153640511348.6953706860006.835464662474.83 54769888194.8255778236477.8456644364524.8356804907040.8356830590924.8257064704805.8257199698906.8358116526106.8359308628179.7359338331354.8359917383078.8260118775914.8362055344378.8362098338330.8362760451890.8363679220824.826386823154.83 63958622316.8364555500442.8366824274186.8366867539939.8266919845736.8267570253864.826794595386.83 68366496660.817039361418.83 7139856330.83 9899865354.83 00000500600;00<00c00h00i01P01Q01V01W01m02T02U02V02W03>03C03D03E03F03G03H03M03Z04A04F04m05C05Y05Z05[05\05a06706806906:06a06b06c06d07K08208308808_09509J09K09a0:H0:I0:N0:O0:e0:i0:n0;30;40;90;>0;?0;D0;I0;R0;W0;`0;e0;j0;k0;l0;m0<C0<D0<k0=00=10=20=30=40=90=>0=T0=j0=o0>00>F0>m0>n0>o0?00?10?J0?`0?e0?m0@20@60@L0@Q0@V0A=0A>0Ae0Af0B<0BR0BW0BX0BY0Bo0C00C50C:0C?S3FHdSS3BSFSS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3BSFSS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SS3FHdSS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SSSS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3BSFSSSSSS3BSFS3FHa3FHc3ATRS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3BSFS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHc3ATR4SPABS3LOS3LOC3FHc3ATR4SPABSSSS3BSFS3LOS3LOC3ATR4SPAB3BSFSSSS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SSSS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SS3FHdS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3FHc4SPAB2HBSS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SS3BSFSS3LOS3LOC3ATR4SPAB3BSFS2HBS3BSFS3BSFSS3FHaS3BSFSS3FHaS3BSFS3FHa3FHdS3BSFS3FHa3FHdS3BSFS3BSFSSSS3LOS3LOC3ATR4SPAB3BSFSS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0S3BSFSSSSS3BSFS3BSFS3LOS3LOC3FHc3ATR4SPABS3LOS3LOC3FHb3ATR4SPABS3FHbSS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SSSSS3LOS3LOC3ATR4SPAB3BSF2HBS3LOS3LOC3ATR4SPAB3BSFS3BSFS3FHa2K0S3BSFS2HBS3LOS3LOC3ATR4SPAB3BSFS3BSFS3BSFS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SS3LOS3LOC3FHa3ATR4SPAB5SPA323BSF3FHu2K0SS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFS3FHaSSS3LOS3LOC3ATR4SPAB3BSFSS3BSFS3BSFS3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2148232192 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
      by (clear - FHa FHb FHc ATR; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    assert (RSA : rng RNG SPAh 24) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (munch_refl [(SPAh + 16, SPAh + 24); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 16)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    clear SP16 F128.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 8 zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. neglit (-15).                          (* [comment removed for export] *)
    sok0 (Z.shiftr FF 3 + 2147450880).
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep. neglit (-13).                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done. eapply K; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="Type"] Lemma ltoi_sel : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (FF D n : Z),
    rw_cells asegs m (Z.shiftr FF 3 + 2147450880) LSH1 -> mem_inv asegs m ->
    ablk FF (FF + 128) -> rng RNG (shad FF) 16 -> 0 <= D < 2^64 -> 0 <= n < 2^62 ->
    evtF asegs RNG (fun ms' => exists (y10 : word) m',
        ms' = MS (mkR (Z_to_bv 64 0x7fc94) (Z_to_bv 64 SPAh) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAh)
                     y10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 n) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (if n =? 0 then 0 else D)) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                     s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x7fd4c) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) LSH1)
      (MS (mkR (Z_to_bv 64 0x7fc94) (Z_to_bv 64 SPAh) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAh)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 n) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 D) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
               s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x7fd30) fc None m (seg_rom asegs)).
  Proof.
    intros until n. intros SHF MI FH RSF HD HN.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *. pose proof atop_range as ATR.
    Local Ltac2 Set LiaHints.tbl := fun () => "00L0>11805467289.6611805467289.6712066655206.6712480025755.6613067081226.6715160347210.6716867429482.6721470349994.6722074372731.6622700267513.6223584418860.662427397974.60 24521592556.6726774769626.6728897571974.6728987856538.6732365281766.6636685953222.6738709023052.6740971859371.6552076332702.7053653386452.5757533215052.6761937685147.6861993467723.6664026414714.6668066155898.668550771108.60 00000100200300400800<00@00D00E00H00I00M00N00R00S00W00X00Y00Z00[00\00]00^00b00c00g00k00oSSSSS2HBS2HBS2HBS2HBSS1HSS2HNSS2HBSS2HBSSSSFSSS2HNSS2HBS2HBS2HD".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia). unfold LSH1 in SHF.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    rewrite (sel_mask n D) by lia.
    apply evtF_done. eexists _, _. split; [reflexivity|].
    split; [first [exact MU| eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia]|].
    split; [exact WM|]. split; [assumption|]. unfold LSH1. assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="SP16 LOS LOC RSTK"] Lemma ltoi_tail : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y28 y29 y30 y31 : word) mx (FF FLG : Z) (j16 : list byte),
    rw_cells asegs mx (SP + -72) LRB -> rw_cells asegs mx (FF + 120) [C8 (Z_to_bv 64 FLG)] -> rw_cells asegs mx FLG [C1 (Z_to_bv 8 1)] ->
    stk asegs mx (SPAh + 24) (SP + -72) -> stk asegs mx lo SPAh -> rw_cells asegs mx SPAh [CB 16 j16; C8 (Z_to_bv 64 FF)] ->
    rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) LSH1 -> rw_cells asegs mx FF LHDR -> mem_inv asegs mx ->
    ablk FF (FF + 128) -> FF + 128 <= ATOP -> rng RNG FF 128 -> rng RNG (shad FF) 16 ->
    ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 128 <= FLG) -> rng RNG FLG 1 ->
    evtF asegs RNG (fun ms' => exists mp m',
        ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 16); (FF, FF + 8)] mx mp /\ wmono asegs mx mp /\ mem_inv asegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono asegs mp m' /\ mem_inv asegs m'
        /\ stk asegs m' lo SP /\ rw_cells asegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR y1 (Z_to_bv 64 SPAh) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAh) y10 y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 FF) y19 y20 y21 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) s8 s9 s10 s11 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x7fdd0) fc None mx (seg_rom asegs)).
  Proof.
    intros until j16. intros FRB FF120 FLC STG STL FRA SHF FF0 MI FH FC RF RSF GH GC GF RG.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AHARNESS_STACK in LOS.
    pose proof (proj1 spah_props) as SPAB.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa. pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    Local Ltac2 Set LiaHints.tbl := fun () => "04D0>1017856489.92 1017856489.93 10299541350.9410841825258.9411603250610.9412066655206.9212066655206.9312480025752.9112480025752.9213038036500.9713067081226.9213067081226.9313641502813.9514030259705.9414793220770.9414866570234.941507374777.94 15160347210.9215160347210.9315170394089.9415341314694.9416283555162.9216283555162.9316753464773.9416867429482.9216867429482.931702481864.93 17404902110.9417513677241.9417693634345.9417941155254.9418138708044.9418343703478.9418368439854.9418369228174.9419202614250.9119202614250.9319218568712.9319570126950.9420139715884.9220139715884.9420200392866.9420749162842.9420874077976.932139396638.94 21470349994.9221470349994.9321525666008.9322042559940.9022074372728.9122074372728.9222700267513.9222724917048.9322741270105.942296821401.92 2296821401.93 23098415148.9423404677272.972342125148.96 23499785897.9223499785897.932353938568.93 23584418860.9123584418860.9323687287154.9223687287154.9323716884570.9423868465886.9023950456754.6 24289051761.9624521592556.9224521592556.9324686014778.9224686014778.9425071629079.9125071629079.9225071629079.9325071629079.9425220040706.9425418808852.9425653217698.9725753502808.9725862343643.9725927005322.9225927005322.932673550442.92 2673550442.94 26774769626.9226774769626.9327054816089.9227054816089.9427238062074.9427798408553.942818573085.94 28897571974.9228897571974.9328987856538.9228987856538.9329181457478.9429765937165.9429786463883.6 30460132882.9430906104780.9431153539000.9131153539000.9331693696482.9231693696482.9331930091218.9231930091218.9432365281766.9132365281766.9333416653251.973342490946.94 33969101564.9734098841190.9234098841190.9434501900210.9434597926842.9434716068297.9234716068297.9335235452859.9735301401292.94353645442.92  353645442.93  36550167516.9636627825777.9736685953222.9236685953222.9336737505306.9236737505306.9436918791753.9437123351842.9438389508810.9238389508810.9438709023052.9238709023052.9339178121190.9439322872841.9239322872841.9439656437418.9239656437418.9440419189385.9440773126249.9440781609801.9240781609801.9440811138462.9440971859368.9040971859368.9241044649514.9441091132398.9441615107788.944190291281.96 41954984985.9141954984985.9342200342570.9442322675313.9642450266737.9842452747910.9242452747910.9442643832943.9442831019478.9443641966310.9643872218225.9743872227804.9644157721241.9444417097546.94449256530.85  45221239098.9245221239098.9445508725130.9445540112505.9445585588076.9445982589382.944606400646.94 46378729034.944641771485.95 46491404822.9146647744021.9446787521756.9646901542423.9446924073390.9447747998098.9147747998098.9347946365538.9448046123689.9748162556019.9748211285674.9448297037321.9148297037321.9348639348472.9349943447116.9450050922984.9150050922984.93502495215.90  50524051526.9451159854377.9451636304249.9451781592412.9651816630506.9452107682714.9452598767571.9453653289649.7953706860006.9454068232029.9554077074143.9754374972478.9254374972478.9454374994186.955464662474.94 54769888194.9254769888194.9455060265338.9255060265338.9355778236476.9356392233662.9456644364524.9456804907040.9456830590924.9256830590924.9457199698906.9457533215052.9257533215052.9357622410744.9257871968190.9458116526106.9458680421489.9659118738686.9459161080025.9259161080025.9459308628179.8559338331354.9460118775914.9460211452398.9461452997881.9461993467720.9161993467720.9262055344378.9462098338330.9462598956670.9262598956670.9362760451890.9462814293305.9262814293305.9363655626921.9463679220824.9363700058990.9263700058990.936386823154.94 63958622316.9464026414714.9164026414714.9364555500442.9464562105998.9466824274186.9466919845736.9367079600409.9467570253864.9367706252913.9767871293851.946794595386.94 68066155898.9168066155898.9368237603789.9768287079817.946968827998.92 6968827998.93 7039361418.94 7139856330.94 7342793742.91 7342793742.93 7942663737.92 7942663737.93 9130008270.92 9130008270.94 9453015665.97 9899865354.94 00000Q01901:01?01@01A01B01C01D01U01Z01_01d02502]02b03J03O03T03e03f04<04R05305805=05>05f06706H06M06N06d07L08408J08`08a08b08c08d09L09Q09R0::0:?0:D0:E0:W0:X0:Y0:c0:d0;50;F0;W0;X0;]0;b0<30<D0<E0<F0<G0<h0=P0=U0=g0>40>50>60>70><0>A0>B0>C0>D0>E0>m0?C0?D0?H0?I0?_0@50@:0@?0@D0@I0@j0AR0Ah0B90B:0B;0B<0BA0BF0BG0Bo0C00CX0CY0CZ0C[0D<0Dd0EE0Em0En0Eo0F30F[0GC0GD0GE0Gm0HC0Hd0IL0IQ0IR0J30J[0J`0Ja0Jb0Jc0K90KO0L70L_0Ld0Li0Lj0Lk0Ll0MM0N50NK0Na0O20OZ0Ok0P<0Pd0Pe0Pf0Pk0Q00Q10Q20QS0R;0R@0RA0RB0RC0RD0RI0RN0RO0RP0RU0S=0SB0SK0SP0SU0SZ0Sk0Sl0Sm0Sn0TD0TI0TN0T_0Td0Te0UM0Un0VV0W>0W?0WU0WZ0Wk0X<0X=0X>0X?0X@0XA0XB0Xj0YR0YW0Y\0Ya0Yb0Yc0Yd0Yi0Yn0ZO0[70[80[N0[o0\W0\m0]C0]D0]H0]I0]J0]K0]L0]b0]c0]d0]n0^V0^[0^\0_D0_U0_f0_n0`30`I0a10aY0aZ0a[0a`0ae0bF0bn0cV0cg0d80d`0da0eB0ej0fR0fS0fX0f]0g30g[0h10h20hC0hD0hE0hV0hl0i10i60i70i_0j@0jh0jm0k20kS0l;0l\0mD0me0nM0nN0nSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS3BSFSSSSSS3LOS3LOC3ATR3GHcS3BSFS3BSFS3LOSS3LOS3LOC3ATR3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS3BSFS3LOS3LOC3ATR3BSFSS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS3BSFS3BSFSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFS3FHdSS3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFSSSSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS3BSFSS3LOS3LOC3ATR4SPABSSS3FHa2K01HSS3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFSS3GHaS3LOSS3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFSSSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS3LOS3LOC3ATR4SPABS3ATR3FHa3FHcSSSS3BSFS3BSFSSSSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3FHcSS2GFSS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFS3BSFS3BSFS3BSFS3BSFS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR3BSFSSSS3BSFS3BSFSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SSSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SSS2GFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3GHdSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOSSSSS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS3BSFSSSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SSS3BSFS3BSFSSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFSSSSS3FHaS3BSFSSS3LOSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS3FHa3FHdS3BSFS3BSFS3BSFS3LOS3LOC3ATR3BSFSSSS3LOS3LOC3ATR4SPAB3BSFS3LOSS3LOSS3LOS3LOC3ATR3BSFS3LOSSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS3LOS3LOC3ATR4SPAB3GHcS3BSFS3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFSSSSSSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOSS3BSFS3BSFSSSS3LOSS3LOSS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3BSFS3LOS3LOC3ATR4SPAB3BSFSS2GFSSSSS3LOS3LOC3ATR4SPAB3BSFSSS3FHa2K01HS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFS3FHa2K0S3BSFS3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SSS3BSFS3BSFS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR3BSFS3LOS3LOC3ATR3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS3BSFS3BSFS3LOS3LOC3ATR4SPAB3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3LOS3LOC3ATR4SPAB3BSFSS3LOS3LOC3ATR3BSFSSS3LOS3LOC3ATR3FHcS3LOS3LOC3ATR4SPAB3BSFS3BSFS3BSFSS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S3BSFS3BSFS4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0S4SP163LOS3LOC2GF3ATR3FHu3GHu3BSFS4SP163LOS3LOC2GF3ATR3FHa3FHu3GHu3BSF2K0SS3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2148232192 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
      by (clear - FHa FHb FHc ATR; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    unfold LSH1 in SHF. unfold LHDR in FF0. unfold LRB in FRB.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 16); (FF, FF + 8)] mx) as MU1. pose proof (wmono_refl asegs mx) as WM1.
    zstep. neglit (-8).                           (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. neglit (-11).                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    sok0 (Z.shiftr FF 3 + 2147450880).
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mp _) =>
      lazymatch goal with MIx : mem_inv asegs mp |- _ => pose proof MIx as MIp; change (mem_inv asegs mp) with (bx (mem_inv asegs mp)) in MIp end;
      pose proof (munch_refl [(FLG, FLG + 1)] mp) as MU2; pose proof (wmono_refl asegs mp) as WM2 end.
    lazymatch type of MU1 with ?T => change T with (bx T) in MU1 end. lazymatch type of WM1 with ?T => change T with (bx T) in WM1 end.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 9 zstep.                                   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    eapply stk_release in FRA; [| exact STL| lia]. cbn [cells_size csize Nat.add] in FRA. change (Z.of_nat 24) with 24 in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      pose proof (stk_merge asegs mf lo (SPAh + 24) (SP + -72) FRA STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _. split; [reflexivity|].
    split; [first [exact MU1| eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia]|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| assumption].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM1 : stack_malloc_1_stmtk AI fflag rng_fs 0.
Hypothesis GFCS : gfcsA_stmt AI rng_fs.
Hypothesis GDS : gdsA_stmt AI rng_fs.
Hypothesis FFCS : ffcsA_stmt AI rng_fs.
Hypothesis GDID : gdidA_stmt AI rng_fs.
Hypothesis FDS : fdsA_stmt AI rng_fs.
Hypothesis DBOUND : dboundA_stmt AI rng_fs.
Hypothesis FHSIZE : fhsizeA_stmt AI.
Hypothesis ISFRAME : isframeA_stmt AI.
Hypothesis GFH : gfhA_stmt AI rng_fs.
Hypothesis GFHA : gfhaA_stmt AI rng_fs.
Hypothesis GIMG : In (0x20d40, 0x20dc0)%Z CI.
Notation FB1 F := (mkABlock (ABFake 1) F 128).

(* [comment removed for export] *)
Ltac carry_cells MG CL :=
  lazymatch type of MG with magree _ _ ?ma ?mb =>
    repeat match goal with
    | H : rw_cells asegs ma ?A ?cs |- _ =>
        let H' := fresh H in
        assert (H' : rw_cells asegs mb A cs)
          by (eapply rw_cells_magree; [exact MG| exact H|]; cbn [cells_size csize Nat.add length LSH1 LHDR LRB app]; intros a' Ha'; CL a' Ha');
        clear H; rename H' into H
    end
  end.

(* [comment removed for export] *)
Ltac wrapP PB GSH RC STL LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32 :=
    first [ exact LE11 | exact LE00 | exact LE20 | exact LBH' | split; [exact PB| exact PR] | exact HC' | exact GSH | exact STL | exact BOT | exact TP
          | exact RSTK | exact RI | exact RIS | exact RFS | reflexivity | eassumption
          | eapply unpoisoned_sub; [exact (shclean_unpoisoned _ _ _ _ _ (rclean_shclean _ _ RC))| lia| lia]
          | eapply rng_sub'; [exact RR|]; unfold rrng; rewrite !shad_div; unfold ASHOFF; clear - R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | clear - SPA32; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
          | unfold GFCS_STACK_A, GDS_STACK_A, GDID_STACK_A, FDS_STACK_A, AFI_FFSI_STACK, AFI_STACK in *; lia
          | lia ].

#[using="fflag FFLAG FREL SM1 GFCS GDS FFCS GDID FDS DBOUND FHSIZE ISFRAME GFH GFHA GIMG"] Theorem ltoiA_proof : ltoiA_stmt AI rng_fs.
Proof.
  unfold ltoiA_stmt.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB D pl lo rstk
         AH LBH0 PAY PB PR D16 SZ GSH ST BOT LO DEPTH SP16 RC R1 R2 R3 ES0 MI FC TP -> -> ERA RSTK RI RIS RFS RR.
  unfold payload_atA in PAY. unfold zlength in *.
  pose proof atop_range as ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  set (SP := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "04>0?10082356837.2  10508801424.26510508801427.24910508801437.21710510407065.4  11400842896.3  11632986708.4  11801222821.19611801225125.19411803323301.19711803468325.1931491121425.249 15042936624.10315860008408.35616130647969.17916130649904.12716212326257.30016443682382.6  16457969228.10317113326105.20717113326105.22317113326105.23917113326105.25517113326105.27117113326105.28717113326105.29417113326105.30117113326105.32317113326105.34317991086127.11817991089884.34417991432202.17818614817987.7  18637139736.29819306802303.5  19359633007.3  19613545634.17820133606887.2  20667538767.18520923194843.4  21176979429.26521476354135.29822275235044.7  22706556809.20322706556809.20423598554287.18523760811842.93 23813426100.3  23890033195.6  23950456754.6  24373109334.18024373109334.18124373111495.36024620255495.12624622352562.15725134018897.5  25135890228.22125189344836.12625191243215.4  26120753523.18526120852592.20126120852606.23326341871803.23726492779925.18826780783605.12626784963315.31826784963316.29827533015186.12927680252381.16 27923653857.29827923653862.31827997028366.31828573892092.19428573892092.19528744653316.28828744653319.28129454436899.30029782628086.30029784460045.17529786463883.6  29786692570.20129786692571.19229788740058.19129788740059.18629790656601.35429908927524.17 30039705589.35930879664818.28531137467146.30031329808616.2173154183863.5   31936966334.12732769802564.3  33817571068.17 33839475894.34233906615552.35835056585985.17 3530501799.3   35765329942.36036022317931.10336339867082.18636341750856.35436432316960.10636436609578.10336438776513.17736438776513.32637860099236.17 37896632411.10538005880971.31838005880972.29838738239746.35639463546480.11839473606138.2  39823947764.4  39824308213.28839824308214.28139831286831.18540577543123.30041338309561.26941437301228.1844219455401.300 42229251869.18943031958227.3  43380267837.17843380577048.11843380579819.34443895100227.18743895100227.18844518355164.36044928493900.12545121569851.31845292858295.17 46017724540.21746575934508.2  47189509937.29247436798947.18348367554267.4  48557404258.3  48716904153.10349898301661.1985033780125.5   50506967736.18650950165260.19050950165260.32950950165260.34650950165260.36050950167453.17451460956085.6  51515797303.32251674390222.6  52031182903.18652031255575.3  52101693566.32452101693566.32552101693566.32752101693566.34352101693566.34452101862297.32752551279229.18152793109692.17 53244475689.17753244475689.19153427254030.3  54390175188.19054527933297.26554573335012.6  55177438670.4  55179320644.5  56090055303.20756090055303.22356090055303.23956090055303.25556090055303.27156090055303.28756090055303.29456090055303.30156090055303.32356090055303.34356170235708.11856170236367.34456170417945.17856182918168.28856182918171.28156483181196.3  56765667309.7  57311233691.18457481071355.19558465955866.31858465955869.29858553639182.4  58553641737.31858553641742.29858553934092.28158553934095.28858555737096.18558555947396.3  58556031236.24958556031237.23358556031239.26558556031242.21758556031243.20159015703425.2  59308585216.17659578179139.17359578179139.21059578179139.22659578179139.24259578179139.25859578179139.27459578179139.29059578179139.29759578179139.30459578179139.32759578179139.34459828027751.2  60345304890.25360477472619.10360722720694.20760722720694.22360722720694.23960722720694.25560722720694.27160722720694.28760722720694.29460722720694.30160722720694.32360722720694.34361149777858.30061966492336.29962010265451.3  62012585953.4  63152079932.17 63183223768.18563868847056.16364340695447.18264694790200.5  64696701106.4  64696703666.29864696703669.31864709268403.12666445616639.2  67329310600.4  67474841899.29867474841900.31868214816631.30068621717508.15768652184072.10 7304115508.323 7304115508.343 771835485.190  771835485.195  771835485.360  7780033100.356 7985583209.169 7999255711.4   7999419549.281 7999419550.288 8001352089.185 8001516692.233 8001516693.249 8001516694.265 8001516698.201 8001516699.217 8119804454.11  8119806256.8   8544479511.185 8551017647.188 9414781166.123 9780246397.16  9785023413.205 00000100\01G02202302402503?03n05805g06U06V06c07N08508B08C08D09:0:00:f0;\0<R0=H0>>0?40?j0@`0@i0A60AC0AR0AS0AT0AU0AV0A\0Ae0Af0BT0BU0B]0CS0DE0DQ0DV0DW0DX0De0EP0F;0Ff0GT0HB0HC0HL0HU0HV0ID0J20J`0Ji0K\0LF0M40Mb0NM0Nd0Ne0Nf0Ng0Oa0PW0PX0PY0Pf0Po0Q80Q90QB0QK0QT0Q]0Qf0R70RD0RM0RZ0SH0SI0T00T10T=0TF0UQ0Ua0Ub0Uo0V30V<0VE0VI0VM0VY0Ve0Vm0W10W:0WC0WP0Wk0X10X20X`0YN0YW0Y`0Yi0ZH0ZQ0[\0[]0[^0[_0[`0[n0\<0\H0\k0\l0]00]a0]b0]k0^N0^O0^U0^V0^c0^l0_^0_j0`60`B0`N0`Z0`[0`d0`e0`n0a40b=0bI0c;0dD0e60f>0fG0f\0fh0g40g50gc0hT0hU0hV0hW0hd0i10i>0iK0iX0ie0j20j?0jL0jY0ja0jm0k90kk0l]0l^0lj0m30n=0n>0n?0n@0nL0nX0nd0o00o<0o=0oI0oU0oa0om10910:10F10R11811^12D12j13P14614\15B15h16N16T16]16a16n17;17H17U17b17o18<18I18V18c19019919@19A19M19V19_1:>1:?1:@1;21;d1<R1<S1<T1<U1<V1<_1<d1=71>L1?a1?m1@91@E1@R1@^1@_1AQ1BC1C51Cg1DY1EK1F=1Fo1G>1GM1GN1HA1Ho1IF1IOSS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbFFFS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb3FHu3BSFS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3BSFS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb3FHu3BSFS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3BSFS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbSS3HU53FHb3GHaS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU5S3HU53FHa3FHbFSS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb3Ha'3ATR3LY13LY42T2S2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU53FHb3Ha'S2R23RSP3LY32T14SPAB2BB3HU23HU53FHb3Ha'3ATR3LY13LY42T2S2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU53FHb3Ha'S2R23RSP3LY32T14SPAB2BB3HU23HU53FHb3Ha'3ATR3LY13LY42T2S2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU53FHb3Ha'S2R23RSP3LY32T14SPAB2BB3HU23HU53FHb3Ha'3ATR3LY13LY42T2S2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU53FHb3Ha'S2R23RSP3LY32T14SPAB2BB3HU23HU53FHb3Ha'3ATR3LY13LY42T2S2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU53FHb3Ha'S3BOT3HU5S3BOT3HU53FHbS3BOT3HU53FHbS2R33ATR3HU62HsFFFFS4F128S3HU53FHbFS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbFS3BSF2DHS3BOT2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3BSF2HxS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3BSF2HxS2SZ3HU53FHbS3RSPFFS3ATR3FHa3FHcS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU5S2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU5FS3HU53FHbS3BOT3HU5FS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS3HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3FHc3BSFS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU5S2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53BBKS2LO2R12R24SPAB3HU13HU2FFFS3BOT2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3FHc3BSF2HxS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3FHc3BSF2HxFFS3HU53FHb3FHdS3HU53FHbS3HU53FHbSS3HU53FHbS3HU53FHbS3HU53FHbS3HU53FHbS3HU53FHbS3BOT2LO4SPAB3BBKS3RSP3HU53FHbS3HU53FHbS3HU53FHb3FHdS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbFS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU5FS2R33ATR3FHuS3HU53FHbS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU54F1283FHb3BSFS2R33ATR3HU63FHuFS3HU53FHb3GHuS2BBS3HU53FHbS3HU53FHbS2HnS2HnS2Hn3HU53FHbS2Hn3HU53FHbS3BSF2DHS2HiS3HU53FHbS3HU53FHbS3HU53FHb3GHdS2R23LY32T14SPAB2BB3HU23HU5S4F128FS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS2LO2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbS3HU53FHbS3HU53FHbS3HU53FHbS2R23LY32T14SPAB2BB3HU23HU53FHbS3HU53FHbS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU54F1283FHb3BSFFFFFS4SPAB3HU53FHbS4SPAB3HU53FHbS3HU53FHb2HrS2R23ATR3LY13LY42T24SPAB2BB3HU23HU5FS2FDS2LO2R12R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbFS3HU53FHbS2R23RSP3LY32T14SPAB2BB3HU23HU53FHbFS4F128SS3HU53FHb3BSFS4F1282HaS2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU53FHbS3HU53FHb2HrS3HU53FHb2HrS3HU53FHb2HrS3HU53FHb2HrS3HU53FHb2HaFS3HU53FHbFS3HU53FHbS4F128S3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb3FHu2HaS3HU53FHb2HaS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3FHc2HaS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb3FHu2HaS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3FHc2HaS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb2Ha2FDS3HU53FHbS3BOT2LO3ATR4SPAB3HU6S3HU53FHb2HaS3HU53FHb2HaFS2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb2HrS2LO2R12R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHbFFFS3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S2T13HU5S2T13HU53FHbS2T13HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbFS3ATR3RSP2HaS3HU53FHbS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb3FHu3BSFFFFS2SZ3HU53FHbS2SZ3HU53FHbS2SZ3HU53FHbS2SZ3HU53FHbS2SZ3HU53FHbFS2SZ3HU53FHbS2SZ3HU53FHbS2SZ3HU53FHbS2SZ3HU53FHbS2SZ3HU53FHbFS3HU53FHb2HaS3HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS2R23RSP3LY32T14SPAB2BB3HU23HU53FHb2HaS4F128S3HU53FHbS2SZS3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHb3Ha'S3HU53FHa3FHbS3HU53FHbS5SPA32FS2R33ATR3FHuS3HU53FHbS3HU53FHbS2R23LY32T14SPAB2BB3HU23HU53FHbFFS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU5FFFFS3HU53FHbS3HU5S2R33ATR3HU63FHu2HsS3HU53FHb3Ha'2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23FHc3BOT2LO4SP163LY25SPA323HU43FHu3BSFS3BOT2LO4SP162R23ATR3RSP3LY13LY23LY44SPAB5SPA322BB3HU23HU43HU53FHb3FHu3BSF3Ha'2T23FHcS3HU53FHb2HrS3HU53FHb2HrS3HU53FHb2HrS3HU53FHb3GHaS3HU53FHb2DJFS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3BOT2LO2R23ATR3RSP3LY13LY42T14SPAB2BB3HU23HU53FHbS3LY32T13A162HaS2R33HU33HU62HsFS3Hn'2R23ATR3RSP3LY13LY42T24SPAB2BB3HU23HU53FHb3BBKS2R23ATR3RSP3LY13LY33LY42T12T24SPAB2BB3HU23HU5S2LO2R12R24SPAB3HU13HU2S3HU53FHb".
pose proof (harness_topL L SP DEPTH ltac:(lia)) as [T1 T2].
  unfold AHARNESS_STACK in LO.
  pose proof (spah_props SP SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (bytes_at_bound _ _ _ _ PB) as BB. rewrite length_map in BB.
  assert (LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b Hb. destruct (LBH0 b Hb) as (p & A & n & ->). destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (_ & (R1' & _) & _). exact R1'. }
  (* [comment removed for export] *)
  set (S' := if zlen pl =? 0 then 0 else D).
  assert (HC0 : hcoverA LB S' (zlen pl)).
  { subst S'. destruct PAY as [(p & Hin & Hn)|[-> ED]].
    - replace (zlen pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. exists p, D, (zlen pl). split; [exact Hin| lia].
    - change (hcoverA LB 0 0). left. reflexivity. }
  assert (PBX : forall mx, bytes_at asegs mx D (map (Z_to_bv 8) pl) -> bytes_at asegs mx S' (map (Z_to_bv 8) pl)).
  { intros mx B. subst S'. destruct PAY as [(p & Hin & Hn)|[-> ED]].
    - replace (zlen pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact B.
    - change (bytes_at asegs mx 0 []). split; [lia|]. split; [change (0 + Z.of_nat 0 <= 2^64); lia|]. intros i Hi. cbn in Hi. lia. }
  assert (S0B : 0 <= S' /\ S' + zlen pl <= 2^64) by (subst S'; destruct (zlen pl =? 0); lia).
  (* [comment removed for export] *)
  assert (NOF : forall c F n, ~ In (mkABlock (ABFake c) F n) LB).
  { intros c F n Hin. destruct (LBH0 _ Hin) as (p & A & k & E). discriminate E. }
  (* [comment removed for export] *)
  pose proof (rclean_shclean _ _ RC) as SHC. pose proof (shclean_hull _ _ _ _ _ SHC) as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6). pose proof (rclean_lt _ _ RC) as RLT.
  unfold KEND in HU6.
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (_ & GOT & _ & _ & SHB & SUA & _).
  pose proof (ltoi_got_cells m (AI_relro AI _ _ _ _ _ AH)) as GSU.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply ltoi_pro with (lo := lo); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    all: try (unfold KEND; lia). all: try (eapply rng_sub'; [exact RSTK| lia]). all: try (unfold AHARNESS_STACK; lia). }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear GOT SHB SUA GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  assert (MG1 : magree asegs (aclient_addr CI LB SP) m m1).
  { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
    intros Hr. exact (stack_not_client CI LB SP (SP - 128) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
  assert (GSH1 : gshA m1).
  { unfold harness_invA, GSH_ADDR in *. eapply rw_cells_transport; [exact GSH| exact MU1| exact WM1|]. cbn. lia. }
  assert (PB1 : bytes_at asegs m1 D (map (Z_to_bv 8) pl)).
  { destruct PAY as [(p & Hin & Hn)|[EP ED]].
    - eapply bytes_at_transport; [exact PB| exact MU1|]. rewrite length_map. cbn [disjoint_from]. split; [| exact I].
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as BBK. cbn in BBK. lia.
    - rewrite EP in PB |- *. exact (bytes_at_nil_any m m1 D PB). }
  assert (RC1 : rclean m1 rstk).
  { eapply rclean_transport; [exact RC| exact MU1| exact WM1|]. apply appW_cons; [unfold KLOW, KHIGH; right; lia| apply appW_nil]. }
  clear MU1 WM1.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof SM1 as SMC. unfold stack_malloc_1_stmtk, sm_stmtk in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPAh SP)) by lia;
      first [exact AH1| apply fake_lek_none; intros F n; apply NOF| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F128 & FH & FC' & FFC2 & SHF2 & RFF & RSFF).
  rewrite ?(unsigned_lit (SPAh SP)) in ST2, HPR2 by lia.
  retlitA.
  change (Z.to_nat (128 - 32)) with 96%nat in FFC2. change (128 / 8) with 16 in RSFF.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
  assert (BSF : 2148232192 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 16 <= 17594333495296)
    by (clear - FHa FHb FHc ATR; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (NFB : ~ In (FB1 FF) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
  assert (FFD : forall b, In b LB -> FF + 128 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
  { intros b Hb. assert (NE : FB1 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as DJ. cbn in DJ. lia. }
  assert (LBH' : forall b, In b (FB1 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
  assert (LE11 : fake_lek 1 1 (FB1 FF :: LB)) by (apply (fake_lek_pushc 1 0); apply fake_lek_none; intros F' n'; apply NOF).
  assert (LE00 : fake_lek 0 0 (FB1 FF :: LB)) by (apply fake_lek_push; [intros F' n' E; discriminate E| apply fake_lek_none; intros F' n'; apply NOF]).
  assert (LE20 : fake_lek 2 0 (FB1 FF :: LB)) by (apply fake_lek_push; [intros F' n' E; discriminate E| apply fake_lek_none; intros F' n'; apply NOF]).
  assert (HC' : hcoverA (FB1 FF :: LB) S' (zlen pl)) by (apply hcoverA_cons_fake; exact HC0).
  (* [comment removed for export] *)
  assert (CLS : forall a, SPAh SP <= a < 2^47 -> aclient_addr CI (FB1 FF :: LB) (SPAh SP) a) by (intros a Ha; apply cl_stack; lia).
  assert (CLB : forall a, FF <= a < FF + 128 -> aclient_addr CI (FB1 FF :: LB) (SPAh SP) a).
  { intros a Ha. apply (cl_block CI (FB1 FF :: LB) (SPAh SP) (FB1 FF) a ltac:(left; reflexivity)). cbn. lia. }
  assert (CLH : forall a, Z.shiftr FF 3 + 2147450880 <= a < Z.shiftr FF 3 + 2147450880 + 16 -> aclient_addr CI (FB1 FF :: LB) (SPAh SP) a).
  { intros a Ha. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    right; right. exists 1, FF, 128. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    unfold ASHOFF. clear - Ha FHb F128. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (CLP : forall a, S' <= a < S' + zlen pl -> aclient_addr CI (FB1 FF :: LB) (SPAh SP) a).
  { intros a Ha. subst S'. destruct PAY as [(p & Hin & Hn)|[EP ED]].
    - replace (zlen pl =? 0) with false in Ha by (symmetry; apply Z.eqb_neq; lia). apply (cl_block CI (FB1 FF :: LB) (SPAh SP) (HB p D (zlen pl)) a ltac:(right; exact Hin)). cbn. lia.
    - exfalso. rewrite EP in Ha. cbn in Ha. lia. }
  assert (CLR : forall s, shad (r_rlo rstk) <= s < shad (r_rhi rstk) -> 0 <= s < 2^64 /\ aclient_addr CI (FB1 FF :: LB) (SPAh SP) s).
  { intros s Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs. split; [clear - Hs R3 HU6 ATR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|].
    right; right; right. exists (8 * (s - ASHOFF)). split; [| symmetry; apply shad_unshad]. left. unfold ASHOFF. clear - Hs R3 HU3 HU6 ATR. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (CLG : forall a, 0x7fffc1a8 <= a < 0x7fffc1b8 -> aclient_addr CI (FB1 FF :: LB) (SPAh SP) a) by (intros a Ha; exact (gsh_client CI _ (SPAh SP) a GIMG Ha)).
  (* [comment removed for export] *)
  assert (NCS : forall a, SP - 128 <= a < SP -> ~ aclient_addr CI LB SP a) by (intros a Ha; exact (stack_not_client CI LB SP (SP - 128) a HCI HCI0 LBH ltac:(lia) Ha)).
  assert (NCF : forall a, FF <= a < FF + 128 -> ~ aclient_addr CI LB SP a) by (intros a Ha; exact (app_not_client CI LB SP FF 128 a HCI HCI0 FH ltac:(lia) LBH FFD Ha)).
  assert (NCH : forall a, Z.shiftr FF 3 + 2147450880 <= a < Z.shiftr FF 3 + 2147450880 + 16 -> ~ aclient_addr CI LB SP a).
  { intros a Ha. refine (shadow_not_clientN CI LB SP FF 128 a HCI HCI0 FH ltac:(clear - F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(reflexivity) ltac:(lia) ltac:(lia) LBH FFD _).
    rewrite ESH. change (128 / 8) with 16. exact Ha. }
  (* [comment removed for export] *)
  assert (MGX : forall ma mb (E : Z -> Prop), magree asegs (aclient_addr CI LB SP) m ma ->
            magree asegs (fun a => aclient_addr CI (FB1 FF :: LB) (SPAh SP) a /\ E a) ma mb ->
            (forall a, aclient_addr CI LB SP a -> E a) -> magree asegs (aclient_addr CI LB SP) m mb).
  { intros ma mb E MA MB HE. eapply magree_trans; [exact MA|]. eapply magree_mono; [exact MB|]. intros a Ha. split; [| exact (HE a Ha)].
    eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| lia]. }
  assert (MGX1 : forall ma mb, magree asegs (aclient_addr CI LB SP) m ma -> magree asegs (aclient_addr CI (FB1 FF :: LB) (SPAh SP)) ma mb ->
            magree asegs (aclient_addr CI LB SP) m mb).
  { intros ma mb MA MB. eapply (MGX ma mb (fun _ => True)); [exact MA| | intros; exact I].
    eapply magree_mono; [exact MB|]. intros a [Ha _]. exact Ha. }
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  assert (MG2 : magree asegs (aclient_addr CI LB SP) m m2).
  { eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
  assert (GSH2 : gshA m2) by (eapply gshA_mg; [exact HPR2| intros a Ha; exact (gsh_client CI LB (SPAh SP) a GIMG Ha)| exact GSH1]).
  assert (PB2 : bytes_at asegs m2 D (map (Z_to_bv 8) pl)).
  { destruct PAY as [(p & Hin & Hn)|[EP ED]].
    - eapply bytes_at_magree; [exact HPR2| exact PB1|]. rewrite length_map. intros a Ha. apply (cl_block CI LB (SPAh SP) (HB p D (zlen pl)) a Hin). cbn. lia.
    - rewrite EP in PB1 |- *. exact (bytes_at_nil_any m1 m2 D PB1). }
  assert (RC2 : rclean m2 rstk).
  { eapply (rclean_mg _ m1 m2); [exact RC1| exact HPR2|]. intros s Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
    split; [clear - Hs R3 HU6 ATR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|].
    right; right; right. exists (8 * (s - ASHOFF)). split; [| symmetry; apply shad_unshad]. left. unfold ASHOFF. clear - Hs R3 HU3 HU6 ATR. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1 GSH1 PB1 RC1.
  (* [comment removed for export] *)
  eapply evtF_cut; [| intros ms' Hms; exact Hms].
  eapply ltoi_hdr with (lo := lo); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  all: try (unfold KEND; lia). all: try (eapply rng_sub'; [exact RSTK| lia]). all: try (unfold AHARNESS_STACK; lia).
  intros m3 j16 MU3 WM3 MI3 FRA3 FFC3 SHF3. cbv beta.
  assert (AH3 : AHEAP AI L RNG st (FB1 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB1 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 1, FF, 128; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; clear - FHb F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]| constructor]. }
  assert (MG3 : magree asegs (aclient_addr CI LB SP) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
    split; [intros Hr; exact (NCS a ltac:(lia) Ha)|]. split; [intros Hr; exact (NCF a ltac:(lia) Ha)|]. split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (GSH3 : gshA m3) by (unfold harness_invA, GSH_ADDR in *; eapply rw_cells_transport; [exact GSH2| exact MU3| exact WM3|]; cbn; lia).
  assert (PB3 : bytes_at asegs m3 D (map (Z_to_bv 8) pl)).
  { destruct PAY as [(p & Hin & Hn)|[EP ED]].
    - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as BBK. cbn in BBK. pose proof (FFD _ Hin) as FD. cbn in FD.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (_ & (DH & _) & _). unfold ablk, AIMG_HI, KLS in DH.
      eapply bytes_at_transport; [exact PB2| exact MU3|]. rewrite length_map. cbn [disjoint_from]. clear - BBK FD DH BSF SPAB LO BOT ATR FHb FHc. repeat split; try exact I; lia.
    - rewrite EP in PB2 |- *. exact (bytes_at_nil_any m2 m3 D PB2). }
  assert (RC3 : rclean m3 rstk).
  { destruct RC2 as [SH2 LT2]. split; [| exact LT2]. eapply shclean_transport; [exact SH2| exact MU3| exact WM3| | exact LT2].
    rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from]. clear - R3 HU6 HU5 ATR SPAB LO BOT R1 FHb FHc FHu. repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (STL3 : stk asegs m3 lo (SPAh SP)) by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk asegs m3 (SPAh SP + 24) (SP + -72)) by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  clear MG2 FRB2 FRA2 STG2 ST2 MI2 FFC2 SHF2 GSH2 PB2 RC2.
  (* [comment removed for export] *)
  unfold LHDR in FFC3.
  lazymatch type of FFC3 with rw_cells _ _ _ ([?h0; ?h1; ?h2] ++ [CB 96 junk; ?fl]) =>
    change ([h0; h1; h2] ++ [CB 96 junk; fl]) with ([h0; h1; h2] ++ [CB 96 junk] ++ [fl]) in FFC3 end.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FF03 FFC3]. cbn [cells_size csize Nat.add] in FFC3.
  apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC3. destruct FFC3 as [FJ3 FF1203]. cbn [cells_size csize Nat.add] in FF1203.
  replace (FF + Z.of_nat 24 + Z.of_nat 96) with (FF + 120) in FF1203 by lia. replace (FF + Z.of_nat 24) with (FF + 24) in FJ3 by lia.
  apply (rw_cells_split_CB asegs m3 _ [] 96 junk [] [8; 48; 40]%nat) in FJ3; [| reflexivity]. cbn [app mk_CB_cells] in FJ3.
  lazymatch type of FJ3 with rw_cells _ _ _ [?c0; ?c1; ?c2] =>
    apply (proj1 (rw_cells_appA _ m3 _ [c0] [c1; c2])) in FJ3; destruct FJ3 as [_ FZ3]; cbn [cells_size csize Nat.add] in FZ3;
    apply (proj1 (rw_cells_appA _ m3 _ [c1] [c2])) in FZ3; destruct FZ3 as [FZ3 _] end.
  replace (FF + 24 + Z.of_nat 8) with (FF + 32) in FZ3 by lia.
  unfold LHDR in FF03 |- *.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply ltoi_sel; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. all: try lia. all: try (rewrite <- ESH; exact RSFF).
    destruct PAY as [(p' & Hin' & Hn')|[EP ED]]; [pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin') as BBK; cbn in BBK; lia| rewrite ED; unfold AEMPTY; lia]. }
  cbv beta. intros ms' (y10 & m4 & -> & MU4 & WM4 & MI4 & SHF4).
  fold S'.
  assert (AH4 : AHEAP AI L RNG st (FB1 FF :: LB) m4).
  { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. constructor; [| constructor]. cbn.
    right; right; right; right. exists 1, FF, 128. split; [left; reflexivity|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. clear - FHb F128. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (MG4 : magree asegs (aclient_addr CI LB SP) m m4).
  { eapply magree_munch_step; [exact MG3| exact MU4| exact WM4|]. intros a Ha. cbn. split; [intros Hr; exact (NCH a ltac:(lia) Ha)| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 ltac:(cbn; lia)) as FRB4.
  pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU4 WM4 ltac:(cbn; lia)) as FRA4.
  pose proof (rw_cells_transport _ _ _ _ _ _ FF03 MU4 WM4 ltac:(cbn; lia)) as FF04.
  pose proof (rw_cells_transport _ _ _ _ _ _ FZ3 MU4 WM4 ltac:(cbn; lia)) as FZ4.
  pose proof (rw_cells_transport _ _ _ _ _ _ FF1203 MU4 WM4 ltac:(cbn; lia)) as FF1204.
  assert (GSH4 : gshA m4) by (unfold harness_invA, GSH_ADDR in *; eapply rw_cells_transport; [exact GSH3| exact MU4| exact WM4|]; cbn; lia).
  assert (PB4 : bytes_at asegs m4 S' (map (Z_to_bv 8) pl)).
  { apply PBX. destruct PAY as [(p & Hin & Hn)|[EP ED]].
    - destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (_ & (DH & _) & _). unfold ablk, AIMG_HI, KLS in DH.
      eapply bytes_at_transport; [exact PB3| exact MU4|]. rewrite length_map. cbn [disjoint_from]. clear - DH BSF. split; [lia| exact I].
    - rewrite EP in PB3 |- *. exact (bytes_at_nil_any m3 m4 D PB3). }
  assert (RC4 : rclean m4 rstk).
  { destruct RC3 as [SH3 LT3]. split; [| exact LT3]. eapply shclean_transport; [exact SH3| exact MU4| exact WM4| | exact LT3].
    rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from]. clear - R3 HU6 HU5 ATR SPAB LO BOT R1 FHb FHc FHu. split; [OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| exact I]. }
  assert (STL4 : stk asegs m4 lo (SPAh SP)) by (eapply stk_transport; [exact STL3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
  assert (STG4 : stk asegs m4 (SPAh SP + 24) (SP + -72)) by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; cbn; lia]).
  clear MG3 FRB3 FRA3 FF03 FZ3 FF1203 SHF3 GSH3 PB3 RC3 STL3 STG3 MI3 AH3 MU3 WM3 MU4 WM4.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep.                            (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof GFCS as G. unfold gfcsA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fd58) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: wrapP PB4 GSH4 RC4 STL4 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold gfcsA_post in PO.
  destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5 & -> & MI5 & STL5 & MG5 & AH5). retlitA.
  carry_cells MG5 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH5 : gshA m5) by (eapply gshA_mg; [exact MG5| intros a Ha; apply CLG; exact Ha| exact GSH4]).
  assert (PB5 : bytes_at asegs m5 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG5| exact PB4| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC5 : rclean m5 rstk) by (eapply rclean_mg; [exact RC4| exact MG5| exact CLR]).
  assert (STG5 : stk asegs m5 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG5| exact STG4| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MG4 MG5) as MGA5.
  clear MG4 MG5 GSH4 PB4 RC4 STG4 STL4 MI4 AH4.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof GDS as G. unfold gdsA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fd64) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: wrapP PB5 GSH5 RC5 STL5 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold gdsA_post in PO.
  destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m6 & -> & MI6 & STL6 & MG6 & AH6). retlitA.
  carry_cells MG6 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH6 : gshA m6) by (eapply gshA_mg; [exact MG6| intros a Ha; apply CLG; exact Ha| exact GSH5]).
  assert (PB6 : bytes_at asegs m6 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG6| exact PB5| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC6 : rclean m6 rstk) by (eapply rclean_mg; [exact RC5| exact MG6| exact CLR]).
  assert (STG6 : stk asegs m6 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG6| exact STG5| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA5 MG6) as MGA6.
  clear MGA5 MG6 GSH5 PB5 RC5 STG5 STL5 MI5 AH5.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof FFCS as G. unfold ffcsA_stmt, wrapA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fd70) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: try (change (32 / 8 + 1) with 5). all: wrapP PB6 GSH6 RC6 STL6 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold wrapA_post in PO.
  destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m7 & -> & MI7 & STL7 & MG7 & AH7). retlitA.
  carry_cells MG7 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH7 : gshA m7) by (eapply gshA_mg; [exact MG7| intros a Ha; apply CLG; exact Ha| exact GSH6]).
  assert (PB7 : bytes_at asegs m7 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG7| exact PB6| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC7 : rclean m7 rstk) by (eapply rclean_mg; [exact RC6| exact MG7| exact CLR]).
  assert (STG7 : stk asegs m7 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG7| exact STG6| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA6 MG7) as MGA7.
  clear MGA6 MG7 GSH6 PB6 RC6 STG6 STL6 MI6 AH6.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof GDID as G. unfold gdidA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fd7c) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: wrapP PB7 GSH7 RC7 STL7 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold gdidA_post in PO.
  destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m8 & -> & MI8 & STL8 & MG8 & AH8). retlitA.
  carry_cells MG8 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH8 : gshA m8) by (eapply gshA_mg; [exact MG8| intros a Ha; apply CLG; exact Ha| exact GSH7]).
  assert (PB8 : bytes_at asegs m8 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG8| exact PB7| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC8 : rclean m8 rstk) by (eapply rclean_mg; [exact RC7| exact MG8| exact CLR]).
  assert (STG8 : stk asegs m8 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG8| exact STG7| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA7 MG8) as MGA8.
  clear MGA7 MG8 GSH7 PB7 RC7 STG7 STL7 MI7 AH7.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof FDS as G. unfold fdsA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fd88) (SPAh SP)) with (lo := lo) (S := S') (bl := pl) (rstk := rstk); clear G.
    all: wrapP PB8 GSH8 RC8 STL8 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold fdsA_post in PO.
  destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m9 & -> & MI9 & STL9 & MG9 & AH9). retlitA.
  carry_cells MG9 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH9 : gshA m9) by (eapply gshA_mg; [exact MG9| intros a Ha; apply CLG; exact Ha| exact GSH8]).
  assert (PB9 : bytes_at asegs m9 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG9| exact PB8| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC9 : rclean m9 rstk) by (eapply rclean_mg; [exact RC8| exact MG9| exact CLR]).
  assert (STG9 : stk asegs m9 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG9| exact STG8| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA8 MG9) as MGA9.
  clear MGA8 MG9 GSH8 PB8 RC8 STG8 STL8 MI8 AH8.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof DBOUND as G. unfold dboundA_stmt, wrapA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fd94) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: try (change (80 / 8 + 1) with 11). all: wrapP PB9 GSH9 RC9 STL9 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold wrapA_post in PO.
  destruct PO as (o5 & o6 & o7 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & m10 & -> & MI10 & STL10 & MG10 & AH10). retlitA.
  carry_cells MG10 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH10 : gshA m10) by (eapply gshA_mg; [exact MG10| intros a Ha; apply CLG; exact Ha| exact GSH9]).
  assert (PB10 : bytes_at asegs m10 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG10| exact PB9| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC10 : rclean m10 rstk) by (eapply rclean_mg; [exact RC9| exact MG10| exact CLR]).
  assert (STG10 : stk asegs m10 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG10| exact STG9| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA9 MG10) as MGA10.
  clear MGA9 MG10 GSH9 PB9 RC9 STG9 STL9 MI9 AH9.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof FHSIZE as G. unfold fhsizeA_stmt, leafA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fda0) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: try (eapply rng_sub'; [exact RSTK| lia]). all: wrapP PB10 GSH10 RC10 STL10 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold leafA_post in PO.
  destruct PO as (r7 & n11 & n12 & n13 & n14 & n15 & m11 & -> & MI11 & STL11 & MG11 & AH11). retlitA.
  carry_cells MG11 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH11 : gshA m11) by (eapply gshA_mg; [exact MG11| intros a Ha; apply CLG; exact Ha| exact GSH10]).
  assert (PB11 : bytes_at asegs m11 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG11| exact PB10| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC11 : rclean m11 rstk) by (eapply rclean_mg; [exact RC10| exact MG11| exact CLR]).
  assert (STG11 : stk asegs m11 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG11| exact STG10| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA10 MG11) as MGA11.
  clear MGA10 MG11 GSH10 PB10 RC10 STG10 STL10 MI10 AH10.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evtF_cut.
  { pose proof ISFRAME as G. unfold isframeA_stmt, leafA_stmt in G. eapply (G L RNG (Z_to_bv 64 0x7fdac) (SPAh SP)) with (lo := lo) (S := S') (bl := pl); clear G.
    all: try (eapply rng_sub'; [exact RSTK| lia]). all: wrapP PB11 GSH11 RC11 STL11 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold leafA_post in PO.
  destruct PO as (r8 & l11 & l12 & l13 & l14 & l15 & m12 & -> & MI12 & STL12 & MG12 & AH12). retlitA.
  carry_cells MG12 ltac:(fun a Ha => first [apply CLS; lia | apply CLB; lia | apply CLH; lia]).
  assert (GSH12 : gshA m12) by (eapply gshA_mg; [exact MG12| intros a Ha; apply CLG; exact Ha| exact GSH11]).
  assert (PB12 : bytes_at asegs m12 S' (map (Z_to_bv 8) pl)) by (eapply bytes_at_magree; [exact MG12| exact PB11| rewrite length_map; intros a Ha; apply CLP; exact Ha]).
  assert (RC12 : rclean m12 rstk) by (eapply rclean_mg; [exact RC11| exact MG12| exact CLR]).
  assert (STG12 : stk asegs m12 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG12| exact STG11| intros a Ha; apply CLS; lia]).
  pose proof (MGX1 _ _ MGA11 MG12) as MGA12.
  clear MGA11 MG12 GSH11 PB11 RC11 STG11 STL11 MI11 AH11.
  (* [comment removed for export] *)
  assert (ZFP : forall mx zj, rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) LSH1 -> rw_cells asegs mx (FF + 32) [CB 48 zj] ->
            fcellA mx (FB1 FF :: LB) (FF + 32) 48 /\ shullA RNG mx (FB1 FF :: LB) (FF + 32) 48).
  { intros mx zj SH ZC. unfold LSH1 in SH.
    assert (SHZ : rw_cells asegs mx (Z.shiftr (FF + 32) 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 6)).
    { lazymatch type of SH with rw_cells _ _ _ [?a'; ?b'; ?c'; ?d'; ?e0; ?e1; ?e2; ?e3; ?e4; ?e5; ?g0; ?g1; ?g2; ?g3; ?g4; ?g5] =>
        change [a'; b'; c'; d'; e0; e1; e2; e3; e4; e5; g0; g1; g2; g3; g4; g5] with ([a'; b'; c'; d'] ++ [e0; e1; e2; e3; e4; e5] ++ [g0; g1; g2; g3; g4; g5]) in SH end.
      pose proof (proj1 (rw_cells_appA _ _ _ _ _) SH) as [_ X]. apply (proj1 (rw_cells_appA _ _ _ _ _)) in X. destruct X as [X _].
      cbn [cells_size csize Nat.add] in X.
      replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact X|].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F128 FHb. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    split.
    - split.
      + exists 1, FF, 128. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact FH| clear - F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
      + replace (FF + 32 + 48) with ((FF + 32) + 8 * Z.of_nat 6) by lia. apply (c1z_cells_unpoisoned 6 mx (FF + 32) SHZ); [clear - F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| unfold KEND in *; lia].
    - exists 1, FF, 128. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. split; [reflexivity|].
      split; [lia|]. split; [unfold KEND in *; lia|]. change (128 / 8) with 16. split; [rewrite ESH; exact (proj2 SH)| exact RSFF]. }
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
  lazymatch goal with SH : rw_cells asegs m12 (Z.shiftr FF 3 + 2147450880) LSH1, ZC : rw_cells asegs m12 (FF + 32) [CB 48 _] |- _ =>
    destruct (ZFP m12 _ SH ZC) as [FCE12 SHU12] end.
  eapply evtF_cut.
  { pose proof GFH as G. unfold gfhA_stmt, gfhaA_stmt_at in G. eapply (G L RNG (Z_to_bv 64 0x7fdbc) (SPAh SP)) with (lo := lo) (S := S') (bl := pl) (ZF := FF + 32); clear G.
    all: try exact FCE12. all: try exact SHU12. all: try exact I.
    all: try (eapply rng_sub'; [exact RFF| lia]). all: try (eapply rng_sub'; [exact RSFF|]; rewrite !shad_div; clear - FHb; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    all: try (clear - F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    all: wrapP PB12 GSH12 RC12 STL12 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold gfhaA_post in PO.
  destruct PO as (r9 & k5 & k6 & k7 & k11 & k12 & k13 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & zj1 & hb1 & zj2 & m13 & -> & MI13 & STL13 & MG13 & AH13 & ZFH13 & _). retlitA.
  lazymatch goal with ZC : rw_cells asegs m12 (FF + 32) [CB 48 _] |- _ => clear ZC end.
  carry_cells MG13 ltac:(fun a Ha => split; [first [apply CLS; lia | apply CLB; lia | apply CLH; lia]| lia]).
  destruct (rw_cells_forget asegs _ _ _ ZFH13) as [zj13 ZF13]. cbn [cells_size csize Nat.add] in ZF13. clear ZFH13.
  assert (GSH13 : gshA m13) by (eapply gshA_mg; [exact MG13| intros a Ha; split; [apply CLG; exact Ha| lia]| exact GSH12]).
  assert (PB13 : bytes_at asegs m13 S' (map (Z_to_bv 8) pl)).
  { eapply bytes_at_magree; [exact MG13| exact PB12| rewrite length_map; intros a Ha]. split; [apply CLP; exact Ha|].
    subst S'. destruct PAY as [(p & Hin & Hn)|[EP ED]]; [| rewrite EP in Ha; cbn in Ha; lia].
    replace (zlen pl =? 0) with false in Ha by (symmetry; apply Z.eqb_neq; lia). pose proof (FFD _ Hin) as FD. cbn in FD. lia. }
  assert (RC13 : rclean m13 rstk) by (eapply rclean_mg; [exact RC12| exact MG13| intros s Hs; destruct (CLR s Hs) as [X Y]; split; [exact X| split; [exact Y|]]; rewrite !shad_div in Hs; unfold ASHOFF in Hs; clear - Hs FHb FHu HU6 R3 ATR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  assert (STG13 : stk asegs m13 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG13| exact STG12| intros a Ha; split; [apply CLS; lia| lia]]).
  pose proof (MGX _ _ _ MGA12 MG13 (fun a Ha Hr => NCF a ltac:(lia) Ha)) as MGA13.
  clear MGA12 MG13 GSH12 PB12 RC12 STG12 STL12 MI12 AH12 FCE12 SHU12.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.              (* [comment removed for export] *)
  lazymatch goal with SH : rw_cells asegs m13 (Z.shiftr FF 3 + 2147450880) LSH1 |- _ => destruct (ZFP m13 _ SH ZF13) as [FCE13 SHU13] end.
  eapply evtF_cut.
  { pose proof GFHA as G. unfold gfhaA_stmt, gfhaA_stmt_at in G. eapply (G L RNG (Z_to_bv 64 0x7fdd0) (SPAh SP)) with (lo := lo) (S := S') (bl := pl) (ZF := FF + 32); clear G.
    all: try exact FCE13. all: try exact SHU13.
    all: try (eapply rng_sub'; [exact RFF| lia]). all: try (eapply rng_sub'; [exact RSFF|]; rewrite !shad_div; clear - FHb; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    all: try (clear - F128; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    all: wrapP PB13 GSH13 RC13 STL13 LE11 LE00 LE20 LBH' PR HC' BOT TP RSTK RI RIS RFS RR R1 R2 R3 HU1 HU2 HU5 HU6 SPAB LO ATR RLT SPA32. }
  cbv beta. intros ms' PO. unfold gfhaA_post in PO.
  destruct PO as (r10 & i5 & i6 & i7 & i11 & i12 & i13 & i14 & i15 & i16 & i17 & i28 & i29 & i30 & i31 & zk1 & hb2 & zk2 & m14 & -> & MI14 & STL14 & MG14 & AH14 & ZFH14 & _). retlitA.
  clear ZF13.
  carry_cells MG14 ltac:(fun a Ha => split; [first [apply CLS; lia | apply CLB; lia | apply CLH; lia]| lia]).
  assert (GSH14 : gshA m14) by (eapply gshA_mg; [exact MG14| intros a Ha; split; [apply CLG; exact Ha| lia]| exact GSH13]).
  assert (STG14 : stk asegs m14 (SPAh SP + 24) (SP + -72)) by (eapply stk_magree; [exact MG14| exact STG13| intros a Ha; split; [apply CLS; lia| lia]]).
  pose proof (MGX _ _ _ MGA13 MG14 (fun a Ha Hr => NCF a ltac:(lia) Ha)) as MGA14.
  clear MGA13 MG14 GSH13 PB13 RC13 STG13 STL13 MI13 AH13 FCE13 SHU13.
  (* [comment removed for export] *)
  destruct (FFLAG _ _ _ _ _ _ _ _ AH14 ltac:(left; reflexivity)) as (FLC14 & RG & GH & GC & GBL & GCI).
  pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
  eapply evtF_cut.
  { eapply ltoi_tail with (lo := lo) (FLG := fflag L 1 FF); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    all: try (unfold KEND; lia). all: try (eapply rng_sub'; [exact RSTK| lia]). all: try (unfold AHARNESS_STACK; lia).
    all: try (rewrite <- ESH; exact RSFF). }
  cbv beta. intros ms' (mp & m15 & -> & MU15 & WM15 & MIp & MU16 & WM16 & MI15 & ST15 & FLC15).
  assert (AHp : AHEAP AI L RNG st (FB1 FF :: LB) mp).
  { eapply (AI_frame AI); [exact AH14| exact MU15| exact WM15|].
    constructor; [cbn| constructor; [cbn; right; left; exists (FB1 FF); split; [left; reflexivity| cbn; lia]| constructor]].
    right; right. right; right. exists 1, FF, 128. split; [left; reflexivity|].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. clear - FHb F128. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
  assert (AH15 : AHEAP AI L RNG st LB m15).
  { eapply aheap_eqA; [exact AHr|].
    apply (mem_eq_singleA mp m15 (fflag L 1 FF) (Z_to_bv 8 0)); [lia| lia| exact MU16| apply byte_of_c1A; [exact FLC15| lia]]. }
  assert (MG15 : magree asegs (aclient_addr CI LB SP) m m15).
  { eapply magree_munch_step; [| exact MU16| exact WM16|].
    - eapply magree_munch_step; [exact MGA14| exact MU15| exact WM15|]. intros a Ha. cbn.
      split; [intros Hr; exact (NCH a ltac:(lia) Ha)|]. split; [intros Hr; exact (NCF a ltac:(lia) Ha)| exact I].
    - intros a Ha. cbn. split; [| exact I].
      intros Hr. refine (app_not_client CI LB SP (fflag L 1 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
      intros b Hb. exact (GBL b (or_intror Hb)). }
  assert (GSH15 : gshA m15).
  { unfold harness_invA, GSH_ADDR in *.
    pose proof (rw_cells_transport _ _ _ _ _ _ GSH14 MU15 WM15 ltac:(cbn; lia)) as X.
    eapply rw_cells_transport; [exact X| exact MU16| exact WM16|]. cbn. pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu. lia. }
  apply evtF_done. unfold ltoiA_post. rewrite !(unsigned_lit SP) by lia. do 14 eexists. exists FR, fc, m15. split; [reflexivity|].
  split; [exact MI15|]. split; [exact FC|]. split; [exact ST15|].
  split; [intros a Ha Hc; exact (MG15 a Ha Hc)|].
  split.
  { pose proof ATOP_al16 as A16. intros a Ha. refine (proj1 (MG15 a _ _)).
    - rewrite !shad_div in Ha. unfold ASHOFF in Ha. clear - Ha ATR RSP. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
      rewrite !shad_div in Ha. unfold ASHOFF in *. clear - Ha ATR A16 RSP T1 LY3. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split; [exact AH15| exact GSH15].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
End CANSEC1.
