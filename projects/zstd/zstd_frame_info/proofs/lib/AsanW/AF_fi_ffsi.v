(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem Mem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree StrFun Stdio_pure.
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
Ltac gfact CK := let C := fresh in destruct CK as [C|C]; [left; exact C| right; lia].
(* [comment removed for export] *)
Ltac umod K EB :=
  lazymatch type of EB with (0 <= ?v < _) =>
    try (change (Z.land (v + 8) 18446744073709551615) with (Z.land (v + 8) (2^64 - 1)) in K; rewrite (zb_land_mask (v + 8) 64) in K by lia);
    try (change (Z.land v 18446744073709551615) with (Z.land v (2^64 - 1)) in K; rewrite (zb_land_mask v 64) in K by lia);
    rewrite ?(unsigned_lit (v + 8)), ?(unsigned_lit v) in K by (clear - EB; lia);
    rewrite ?(Z.mod_small (v + 8) (2^64)), ?(Z.mod_small v (2^64)) in K by (clear - EB; lia)
  end.
Definition bx (P : Prop) : Prop := P.
Ltac boxH H := lazymatch type of H with ?T => change T with (bx T) in H end.
(* [comment removed for export] *)
Ltac neglit z := lazymatch z with
  | -8 => replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity)
  | -11 => replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity)
  | -13 => replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity)
  | -14 => replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity)
  | -15 => replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity)
  end.
(* [comment removed for export] *)
Ltac sok0 base :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SH : rw_cells asegs mx base _ |- _ =>
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.

Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SUAR_F : Z := 0x98e90.    (* [comment removed for export] *)

#[using="Type"] Lemma ffsi_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m AGOT_SUAR_F [C8 (Z_to_bv 64 0xa0e80)].
Proof.
  intros m R. unfold AGOT_SUAR_F. apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow32_c1sA : forall m s, rw_cells asegs m s (repeat (C8 (Z_to_bv 64 0)) 4) -> rw_cells asegs m s (repeat (C1 (Z_to_bv 8 0)) 32).
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Notation f1c := (C1 (Z_to_bv 8 18446744073709551601)).
Notation f2c := (C1 (Z_to_bv 8 18446744073709551602)).
Notation f3c := (C1 (Z_to_bv 8 18446744073709551603)).
Notation f5c := (C1 (Z_to_bv 8 18446744073709551605)).
Notation f8c := (C1 (Z_to_bv 8 18446744073709551608)).
Notation z1c := (C1 (Z_to_bv 8 0)).
Notation c04 := (C1 (Z_to_bv 8 4)).
(* [comment removed for export] *)
Definition FSHZ : list cell := [z1c; z1c; z1c; z1c; z1c; z1c; z1c; z1c; z1c; z1c; z1c; z1c].
Definition FSH1 : list cell := [f1c; f1c; f1c; f1c; f8c; f8c; f8c; f8c; f8c; f8c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ.
Definition FSH2 : list cell := [f1c; f1c; f1c; f1c; z1c; z1c; z1c; z1c; z1c; z1c; f2c; f2c; f2c; f2c; f8c; f8c; f3c; f3c; f3c; f3c] ++ FSHZ.
Definition FSH5 : list cell := [f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c;
                                f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c].
(* [comment removed for export] *)
Definition FFHDR : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x814a0)].

(* [comment removed for export] *)
#[using="Type"] Lemma lor_lt_pow2A : forall a b k, 0 <= a < 2^k -> 0 <= b < 2^k -> 0 <= Z.lor a b < 2^k.
Proof.
  intros a b k Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>26983584907.9 43330057433.7 44204549936.6 51796692231.7 59314955108.1161883703582.9 62711757.6    62742594.9    67469320460.7 67469320589.9 9666691384.11 00000700:00A00E00V00c00g00k00o01301ES2Ha2NaS1HS2Ha2HbS2HaS2Ha2Hb2Na2Nb1H1ES2Hb2Ha2Na2NbS2HbS2HbS2HaS2HaS2Ha2Hb2Na2Nb1H2H0".
split; [apply Z.lor_nonneg; lia|].
  assert (Hk : 0 <= k). { destruct (Z.le_gt_cases 0 k); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
  apply Z.log2_lt_pow2. { pose proof (Z.lor_nonneg a b). assert (Z.lor a b <> 0). { intros E. apply Z.lor_eq_0_iff in E. lia. } lia. }
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le32_boundA : forall b4 b5 b6 b7, 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  0 <= Z.lor (Z.lor (Z.land (Z.shiftl b7 24) 18446744073709551615) (Z.land (Z.shiftl b6 16) 18446744073709551615))
             (Z.lor (Z.land (Z.shiftl b5 8) 18446744073709551615) b4) < 2^32.
Proof.
  intros b4 b5 b6 b7 H4 H5 H6 H7. change 18446744073709551615 with (Z.ones 64).
  rewrite !Z.shiftl_mul_pow2, !Z.land_ones by lia. rewrite !Z.mod_small by lia.
  apply lor_lt_pow2A; apply lor_lt_pow2A; lia.
Qed.

(* [comment removed for export] *)
Ltac pose_rdA k H V :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with PLx : bytes_at asegs mx ?S (map (Z_to_bv 8) ?bl), PLR : Forall _ ?bl |- _ =>
      pose proof (buf_readA mx S bl k (conj PLx PLR) ltac:(lia)) as H;
      destruct (buf_nthA mx S bl k (conj PLx PLR) ltac:(lia)) as [_ V];
      try replace (wa (S + 0)) with (wa S) in H by (unfold wa; f_equal; lia) end end.
(* [comment removed for export] *)
#[using="Type"] Lemma shaccS : forall (RNG : footprint) D N S n i, rng RNG (shad D) (shlen (N + 7)) -> D mod 16 = 0 -> 0 <= D -> D <= S -> S + n <= D + N ->
  0 <= i < n -> acc_in RNG (Z_to_bv 64 (Z.shiftr (S + i) 3 + 2147450880), 1%nat).
Proof.
  intros RNG D N S n i RG D16 D0 DS SN Hi.
  eapply (rng_acc_litZ' RNG _ _ _ 1%nat 1 RG eq_refl eq_refl).
  unfold shlen. Local Ltac2 Set LiaHints.tbl := fun () => "0020>29784461061.1364396480240.1300000100?SS3D162DS2SN2Hi".
rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shaccS0 : forall (RNG : footprint) D N S n, rng RNG (shad D) (shlen (N + 7)) -> D mod 16 = 0 -> 0 <= D -> D <= S -> S + n <= D + N ->
  0 < n -> acc_in RNG (Z_to_bv 64 (Z.shiftr S 3 + 2147450880), 1%nat).
Proof. intros RNG D N S n RG D16 D0 DS SN Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0020>21007906567.1230826017513.12000004005S2HnS".
replace S with (S + 0) by lia. eapply shaccS; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shaccR : forall (RNG : footprint) R k, rng RNG (shad R) 3 -> 0 <= R -> 0 <= k -> k + 8 <= 24 ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr (R + k) 3 + 2147450880), 1%nat).
Proof.
  intros RNG R k RG R0 K0 K1. eapply (rng_acc_litZ' RNG _ _ _ 1%nat 1 RG eq_refl eq_refl).
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=18349166506.829784417117.8000007008S2K02K1S".
rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shaccR0 : forall (RNG : footprint) R, rng RNG (shad R) 3 -> 0 <= R -> acc_in RNG (Z_to_bv 64 (Z.shiftr R 3 + 2147450880), 1%nat).
Proof. intros RNG R RG R0. Local Ltac2 Set LiaHints.tbl := fun () => "0040=15045281282.522974238465.53190203068.5 45046991539.5000001002006007SSS2R0S".
replace R with (R + 0) by lia. apply shaccR; [exact RG| lia| lia| lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 192 - AFI_STACK.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition SPAz : Z := (SP - 160) - (SP - 160) mod 32.
  #[using="rc SP16"] Lemma spa160_propsA : SP - 191 <= SPAz <= SP - 160 /\ SPAz mod 32 = 0 /\ (SP + -160) - (SP + -160) mod 2^5 = SPAz.
  Proof. unfold SPAz. change (2^5) with 32. Local Ltac2 Set LiaHints.tbl := fun () => "0010>57856635280.27000006S4SP16".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition FFRB : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="rc SP16 SPT LOS LOC RSTK RI"] Lemma ffsi_pro : forall (t0 t1 t2 aR aS aN a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m ->
    rt_got m -> rt_shbase m -> rw_cells asegs m AGOT_SUAR_F [C8 (Z_to_bv 64 0xa0e80)] -> rw_cells asegs m 0xa0e80 [C4 (Z_to_bv 64 1)] ->
    evtF asegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     (Z_to_bv 64 160) (Z_to_bv 64 0xa0e78) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     a3 aR aS aN s6 s7 s8 s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
                 FR (Z_to_bv 64 AFI_SM2) fc None m' (seg_rom asegs)
        /\ munch [(SP - 192, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SP + -104) FFRB /\ rw_cells asegs m' SPAz [CB 56 jA]
        /\ stk asegs m' lo SPAz /\ stk asegs m' (SPAz + 56) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 aR aS aN a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFI_FFSI) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_F, AFI_FFSI, AFI_SM2 in *.
    unfold KEND in SPT. unfold AFI_STACK in LOS. pose proof atop_range as ATR.
    pose proof spa160_propsA as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 192, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "02N0>10047693422.6810287669065.6510287669065.6710287669065.6810287669065.6910382188910.6812871218414.681340665966.68 13641502813.66136972401.67  14033283697.6814689973870.6914809345196.6816200917870.6816622434386.6516622434386.6816851888622.6717264948956.6717544628206.6718074052718.6818860676809.6719183954030.6919750732782.672027029998.67 20836929836.6721155567546.6721656933230.6822163107130.672342125148.67 23426836628.6124630998586.6725085635185.6125240764910.6725259836654.6725975660526.67261014828.68  26486697545.6826669182065.6726746114263.6726845759404.6828123739863.6829514832494.6829789957596.6729954433683.6530013766257.6830196181434.6830888554350.673095167572.65 3100905814.61 31058586091.613106977902.68 31227244142.693147928521.67 31539821806.683199430677.65 32043890889.6732087020145.6932345147607.6732377744366.6732651489978.6832735658066.6532735658066.6832873346092.6733501386478.6733548848474.6433680001082.6734490278001.6734782976605.6634784644311.6835010564462.6835394805971.6035660069705.6836550167516.6738314496329.6838884154028.6839046174665.6839219183342.6739235794249.6739302203090.5639912449485.6542831019478.6542831019478.684359095406.68 43872227804.6744905565996.6744908879575.6845003960669.6645221239098.6745713281902.6846024206162.6546024206162.6846051971694.6846232973498.6946356275438.674641771485.66 46595340782.6746787521756.6746949129329.6747219577582.6747297859287.6747402546926.6748705164526.6849738116823.6749835279726.6750933153196.6851106262638.6851115376494.6751781592413.6652026536339.685217574615.68 54068232029.6654077074143.6854226150513.6854256297073.6755866736855.6956064834414.68563227834.68  56941978156.6757334927063.6757496662641.6857745675194.685853766638.67 58687748809.6758866340206.6859116267735.6859308628179.6259468189348.5859705885297.6759743357778.6559743357778.6860404403273.6860492306926.676063100795.63 6101228726.60 61479303406.6761801218030.6761936291913.6962044423918.6862194574793.6762289745774.6762773241808.586290697132.67 62969565356.6963278952554.6064311933975.6164993435597.686562377109.68 65805175866.6865997241966.696652598510.67 67810302577.68698988910.68  7136133920.68 7906086560.65 8013425879.67 8583720762.67 8796323372.67 9155751918.67 00000B00C00D00E00F00X00j01<01A01B01C01U01Y01k02=02O02a02f03803J03K03]03o04A04E04J04\04a04f04k05005B05T05f06806<06=06>06?06C06D06V06[06\06]06b07407E07V07W07i08;08<08N08O08P08Q08R08d08i09;09M09Q09c09h09m09n0:30:40:F0:X0:Y0:^0:_0:c0:d0;60;70;<0;=0;B0;G0;Y0;^0;b0;c0;h0;m0<?0<Q0<c0=50=:0=L0=Q0=c0=h0=i0>;0><0>N0>`0>a0?30?70?I0?[0?`0?a0?b0?g0?l0?m0?n0?o0@A0@F0@J0@K0@L0@Q0@c0@d0A60A70A;0A<0A=0AO0Aa0Ab0B40B50B60BH0BZ0B[0Bm0Bn0C@0CE0CI0CM0CN0CO0CP0CQ0CV0Ch0D:0D;0DM0DQ0DU0DV0D[0D_0E1S3LOS3LOC3ATR4SPABSSSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSSSS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3SPTS3LOS3LOC3ATR4SPABS3SPTS3LOSS3LOSS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBSSSS2HBSS3LOS3LOC3ATR4SPABS3LOSSSS3SPTS3LOS3LOC3ATR4SPABS3SPT3LOS3LOC3ATRS3SPT3LOS3LOC3ATRSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSSSSS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOSS3SPTSS3LOSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOSSS2HBSS3LOS3LOC3ATR4SPABSS3LOSSS3SPTS3SPTS3LOS3LOC3ATR4SPABS3LOSS2HBSS3LOSS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3LOSSS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSSSS3LOSS3LOSSSSS3LOS3LOC3ATR4SPABS3SPTS2HBSSS3SPTS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSS2K0SSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOSS2HBS2HBSSSSS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS2HBS2HBSS3SPTS2HBS3LOS3LOC3ATR4SPAB".
carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ (SP + -160) _ |- _ => release_frame H ST (SP + -104) end.
    destruct (stk_split asegs _ lo (SPAz + 56) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPAz + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 56) with 56 in STL, FRA. replace (SPAz + 56 - 56) with SPAz in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [lazymatch goal with H : rw_cells _ _ (SP + -104) _ |- _ => exact H end|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="lo SP16 LOS LOC RSTK"] Lemma ffsi_hdr : forall (x5 x6 x7 x11 x12 x13 fmt x14 x15 x16 x17 aR aS aN x28 x29 x30 x31 : word) m (FF FLG : Z)
      (j0 j1 j2 : word) (junk : list byte) (jA : list byte) (Q : machine_state -> Prop),
    rw_cells asegs m SPAz [CB 56 jA] ->
    rw_cells asegs m FF [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells asegs m (shad FF) (repeat (C8 (Z_to_bv 64 0)) 4) ->
    mem_inv asegs m ->
    ablk FF (FF + 256) -> FF + 256 <= ATOP -> FF mod 256 = 0 ->
    rng RNG FF 256 -> rng RNG (shad FF) 32 ->
    (forall m' j48,
        munch [(SPAz + 48, SPAz + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 20)] m m' ->
        wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
        rw_cells asegs m' FF (FFHDR ++ [CB 224 junk; C8 (Z_to_bv 64 FLG)]) -> rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) FSH1 ->
        Q (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 8) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x814a0) fmt (Z_to_bv 64 18446744073709551608)
                   (Z_to_bv 64 18446744073709551601) x16 x17
                   (Z_to_bv 64 FF) aR aS aN s6 s7 s8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                   x28 x29 x30 x31)
              FR (Z_to_bv 64 0x815ec) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               fmt aR aS aN s6 s7 s8 s9 s10 (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8151c) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros FRA FFC SHF MI FH FC F256 RF RSF K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa160_propsA as (SPAB & SPA32 & _).
    apply shadow32_c1sA in SHF. cbn [repeat] in SHF. Local Ltac2 Set LiaHints.tbl := fun () => "02a0>10068480930.8810191062042.8710299541350.8810841825258.9011603250610.8812066655206.9013067081226.9013557852353.8713985161282.8814866570234.9015010729540.8915160347210.9015341314694.8816036404116.8916119891775.8816283555162.9016753464773.8416867429482.9017317695508.8917941155254.8418138708044.9018343703478.881834424837.88 18369228174.8818660396218.8819202614250.9019272833700.8919570126950.9020139715884.9020200392866.8820749162842.9021470349994.9021501873338.882221633114.87 22775997702.8723098415148.9023584418860.9023687287154.9023716884570.902408208164.89 24085599108.8924200872257.8924521592556.9024686014778.9025082048468.8925220040706.9025334232912.8725418808852.8425927005322.9026494647592.8426494647592.8726494647592.8826494647592.8926494647592.902673550442.90 26739224554.8826774769626.9026983927141.7127238062074.9027320971313.8327818633126.882818573085.84 28322672356.8928339690854.8728897571974.9028987856538.9029181457478.8829192875980.8829790837596.7129792256213.8730460132882.9030906104780.8831518365030.8831693696482.9031930091218.9032130763846.8832365281766.9032376603722.8832651601889.873342490946.88 33965537418.8834098841190.90341926772.89  34252541850.8934501900210.9034597926842.8835301401292.88353645442.90  36172772266.8836685953222.9036737505306.9037123351842.9038350898988.8838389508810.9038709023052.9039178121190.9039656437418.9041044649514.9041091132398.8841377675910.8841615107788.904173552739.87 41947725142.8742200342570.9042452747910.9042643832943.8442831019478.8843293708626.8844229320300.8844285789433.87443350610.89  44417097546.8844456543798.87449256530.76  45221239098.9045508725130.8845585588076.90456469350.88  45982589382.904606400646.90 46080113946.8846378729034.9046901542423.8447747998098.9047784655834.8847946365538.9048211285674.8848690461892.8949943447116.9050524051526.9051461429402.8851816630506.8852107682714.9052196777460.8953156436688.8953640511348.7153706860006.9054380492074.885464662474.88 54769888194.9055060265338.90563227834.88  56644364524.9056804907040.8856830590924.9057199698906.9057533215052.9058116526106.8858853655090.885927369222.87 59308628179.7659338331354.8859982339894.8760118775914.9061086006986.8861756290341.8862055344378.9062098338330.9062760451890.8863362316390.876386823154.90 63958622316.8864026414714.9064555500442.8865322707207.8766111488204.8866824274186.9066867539939.896794595386.90 68066155898.9068225802119.8668604035204.886961534550.87 7039361418.90 7139856330.90 9417716916.89 9899865354.90 00000`00i00n01701<01A01J02:02j03303803A03F03K03S03m04]04f04k05405905S05X06H06Q06k07007507:07j08308<08V08W08\08a08f09V09_09d09i0:Y0:^0:g0:l0;\0<60<P0<j0<o0=40=90=>0=C0=L0=U0=^0>00>J0>O0>W0>\0>a0>f0>k0?40?90?>0?C0?H0@80@=0@B0A20Ab0Ag0Al0B50B60Bf0Bo0C40C90CB0D20DL0DQ0EA0EJ0EO0Ei0FY0F^0Fg0Fl0G10GK0GT0G]0Gb0Gg0H00H50H>0HC0HL0HU0IE0IJ0IK0IX0Ia0If0J30J<0JE0JJ0JO0JT0JY0Jb0K<0KA0L10L:0Lj0M30M80M=0MB0M\0Me0Mn0N30NM0NR0NW0O10OK0P;0PU0P^0Pc0Ph0Pm0QG0QL0QU0RE0RJ0RV0R_0Rd0S>0SX0T50T>0TG0U70U<0Ul0V10V:0VT0Vj0Vo0WI0WR0Wl0X50X:0XW0X\0Xe0Xn0Y30Y<S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3FHdS3FHbS3FHb3BSFS3FHbS3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHb3BSFS3FHbS3FHbS3FHb2HBS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHb3FHdS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFFS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3FHc3ATR4SPABS3LOS3LOC3FHb3FHc3ATR4SPABS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3FHb3BSFS3FHb3BSFS4F2563FHa3FHc3ATRS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHb2HBS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHbS3FHb3BSFFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHbS3FHb3FHdS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHb3BSFS3FHbS3FHbS3FHa3FHbS3FHbS3FHb3BSFS3FHbS3FHa3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbFS3FHa3FHb3FHdS3FHb3BSFS3FHbS3FHa3FHb3FHdS3FHb3BSFS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHb3BSFS3FHbS3LOS3LOC3FHb3FHc3ATR4SPABS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHa3FHb2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSF2HBS3FHb3BSFS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPABS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHa3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHbS3LOS3LOC3FHb3FHc3ATR4SPAB2HBS3FHbS3FHb3BSFS3FHb3BSFS3FHbS3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.   (* [comment removed for export] *)
    pose proof (munch_refl [(SPAz + 48, SPAz + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 20)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 9 zstep.                                   (* [comment removed for export] *)
    neglit (-8). neglit (-15).
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. neglit (-14).                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    sok0 (Z.shiftr FF 3 + 2147450880).
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    zstep. neglit (-13).                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    apply evtF_done. eapply K; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  Section Disp.
    Variables (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (m : amem) (FF S : Z) (bl : list Z) (D N R : Z) (r0 r1 r2 : list byte).
    Definition WD : list (Z * Z) := [(R, R + 24); (FF, FF + 8); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 10)].
    Definition POST_GF : machine_state -> Prop :=
      fun ms' => exists (y14 : word) m',
        ms' = MS (mkR (Z_to_bv 64 0x8178c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 0) y14 x15 x16 x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 (FF + 32)) s7 s8
                     (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
                 FR (Z_to_bv 64 AFI_GFHA) fc None m' (seg_rom asegs)
        /\ munch WD m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) FSH2
        /\ rw_cells asegs m' R [CB 8 r0; CB 8 r1; CB 8 r2] /\ rw_cells asegs m' FF FFHDR.
    Definition POST_SK : machine_state -> Prop :=
      fun ms' => exists (y10 y11 y12 y13 y14 : word) (cs : word) m',
        ms' = MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     y10 y11 y12 y13 y14 x15 x16 x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 s7 s8
                     (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x8182c) fc None m' (seg_rom asegs)
        /\ munch WD m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) FSH1
        /\ rw_cells asegs m' R [C8 (Z_to_bv 64 0); C8 cs; C8 (Z_to_bv 64 0)]
        /\ rw_cells asegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x814a0)]
        /\ (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl).
    Definition POST_D : machine_state -> Prop := fun ms' => POST_GF ms' \/ POST_SK ms'.

    Hypotheses (PL : bytes_at asegs m S (map (Z_to_bv 8) bl)) (PLR : Forall (fun c => 0 <= c < 256) bl) (UNP : unpoisoned m S (S + zlen bl)) (NB : zlen bl < 2^62).
    (* [comment removed for export] *)
    Hypothesis PAY : 0 < zlen bl -> D <= S /\ S + zlen bl <= D + N /\ N <= 2^40 /\ ablk D (D + N) /\ D mod 16 = 0 /\ rng RNG D N /\ rng RNG (shad D) (shlen (N + 7))
                     /\ (D + N <= FF \/ FF + 256 <= D).
    Hypotheses (RR : rw_cells asegs m R [CB 8 r0; CB 8 r1; CB 8 r2]) (RU : unpoisoned m R (R + 24)) (R8 : R mod 8 = 0) (RLO : SP <= R) (RHI : R + 24 <= KEND).
    Hypotheses (RGR : rng RNG R 24) (RGRS : rng RNG (shad R) 3).
    Hypotheses (FF0 : rw_cells asegs m FF FFHDR) (SHF : rw_cells asegs m (Z.shiftr FF 3 + 2147450880) FSH1).
    Hypotheses (FH : ablk FF (FF + 256)) (FC : FF + 256 <= ATOP) (F256 : FF mod 256 = 0).
    Hypotheses (RF : rng RNG FF 256) (RSF : rng RNG (shad FF) 32) (MI : mem_inv asegs m).

    (* [comment removed for export] *)
    #[using="rc FH"] Lemma ffsi_bsf : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 32 <= 17594333495296.
    Proof.
      pose proof atop_range as ATR. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). clear - ATR FHb FHc FHd.
      Local Ltac2 Set LiaHints.tbl := fun () => "0020=26987940019.629786463882.600000=00>S3ATR3FHb3FHcS".
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    #[using="rc SP lo LOS LOC RLO RHI FH"] Lemma ffsi_djr : disjoint_from WD (shad R) (shad (R + 24 - 1) + 1 - shad R).
    Proof.
      pose proof atop_range as ATR. pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
      pose proof ffsi_bsf as BSF. unfold AFI_STACK in LOS. unfold KEND in RHI.
      unfold WD. clear - ATR FHb FHc FHu BSF LOC LOS RLO RHI.
      Local Ltac2 Set LiaHints.tbl := fun () => "0040>29786394728.145032109165.14 57344981232.1465919105416.1400000100F00_010SS3LOS3LOC3RLO3ATR3FHuS3LOS3LOC3RLO3RHI3ATR3FHuS3LOS3LOC3RLO3ATR".
rewrite !shad_div, ?Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8. cbn [disjoint_from].
      repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
    (* [comment removed for export] *)
    Ltac rsh8 k H :=
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with MUx : munch _ _ mx |- _ =>
          let U := fresh "RU" in
          assert (U : unpoisoned mx R (R + 24)) by (eapply unpoisoned_munch; [exact RU| exact MUx| exact ffsi_djr]);
          pose proof (chk8_zero mx R (R + 24) (R + k) U ltac:(lia) ltac:(lia) ltac:(clear - R8; unfold bx in R8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as H;
          let A := fresh "RA" in
          pose proof (shaccR RNG R k RGRS ltac:(lia) ltac:(lia) ltac:(lia)) as A;
          try replace (R + 0) with R in H, A by lia; clear U end end.

    (* [comment removed for export] *)
    Ltac prep :=
      pose proof atop_range as ATR; unfold KEND in SPT, RHI; unfold AFI_STACK in LOS;
      pose proof (proj1 spa160_propsA) as SPAB;
      pose proof (bytes_at_bound _ _ _ _ PL) as BB; rewrite length_map in BB;
      pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd); unfold AIMG_HI in FHa; pose proof FH as FHu; unfold ablk, AIMG_HI, KLS in FHu;
      pose proof RSF as RSF'; replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF' by (unfold shad, ASHOFF; lia);
      boxH SP16; boxH F256; boxH R8;
      pose proof ffsi_bsf as BSF;
      pose proof SHF as SHF'; unfold FSH1, FSHZ in SHF'; cbn [app] in SHF'; pose proof FF0 as FF0'; unfold FFHDR in FF0';
      pose proof (munch_refl WD m) as MU; pose proof (wmono_refl asegs m) as WM; unfold WD in MU.
    (* [comment removed for export] *)
    Ltac payload K :=
      destruct (PAY ltac:(clear - K; lia)) as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF);
      pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd); unfold AIMG_HI in DHa; pose proof DH as DHu; unfold ablk, AIMG_HI, KLS in DHu;
      assert (RGP : rng RNG S (zlen bl)) by (eapply rng_sub'; [exact RGA| clear - DS SN; lia]);
      boxH D16.

    (* [comment removed for export] *)
    #[using="rc lo SP16 LOS LOC D PL RR RLO FF0 SHF FH RSF MI"] Lemma ffsi_fopen : forall (y10 y11 y12 y14 : word),
      evtF asegs RNG POST_GF
        (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 y11 y12 (Z_to_bv 64 0) y14 x15 x16 x17
                 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) s6 s7 s8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81760) fc None m (seg_rom asegs)).
    Proof.
      intros. Local Ltac2 Set LiaHints.tbl := fun () => "00]0>12066655206.8913067081226.8915010729544.8815160347210.8916036404120.8816867429482.8918909631322.8919272833704.8720139715884.8921470349994.8923584418860.8823687287154.8923823397578.8824521592556.8924686014778.892673550442.89 26774769626.8928322672360.8828897571974.8928987856538.8931693696482.8931930091218.8932365281766.8834098841190.89341926776.88  353645442.89  36685953222.8938389508810.8938709023052.8941141437076.8841141437076.8942452747910.8945221239098.8945958212890.894605189994.89 46553288074.8947747998098.8853638430191.8054769888194.8956830590924.8957533215052.8964026414714.8868066155898.887303350522.89 9417716920.88 00000500>00C00L00Q00Z01301801=01F01K01h02A02F02O02X02a02f02k03403Q03n04304804=04Z04_04h04m05205705<05E05^06706P06m07207O07T07Y07b07k08D08IS3FHbS3FHb3BSFS3FHbS3FHb3BSFS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHbS3FHbS3FHb3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHbS3FHb3BSFS3FHb3BSFS3FHb3BSFS3FHbS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3FHbS3FHb3BSFS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHb".
prep. clear PL UNP RSF SHF FF0.
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      apply evtF_done. unfold POST_GF, AFI_GFHA, WD, FSH2, FSHZ, FFHDR. cbn [app]. eexists _, _.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc lo SP16 LOS LOC D r0 r1 r2 PL RR RU R8 RLO RHI RGR RGRS FF0 SHF FH RF RSF MI"] Lemma ffsi_skst : forall (y10 y12 y13 y14 : word) (cs : word),
      (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
      evtF asegs RNG POST_SK
        (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 cs y12 y13 y14 x15 x16 x17
                 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 s7 s8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x816c8) fc None m (seg_rom asegs)).
    Proof.
      intros y10 y12 y13 y14 cs CS. Local Ltac2 Set LiaHints.tbl := fun () => "00a0>10990985245.931532592238.92 15334474333.9816439798173.9816753464773.9817941155254.9818437397164.9319039061412.9819302942247.9322527583800.9322954551237.9324004349677.9727320971313.972818573085.98 29018245758.9329791052619.933188101182.89 3188101183.85 35672354525.8435970547509.9237038741246.9837254250633.9337371137959.9838453056857.8841141437076.9341141437076.9842643832943.9843754901852.8544793722668.98449256530.92  46901542423.985091546205.88 53638430191.8254302169230.2 56498826713.8457018326411.8957020423608.8559308627018.1 59308628179.9259314923118.1 59988911958.956192067805.89 63370524077.8564373332722.9365071494699.9065073591832.8665093347183.9365499904044.8968516218382.2 00000L00Q00j01F01c01l02H02a02i03E03J03O03T03Y03b03j04?04T04Y04^04g05C05K05P05U05Z05c05h06D06Q06V06[06`06d06i06n07307707C07F07_07d07i08208708<08A08F08JS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHb3FHdS3LOS3LOC3RLO3ATR3FHb3FHc2HBS3LOS3LOC3RLO3ATR3FHb3FHcS3FHb2HBS3LOS3LOC3RLO3ATR3FHb3FHc2HBS3FHbS3FHbS3FHbS3FHbS3RHI3FHbS3FHb2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3RHI3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHb2HBS3FHbS3FHbS3FHbS3FHa3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc2HBS3FHa3FHb3FHdS3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3FHbS2K'S3FHa3FHb2K0S1KS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3RHI3FHbS3FHbS3FHbS3FHbS3FHbS2R8".
prep. clear PL UNP RSF SHF FF0.
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      rsh8 8 RS1.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.   (* [comment removed for export] *)
      zstep. bcase K; [exfalso; clear - K; lia|].  (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      rsh8 16 RS2.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.   (* [comment removed for export] *)
      zstep. bcase K'; [exfalso; clear - K'; lia|]. (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
      apply evtF_done. unfold POST_SK, WD. do 7 eexists.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc lo SP16 LOS LOC D r0 r1 r2 PL RR RU R8 RLO RHI RGR RGRS FF0 SHF FH RF RSF MI"] Lemma ffsi_skA : forall (y10 y12 y13 y14 : word) (cs : word),
      (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl) ->
      evtF asegs RNG POST_SK
        (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 cs y12 y13 y14 x15 x16 x17
                 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 s7 s8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x816b8) fc None m (seg_rom asegs)).
    Proof.
      intros y10 y12 y13 y14 cs CS. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>15047390338.893188101180.89 35894200129.8845049100339.8946134221986.2 51619822405.8853638430191.8255320869226.9757020423608.8959314923118.1 65073591832.9000000500J00O00T00X00]00b01;01@01C01HS3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS1KS3FHb".
prep.
      zstep. zstep.                               (* [comment removed for export] *)
      rsh8 0 RS0.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.   (* [comment removed for export] *)
      zstep. bcase K; [exfalso; clear - K; lia|].  (* [comment removed for export] *)
      apply ffsi_skst. exact CS.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    (* [comment removed for export] *)
    #[using="rc lo SP16 LOS LOC D r0 r1 r2 PL RR RU R8 RLO RHI RGR RGRS FF0 SHF FH RF RSF MI"] Lemma ffsi_skB : forall (y10 y11 y12 y13 y14 : word),
      evtF asegs RNG POST_SK
        (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 y11 y12 y13 y14 x15 x16 x17
                 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 s7 s8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x8199c) fc None m (seg_rom asegs)).
    Proof.
      intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>15047390338.883188101180.88 35894200129.8745049100339.8846134221986.2 51619822405.8753638430191.8155320869226.9657020423608.8859314923118.1 65073591832.8900000500J00O00T00X00]00b01;01@01C01HS3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS1KS3FHb".
prep.
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      rsh8 0 RS0.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.   (* [comment removed for export] *)
      zstep. bcase K; [| exfalso; clear - K; lia].  (* [comment removed for export] *)
      apply ffsi_skst. intros C. exfalso. rewrite unsigned_lit_wrap in C. revert C. vm_compute. discriminate.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    #[using="rc lo SP16 LOS LOC D N PL PLR UNP NB PAY RR RU R8 RLO RHI RGR RGRS FF0 SHF FH RF RSF MI"] Lemma ffsi_disp : forall (x11 x12 x14 : word),
      evtF asegs RNG POST_D
        (MS (mkR (Z_to_bv 64 0x8151c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 (Z_to_bv 64 8) x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17
                 (Z_to_bv 64 FF) (Z_to_bv 64 R) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) s6 s7 s8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 2147450880)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x815ec) fc None m (seg_rom asegs)).
    Proof.
      intros. Local Ltac2 Set LiaHints.tbl := fun () => "01F0?1038192613.109 10642097183.11010644847645.11110995361127.10911005214441.11513089779087.13014202172478.11414204193983.11515532809353.13715532809355.12115876805562.12815878973755.12916075584073.12816075585474.83 16800856201.12316806667014.11718396331479.12119900154986.12819907059691.12321920002366.11321922154557.11223594159546.12723596332729.12625828295587.12827480200164.11228463136875.13028463137002.12828463137129.12628463137256.11828463137391.11628463137518.11428463137645.11228463138788.13228915217076.12028915217081.13728915217083.12128922925488.12929480061519.6  30095423860.1183130479241.137 3130479243.121 32243202979.2  32245681835.10233232332149.13735128348588.98 37333118246.12741558158972.12941565867381.137415690285.103  43927186569.12343927186569.13743935878913.12843935878913.3  43978883656.10445069577529.12545069591865.11645071062585.12445689441237.13748153790514.10448208706517.12348208706519.12148208706520.12049382931351.13549654857396.14350181107707.12450398796620.14550506763632.98 52865404021.11752872182392.12053638430191.79 53670234653.12354240878742.14156733482216.13957686855230.11258811303191.12159310728147.1  61448148287.11661450298680.10861450317112.11763108286900.13163108301236.12263110460347.13064295209549.10964305156550.1036610091662.118 9396311051.4   00000>00J00V01<01b01n02:02F02G02H02T02`02o03703]04C04R05805^05j06606B06N06Z06f06o07807A07J07S07\07e07n08708@08I08R08Y08e08f08g08k09709F09O09[09j0:90:G0:H0:I0:X0:\0:e0;10;=0;I0;X0;d0<30<B0<Q0<`0<l0=80=D0=P0=^0=m0>20>@0>L0>X0>a0?00?50?A0?M0?Y0?e0@10@=0@c0AI0AR0AYS3FHb2K83DHb1HS3FHb2K83DHbS3FHb2K83DHbS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbFFS3FHb2K83DHbS3FHb2K83DHbS2NB3FHb2K83DHbS2NB3FHbS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb2K83DHb2V1S3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS2DS2SNS3FHb2K83DHbFFS2K8S3FHb2K83DHbS3FHb2K83DHb2V6S3FHb3DHbS3FHb2K83DHbS3FHb2K83DHb2V4S3FHb2K83DHb2V4S3FHb2K83DHb1HFFS3FHb2K83DHb2EBS2EBS3FHb3DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHb2V5S3FHb2K83DHbS3FHb2K83DHb2V0S3FHb2K83DHb2V0S3FHb2K83DHb2V0S3FHb2K83DHb2V7S3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHb1HS3FHb2K83DHb2V2S3FHbS3FHb2K83DHb1HS3FHb2K83DHbS3FHb2K83DHbS3FHb3DHbS3FHb2K83DHb2V3S3KF0S3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb3DHbS2EB2K1".
prep. clear SHF' FF0'.
      zstep. bcase K8.                            (* [comment removed for export] *)
      { eapply evtF_mono; [apply ffsi_fopen|]. intros ms' H. left. exact H. }
      payload K8.
      zstep. bcase KF0; [exfalso; clear - KF0; rewrite ?unsigned_lit in KF0 by lia; lia|].   (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) S UNP ltac:(lia) ltac:(lia)) as (c0 & CR0 & CK0 & SR0).
      pose proof (shaccS0 RNG D N S (zlen bl) RGS D16 DHb DS SN ltac:(lia)) as CA0.
      zstep. rewrite sxb_sval.                    (* [comment removed for export] *)
      eapply chkA_815b0; [gfact CK0| exact SR0| lia| assumption|]. intros y1.
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) (S + 3) UNP ltac:(lia) ltac:(lia)) as (c3 & CR3 & CK3 & SR3).
      pose proof (shaccS RNG D N S (zlen bl) 3 RGS D16 DHb DS SN ltac:(lia)) as CA3.
      zstep. rewrite sxb_sval.                    (* [comment removed for export] *)
      eapply chkA_815c4; [gfact CK3| exact SR3| lia| assumption|]. intros y2.
      pose_rdA 0 RB0 V0. pose_rdA 1 RB1 V1. pose_rdA 2 RB2 V2. pose_rdA 3 RB3 V3.
      zstep. cbv beta. rewrite (byte_litA _ V1).  (* [comment removed for export] *)
      zstep. cbv beta. rewrite (byte_litA _ V0).  (* [comment removed for export] *)
      zstep. cbv beta. rewrite (byte_litA _ V2).  (* [comment removed for export] *)
      zstep. cbv beta. rewrite (byte_litA _ V3).  (* [comment removed for export] *)
      clear RB0 RB1 RB2 RB3 CR0 CR3.
      do 9 zstep.                                 (* [comment removed for export] *)
      zstep. if_cases KM; clear KM.               (* [comment removed for export] *)
      { eapply evtF_mono; [apply ffsi_fopen|]. intros ms' H. left. exact H. }
      (* [comment removed for export] *)
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) (S + 4) UNP ltac:(lia) ltac:(lia)) as (c4 & CR4 & CK4 & SR4).
      pose proof (shaccS RNG D N S (zlen bl) 4 RGS D16 DHb DS SN ltac:(lia)) as CA4.
      zstep. rewrite sxb_sval.
      eapply chkA_81610; [gfact CK4| exact SR4| lia| assumption|]. intros y3.
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) (S + 7) UNP ltac:(lia) ltac:(lia)) as (c7 & CR7 & CK7 & SR7).
      pose proof (shaccS RNG D N S (zlen bl) 7 RGS D16 DHb DS SN ltac:(lia)) as CA7.
      zstep. rewrite sxb_sval.
      eapply chkA_81624; [gfact CK7| exact SR7| lia| assumption|]. intros y4.
      pose_rdA 4 RB4 V4. pose_rdA 5 RB5 V5. pose_rdA 6 RB6 V6. pose_rdA 7 RB7 V7.
      zstep. cbv beta. rewrite (byte_litA _ V5).  (* [comment removed for export] *)
      zstep. cbv beta. rewrite (byte_litA _ V4).  (* [comment removed for export] *)
      zstep. cbv beta. rewrite (byte_litA _ V6).  (* [comment removed for export] *)
      zstep. cbv beta. rewrite (byte_litA _ V7).  (* [comment removed for export] *)
      clear RB4 RB5 RB6 RB7 CR4 CR7.
      do 6 zstep.                                 (* [comment removed for export] *)
      pose proof (le32_boundA _ _ _ _ V4 V5 V6 V7) as EB.
      zstep.                                      (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; umod K1 EB.   (* [comment removed for export] *)
      - (* [comment removed for export] *)
        zstep.                                    (* [comment removed for export] *)
        zstep. zstep. zstep.                      (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; umod K2 EB.   (* [comment removed for export] *)
        + eapply evtF_mono; [apply ffsi_skA|]; [| intros ms' H; right; exact H].
          intros C. exfalso. rewrite unsigned_lit_wrap in C. revert C. vm_compute. discriminate.
        + eapply evtF_mono; [apply ffsi_skB|]. intros ms' H; right; exact H.
      - zstep. zstep. zstep.                      (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; umod K2 EB.   (* [comment removed for export] *)
        + eapply evtF_mono; [apply ffsi_skB|]. intros ms' H; right; exact H.
        + eapply evtF_mono; [apply ffsi_skA|]; [| intros ms' H; right; exact H].
          intros _. rewrite unsigned_lit by (clear - EB K1; lia). clear - EB K1 K2. lia.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  End Disp.
End S.
End CANSEC1.
