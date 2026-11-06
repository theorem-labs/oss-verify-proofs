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
Ltac gfact CK := let C := fresh in destruct CK as [C|C]; [left; exact C| right; lia].
Ltac brr := first [if_true | if_false].
(* [comment removed for export] *)
Ltac guard_false :=
  first [ brr
        | let G := fresh "G" in if_cases G; zify_cond G;
          [ exfalso; first [ lia | rewrite ?unsigned_lit in G by lia; lia | rewrite ?unsigned_lit_wrap in G; rewrite ?Z.mod_small in G by lia; lia ]
          | clear G ] ].
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
    lazymatch goal with SH : rw_cells bsegs mx base _ |- _ =>
      pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.

Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SUAR_F : Z := 0x99068.    (* [comment removed for export] *)

#[using="Type"] Lemma ffsi_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m AGOT_SUAR_F [C8 (Z_to_bv 64 0xa1040)].
Proof.
  intros m R. unfold AGOT_SUAR_F. apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow32_c1sA : forall m s, rw_cells bsegs m s (repeat (C8 (Z_to_bv 64 0)) 4) -> rw_cells bsegs m s (repeat (C1 (Z_to_bv 8 0)) 32).
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
Definition FFHDR : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x81628)].

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
    lazymatch goal with PLx : bytes_at bsegs mx ?S (map (Z_to_bv 8) ?bl), PLR : Forall _ ?bl |- _ =>
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
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_F [C8 (Z_to_bv 64 0xa1040)] -> rw_cells bsegs m 0xa1040 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     (Z_to_bv 64 160) (Z_to_bv 64 0xa1038) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     (Z_to_bv 64 2147450880) a3 aS aN s6 aR s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 AFI_SM2) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 192, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -104) FFRB /\ rw_cells bsegs m' SPAz [CB 56 jA]
        /\ stk bsegs m' lo SPAz /\ stk bsegs m' (SPAz + 56) (SP + -104))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 aR aS aN a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFI_FFSI) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_F, AFI_FFSI, AFI_SM2 in *.
    unfold KEND in SPT. unfold AFI_STACK in LOS. pose proof atop_range as ATR.
    pose proof spa160_propsA as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 192, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "02N0>10287669065.6510287669065.6710287669065.6810287669065.6912797141358.6813641502813.66136972401.67  14033283697.6814159447534.6714809345196.6815696294482.6515696294482.6816033677678.6817264948956.6718860676809.6719007305966.671931560046.68 19737586030.6820555087086.6720609531986.6520609531986.6820836929836.6721155567546.6721360580334.6722163107130.672342125148.67 23426836628.6123814431342.6824630998586.6725085635185.61261014828.68  26181762798.6826368591214.6726486697545.6826669182065.6726746114263.6726845759404.6828123739863.6828975917550.6729789957596.6729954433683.6530013766257.6830196181434.6830718442606.683095167572.65 3100905814.61 31058586091.613147928521.67 31546410990.673199430677.65 32043890889.6732087020145.6932345147607.6732492854638.6732595612014.6832651489978.6832873346092.6733510318702.6833548848474.643355483630.67 33680001082.6733787253614.6834454534638.6734490278001.6734782976605.6634784644311.6835394805971.6035660069705.6836550167516.6737164696046.6737390157038.6737855536750.6838314496329.6838884154028.6838982958958.6739046174665.6839235794249.6739302203090.5639912449485.654068500334.68 4182447342.68 42831019478.6542831019478.6843473821806.6943609253714.6543609253714.6843872227804.6744804625134.6744905565996.6744908879575.6845003960669.6645221239098.6745751589358.6746232973498.694641771485.66 46787521756.6746949129329.6747297859287.6749738116823.675012112366.67 50565006190.6850933153196.6851124180206.6851781592413.6652026536339.685217574615.68 54068232029.6654077074143.6854226150513.6854256297073.6754452579182.6855866736855.69563227834.68  56777351022.6756941978156.6757334927063.6757496662641.6857745675194.6858536729426.6558536729426.6858687748809.6758906746862.6759116267735.6859308628179.6259468189348.5859629471470.6859700328558.6859705885297.6759748865774.6760404403273.686063100795.63 6101228726.60 61096069870.6761936291913.6962194574793.6762773241808.586290697132.67 62969565356.6963249165934.6863278952554.6063894255854.6764228753390.6764311933975.6164434514030.6964556005486.6864993435597.686562377109.68 65805175866.686736605166.67 67810302577.6868412063342.697136133920.68 7906086560.65 8013425879.67 8264524782.67 8583720762.67 8796323372.67 8989589102.69 00000100200300400F00K00L00M00_00c01501G01Y01^01_02102C02U02g03903K03O03T03f03k04004504G04L04^04b05405F05G05H05I05M05N05`05e05f05g05l06>06O06`06a06b07407507607707807J07\07a07e08708<08N08S08e09709809=09>09P09Q09V09h0::0:L0:M0:Q0:c0:d0:e0:j0:k0;=0;O0;T0;Y0;k0<=0<O0<T0<f0<j0<k0=00=50=G0=L0=Q0=V0=W0=X0=Y0=k0>=0>A0>S0>X0>Y0>Z0>_0>d0>e0>f0?80?90?>0?P0?T0?U0?V0?[0?m0@?0@@0@R0@S0@W0@X0@j0A<0A=0AO0AP0AQ0AR0Ad0Ae0Af0Ak0Ao0B30BE0BF0BX0Bj0Bk0C=0CO0CP0CQ0CV0Ch0Ci0D;0D?0DC0DD0DV0D[0D_0E1SSSSS3LOS3LOC3ATR4SPABS3LOSSSS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3SPTS3LOS3LOC3ATR4SPABS3SPTS3LOSS3LOSS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSSSS2HBSS3LOS3LOC3ATR4SPABS3LOSSSS3SPTS3LOS3LOC3ATR4SPABS3SPT3LOS3LOC3ATRS3SPT3LOS3LOC3ATRSSS3LOS3LOC3ATR4SPABSSSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3SPTS2HBS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOSSS3LOS3LOC3ATR4SPABSS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS2HBS3LOS3LOC3ATR4SPABSSS3LOSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3SPTS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS2HBSS3LOSS3SPTS3LOS3LOC3ATR4SPABS3SPTS3LOSS3LOSSSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOSSSS3LOSS3LOSSSS3LOS3LOC3ATR4SPABSS3SPTS3LOS3LOC3ATR4SPABS2HBSSS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSS2K0SS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSSSS3LOS3LOC3ATR4SPABSSS3LOSS2HBS2HBS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSSS3SPTS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS2HBS2HBSS3LOS3LOC3ATR4SPABS3SPTS2HBS3LOS3LOC3ATR4SPAB".
carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ (SP + -160) _ |- _ => release_frame H ST (SP + -104) end.
    destruct (stk_split bsegs _ lo (SPAz + 56) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPAz + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
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
    rw_cells bsegs m SPAz [CB 56 jA] ->
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) (repeat (C8 (Z_to_bv 64 0)) 4) ->
    mem_inv bsegs m ->
    ablk FF (FF + 256) -> FF + 256 <= ATOP -> FF mod 256 = 0 ->
    rng RNG FF 256 -> rng RNG (shad FF) 32 ->
    (forall m' j48,
        munch [(SPAz + 48, SPAz + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 20)] m m' ->
        wmono bsegs m m' -> mem_inv bsegs m' ->
        rw_cells bsegs m' SPAz [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
        rw_cells bsegs m' FF (FFHDR ++ [CB 224 junk; C8 (Z_to_bv 64 FLG)]) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) FSH1 ->
        Q (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 8) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x81628) fmt (Z_to_bv 64 18446744073709551608)
                   (Z_to_bv 64 18446744073709551601) x16 x17
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) aS aN s6 aR s8 s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                   x28 x29 x30 x31)
              FR (Z_to_bv 64 0x81774) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 2147450880) fmt aS aN s6 aR s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x816a4) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros FRA FFC SHF MI FH FC F256 RF RSF K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa160_propsA as (SPAB & SPA32 & _).
    apply shadow32_c1sA in SHF. cbn [repeat] in SHF. Local Ltac2 Set LiaHints.tbl := fun () => "02a0>10068480930.9010191062042.8910299541350.9010841825258.8711603250610.9012066655206.8713067081226.8713557852353.8913985161282.9014866570234.8515010729545.8615160347210.8715341314694.9016036404121.8616119891775.8516283555162.8716753464773.8916867429482.8717317695513.8617941155254.8918138708044.8518343703478.901834424842.83 18369228174.9018660396218.9019202614250.8719272833705.8619570126950.8520139715884.8720200392866.9020749162842.8721470349994.8721501873338.902221633111.84 22775997700.8923098415148.8523584418860.8723687287154.8723716884570.852408208171.84 24085599115.8424200872257.8424521592556.8724686014778.8725082048475.8425220040706.8525334232912.8925418808852.8925927005322.8726494647592.8426494647592.8526494647592.8726494647592.8926494647592.902673550442.87 26739224554.9026774769626.8726983927141.7127238062074.8727320971326.8827818633126.852818573085.89 28322672361.8628339690852.8928897571974.8728987856538.8729181457478.9029192875980.9029790837596.7129792256216.8430460132882.8530906104780.9031518365030.9031693696482.8731930091218.8732130763846.9032365281766.8732376603722.9032651601900.843342490946.90 33965537418.9034098841190.87341926777.86  34252541850.8434501900210.8534597926842.9035301401292.90353645442.87  36172772266.9036685953222.8736737505306.8737123351842.8538350898988.9038389508810.8738709023052.8739178121190.8739656437418.8741044649514.8541091132398.9041377675910.9041615107788.854173552739.89 41947725140.8942200342570.8542452747910.8742643832943.8942831019478.9043293708626.90441253465.88  44229320300.9044285789428.8444417097546.9044456543796.89449256530.76  45221239098.8745508725130.9045585588076.85456469350.90  45982589382.874606400646.85 46080113946.9046378729034.8546901542423.8947747998098.8747784655834.9047946365538.8748211285674.9048690461897.8649943447116.8750524051526.8551461429402.9051816630506.9052107682714.8552196777467.8453156436688.8453640511348.7153706860006.8554380492074.905464662474.90 54769888194.8755060265338.87563227834.90  56644364524.8756804907040.9056830590924.8757199698906.8557533215052.8758116526106.9058853655090.905927369220.89 59308628179.7659338331354.9059982339892.8960118775914.8561086006986.9061756290341.8562055344378.8562098338330.8762760451890.9063362316388.896386823154.87 63958622316.9064026414714.8764555500442.9065322707210.8466111488204.9066824274186.8766867539939.846794595386.85 68066155898.8768225802117.8868604035204.856961534548.89 7039361418.85 7139856330.87 9417716921.86 9899865354.85 00000`00i00n01701<01A01J02:02j03303803A03F03K03S03m04]04f04k05405905S05X06H06Q06k07007507:07j08308<08V08W08\08a08f09V09_09d09i0:Y0:^0:g0:l0;\0<60<P0<j0<o0=40=90=>0=C0=L0=U0=^0>00>J0>O0>W0>\0>a0>f0>k0?40?90?>0?C0?H0@80@=0@B0A20Ab0Ag0Al0B50B60Bf0Bo0C40C90CB0D20DL0DQ0EA0EJ0EO0Ei0FY0F^0Fg0Fl0G10GK0GT0G]0Gb0Gg0H00H50H>0HC0HL0HU0IE0IR0IW0IX0Ia0If0J30J<0JE0JJ0JO0JT0JY0Jb0K<0KA0L10L:0Lj0M30M80M=0MB0M\0Me0Mn0N30NM0NR0NW0O10OK0P;0PU0P^0Pc0Ph0Pm0QG0QL0QU0RE0RJ0RV0R_0Rd0S>0SX0T50T>0TG0U70U<0Ul0V10V:0VT0Vj0Vo0WI0WR0Wl0X50X:0XW0X\0Xe0Xn0Y30Y<S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3FHdS3FHbS3FHb3BSFS3FHbS3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHb3BSFS3FHbS3FHbS3FHb2HBS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHb3FHdS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFFS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3FHc3ATR4SPABS3LOS3LOC3FHb3FHc3ATR4SPABS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3FHb3BSFS3FHb3BSFS4F2563FHa3FHc3ATRS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHb2HBS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHbS3FHb3BSFFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHbS3FHb3FHdS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHb3BSFS3FHbS3FHbS3FHa3FHbS3FHbS3FHb3BSFS3FHbS3FHa3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHa3FHb3FHdS3FHbFS3FHb3BSFS3FHbS3FHa3FHb3FHdS3FHb3BSFS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHb3BSFS3FHbS3LOS3LOC3FHb3FHc3ATR4SPABS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHa3FHb2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSF2HBS3FHb3BSFS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPABS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHa3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHbS3LOS3LOC3FHb3FHc3ATR4SPAB2HBS3FHbS3FHb3BSFS3FHb3BSFS3FHbS3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.   (* [comment removed for export] *)
    pose proof (munch_refl [(SPAz + 48, SPAz + 56); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 20)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
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
        ms' = MS (mkR (Z_to_bv 64 0x81920) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 0) y14 x15 x16 x17
                     (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 R) s8
                     s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
                 FR (Z_to_bv 64 AFI_GFHA) fc None m' (seg_rom bsegs)
        /\ munch WD m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) FSH2
        /\ rw_cells bsegs m' R [CB 8 r0; CB 8 r1; CB 8 r2] /\ rw_cells bsegs m' FF FFHDR.
    Definition POST_SK : machine_state -> Prop :=
      fun ms' => exists (y10 y11 y12 y13 y14 : word) (cs : word) m',
        ms' = MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     y10 y11 y12 y13 y14 x15 x16 x17
                     (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 (Z_to_bv 64 R) s8
                     s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x819c0) fc None m' (seg_rom bsegs)
        /\ munch WD m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) FSH1
        /\ rw_cells bsegs m' R [C8 (Z_to_bv 64 0); C8 cs; C8 (Z_to_bv 64 0)]
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x45e0360e); C8 (Z_to_bv 64 0x1a436); C8 (Z_to_bv 64 0x81628)]
        /\ (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= zlen bl).
    Definition POST_D : machine_state -> Prop := fun ms' => POST_GF ms' \/ POST_SK ms'.

    Hypotheses (PL : bytes_at bsegs m S (map (Z_to_bv 8) bl)) (PLR : Forall (fun c => 0 <= c < 256) bl) (UNP : unpoisoned m S (S + zlen bl)) (NB : zlen bl < 2^62).
    (* [comment removed for export] *)
    Hypothesis PAY : 0 < zlen bl -> D <= S /\ S + zlen bl <= D + N /\ N <= 2^40 /\ ablk D (D + N) /\ D mod 16 = 0 /\ rng RNG D N /\ rng RNG (shad D) (shlen (N + 7))
                     /\ (D + N <= FF \/ FF + 256 <= D).
    Hypotheses (RR : rw_cells bsegs m R [CB 8 r0; CB 8 r1; CB 8 r2]) (RU : unpoisoned m R (R + 24)) (R8 : R mod 8 = 0) (RLO : SP <= R) (RHI : R + 24 <= KEND).
    Hypotheses (RGR : rng RNG R 24) (RGRS : rng RNG (shad R) 3).
    Hypotheses (FF0 : rw_cells bsegs m FF FFHDR) (SHF : rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) FSH1).
    Hypotheses (FH : ablk FF (FF + 256)) (FC : FF + 256 <= ATOP) (F256 : FF mod 256 = 0).
    Hypotheses (RF : rng RNG FF 256) (RSF : rng RNG (shad FF) 32) (MI : mem_inv bsegs m).

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
      pose proof (munch_refl WD m) as MU; pose proof (wmono_refl bsegs m) as WM; unfold WD in MU.
    (* [comment removed for export] *)
    Ltac payload K :=
      destruct (PAY ltac:(clear - K; lia)) as (DS & SN & NN & DH & D16 & RGA & RGS & SEPF);
      pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd); unfold AIMG_HI in DHa; pose proof DH as DHu; unfold ablk, AIMG_HI, KLS in DHu;
      assert (RGP : rng RNG S (zlen bl)) by (eapply rng_sub'; [exact RGA| clear - DS SN; lia]);
      boxH D16.

    (* [comment removed for export] *)
    #[using="rc lo SP16 LOS LOC D PL RR RLO FF0 SHF FH RSF MI"] Lemma ffsi_fopen : forall (y10 y11 y12 y14 : word),
      evtF bsegs RNG POST_GF
        (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 y11 y12 (Z_to_bv 64 0) y14 x15 x16 x17
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) s6 (Z_to_bv 64 R) s8 s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x818f4) fc None m (seg_rom bsegs)).
    Proof.
      intros. Local Ltac2 Set LiaHints.tbl := fun () => "00]0>12066655206.8813067081226.8815010729547.8715160347210.8816036404123.8716867429482.8818909631322.8819272833707.8620139715884.8821470349994.8823584418860.8723687287154.8823823397578.8724521592556.8824686014778.882673550442.88 26774769626.8828322672363.8728897571974.8828987856538.8831693696482.8831930091218.8832365281766.8734098841190.88341926779.87  353645442.88  36685953222.8838389508810.8838709023052.8841141437076.8741141437076.8842452747910.8845221239098.8845958212890.884605189994.88 46553288074.8847747998098.8753638430191.8054769888194.8856830590924.8857533215052.8864026414714.8768066155898.877303350522.88 9417716923.87 00000500>00C00L00Q00Z01301801=01F01K01h02A02F02O02X02a02f02k03403Q03n04304804=04Z04_04h04m05205705<05E05^06706P06m07207O07T07Y07b07k08D08IS3FHbS3FHb3BSFS3FHbS3FHb3BSFS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHbS3FHbS3FHb3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHbS3FHb3BSFS3FHb3BSFS3FHb3BSFS3FHbS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHbS3FHbS3FHb3BSFS3FHb3BSFS3LOS3LOC3RLO3ATR3FHb3BSFS3FHb".
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
      evtF bsegs RNG POST_SK
        (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 cs y12 y13 y14 x15 x16 x17
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 (Z_to_bv 64 R) s8 s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x8185c) fc None m (seg_rom bsegs)).
    Proof.
      intros y10 y12 y13 y14 cs CS. Local Ltac2 Set LiaHints.tbl := fun () => "00c0?10990985245.94 1532592237.93  15334474333.98 16439798173.98 16753464773.10317941155254.10318437397164.94 19039061412.10319302942247.94 22527583800.93 22954551237.93 24004349677.97 27320971326.1022818573085.103 29018245758.94 29791052619.93 3188101182.89  3188101183.85  35672354525.84 35970547509.92 37038741246.98 37254250633.93 37371137959.98 38453056857.88 41141437076.10341141437076.93 41141437076.94 41141437076.98 42643832943.10343754901852.85 44793722668.98 449256530.92   46901542423.1035091546205.88  53638430191.82 54302169230.2  56498826713.84 57018326411.89 57020423608.85 59308627018.1  59308628179.92 59314923118.1  59988911958.95 6192067805.89  63370524077.85 64373332722.93 65071494699.90 65073591832.86 65093347183.93 65499904044.89 68516218382.2  00000L00Q00j01F01c01l02H02a02i03E03J03O03T03Y03b03j04?04T04Y04^04g05C05K05P05U05Z05_05d05m06206N06[06`06e06j06n07307807=07A07M07P07i07n08308<08A08F08K08P08TS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3LOS3LOC3RLO3ATR3FHb3FHu3BSFS3FHb3FHdS3LOS3LOC3RLO3ATR3FHb3FHc2HBS3LOS3LOC3RLO3ATR3FHb3FHcS3FHb2HBS3LOS3LOC3RLO3ATR3FHb3FHc2HBS3FHbS3FHbS3FHbS3FHbS3RHI3FHbS3FHb2HBS3LOS3LOC3RLO3ATR3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS3RHI3FHbS3LOS3LOC3RLO3ATR3FHb3BSF2HBS3FHb2HBS3FHbS3FHbS3FHbS3FHbS3FHbS3FHa3FHbS3FHbS3LOS3LOC3RLO3ATR3FHb3FHc2HBS3FHa3FHb3FHdS3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3FHbS2K'S3FHa3FHb2K0S1KS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS3FHbS3RHI3FHbS3FHbS3FHbS3FHbS3FHbS2R8".
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
      evtF bsegs RNG POST_SK
        (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 cs y12 y13 y14 x15 x16 x17
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 (Z_to_bv 64 R) s8 s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x8184c) fc None m (seg_rom bsegs)).
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
      evtF bsegs RNG POST_SK
        (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 y10 y11 y12 y13 y14 x15 x16 x17
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (S + 7)) (Z_to_bv 64 (zlen bl)) s6 (Z_to_bv 64 R) s8 s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81b54) fc None m (seg_rom bsegs)).
    Proof.
      intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>15047390338.883188101180.88 35894200129.8745049100339.8846134221986.2 51619822405.8753638430191.8155320869225.9757020423608.8859314923118.1 65073591832.8900000500J00O00T00X00]00b01;01@01C01HS3FHbS3LOS3LOC3RLO3ATR3FHbS3FHbS3FHbS2R8S3FHbS3FHbS3LOS3LOC3RLO3RHI3ATR3FHbS3FHbS1KS3FHb".
prep.
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      rsh8 0 RS0.
      zstep. cbv beta. rewrite (byte_litA 0) by lia.   (* [comment removed for export] *)
      zstep. bcase K; [| exfalso; clear - K; lia].  (* [comment removed for export] *)
      apply ffsi_skst. intros C. exfalso. rewrite unsigned_lit_wrap in C. revert C. vm_compute. discriminate.
    Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

    #[using="rc lo SP16 LOS LOC D N PL PLR UNP NB PAY RR RU R8 RLO RHI RGR RGRS FF0 SHF FH RF RSF MI"] Lemma ffsi_disp : forall (x11 x12 x14 : word),
      evtF bsegs RNG POST_D
        (MS (mkR (Z_to_bv 64 0x816a4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                 (Z_to_bv 64 8) x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 S) (Z_to_bv 64 (zlen bl)) s6 (Z_to_bv 64 R) s8 s9 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF)
                 x28 x29 x30 x31)
            FR (Z_to_bv 64 0x81774) fc None m (seg_rom bsegs)).
    Proof.
      intros. Local Ltac2 Set LiaHints.tbl := fun () => "01N0?1038192613.109 10642097183.11010644847645.11110995361127.10911005214441.11513089779087.13013719952090.11214202172478.11414204193983.11515532809353.13715532809355.12115876805562.12815878973755.12916075584073.12816075585474.83 16800856201.12316802407995.11316806667014.11718396331479.12119900154986.12819907059691.12321207872554.98 21920002366.11321922154557.11223594159546.12723596332729.12625828295587.12827480200164.11228463136875.13028463137002.12828463137129.12628463137256.11828463137391.11628463137518.11428463137645.11228463138788.13228915217076.12028915217081.13728915217083.12128922925488.12929480061519.6  30095423860.1183130479241.137 3130479243.121 32243202979.2  32245681835.10233232332149.13735128348588.98 37333118246.12740489045054.98 41558158972.12941565867381.137415690285.103  43927186569.12343927186569.13743935878913.12843935878913.3  43978883656.10445069577529.12545069591865.11645071062585.12445689441237.13748153790514.10448208706517.12348208706519.12148208706520.12049382931351.13549654857396.14350181107707.12450398796620.14550506763632.98 52865404021.11752872182392.12053638430191.79 53670234653.12354240878742.14156733482216.13957686855230.11258811303191.12159310728147.1  59314988138.11359314988138.99 61448148287.11661450298680.10861450317112.11761941556568.11263108286900.13163108301236.12263110460347.13064295209549.10964301028607.99 64305156550.1036610091662.118 9396311051.4   00000>00J00V01<01b01n01o02;02G02H02I02U02a03003803^04D04j05905_06E06F06R06^06j07607B07N07W07`07i08208;08D08M08V08_08h09109:09A09M09N09O09S09_09n0:70:C0:D0:S0:b0;00;10;20;A0;E0;N0;Z0;f0<20<A0<M0<\0<k0=:0=I0=U0=a0=m0>90>G0>V0>[0>i0?50?A0?J0?Y0?^0@C0@h0A40A@0AL0AM0AY0Ae0B10BW0C=0Cc0Cl0D3S3FHb2K83DHb1HS3FHb2K83DHbS3FHb2K83DHbS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb2K83DHbFS3FHb2K83DHbS3FHb2K83DHbFFS3FHb2K83DHbS3FHb2K83DHbS2NB3FHb2K83DHbS2NB3FHbS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb2K83DHb2V1S3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcFS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS3FHb3DHbS2DS2SNS3FHb2K83DHbFFS2K8S3FHb2K83DHbS3FHb2K83DHb2V6S3FHb3DHbS3FHb2K83DHbFS3FHb2K83DHb2V4S3FHb2K83DHb2V4S3FHb2K83DHb1HFFS3FHb2K83DHb2EBS2EBS3FHb3DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHb2V5S3FHb2K83DHbS3FHb2K83DHb2V0S3FHb2K83DHb2V0S3FHb2K83DHb2V0S3FHb2K83DHb2V7S3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHb1HS3FHb2K83DHb2V2S3FHbS3FHb2K83DHb1HS3FHb2K83DHbS3FHb2K83DHbS3FHb3DHbS3FHb2K83DHb2V3S3KF0S3LOS3LOC3RLO3ATR3FHb2K82DS3DHa3DHb1GS3LOS3LOC3RLO3ATR3FHb2K82DS3DHa3DHb1GS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbFS3FHb2K83DHbS3FHb2K83DHbS3FHb2K83DHbS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3LOS3LOC3RLO3ATR2BB3FHb2K82SN3DHb3DHcS3FHb3DHbS2EB2K1".
prep. clear SHF' FF0'.
      zstep. bcase K8.                            (* [comment removed for export] *)
      { eapply evtF_mono; [apply ffsi_fopen|]. intros ms' H. left. exact H. }
      payload K8.
      zstep. bcase KF0; [exfalso; clear - KF0; rewrite ?unsigned_lit in KF0 by lia; lia|].   (* [comment removed for export] *)
      zstep. guard_false.                         (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) S UNP ltac:(lia) ltac:(lia)) as (c0 & CR0 & CK0 & SR0).
      pose proof (shaccS0 RNG D N S (zlen bl) RGS D16 DHb DS SN ltac:(lia)) as CA0.
      zstep. rewrite sxb_sval.                    (* [comment removed for export] *)
      eapply chkA_81744; [gfact CK0| exact SR0| lia| assumption|]. intros y1.
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) (S + 3) UNP ltac:(lia) ltac:(lia)) as (c3 & CR3 & CK3 & SR3).
      pose proof (shaccS RNG D N S (zlen bl) 3 RGS D16 DHb DS SN ltac:(lia)) as CA3.
      zstep. rewrite sxb_sval.                    (* [comment removed for export] *)
      eapply chkA_81758; [gfact CK3| exact SR3| lia| assumption|]. intros y2.
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
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. guard_false.                  (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) (S + 4) UNP ltac:(lia) ltac:(lia)) as (c4 & CR4 & CK4 & SR4).
      pose proof (shaccS RNG D N S (zlen bl) 4 RGS D16 DHb DS SN ltac:(lia)) as CA4.
      zstep. rewrite sxb_sval.
      eapply chkA_817ac; [gfact CK4| exact SR4| lia| assumption|]. intros y3.
      zstep. zstep. zstep.                        (* [comment removed for export] *)
      destruct (chkB _ S (S + zlen bl) (S + 7) UNP ltac:(lia) ltac:(lia)) as (c7 & CR7 & CK7 & SR7).
      pose proof (shaccS RNG D N S (zlen bl) 7 RGS D16 DHb DS SN ltac:(lia)) as CA7.
      zstep. rewrite sxb_sval.
      eapply chkA_817c0; [gfact CK7| exact SR7| lia| assumption|]. intros y4.
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
