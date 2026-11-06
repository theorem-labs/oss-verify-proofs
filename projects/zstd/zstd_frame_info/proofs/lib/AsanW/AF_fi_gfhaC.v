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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AH_fi_iface AF_fi_kit AF_fi_gfha_iface AF_fi_mem AF_fi_chk.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Ltac brr := first [if_true | if_false].
Definition bx (P : Prop) : Prop := P.
Ltac boxH H := lazymatch type of H with ?T => change T with (bx T) in H end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition AGOT_SUAR_F : Z := 0x98e90.    (* [comment removed for export] *)
Definition AGOT_GFHA_PC : Z := 0x99ab0.   (* [comment removed for export] *)

#[using="Type"] Lemma gfha_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m AGOT_SUAR_F [C8 (Z_to_bv 64 0xa0e80)] /\ rw_cells asegs m AGOT_GFHA_PC [C8 (Z_to_bv 64 0x800b0)].
Proof.
  intros m R. unfold AGOT_SUAR_F, AGOT_GFHA_PC. split;
    (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow8_c1sA : forall m s, rw_cells asegs m s [C8 (Z_to_bv 64 0)] -> rw_cells asegs m s (repeat (C1 (Z_to_bv 8 0)) 8).
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP <= KEND.
  Hypothesis LOS : lo <= SP - AFI_STACK.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition SPAz : Z := (SP - 128) - (SP - 128) mod 32.
  #[using="rc SP16"] Lemma spa_propsA : SP - 144 <= SPAz <= SP - 128 /\ SPAz mod 32 = 0 /\ (SP + -128) - (SP + -128) mod 2^5 = SPAz.
  Proof. unfold SPAz. change (2^5) with 32. Local Ltac2 Set LiaHints.tbl := fun () => "0010>57856635280.27000006S4SP16".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition GFRB : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="rc SP16 SPT LOS LOC RSTK RI"] Lemma gfha_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m ->
    rt_got m -> rt_shbase m -> rw_cells asegs m AGOT_SUAR_F [C8 (Z_to_bv 64 0xa0e80)] -> rw_cells asegs m 0xa0e80 [C4 (Z_to_bv 64 1)] ->
    evtF asegs RNG (fun ms' => exists m' jA,
        ms' = MS (mkR (Z_to_bv 64 0x80128) (Z_to_bv 64 SPAz) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                     (Z_to_bv 64 64) (Z_to_bv 64 0xa0e78) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 a0 a1 a2 a3 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFI_SM0) fc None m' (seg_rom asegs)
        /\ munch [(SP - 144, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SP + -96) GFRB /\ rw_cells asegs m' SPAz [CB 32 jA]
        /\ stk asegs m' lo SPAz /\ stk asegs m' (SPAz + 32) (SP + -96))
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFI_GFHA) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_F, AFI_GFHA, AFI_SM0 in *.
    unfold KEND in SPT. unfold AFI_STACK in LOS. pose proof atop_range as ATR.
    pose proof spa_propsA as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 144, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "02D0>10047693422.6710287669065.6510287669065.6710287669065.6810287669065.6910371693015.6810382188910.6710393098569.6711999059405.6512101529815.6712871218414.671340665966.67 13641502813.6614536006483.6014689973870.6815256069321.6915649124780.6816200917870.6716622434386.6516622434386.6716851888622.6917264948956.6717544628206.6918074052718.6719152212908.6719183954030.6819209691573.6019750732782.682027029998.68 21656933230.6721659919916.6721782962336.6522163107130.6923144071639.6723344239986.582342125148.67 24232518001.6924630998586.6825181880364.6825240764910.6825259836654.682533208966.58 25975660526.6926035549399.6926798724209.6727687638188.6828433776073.6829514832494.6730196181434.6731056488905.613106977902.67 31192823468.6931227244142.6831539821806.6731598888919.6731731548819.6732377744366.6832651489978.6732735658066.6532735658066.6733501386478.6833680001082.6833700542764.6734782976605.6635010564462.6735129172553.6736300595415.6836485046743.6736550167516.6736665128521.6836923423689.6837218310956.6739219183342.6839302203090.5639728246700.6842768970324.6542776797556.6142831019478.6542831019478.674359095406.67 43872227804.6744148617417.6845003960669.6645221239098.6845713281902.6745736959020.6746024206162.6546024206162.6746051971694.6746232973498.6846356275438.684641771485.66 46564874353.6746595340782.6846787521756.6747219577582.6847402546926.6847497584310.6148705164526.6749741439345.6850006492053.6750900201107.6551106262638.6751764527788.6851770312777.6751781592413.6654068232029.6654077074143.685432979569.68 54729132247.6856064834414.67563227834.67  57745675194.6757877014385.685853766638.68 58866340206.6759308628179.6259743357778.6559743357778.6760492306926.6861066828181.6561198613617.6761479303406.6861801218030.6962044423918.6762140770976.6762947167693.6763430708081.6863600210761.6764311933975.6164323629513.6764517175537.6164798196951.6865805175866.6765888922839.6865997241966.686652598510.68 66840963185.6767091113851.636755950281.68 68073979882.60698988910.67  7237347185.67 8514435441.68 8553591767.67 8583720762.68 8659565402.64 9155751918.68 00000B00C00D00E00F00G00Y00Z00[00\00n01@01E01W01i01j01n02@02R02d03603;03M03_03c04504604H04Z04l05005405905:05?05D05E05J05N05`06206306E06F06G06K06L06^06c06d07607:07L07^07_07`08208708I08[08m09209609;09M09N09O09P09U09V09W09[09m0:20:60:G0:X0:]0:b0;40;90;:0;?0;D0;V0;Z0;l0<>0<P0<U0<g0<l0<m0=?0=D0=V0=h0=m0>?0>@0>A0>B0>T0>X0>Y0>^0>c0>h0>i0>j0?<0?A0?F0?G0?Y0?k0?o0@A0@S0@e0@f0@g0A90AK0A]0Aa0Ab0Ac0Ad0Ae0Af0B80B90B>0B?0BQ0Bc0Bd0Be0Bf0Bg0C90C:0C;0C<0CA0CF0CXS3LOS3LOC3ATR4SPABSSSSSS3LOS3LOC3ATR4SPABSSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS2HBS3SPTSS3LOSS3LOSSS3SPTS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSSS2HBSS3LOS3LOC3ATR4SPABS3SPTSS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSSS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3SPTS2HBS3LOSS3LOS3LOC3ATR4SPABSSSS3LOSSSS2HBS3LOS3LOC3ATR4SPABS3LOSS2HBS3SPT3LOS3LOC3ATRS3SPT3LOS3LOC3ATRS3SPTS3SPTS3LOS3LOC3ATR4SPABS3LOSSS3LOSS3SPTS3LOS3LOC3ATR4SPABS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOSSS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABSSSS3LOS3LOC3ATR4SPABS2HBSS3LOSS3LOSS3LOSSSS3LOS3LOC3ATR4SPABS3SPTS3SPTSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2K0S3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBSSSSSS3LOS3LOC3ATR4SPABSS3SPTSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSSSSS3LOS3LOC3ATR4SPABSSSS3SPTS3LOSS3LOS3LOC3ATR4SPAB".
carve_frame 96%nat ST. carve_frame 32%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 12 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    release_frame FR0 ST (SP + -96).
    destruct (stk_split asegs _ lo (SPAz + 32) (SP + -96) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPAz + 32) 32 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 32) with 32 in STL, FRA. replace (SPAz + 32 - 32) with SPAz in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    clear GOT GSU.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  Definition GHDR (FF FLG : Z) (junk : list byte) : list cell :=
    [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800b0); CB 32 junk; C8 (Z_to_bv 64 FLG)].
  Notation f1c := (C1 (Z_to_bv 8 18446744073709551601)).
  Notation f3c := (C1 (Z_to_bv 8 18446744073709551603)).
  Notation f5c := (C1 (Z_to_bv 8 18446744073709551605)).
  Notation f8c := (C1 (Z_to_bv 8 18446744073709551608)).
  Notation z1c := (C1 (Z_to_bv 8 0)).
  Definition GSH1 : list cell := [f1c; f1c; f1c; f1c; f8c; f3c; f3c; f3c].
  Definition GSH5 : list cell := [f5c; f5c; f5c; f5c; f5c; f5c; f5c; f5c].

  (* [comment removed for export] *)
  #[using="lo SP16 LOS LOC RSTK RI"] Lemma gfha_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 aZ aS aN aF x28 x29 x30 x31 : word) m (FF FLG : Z)
      (j0 j1 j2 : word) (junk : list byte) (jA : list byte) (Q : machine_state -> Prop),
    rw_cells asegs m SPAz [CB 32 jA] ->
    rw_cells asegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells asegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m AGOT_GFHA_PC [C8 (Z_to_bv 64 0x800b0)] -> mem_inv asegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    (forall m' j24,
        munch [(SPAz, SPAz + 32); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450888)] m m' ->
        wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' SPAz [CB 24 j24; C8 (Z_to_bv 64 FF)] ->
        rw_cells asegs m' FF (GHDR FF FLG junk) -> rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) GSH1 ->
        Q (MS (mkR (Z_to_bv 64 0x80128) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 18446744073709551601) (Z_to_bv 64 0x1dcc9) (Z_to_bv 64 0x800b0) (Z_to_bv 64 18446744073709551603) x14 x15 x16 x17
                   (Z_to_bv 64 FF) aZ aS aN aF (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880)
                   s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x801bc) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR (Z_to_bv 64 0x80128) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               s2 aZ aS aN aF s7 s8 (Z_to_bv 64 2147450880) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x80128) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros FRA FFC SHF GPC MI FH FC F64 RF RSF K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold AGOT_GFHA_PC in *. pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    apply shadow8_c1sA in SHF. cbn [repeat] in SHF. Local Ltac2 Set LiaHints.tbl := fun () => "01X0>10191062042.8910299541350.8911543297765.7211603250610.8912066655206.9013067081226.9013557852353.8913739019142.8814105043984.8615160347210.9015186770862.8815341314694.8915849985162.8516283555162.9016753464773.8916867429482.9017941155254.8918343703478.8918369228174.8919202614250.8819599858853.861969924926.89 20200392866.8921470349994.9023584418860.8823687287154.9024200872257.8624521592556.9025334232912.8925418808852.8925927005322.9026774769626.902818573085.89 28897571974.9028987856538.9029181457478.8929417129412.8929790837596.7229792256216.8530781785830.8830906104780.8931693696482.9032365281766.8832923343604.893342490946.89 34167244991.8634252541850.8634437547116.8634437547116.8834437547116.8934437547116.9034597926842.8935301401292.89353645442.90  36685953222.9037568097140.8538709023052.9040737376082.8941091132398.8941188869198.8941545411645.884172397972.89 4173552739.89 42643832943.8942831019478.89441253466.88  44417097546.89449256530.77  45508725130.8946037991020.8546901542423.8947747998098.8848211285674.8948618085652.8951745884286.9051816630506.8951833088772.8651854515238.8751884304678.8653156436688.8653640511348.725464662474.89 55060265338.9056179406356.8656329465353.8556804907040.8957533215052.9058116526106.895812810966.88 58862976438.8859137473520.8959308628179.7759338331354.8962760451890.8963958622316.8964026414714.8864555500442.8966867539939.8667483587358.89678924119.85  68066155898.888369729414.88 861974622.90  8713374350.90 00000900>00O00T00Y00b01R01W01m02602?02D02Z03403d03m04604P05@05Z06706@07007907>07n08^08c09=09W0:10::0:?0:D0:M0:R0:W0:\0:a0:f0:k0;[0;`0;e0<U0<]0<f0<k0=00=50=:0=T0=Y0>I0>N0>O0>T0>]0>f0>o0?40?=0?F0?O0?X0?e0?n0@;0@D0@E0@J0A:0AC0AH0AQ0AZ0B70B<0BD0B^0Bc0C=0CW0C`0Ce0Cj0Co0D80D=0DB0DK0DW0D`0EP0EU0E^0F80FA0FJ0FK0FT0FY0Fb0FkS3FHb3FHdS3FHbS3F643FHa3FHc3ATRS3FHbS3FHbS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3LOS3LOC3FHb3ATR4SPABS3FHb3BSFS3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPABS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHb3FHdS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSF2HBS3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3LOS3LOC3FHb3FHc3ATR4SPABS3LOS3LOC3FHb3FHc3ATR4SPABS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHbS3FHbS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb2HBS3FHb3FHdS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbFS3FHbS3FHb3BSFS3FHb3BSFS3FHb3BSFS3FHbS3FHa3FHbS3FHa3FHbS3FHa3FHbS3FHb3BSFS3FHa3FHb3FHdS3FHb3BSFS3FHa3FHb3FHdS3FHb3BSFFS3FHbS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BSFS3FHbS3FHb3BSFS3FHb3BSFS3LOS3LOC3FHb3FHc3ATR4SPAB2HBS3FHbS3FHb2HBS3LOS3LOC3FHb3FHc3ATR4SPABS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHa3FHbS3FHbS3FHbS3FHbS3FHb3BSFS3FHbS3FHbS3FHa3FHbS3FHa3FHb2K0S3FHb3BSFS4SP163LOS3LOC3FHa3FHb3ATR4SPAB5SPA323BSF3FHu2K0S3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHa3FHbS3FHb3BSFFS3FHb3BSFS3FHbS3FHb3BSFS3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450888 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(SPAz, SPAz + 32); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450888)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).    (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    apply evtF_done. eapply K; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  Notation RET mm x5 x6 x7 x10 y11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 y11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (ret_pc ra) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  #[using="SP16 LOS LOC RSTK"] Lemma gfha_exit : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word) m (FF FLG : Z)
      (h0 : word) (j24 : list byte),
    rw_cells asegs m (Z.shiftr FF 3 + 2147450880) GSH1 ->
    rw_cells asegs m FF [C8 h0] -> rw_cells asegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells asegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells asegs m (SP + -96) GFRB -> rw_cells asegs m SPAz [CB 24 j24; C8 (Z_to_bv 64 FF)] ->
    stk asegs m lo SPAz -> stk asegs m (SPAz + 32) (SP + -96) -> mem_inv asegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 64 <= FLG) ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG FLG 1 ->
    evtF asegs RNG (fun ms' => exists (y11 : word) mp m',
        ms' = RET m' x5 x6 x7 x10 y11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
        /\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450888); (FF, FF + 8)] m mp /\ wmono asegs m mp /\ mem_inv asegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono asegs mp m' /\ mem_inv asegs m'
        /\ stk asegs m' lo SP /\ rw_cells asegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 x20 x21 x22 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x801dc) fc None m (seg_rom asegs)).
  Proof.
    intros until j24. intros SHF FF0 FF56 FLC FRB FRA STL STG MI FH FC F64 GH GC GF RF RSF RG.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
    unfold GSH1 in SHF. unfold GFRB in FRB.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "02=0?10299541350.10311556321255.84 11603250610.10312066655206.10213067081226.10213111200937.10313375273961.10313641502813.10114534088772.96 14793220770.10315160347210.10215341314694.10316283555162.10216407779222.97 16753464773.96 16867429482.10217264948956.10217738602889.10317941155254.96 18343703478.10318369228174.10319202614250.10220200392866.10321470349994.10222700267513.98 23404677272.1022342125148.102 23584418860.10223687287154.10223868465886.96 24232518001.10424521592556.10225071629079.10225071629079.10325071629079.96 25418808852.96 25653217698.10225862343643.10225927005322.10226101064249.10226676368569.10226774769626.10226798724209.1022818573085.96  28897571974.10228987856538.10229181457478.10329417129415.10129786624606.84 30781785831.10230906104780.10331693696482.10232365281766.10232923343607.10133416653251.1023342490946.103 33969101564.10234442460115.96 34597926842.10334782976605.10134878372889.10235235452859.10235301401292.103353645442.102  36550167516.10236685953222.10238709023052.10240811138462.10341091132398.10341545411633.95 42643832943.96 42831019478.10343279913209.10343641966309.10143872227807.10343928696920.10244417097546.103449256530.91   45003960669.10145508725130.10345619588500.1024641771485.101 46564874353.10246611809145.10346787521756.10246901542423.96 46924073390.10347747998098.10247936924685.10348046123689.10248162556019.10248211285674.10348618085655.10149741439345.10351574738409.10251781592413.10151816630506.10351854515239.10152889152969.10253443837467.96 53653468790.84 54068232029.10154077074143.1035432979569.103 5464662474.103 55060265338.10256392233662.96 56804907040.10357533215052.10257622410744.98 57871968190.10357877014385.10358116526106.1035812810967.102 58862976439.10259308628179.91 59338331354.10360125984793.10260243484271.96 61066828181.10361198613617.10262598956670.10262720184713.10262760451890.10362947167693.10263430708081.10463700058990.10263958622316.10364026414714.10264555500442.10366840963185.10268066155898.1026968827998.102 7237347185.102 7342793742.102 7698681169.105 8313926873.103 8369729415.102 8514435441.103 8715731207.104 9089233705.102 00000500J00O00T00]01T01n02702M03D03M03R03l04504e04n05705n06706Q07H07b08Y08b09009909B09G0:>0:T0:Y0:^0:c0:h0:m0;G0;L0;Q0;k0<b0=<0=E0=J0=O0=T0=]0=b0=g0=l0>10>60>m0?20?70??0@60@m0A20AL0AU0Ao0B80B=0C40C=0CB0CG0D>0DG0DL0DU0D^0EU0EZ0Ec0Ek0F40FA0FJ0FS0Fm0G60G;0GU0G^0Gc0HZ0IQ0JH0JM0Jg0K00K50K:0L10L:0LC0LH0M?0MY0M^0Mg0N00N50NO0Ni0O10O60O;0OI0P@0PE0PN0PS0PX0Pd0Pm0Qd0Qi0RC0RH0S?0SY0TP0TU0TZ0UQ0UV0U_0V90V>0VG0W>0WC0X:0X?0XY0X^0Xc0Xh0YBS3FHbS3F643FHa3FHc3GHc3ATRS3FHbS3FHbS3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3FHbS3LOS3LOC3FHb3ATR4SPABS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3FHbS4SP163LOS3LOC2GF3FHb3ATR4SPAB5SPA323BSF3FHu3GHuS3FHb3BSFS3LOS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3FHdS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3BSFS3FHa3FHb2K01HS3FHb3GHaS3LOS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPABS3FHbS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3FHb3FHc3ATR4SPABS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3BSFS3FHbS3FHbS3FHbS3FHb3BSFS3FHbS3FHbS3FHbS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHbS2GF3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHb3GHdS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3FHbS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3BSFS3FHbS3FHa3FHbS3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3FHbS2GF3FHbS3FHb3BSFS3FHa3FHb3FHdS3LOS3FHbS3FHb3BSFS3LOS3LOC3FHb3GHc3ATR4SPABS3LOS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3LOC3FHb3GHc3ATR4SPABS3FHb3BSFS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3FHbS3FHb3BSFS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3FHc3ATR4SPABS3FHbS3LOS3FHbS3LOS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS2GF3FHbS3FHbS3FHbS3FHa3FHb2K01HS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHb3BSFS3FHbS3FHbS3FHa3FHb2K0S3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450888 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450888); (FF, FF + 8)] m) as MU1.
    pose proof (wmono_refl asegs m) as WM1.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).  (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells asegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
        pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. zstep. zstep. zstep.        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv asegs mx |- _ => pose proof MIx as MIp; boxH MIp end end.
    boxH MU1. boxH WM1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl asegs mx) as WM2 end.
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    do 12 zstep. zstep. zstep.                    (* [comment removed for export] *)
    eapply stk_release in FRA; [| exact STL| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge asegs mx lo (SPAz + 32) (SP + -96) FRA STG ltac:(lia)) as ST2 end.
    release_frame FRB ST2 SP.
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    eexists _, _, _. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM1|]. split; [exact MIp|].
    split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
    split; [exact ST2| exact FLC].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  Definition GSH4 : list cell := [f1c; f1c; f1c; f1c; C1 (Z_to_bv 8 4); f3c; f3c; f3c].

  (* [comment removed for export] *)
  #[using="lo SP16 LOS LOC"] Lemma gfha_sm1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 aZ aS aN x28 x29 x30 x31 : word) m (FF FLG : Z)
      (junk : list byte) (Q : machine_state -> Prop),
    rw_cells asegs m (Z.shiftr FF 3 + 2147450880) GSH1 ->
    rw_cells asegs m FF (GHDR FF FLG junk) -> mem_inv asegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    (forall m' (hw : word) j8 j20,
        munch [(Z.shiftr FF 3 + 2147450884, Z.shiftr FF 3 + 2147450885); (FF + 32, FF + 36)] m m' ->
        wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) GSH4 ->
        rw_cells asegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800b0)] ->
        rw_cells asegs m' (FF + 24) [CB 8 j8; C4 hw; CB 20 j20] -> rw_cells asegs m' (FF + 56) [C8 (Z_to_bv 64 FLG)] ->
        Q (MS (mkR (Z_to_bv 64 0x80258) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 (FF + 32)) aS aN x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 32)) aS aN (Z_to_bv 64 5) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
                   (Z_to_bv 64 (-47205080)) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 AFI_AMEMCPY) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 5) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) aZ aS aN (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880)
               s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8022c) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros SHF FFC MI FH FC F64 RF RSF K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold AFI_AMEMCPY in *. pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    unfold GSH1 in SHF. unfold GHDR in FFC.
    Local Ltac2 Set LiaHints.tbl := fun () => "00G0>11543297765.6612166908997.8416683833881.8216687308951.8523584418860.8224955596333.8525071629079.8225071629079.8529790837596.6631930091218.8532365281766.824459438317.70 45217415001.8545221239098.8547747998098.8250945549068.8551854515238.8153640511348.6660125984793.8263198083866.7064026414714.8268066155898.828403067759.85 00000A00F00o01X01]01b01g01l02102602;02@02E02N03703@03E03J04304804A04J04OS3F643FHa3FHc3ATRS3FHbS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHb3FHdS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS3FHa3FHbS3FHbS3FHbS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS3FHbS3FHb3BSFS3FHb3BSFS3FHb".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450888 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    (* [comment removed for export] *)
    change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800b0); CB 32 junk; C8 (Z_to_bv 64 FLG)])
      with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1dcc9); C8 (Z_to_bv 64 0x800b0)] ++ [CB 32 junk] ++ [C8 (Z_to_bv 64 FLG)]) in FFC.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC. destruct FFC as [FF0 FFC]. cbn [cells_size csize Nat.add] in FFC.
    apply (proj1 (rw_cells_appA _ _ _ _ _)) in FFC. destruct FFC as [FJ FF56]. cbn [cells_size csize Nat.add] in FF56.
    replace (FF + Z.of_nat 24 + Z.of_nat 32) with (FF + 56) in FF56 by lia. replace (FF + Z.of_nat 24) with (FF + 24) in FJ by lia.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450884, Z.shiftr FF 3 + 2147450885); (FF + 32, FF + 36)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    apply evtF_done. eapply K; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="rc"] Lemma gfha_disp : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word) m (FF S nn : Z)
      (Q : machine_state -> Prop),
    0 <= S <= 2^64 -> 0 <= nn < 2^64 -> mem_inv asegs m ->
    (forall r : Z, (r = 5 /\ nn = 0) \/ (r = -1 /\ 0 < nn) ->
        Q (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) x19 (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x801dc) fc None m (seg_rom asegs))) ->
    (0 < nn < 5 -> 0 < S < 2^64 ->
        Q (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 5) (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) x19 (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x8022c) fc None m (seg_rom asegs))) ->
    (5 <= nn -> 0 < S < 2^64 ->
        Q (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 5) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) x19 (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x802fc) fc None m (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) x19 (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x801bc) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros SR NR MI K1 K2 K3.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "00=0>11607912823.5816631497688.6619256615076.6619570185257.6719570185257.6829426380195.6738954701265.5959314873579.6759314873579.6864300782718.6064300782718.6664300782718.677865969431.66 00000100200600=00D00U00V00]00h01201>01J01QSFS2K5S2NR2K0S2NR2K0S2NR3S0R2KS2K52K0SS2K02K5S2NR2K03K00S2SR3S0R1HS3S0R3S0E2KSS3S0R3S0E2KSS2NR2K0".
assert (ES : Z_to_bv 64 S = Z_to_bv 64 (S mod 2^64)) by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity).
    rewrite ES in K1, K2, K3 |- *. pose proof (Z.mod_pos_bound S (2^64) ltac:(lia)) as S0R. set (S0 := S mod 2^64) in *.
    assert (S0E : S0 <> 0 -> 0 < S < 2^64) by (subst S0; intros H; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    clearbody S0.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. brr.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. bcase KS.                              (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep. bcase K5.                            (* [comment removed for export] *)
      + apply evtF_done. apply K3; lia.
      + zstep. bcase K0.                          (* [comment removed for export] *)
        * apply evtF_done. apply K1. left. lia.
        * zstep. zstep. brr.                      (* [comment removed for export] *)
          apply evtF_done. apply K2; lia.
    - (* [comment removed for export] *)
      zstep. bcase K0.                            (* [comment removed for export] *)
      + zstep. bcase K5; [exfalso; lia|].         (* [comment removed for export] *)
        zstep. bcase K00; [| exfalso; lia].       (* [comment removed for export] *)
        apply evtF_done. apply K1. left. lia.
      + zstep.                                    (* [comment removed for export] *)
        apply evtF_done. apply K1. right. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="lo SP16 LOS LOC"] Lemma gfha_sm2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (FF S nn : Z) (hb : list byte)
      (Q : machine_state -> Prop),
    rw_cells asegs m (Z.shiftr FF 3 + 2147450880) GSH4 ->
    rw_cells asegs m (FF + 32) [CB 4 hb] -> mem_inv asegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    (forall m',
        munch [(Z.shiftr FF 3 + 2147450884, Z.shiftr FF 3 + 2147450885)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) GSH1 -> rw_cells asegs m' (FF + 32) [CB 4 hb] ->
        Q (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 5) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 5) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
                   (Z_to_bv 64 (-47205080)) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x801dc) fc None m' (seg_rom asegs))) ->
    (forall m',
        munch [(FF + 32, FF + 36)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) GSH4 -> rw_cells asegs m' (FF + 32) [C4 (Z_to_bv 64 0x184d2a50)] ->
        Q (MS (mkR (Z_to_bv 64 0x8027c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
                   (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 nn) x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 5) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
                   (Z_to_bv 64 (-47205080)) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 AFI_AMEMCPY) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 (FF + 32)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 5) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
               (Z_to_bv 64 (-47205080)) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x80258) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros SHF HB MI FH FC F64 RF RSF K1 K2.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    unfold AFI_AMEMCPY in *. pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    unfold GSH4 in SHF.
    Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11543297765.6511805467289.8111805467289.8212166908997.8012166908999.7614527708843.8123584418860.8229790837596.6532365281766.824104107904.81 42831019478.8149259209113.825023289763.81 51856612399.8153640511348.6564026414714.8267190198865.7767190198865.8168066155898.8200000A00F00K00P00U00Z00_00d00i01201;01d02M02R02W02`02e02j033S3F643FHa3FHc3ATRS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHbS3FHa3FHbS3FHb3FHdS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS3FHbS3FHbS3FHb3BSFS3FHbS3FHbS3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450888 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    zstep.                                        (* [comment removed for export] *)
    zstep. if_cases KQ; clear KQ.                 (* [comment removed for export] *)
    - (* [comment removed for export] *)
      pose proof (munch_refl [(Z.shiftr FF 3 + 2147450884, Z.shiftr FF 3 + 2147450885)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).    (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      apply evtF_done. apply K1; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
    - (* [comment removed for export] *)
      pose proof (munch_refl [(FF + 32, FF + 36)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      zstep. zstep.                               (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.                 (* [comment removed for export] *)
      apply evtF_done. apply K2; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="lo SP16 LOS LOC"] Lemma gfha_sm3 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (FF S nn : Z) (hb : list byte)
      (Q : machine_state -> Prop),
    rw_cells asegs m (Z.shiftr FF 3 + 2147450880) GSH4 ->
    rw_cells asegs m (FF + 32) [CB 4 hb] -> mem_inv asegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
    rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    (forall m' (r : Z) (x10' x11' : word), (r = 5 \/ r = -10) ->
        munch [(Z.shiftr FF 3 + 2147450884, Z.shiftr FF 3 + 2147450885)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' (Z.shiftr FF 3 + 2147450880) GSH1 -> rw_cells asegs m' (FF + 32) [CB 4 hb] ->
        Q (MS (mkR (Z_to_bv 64 0x8027c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 r) x11' x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 5) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
                   (Z_to_bv 64 (-47205080)) s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x801dc) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR (Z_to_bv 64 0x8027c) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) (Z_to_bv 64 (FF + 32)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 nn) (Z_to_bv 64 5) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
               (Z_to_bv 64 (-47205080)) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8027c) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros SHF HB MI FH FC F64 RF RSF K.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT. unfold AFI_STACK in LOS.
    pose proof spa_propsA as (SPAB & SPA32 & _).
    unfold GSH4 in SHF.
    Local Ltac2 Set LiaHints.tbl := fun () => "00<0>11543297765.6311805467289.8112166908998.7723584418860.8129790837596.6332365281766.8149259209113.8151856612396.8053640511348.6364026414714.8167190198865.7868066155898.8100000A00F00K00P00U00Z01C01H01M01V01[01dS3F643FHa3FHc3ATRS3FHbS3FHbS3FHbS3FHbS3FHbS4SP163LOS3LOC3FHb3ATR4SPAB5SPA323BSF3FHuS3FHbS3FHbS3FHb3BSFS3FHbS3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450888 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(Z.shiftr FF 3 + 2147450884, Z.shiftr FF 3 + 2147450885)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. if_cases KQ; clear KQ.                 (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).    (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      apply evtF_done. apply K; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; first [left; reflexivity | right; reflexivity].
    - zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).    (* [comment removed for export] *)
      zstep.                                      (* [comment removed for export] *)
      zstep. zstep.                               (* [comment removed for export] *)
      apply evtF_done. apply K; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; first [left; reflexivity | right; reflexivity].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
