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
Ltac gfact CK := let C := fresh in destruct CK as [C|C]; [left; exact C| right; lia].
Ltac brr := first [if_true | if_false].
(* [comment removed for export] *)
Ltac guard_false :=
  first [ brr
        | let G := fresh "G" in if_cases G; zify_cond G;
          [ exfalso; first [ lia | rewrite ?unsigned_lit in G by lia; lia | rewrite ?unsigned_lit_wrap in G; rewrite ?Z.mod_small in G by lia; lia ]
          | clear G ] ].

Section CANSEC1. Context {rc : runConstT}.
Definition AFI_CBS : Z := 0x81f68.

(* [comment removed for export] *)
Definition cbsA_post (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (B lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (rw a1' a2' a3' a4' a5' a6' a7' : word) (w0 w1 w2 : list byte) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 rw a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPV - 16, SPV); (B, B + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' B [CB 4 w0; CB 4 w1; CB 4 w2].

(* [comment removed for export] *)
Definition cbsA_stmt : Prop :=
  forall (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (S : Z) (bl : list Z) (D N B lo : Z) (j0 j1 j2 : list byte),
  buf_atA m S bl -> unpoisoned m S (S + zlen bl) ->
  D <= S -> S + zlen bl <= D + N -> N <= 2^40 -> ablk D (D + N) -> D mod 16 = 0 -> rng RNG D N -> rng RNG (shad D) (shlen (N + 7)) ->
  rw_cells bsegs m B [CB 4 j0; CB 4 j1; CB 4 j2] -> B mod 8 = 0 -> ablk B (B + 16) -> (S + zlen bl <= B \/ B + 16 <= S) ->
  rw_cells bsegs m (shad B) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4)] ->
  rng RNG B 12 -> rng RNG (shad B) 2 ->
  rt_got m -> rt_shbase m ->
  stk bsegs m lo SPV -> ATOP <= lo -> lo <= SPV - 16 -> SPV <= KEND ->
  mem_inv bsegs m ->
  rng RNG lo (SPV - lo) -> rng_aimg RNG ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) -> a2 = Z_to_bv 64 B ->
  evtF bsegs RNG (cbsA_post ra SPV gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc B lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFI_CBS) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
#[using="Type"] Lemma cbs_sh4 : forall B, B mod 8 = 0 -> 0 <= B -> Z.shiftr (B + 4) 3 = Z.shiftr B 3.
Proof. intros B HB H0. Local Ltac2 Set LiaHints.tbl := fun () => "0020=25937578291.429784466142.4000004005S2HBS".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cbs_sh8 : forall B, B mod 8 = 0 -> 0 <= B -> Z.shiftr (B + 8) 3 = Z.shiftr B 3 + 1.
Proof. intros B HB H0. Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784466142.445070937396.4000001005SS2HB".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cbs_and3 : forall B, B mod 8 = 0 -> 0 <= B -> Z.land B 3 = 0.
Proof. intros B HB H0. change 3 with (Z.ones 2). Local Ltac2 Set LiaHints.tbl := fun () => "0020=41415991886.445299692563.4000001005SS2HB".
rewrite Z.land_ones by lia. change (2^2) with 4. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cbs_and8 : forall B, B mod 8 = 0 -> 0 <= B -> Z.land (B + 8) 7 = 0.
Proof. intros B HB H0. change 7 with (Z.ones 3). Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784466142.461524195958.4000001005SS2HB".
rewrite Z.land_ones by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Theorem cbsA : cbsA_stmt.
Proof.
  unfold cbsA_stmt, AFI_CBS.
  intros until j2. intros BUF UNP DS SN NB DH D16 RGA RGS BP B8 BH SEP SHB RB RSB GOT SHO ST LO0 LO SPK MI RSTK RI -> -> ->.
  pose proof atop_range as ATR. unfold KEND in SPK.
  pose proof (buf_atA_bound _ _ _ BUF) as BB. pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (ablk_lin _ _ DH) as (DHa & DHb & DHc & DHd). pose proof (ablk_lin _ _ BH) as (BHa & BHb & BHc & BHd). unfold AIMG_HI in DHa, BHa.
  pose proof BH as BHu. pose proof DH as DHu. unfold ablk, AIMG_HI, KLS in BHu, DHu.   (* [comment removed for export] *)
  unfold shlen in RGS. Local Ltac2 Set LiaHints.tbl := fun () => "02[0?10644829215.10610644847647.10911091121408.97 11091121410.94 11093218566.12311093218566.12411349999103.1211145821869.125 11519128502.12312042323546.12312112661933.89 12950240825.81 13014099899.10813479821317.12413493628854.1261410765161.103 1410765161.108 1410765161.113 14159447534.94 14202172478.11114204193982.10814549415356.12414722623428.86 15534906503.12516013641076.12716077671799.89 16166233773.96 16687308951.94 17072957449.11117072957576.11217075049779.89 18599469035.95 18714637664.1101874653880.124 19346380785.12619631634016.12620128390293.92 20802867008.81 20874704614.12321207970473.92 21210254767.11321609254393.10321609254393.10821609254393.11321834367905.11221920002365.10721922154557.110246216824.90   28465183341.10728763175104.11228771326923.11128913119920.12028913119921.12128913119927.12528922925877.11128922926004.11229786496665.81 29792256213.12329792256217.10329792256217.10829792256217.11329794353373.12629794353374.1242979471401.110 2979471401.111 2979471401.88  3078308012.126 31181228072.12231819521783.12235128445231.92 35272525002.94 35497698345.11135497698472.11235590246869.12235590246869.12435590246869.12535590246869.94 36197288178.12436197288178.12537246403421.11337553459782.12237553459782.12639188924977.1013968587220.124 40168848424.97 40488946365.92 40928202509.10340928202509.10840928202509.11341602066862.12341842979168.11042002707333.12442619492737.12642619492743.12242624157499.11443099569704.12243895326353.12443895326353.12543895326353.95 43895326353.98 43929283714.11844087318787.10244614245640.11244614245769.11145221239098.94 45221239098.95 45452174887.12345458048804.11245458048933.11146546460635.12346902361521.12447553020011.10647560020833.10147759751858.12447773440144.123477762999.125  49418115928.88 50038540763.1245012112366.94  50249520314.11350506861555.92 52359557716.12653275176713.12353302697915.92 53459164111.12453576224700.12453885437849.10254568502280.10354568502280.10854568502280.11354570599437.12154570599439.12554931758440.12555813923171.89 55833451695.12456570282919.1265909106547.124 59308628304.1  59308628433.1  59308628566.1  59308628695.1  59314988138.11459314988138.93 59316643886.12259776615842.12459781579349.10359781579349.10859781579349.11360385159294.95 60430575271.12462258075378.90 62932519634.97 63447792248.12364295209549.10364301028607.93 64305420614.96 64405586220.10364405586220.10864405586220.11364589843822.1256467166716.126 64780250393.12464886146559.12466841822056.12567263761269.12267863107804.12368060018741.1257029701634.124 7067733018.94  7067733018.95  8740845037.122 00000300600:00>00B00F00G00T00U00V01101201301<01E01F01G01H01T01W01Z01_01c01d01m02702:02J02N02R02V02W02X02Y02Z02[02\03603703803903:03;03<03?03B03E03T03U03f04704804904:04;04<04=04>04?04@04A04B04C04D04E04F04G04L04Q04R04^04_04`04a04b04c04d04m05605705805905<05=05>05?05@05A05B05C05D05E05N05W05`05e05f05g05h05i05j05m05n05o06406906:06;06<06=06I06Z06k06l06m07207307807D07E07H07I07J07K07L07Q07R07S07T07U07V07W07\08508608708808<08@08D08H08O08f08k09009109209309409509B09E09F09W09h0:90:Q0:i0;A0;F0;G0;T0;U0;Z0;f0;o0<;0<<0<@0<D0<QS1KS1KS2LOS2LOS2LOS2LOSS3DHb3BHb3AVBFSS2SN3LO02LO3ATR3BHu3DHu3BSBSSS2DS2SN1KS2DS2SN1KFFFS3LO02LO3ATRS1KS1KS3BHaS2LOFS3BHa3BHdS2DS2SN2NBS1HS3LO02LO3ATR3BSBS2LOS2LOS2LOSSSFFFS2DS2SN2B83SEP3ATR3BHu3DHuFFFFFFS1HS1KS1KS2SN3LO02LO3DHcSS2SN3ATR2BB3DHc1KS2SN3ATR2BB3DHc1KSSSSSSSSSSSSSSSFS3BHaS3BHaSS3LO02LO3BHcSSSSSSS3BHa3BHdS3BHa3BHdFSSS1HFSFFFFFSSS3BHa3BHdS3BHa3BHdS3BHa3BHdS3BHaSSSSFS1KSSS3SPKS3SPKFFFFS3LO02LO3BHcS2SN3ATR2BB3DHc1KS2SN3ATR2BB3DHc1KSFS3BHaSS3BHaS3LO02LO3ATRFS1KFFFSS3BHaSFFFSSS3BHaS2DS2SN3SEP3ATR3BHu3DHu1KFFFS2K1S2K2S2K3S2K4S3BHa1GS2DS3DHa1G2SN3ATR3DHc1KS3BHdS3BHdFFFFFS3SEP3DHb3BHbS1KSS2SN3ATR2BB3DHc1KS2SN3ATR2BB3DHc1KS2SN3ATR2BB3DHc1KS2DS2SN3D162BB3DHb3BHb1KS2DS2SN3D162BB3DHb3BHb1KS2DS2SN3D162BB3DHb3BHb1KS3BHdFS3DHb3BHb3AVBFS3BHaS3LO02LO3BHcS2DS2SN1KS3LO02LO3BHcFS2HBS2HBS3DHb3BHb3AVB".
rewrite Z.shiftr_div_pow2 in RGS by lia. change (2^3) with 8 in RGS.
  replace (shad B) with (Z.shiftr B 3 + 2147450880) in SHB, RSB by (unfold shad, ASHOFF; lia).
  assert (BSB : 2147450880 <= Z.shiftr B 3 + 2147450880 /\ Z.shiftr B 3 + 2147450880 + 2 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (app_vs_shadow B 16 (Z.shiftr B 3 + 2147450880) 2 BH (proj1 BSB) (proj2 BSB)) as AVB.
  assert (LOZ : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(SPV - 16, SPV); (B, B + 12)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.                                   (* [comment removed for export] *)
  zstep.                                          (* [comment removed for export] *)
  zstep. bcase K.                                 (* [comment removed for export] *)
  - (* [comment removed for export] *)
    lazymatch goal with H : munch _ m ?m1 |- _ => rename H into MU1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (UNP1 : unpoisoned m1 S (S + zlen bl)) by
        (eapply unpoisoned_munch; [exact UNP| exact MU1|]; rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from]; repeat split; try exact I; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia);
      assert (PL1 : bytes_at bsegs m1 S (map (Z_to_bv 8) bl)) by
        (refine (proj1 (buf_atA_frame m m1 S bl _ BUF MU1 _)); cbn [disjoint_from]; repeat split; try exact I; lia);
      assert (MI1 : mem_inv bsegs m1) by assumption
    end.
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep. zstep. guard_false.                    (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) S UNP1 ltac:(lia) ltac:(lia)) as (b0 & RD0 & CK0 & SR0).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_81f64; [gfact CK0| exact SR0| lia| assumption|]. intros y1.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) (S + 1) UNP1 ltac:(lia) ltac:(lia)) as (b1 & RD1 & CK1 & SR1).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    eapply chkA_81f78; [gfact CK1| exact SR1| lia| assumption|]. intros y2.
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    destruct (chkB _ S (S + zlen bl) (S + 2) UNP1 ltac:(lia) ltac:(lia)) as (b2 & RD2 & CK2 & SR2).
    zstep. rewrite sxb_sval.                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of PL1 with bytes_at _ ?m1 _ _ =>
      pose proof (buf_readA m1 S bl 0 (conj PL1 PLR) ltac:(lia)) as RB0; replace (wa (S + 0)) with (wa S) in RB0 by (unfold wa; f_equal; lia);
      pose proof (buf_readA m1 S bl 1 (conj PL1 PLR) ltac:(lia)) as RB1;
      pose proof (buf_readA m1 S bl 2 (conj PL1 PLR) ltac:(lia)) as RB2;
      destruct (buf_nthA m1 S bl 0 (conj PL1 PLR) ltac:(lia)) as [_ V0]; destruct (buf_nthA m1 S bl 1 (conj PL1 PLR) ltac:(lia)) as [_ V1];
      destruct (buf_nthA m1 S bl 2 (conj PL1 PLR) ltac:(lia)) as [_ V2] end.
    zstep. zstep.                                 (* [comment removed for export] *)
    eapply chkA_81f94; [gfact CK2| exact SR2| lia| assumption|]. intros y3.
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep. rewrite (cbs_and3 B B8 BHb).           (* [comment removed for export] *)
    zstep. guard_false.                           (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. rewrite (cbs_sh4 B B8 BHb).            (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. rewrite sxb_sval, sval_zero.           (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    clear RD0 RD1 RD2 RB0 RB1 RB2 UNP1 PL1.
    zstep. bcase K1; [exfalso; clear - K1; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. rewrite sxb_sval, sval_zero.           (* [comment removed for export] *)
    zstep. bcase K2; [exfalso; clear - K2; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. rewrite (cbs_sh8 B B8 BHb).            (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. rewrite sxb_sval, (sval_lit 4) by lia. (* [comment removed for export] *)
    zstep. bcase K3; [| exfalso; clear - K3; lia].  (* [comment removed for export] *)
    zstep. rewrite (cbs_and8 B B8 BHb).           (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. if_cases K4; unfold bv_lts in K4; rewrite !signed_lit_small64 in K4 by lia; zify_bool K4; [| exfalso; clear - K4; lia].
                                                  (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ ?m1 B [C4 ?a; C4 ?b; C4 ?c] |- _ =>
      apply (rw_cells_recast bsegs m1 B _ [CB 4 (le4 a); CB 4 (le4 b); CB 4 (le4 c)]) in H;
        [| cbn [cells_wf cell_wf]; rewrite !length_le4; repeat split; reflexivity | reflexivity | reflexivity] end.
    zstep. bcase K5.                              (* [comment removed for export] *)
    + zstep. zstep. zstep.                        (* [comment removed for export] *)
      lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
      apply evtF_done. unfold cbsA_post. do 11 eexists. eexists. split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; eassumption.
    + zstep. zstep. bcase K6.                     (* [comment removed for export] *)
      * zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
        lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
        apply evtF_done. unfold cbsA_post. do 11 eexists. eexists. split; [reflexivity|].
        repeat match goal with |- _ /\ _ => split end; eassumption.
      * zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
        lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
        apply evtF_done. unfold cbsA_post. do 11 eexists. eexists. split; [reflexivity|].
        repeat match goal with |- _ /\ _ => split end; eassumption.
  - (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ (SPV + -16) _, S9 : stk _ _ lo _ |- _ => release_frame H S9 SPV end.
    apply evtF_done. unfold cbsA_post. do 8 eexists. exists j0, j1, j2. eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
