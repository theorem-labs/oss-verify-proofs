(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ F_afree_s F_aalloc3.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S b1 actx lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x9d818) (Z_to_bv 64 hm) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 S)
                  a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x351b4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 18446744069414584320)]
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat.

#[using="Type"] Lemma dealloc_spec : forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  evtF asegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x30ef0) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros ST CEIL LO MI TP -> -> -> HD UW B1 B13 N AL H0 H1 HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RSTK RCTX RT RH. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  do 4 step. zstep. do 5 step.                 (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "04>0?10829118253.87 11054627826.87 11601497306.92 11801586693.92 11801586693.94 11912744615.91 12367362435.91 12367362435.94 12429510126.92 12596293756.99 12596293757.98 12596293758.97 12598390902.95 12614152141.87 12876582062.91 13021749692.91 13205419683.91 13205419683.93 13629548202.87 13696072622.91 13954570866.87 14308723042.87 14761575534.91 15060057555.85 15151140912.87 1527479463.89  15321888238.94 15323985382.96 15328766942.85 15401314670.91 15744906866.87 15835335440.86 16307494931.91 16856831405.87 16872280319.91 17212185306.92 17646078182.82 17755388179.93 17776320431.90 17776320431.93 18065550962.87 18376621181.87 18694006766.92 18944006493.96 19049469500.92 19697446968.84 19825051012.89 19882618009.86 20851542163.89 21918414723.91 21918414723.94 21969407398.86 22700267513.93 22700267513.95 2279663090.87  22981277779.86 23206405539.87 23371224676.85 23480589001.86 23589365338.91 24232371904.87 24254708740.97 24597239871.84 24630998586.89 25314760359.92 25473289966.89 25878270254.91 25878270254.94 26073886434.87 26274742996.99 27133822446.91 27576757255.92 27576757255.94 27802499922.91 27802499922.93 27841752864.87 27923971379.91 28260465738.86 29014636270.89 29510632509.87 29545175216.91 29782367974.85 29782367974.87 30299521578.85 30401015406.92 30597119136.87 30717345253.93 30985181748.88 30985181748.89 31023961714.87 31076427667.92 31081687356.92 31310932627.92 31949077106.87 32186460580.85 3226963954.87  32651489978.91 32805605483.10233039531175.92 33680001082.92 34356250836.89 34457081818.89 35340120754.97 35693303086.89 36115622446.91 36115622446.94 36436153477.86 36646331050.87 36829960868.86 36993589379.92 36993589379.95 37107179452.91 37317216127.92 37436222938.92 37823857774.89 3807747055.98  38211171107.87 38567244270.92 39093924078.92 39235284912.87 3945979267.91  3945979267.94  40608002030.92 40653749742.92 40655079551.89 40818989526.87 41501315873.86 41809558659.89 41809558659.93 41834437230.91 42104396270.92 42443086062.92 42831019478.91 42831019478.93 43060403331.92 43060403331.95 43061431595.80 43493603410.91 43493603410.93 43495041504.98 43495041505.97 43495041510.1004367084307.91  43987951406.91 43987951406.94 44484923210.92 44484923210.94 45065545733.87 45065545733.88 45221239098.92 45415010670.91 45672096911.91 45672096911.93 45998168737.86 46046479982.91 46162087634.91 46162087634.93 47250211438.91 47595661179.97 48057003647.92 4832059926.89  49097393336.86 49257279598.91 49345641752.85 49425192486.86 49671508435.85 49671508435.86 49724318719.91 50077211645.92 50077211645.94 50131772669.87 50354202374.91 50354202374.93 50487304575.92 50655895377.86 51159913016.86 51425718543.91 51425718543.94 51481786499.92 51481786499.95 51678667183.90 51678667183.93 51877860133.85 51877860133.86 52050947361.86 52198366190.92 52567164907.86 52567164907.89 52567164907.91 52567164907.92 52567164907.93 52575291859.87 52931696866.84 52994560594.91 52994560594.93 53089759638.87 53543936754.87 53767577775.90 53767577775.93 54856865902.91 55031195310.91 55539254254.92 55602792399.85 55602792399.86 55707291962.95 56062130284.85 56172410267.84 56172560690.85 56228262055.91 563227834.91   56323790752.92 56323790752.94 56324080430.92 56426686290.91 56426686290.93 56712086766.89 56729251374.92 56757832430.92 57068160275.91 57745675194.91 58057019758.92 59134147250.91 59285968488.92 59314873579.85 59782941985.86 60025031335.92 60223348125.93 60708418864.87 60723900404.10060797519086.91 60976774461.92 60976774461.94 61214533978.91 61415267707.10061454936069.87 61454936069.88 61519228526.91 61534126184.92 61669289758.97 61917199023.90 61917199023.93 61939782290.98 62541917565.92 62541917565.94 62575797294.92 63045513727.91 63235321900.88 63235321900.92 63694018620.92 637930994.87   63903202542.89 64352634714.91 64862446845.92 64862446845.94 65458892654.92 67800801447.91 67950805870.91 68008320110.91 68199404270.91 7010956092.89  7754842205.93  8172837742.91  8583720762.92  8610795133.92  8610795133.94  9151284627.92  9295039668.84  9529829153.86  985337532.91   9956545262.92  00000800@00L00f01@01A01B01C01L01P01T01X01\01a01m02102=02F02G02S02[02d02m02n03203303:03A03J03S03[03_03o04704C04O04P04Q04U04Y04a04m05605;05?05\05]05^05n05o06006406e07V07^07_07h07i07m08908:08;08X08]08^08g08k08o09809=09F09G09H09Q09U09^09_09c09l0:10:50:60:70:80:A0:J0:K0:Z0:i0;10;A0;E0;U0;]0;^0;f0;k0;l0;m0<20<30<?0<@0<L0<P0<T0<X0<[0<d0<e0<f0<j0=60=B0=K0=L0=U0=^0=g0=k0=l0=m0>60>?0>K0>L0>P0>Q0>R0>[0>d0>m0?20?60?70?80?<0?E0?I0?J0?K0?L0?\0?`0?d0?e0?f0?k0@00@50@>0@N0@h0@l0A50A>0AB0AK0AP0A\0A]0Ai0B20B30B80B90B:0BF0BS0B`0Bl0C80C90CE0CI0Cc0Cd0Ce0Cf0Cg0Ck0Co0D30D70D;0DD0DE0DF0DG0DH0DI0DJ0DQ0DZ0D^0D_0Dg0Dk0Do0E80ED0EM0EQ0EU0EV0EW0EX0EY0EZ0E_0Eo0F?0FK0FT0FX0Fa0Fm0G60GF0GK0GT0G`0Ga0Gh0Gl0Gm0H90H:0H;0HD0HQ0H^0Hj0Ho0I40I90IB0IC0IG0IK0IO0IR0I_0Il0J80JD0JH0JL0JP0JX0Ja0Jm0K:0KG0KP0KQ0KZ0Kc0Kl0L00L40L=0LB0LO0L\0Ll0MI0MM0MQ0MZS2T03LSJS2T03LSJS4CEIL2LO2H1S3Hsp4CEIL2LO2C12H12T13LSJS4CEIL2LO2H13Hsp2C12T13LSJSSSS4CEIL2LOS2B1S2B1S2B1S2B1S3LSJS4CEIL2LO2H1S2HBS4CEIL2LO2C1S3LSJ3DHCSS4CEIL2LO2H1S2T03LSJS3LSJ3DHTS4CEIL2LOSS2T1SS2H02H1S2H02H1S2H02H11HS4CEIL2LOS2T03LSJS2B1S4CEIL2LO2T13LSJS2T03LSJS4CEIL2LO2C1S4CEIL2LO2H1SSS2LOS2LOS2T03LSJS4CEIL2LO2T1S4CEIL2LOS3LSJS2HBS2AL2H02C03LSJ3DHT3DHC3CT22K0SSS4CEIL2LO2T13LSJSSS2B1S4CEIL2LO2H02H12C02C12T13LSJ3DHT3DHC3CT22K03Hsp1HS4CEIL2LO2H02H12C02C12T13LSJ3DHT3DHC3CT22K03Hsp1HS2T03LSJSS3LSJ3CT2SS2HBS4CEIL2LO2H1SSS2AL2H02C03LSJ3DHT3DHC3CT22K0S3SPRSS4CEIL2LOS2LOS2LOS3LSJ3DHTS3LSJS4CEIL2LOFFS4CEIL2LOS2H0S3LSJ3DHTSS2H0S4CEIL2LOS3LSJS2HBSSSS4CEIL2LOS3LSJ3DHTSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2T03LSJS4CEIL2LO2T13LSJS2HBS4CEIL2LO2T13LSJS2T03LSJSS2T03LSJS3SPRSSS3SPRSS4CEIL2LO2H1SS4CEIL2LO2H1S2LOS2LOS2LOS1NS3LSJ3DHCSSS2HBS4CEIL2LO2C1S4CEIL2LO2H1S4CEIL2LOSS3LSJ3CT2S4CEIL2LOS4CEIL2LOS2T1SSS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1SS2H0SSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS2HBSSS2LOS4CEIL2LOS2H0FFFS4CEIL2LO2T13LSJS2LOS2LOFFS3LSJS3LSJS3SPRS4CEIL2LOS4CEIL2LO2T13LSJS2H02C03LSJ3DHT3DHC3CT22K0S2H0S4CEIL2LOS4CEIL2LOS2H0S4CEIL2LOS3LSJS4CEIL2LO2C1SS4CEIL2LO2H1S4CEIL2LOSS3CX0SSS4CEIL2LO2C1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T1S4CEIL2LO2H1SS4CEIL2LO2C1S2B1S2H02C03LSJ3DHT3DHC3CT22K0SSSSS2LOS2LOS2LOS2LOS2H0S4CEIL2LOSSSSSSS2H02H1S4CEIL2LOS2H0SS2T03LSJS2LOS2LOS4CEIL2LOS4CEIL2LO2H1S4CEIL2LOS2B1S2B1SSSSSS3SPRS4CEIL2LO2H13HspS4CEIL2LO2H13HspS4CEIL2LO2H1S4CEIL2LOS2H0S4CEIL2LOS4CEIL2LO2H1S4CEIL2LOS4CEIL2LO2T13LSJS3SPRS4CEIL2LOS4CEIL2LO2H1SS2H02K0S2H0SS4CEIL2LO2H1SSS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2H1S3LSJS3LSJS3LSJS4CEIL2LOSS2B1S2LOS2LOS1NS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2H1S4CEIL2LO2C1S2LOS2LOS2HBS2T03LSJS4CEIL2LOS4CEIL2LO2H1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS2H0S4CEIL2LOS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T13LSJS2AL2H02C03LSJ3DHT3DHC3CT22K0S2H0S2HBS4CEIL2LO".
carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  do 6 step. zstep. step.                      (* [comment removed for export] *)
  replace (hm + 16 + -16) with hm by lia.
  box RT. box RCTX. box RH.
  step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
  unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step.              (* [comment removed for export] *)
  change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
  replace (hm - hm mod 2 ^ 2) with hm by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
  (* [comment removed for export] *)
  apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
  assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  amo_stepA AMO. rewrite sx32_lit by lia.      (* [comment removed for export] *)
  zstep. rewrite (byte0_of_word 2 b1) by lia.  (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  rewrite (byte0_cas 2 3 b1) by lia.
  amo_stepA AMO.                               (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
  step. zstep. step.                           (* [comment removed for export] *)
  lstep. zstep. rewrite B13.                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. step. if_lit.                   (* [comment removed for export] *)
  box RT. box RH.
  step. call_sp thread_stats_spec;
    [exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
  unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
  lstep. lstep.                                (* [comment removed for export] *)
  aload STATS 4 (t + 2800 + 32).               (* [comment removed for export] *)
  aload STATS 3 (t + 2800 + 24).               (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.   (* [comment removed for export] *)
  astore STATS 3.                              (* [comment removed for export] *)
  astore STATS 4.                              (* [comment removed for export] *)
  step. step. step. step.                      (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold dealloc_post. finish.
  - exact STATS.
  - rewrite !upd_length. exact LSJ.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
