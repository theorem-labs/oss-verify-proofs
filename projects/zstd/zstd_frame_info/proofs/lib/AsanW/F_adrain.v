(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition drain_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0x9db88, 0x9db88 + 4); (0x9db90, 0x9db90 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x9db88 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x9db90 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells asegs m' glst [C8 (Z_to_bv 64 fst)] else True).

#[using="Type"] Lemma drain_norecycle_spec : forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> gqb + qb <= Q_MAX -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX)] ->
  (if gfull then 0 < gnb /\ rw_cells asegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (drain_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x32c34) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GFST GLST QM GFULL T0 T1 RIMG RSTK RT RGL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0x9db88, 0x9db88 + 4);
                          (0x9db90, 0x9db90 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "05<0>11307624304.7611307624304.8011307624304.8811307624304.9211834763483.9111834763483.9411847508430.8811847508430.9012831430449.8912831430449.931283309518.85 14096856001.9114096856001.9415885320117.9115885320117.9516576250094.8416576250094.8616576250094.8816576250094.9017073101331.8317073101331.8717167966822.8917167966822.9317776320430.8717776320430.9117776320431.8217776320431.861800609155.83 1800609155.87 1800609155.91 18115320132.8918115320132.9318727805075.8418727805075.8818842355121.9118842355121.9418846650606.931980106478.84 1980106478.86 1980106478.88 1980106478.90 19965486782.8619965486782.9020643969545.9521638840877.8621638840877.8721638840877.9021638840877.9122389541692.8122389541692.8523806295746.8023806295746.9223907134830.9424638473347.8424638473347.8824638473347.9224869939761.9125301904978.8625301904978.9025663111059.8125663111059.852597719022.84 2597719022.86 2597719022.88 2597719022.90 25995299646.8625995299646.9027345537325.8627345537325.8727345537325.9027345537325.92276684878.87  27907155621.7927907155621.8327908601838.8127908601838.8528417259964.8328417259964.8728548849043.8428548849043.8829658638916.9131378308326.7531664116794.7631664116794.8031664116794.8831664116794.9232006109630.8632006109630.9033680001082.8433680001082.8633680001082.8833680001082.9033686986086.9133725004155.8633725004155.9033922151879.9133922151879.9534430152252.8434430152252.8834925869678.8334925869678.8634925869678.8734925869678.9035310472686.8435310472686.8635310472686.8835310472686.9035764571985.8535764571985.8635764571985.8735764571985.8935764571985.9036115622446.8336115622446.8736115622446.9136637980185.8636637980185.9037646304622.8337646304622.8738508687005.8638508687005.9038889585390.8438889585390.8638889585390.8838889585390.9038944962887.7638944962887.8038944962887.8838944962887.9240054548974.8440054548974.8640054548974.8840054548974.9040264850523.9140321951854.8340321951854.8640321951854.8740321951854.9040457739452.8340457739452.8742831019478.8642831019478.9043061431595.7343331019246.8143331019246.8543813166070.9543987951393.8843987951393.9243987951406.8343987951406.8743988483203.8143988483203.8543988483203.8643988483203.9044771390349.7644771390349.8044771390349.8844771390349.9245221239098.8445221239098.8645221239098.8845221239098.9045848756903.8145848756903.8546468661564.8446468661564.8846796657246.7646796657246.8047279694931.7947279694931.8348205908814.8748205908814.9048316456345.8648316456345.9048334424923.8948334424923.9348615158610.8648615158610.9048820305897.9449494582016.7849494582016.8249649769127.8449649769127.8850295509458.8650295509458.9050295509459.8550295509459.8950526502779.8650526502779.9050868111643.7950868111643.8350915327827.8550915327827.8950917424980.9050917424980.9451000560815.8651000560815.9051061046081.8951061046081.9351248241994.8651248241994.9051711223320.7851711223320.8252105090727.8352105090727.8752204912112.9152204912112.9552486992325.9552567164907.7652567164907.8052567164907.8152567164907.8352567164907.8452567164907.8552567164907.8652567164907.8752567164907.8852567164907.8952567164907.9052567164907.9152567164907.9252567164907.9352567164907.9452567164907.9553213561530.9153213561530.9553249484066.905328666318.88 5328666318.90 53312313958.9153728509380.9153728509380.9453767577775.8253767577775.8653767577775.9054243526019.8354243526019.8754243526019.8854243526019.9255638280717.9155638280717.95563227834.83  563227834.86  563227834.87  563227834.90  57022093363.7657022093363.7957022093363.8057022093363.8357673015526.9157673015526.9457745675194.8357745675194.8758273841234.8658273841235.8558273841235.8958273841245.9158732652910.8358732652910.8758804816769.7758804816769.8159100916044.9559314873579.7759314873579.7859314873579.7959314873579.8059314873579.8159314873579.8259314873579.8359314873579.8459536183085.8659536183085.9059536183085.9159536183085.9559587366675.8359587366675.8760381563445.7660381563445.8060381563445.8860381563445.9260858483367.8460858483367.8861482382924.7661482382924.8061686930286.8361686930286.8763235321900.8063235321900.8463235321900.8563235321900.8963305555623.8363305555623.8763363822145.916359713254.91 6359713254.94 64997134979.8464997134979.8864997134979.8964997134979.9365276466898.8465276466898.8665276466898.8865276466899.8565276466899.8966397384571.8666397384571.9066418838886.8966418838886.9366650393658.7666650393658.8066650393658.8866650393658.9267582354422.9567691136139.9568023948270.8168023948270.8568393266841.8668393266841.9069425730.95   7021785682.86 7021785682.90 7421359802.91 7421359802.95 7614623990.95 8583720762.81 8583720762.85 9135159889.95 992066670.83  992066670.86  992066670.87  992066670.90  9927891755.95 00000100200300400800<00I00N00O00P00]00f00o01801A01J01N01W01[01g02302402502902=02A02E02F02G02H02I02J02V02b02c02d02i03203603?03C03G03K03Q03R03S03T03U03Y03]03b03g03l03m03n03o04004404804D04P04Y04]04f04j04n05205305405505605C05G05K05T05]05a05e06106=06>06?06@06A06B06C06G06K06P06T06Y06]06^06_06`06d06h06l07007907=07F07J07S07W07`07d07e07f07g07h07i07m08108508A08M08V08_08k09709@09D09M09Q09U09Y09]09a09j09n0:70:;0:?0:H0:L0:U0:Y0:]0:a0:e0:i0:m0;60;?0;D0;H0;L0;P0;T0;U0;V0;W0;X0;Y0;Z0;[0;\0;a0;e0;j0;n0;o0<00<40<80<?0<F0<G0<H0<U0<Z0<f0=20=60=:0=>0=B0=C0=H0=M0=N0=O0=P0=Q0=R0=S0=T0=U0=`0=k0=l0=m0=n0=o0>00>10>:0>C0>G0>K0>L0>M0>N0>O0>P0>Q0>R0>S0>T0>U0>V0>W0>X0>Y0>Z0>[0>\0>]0>^0>_0>`0>a0>b0>c0>d0>i0?60?;0?<0?=0?>0?B0?F0?J0?K0?L0?M0?N0?O0?P0?U0?Y0?^0?b0?c0?d0?e0?f0?g0?h0?m0@20@30@40@50@60@?0@H0@L0@P0@T0@[0@b0A;0AB0AM0AT0A]0Ad0Ae0Af0Ag0Ah0B40B@0BI0BR0B[0Bd0Be0Bf0Bg0Bh0C10C:0C>0CB0CF0CJ0CK0CL0CU0CV0CW0CX0CY0CZ0C[0C\0C]0C^0C_0C`0Ca0Cb0Cc0Cd0Ce0Cf0Cg0Ch0Cm0Cn0D70D@0DL0DX0D]0Da0De0Df0Dg0Dl0E10E60EC0EL0EP0EY0E]0EbSSSSS2T0S2T0S4CEIL2LO3GL1S3DTGSSS4CEIL2LO3GL1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2T0S4CEIL2LOS2T0S4CEIL2LO2T1S4CEIL2LO2T1SSS2LOS2LOS2LOS2LOSSSSSS4CEIL2LO2T1S4CEIL2LO2T1SSS3GL0S4CEIL2LOS2T0S4CEIL2LOS2T0S2HBS2HBS4GLSTSSSSS2HBS2HBS3GL0S3GL0S3GL0SSSSS2T0S2T0S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS2T0S4CEIL2LOS2T0S2HBS2HBSSSSS4CEIL2LO3GL1S2LOS2LOS4CEIL2LOS4CEIL2LOS2HBS2HBS4CEIL2LO2T1S4CEIL2LO2T1SSSSSSS2HBS2HBS3SPRS2HBS3SPRS2HBSSSS2T0S2T0S2HBS2HBS4CEIL2LOS2T0S4CEIL2LOS2T0S4CEIL2LOS2T0S4CEIL2LOS2T0SSSSSS2LOS2LOS2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS2T0S4CEIL2LOS2T0S2T0S2T0S2T0S2T0S4CEIL2LOS2T0S4CEIL2LOS2T0S2T0S4CEIL2LOS2T0S4CEIL2LOS2T0S2HBS2HBS2HBS2HBS2LOS4CEIL2LOS4CEIL2LOS3GL0S2LOS2LOS2LOS2LOSSSSSSSSS3SPRS2HBS3SPRS2HBSSS2HBS2HBS2T02T1S2T02T1SSS4CEIL2LO3GL1S3DTGS4CEIL2LO2T1S4CEIL2LO2T1S2T0S2T0S2T0S2T0SS3GNBS3GNBSSSSSSSSS2QB3GQB2GQS2QB3GQB2GQSSSSSSS4CEIL2LOS4CEIL2LOS2HBS2HBSSSSSSSSSSSSSSSSSSSSSSSSSS3DTGS4CEIL2LO3GL1S3DTGSSSS2LOS2LOS2LOSSSSSSS3SPRS2HBS3SPRS2HBSSSSSSS3SPRS3SPRSSSSS4CEIL2LOS4CEIL2LOS2NBS2NBS2HBS2T02K0S2NB2K1S2NB3GNB2T04GNB02K02K12K2S2GQ2K3S3GL02T02K0S2NB2K1S4GNB12K2S2GQ2K3SSSSS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS2LOSSS4CEIL2LOSSSSSSSSSSSSSSSSSSSS3GL0SS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S3GL0S2T0S2T0SSS3GL0S3SPRS3SPRS4CEIL2LO3GL1S4CEIL2LOS2T0S4CEIL2LOS2T0S3DTG".
carve_frame 48%nat ST.
  destruct gfull.
  - destruct GFULL as (GNB1 & GLB & GL0 & GL1 & DTG).
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. step. zstep.                   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].    (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
    subst gnb. exact GC.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC1.
