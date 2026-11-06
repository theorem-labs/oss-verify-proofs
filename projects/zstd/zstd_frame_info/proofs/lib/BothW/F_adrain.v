(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AKitQ.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0x9dd48, 0x9dd48 + 4); (0x9dd50, 0x9dd50 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0x9dd48 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x9dd50 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells bsegs m' glst [C8 (Z_to_bv 64 fst)] else True).

#[using="Type"] Lemma drain_norecycle_spec : forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> gqb + qb <= Q_MAX -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX)] ->
  (if gfull then 0 < gnb /\ rw_cells bsegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (drain_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x32c38) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GFST GLST QM GFULL T0 T1 RIMG RSTK RT RGL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0x9dd48, 0x9dd48 + 4);
                          (0x9dd50, 0x9dd50 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "05<0>10970293681.9110970293681.9411351570756.8911351570756.9311847508430.8811847508430.901283309518.85 13205895782.9113541873338.9113541873338.951509774273.91 1509774273.94 15776184302.8115776184302.8516981101105.9117073101331.8317073101331.871723618286.81 1723618286.85 17776320430.8717776320430.9117776320431.8217776320431.861800609155.83 1800609155.87 1800609155.91 18623738102.9518727805075.8418727805075.8819965486782.8619965486782.9020643969545.9520928891099.9120928891099.9421595012187.9121638840877.8621638840877.8721638840877.9021638840877.9122389541692.8122389541692.8522793452142.8322793452142.8622793452142.8722793452142.9022892792388.9123243682874.7623243682874.8023243682874.8823243682874.9223301063270.8923301063270.9324638473347.8424638473347.8824638473347.9225260260710.9125449023214.8425449023214.8625449023214.8825449023214.9025663111059.8125663111059.8525995299646.8625995299646.9026312420710.8926312420710.9326757167854.8426757167854.8626757167854.8826757167854.9027345537325.8627345537325.8727345537325.9027345537325.9227650187962.9127650187962.95276684878.87  27716857426.8627716857426.9027907155621.7927907155621.8327922131438.8427922131438.8627922131438.8827922131438.9028417259964.8328417259964.8728548849043.8428548849043.8830915208182.9531378308326.7532006109630.8632006109630.903281461173.91 3281461173.95 3362501458.86 3362501458.90 33680001082.8433680001082.8633680001082.8833680001082.9033725004155.8633725004155.9034430152252.8434430152252.8835764571985.8535764571985.8635764571985.8735764571985.8935764571985.9036115622446.8336115622446.8736115622446.9136637980185.8636637980185.9036901426061.7636901426061.8036901426061.8836901426061.9237738008046.8437738008046.8637738008046.8837738008046.9038457187137.8938457187137.9338508687005.8638508687005.9040057062766.8340057062766.8740457739452.8340457739452.8742732709998.8342732709998.8642732709998.8742732709998.9042831019478.8642831019478.9043061431595.7343987951393.8843987951393.9243987951406.8343987951406.8743988483203.8143988483203.8543988483203.8643988483203.904454318318.84 4454318318.86 4454318318.88 4454318318.90 44927917046.9545014773998.9345221239098.8445221239098.8645221239098.8845221239098.904541777776.76 4541777776.80 4541777776.88 4541777776.92 45455842800.9145455842800.9545745840622.8145745840622.8545848756903.8145848756903.8546468661564.8446468661564.8846600235374.8346600235374.8746796657246.7646796657246.8046962662852.9146962662852.9447279694931.7947279694931.8347762024973.9147762024973.9547794612789.7647794612789.8047794612789.8847794612789.9248205908814.8748205908814.9048316456345.8648316456345.9048820305897.944944820017.89 4944820017.93 49494582016.7849494582016.8249649769127.8449649769127.8850075127150.9450295509458.8650295509458.9050295509459.8550295509459.8950350988994.8050350988994.9250526502779.8650526502779.9050760094273.9150868111643.7950868111643.8350915327827.8550915327827.8950917424980.9050917424980.9451000560815.8651000560815.9051248241994.8651248241994.9051711223320.7851711223320.8252105090727.8352105090727.8752486992325.9552567164907.7652567164907.8052567164907.8152567164907.8352567164907.8452567164907.8552567164907.8652567164907.8752567164907.8852567164907.8952567164907.9052567164907.9152567164907.9252567164907.9352567164907.9452567164907.9553165703398.9153165703398.9453249484066.9053267610178.955328666318.88 5328666318.90 53767577775.8253767577775.8653767577775.9054243526019.8354243526019.8754243526019.8854243526019.92563227834.83  563227834.86  563227834.87  563227834.90  57022093363.7657022093363.7957022093363.8057022093363.8357581223022.8357581223022.8657581223022.8757581223022.9057745675194.8357745675194.8758240445498.7658240445498.8058240445498.8858240445498.9258273841234.8658273841235.8558273841235.8958273841245.9158804816769.7758804816769.8159100916044.9559176389614.8459176389614.8659176389614.8859176389614.9059314873579.7759314873579.7859314873579.7959314873579.8059314873579.8159314873579.8259314873579.8359314873579.8459536183085.8659536183085.9059536183085.9159536183085.9559587366675.8359587366675.876015527771.89 6015527771.93 60324828615.9160324828615.9560858483367.8460858483367.8861482382924.7661482382924.8063235321900.8063235321900.8463235321900.8563235321900.8963305555623.8363305555623.8763617233490.8663617233490.9064101751662.8364101751662.8764997134979.8464997134979.8864997134979.8964997134979.9365276466898.8465276466898.8665276466898.8865276466899.8565276466899.8965347639623.7665347639623.8065347639623.8865347639623.9266397384571.8666397384571.9066658756070.9166658756070.9467691136139.9568393266841.8668393266841.908583720762.81 8583720762.85 9135159889.95 9927891755.95 00000100200300400A00F00S00T00U00V00_00h01101:01;01G01S01\01e01i01m02102502602702802=02I02U02Y02]02c02g02k02o03003103203303703;03D03H03Q03U03V03W03X03Y03Z03[03\03]03^03_03`03i03m04604:04F04R04V04Z04[04\04e04i05205605705805905:05;05<05I05M05Q05U05Y05b05f05o06306706;06G06S06X06Y06]06a06j07307707;07@07D07I07M07N07O07S07W07X07Y07Z07[07\07`07d07h08408@08A08B08C08D08M08Q08Z08^08g09009<09H09Q09Z09^09b09k09o0:80:<0:@0:D0:H0:L0:P0:T0:X0:Y0:Z0:[0:\0:e0:i0;20;60;;0;@0;E0;I0;N0;R0;S0;T0;U0;V0;W0;X0;a0;j0;k0;l0<00<40<=0<F0<M0<T0<U0<V0<W0<X0<Y0<Z0<c0<l0=50=>0=K0=P0=\0=h0=i0=j0=k0>00>50>60>70><0>=0>>0>?0>@0>E0>J0>K0>L0>U0>`0>k0>l0>m0>n0>o0?00?10?50?90?:0?;0?<0?=0?>0??0?@0?A0?B0?C0?D0?E0?F0?G0?H0?I0?J0?K0?L0?M0?N0?O0?P0?U0?Z0?g0?l0@00@40@80@90@:0@;0@<0@A0@E0@J0@N0@O0@P0@Q0@R0@[0@_0@h0@l0A10A60A70A80A90A:0A;0A<0A=0A>0AB0AF0AJ0AS0AW0A`0Ad0Ak0B20BK0BR0B]0Bd0Bm0C40C50C60C70C80CD0CP0CT0CX0C\0C`0Ca0Cb0Cc0Cd0Ch0Cl0D00D40D50D60D:0D>0DG0DP0DQ0DR0DS0DT0DU0DV0DW0DX0DY0D]0Da0De0Di0Dj0Dk0Dl0Dm0Dn0E:0EF0EK0EP0E]0EbSSSSS4CEIL2LO3GL1S3DTGS4CEIL2LO3GL1SSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS2LOSSSS3GL0S4CEIL2LO2T1S4CEIL2LO2T1S2HBS2HBS4GLSTS2T0S2T0S2T0SSSSS2HBS2HBS4CEIL2LOS2T0S4CEIL2LOS2T0SSSSSSSSSSSS4CEIL2LOS2T0S4CEIL2LOS2T0S4CEIL2LO2T1S4CEIL2LO2T1S2HBS2HBSSS4CEIL2LOS2T0S4CEIL2LOS2T0SSSSSSS4CEIL2LO3GL1S2T0S2T0S2LOS2LOS4CEIL2LOS2T0S4CEIL2LOS2T0S2HBS2HBS4CEIL2LO2T1S4CEIL2LO2T1S3GL0SS2HBS2HBS4CEIL2LOS4CEIL2LOS2T0S2T0S3SPRS2HBS3SPRS2HBSSS2HBS2HBSSSSSS2LOS2LOS2LOS4CEIL2LO2T1S4CEIL2LO2T1SSSSS4CEIL2LOS2T0S4CEIL2LOS2T0S4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS2HBS2HBS4CEIL2LOS2T0S4CEIL2LOS2T0S2HBS2HBS2LOS2LOS2LOS2LOS2LOSSSSS4CEIL2LOS2T0S4CEIL2LOS2T0S3GL0S3GL0S3SPRS2HBS3SPRS2HBSSSSSSS4CEIL2LOS4CEIL2LOSSS2HBS2HBS4CEIL2LOS4CEIL2LOS2T02T1S2T02T1SSSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3GL1S3DTGS4CEIL2LO2T1S4CEIL2LO2T1SSSS3GNBS3GNBSSS3GL0SSSSS3GL0S3GL0SSS4CEIL2LOS2QB3GQB2GQS2QB3GQB2GQSSSSSSS2HBS2HBSSSSSSSSSSSSSSSSSSSSSSSS3DTGS3GL0S4CEIL2LO3GL1S3DTGS2LOS2LOS2LOSSSSS3SPRS2HBS3SPRS2HBSSSSS4CEIL2LOS2T0S4CEIL2LOS2T0S3SPRS3SPRSSSSSSSSS2NBS2NBS2HBS4CEIL2LOS2T0S4CEIL2LOS2T0S2T02K0S2NB2K1S2NB3GNB2T04GNB02K02K12K2S2GQ2K3S3GL02T02K0S2NB2K1S4GNB12K2S2GQ2K3SSSSS4CEIL2LO2T1S4CEIL2LO2T1S2T0S2T0S2T0S2T0SSSSS2LOS2LOS2LOS2LOSSS2T0S2T0S4CEIL2LOS4CEIL2LOSSSSSSSSSS2T0S2T0S2T0S2T0SSSSSS4CEIL2LO2T1S4CEIL2LO2T1S3SPRS3SPRS4CEIL2LO3GL1S3DTG".
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
