(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AModelFacts APrimFacts F_aunwind F_aalloc_s F_acache F_aalloc1.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition allocA_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x314cc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x356c0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

#[using="Type"] Lemma allocA_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n -> is_primary n = true -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  pose proof (prim_facts n N PRIM0) as (NS & RZR & RZE & RZM & RLR0 & RSR & RSM & NSR).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "04E0?10000179438.81 1046777916.84  10631675007.81 11016974190.83 11077664131.83 1162083375.82  11801586693.89 11801586693.93 11801586693.98 11805467289.81 11805467289.82 11805467289.83 11805467289.84 11805467289.87 11805467289.88 12279985372.82 12391328750.83 12429510126.87 12546622119.84 13078997820.81 13148467182.84 13153224558.83 13201050402.87 13340275967.83 1351984962.86  14453557927.83 14761575534.88 14869235822.88 15138135406.84 15171934702.83 1533820803.83  15401314670.83 1579170362.81  15813913888.86 16518423935.84 16598865212.84 16872280319.83 17000728814.83 17776320431.82 18445402734.83 18694006766.83 19106585020.83 19239446934.88 19491992743.84 19809976814.83 2044177006.84  2067494638.87  20805333024.78 20805333024.82 20805333024.90 21155567546.83 2167481582.81  22163107130.84 22284289799.89 22284289799.93 22284289799.98 22439364775.82 22544198510.84 22607575996.88 22675801219.84 22700267513.90 22700267513.94 22700267513.99 22711797486.84 24266362535.87 24269065454.84 24559885231.82 2458073255.83  24630998586.83 24794926247.84 24972240369.85 24982576641.86 25029166211.83 25117511228.84 25348482085.78 25348482085.82 25348482085.90 25473289966.83 25787632170.77 25787632170.86 25878270254.83 25898482559.84 26278908583.83 26868428163.82 27017967214.83 27133822446.83 27408782894.83 27514742894.83 27981583342.83 28022296174.83 28355653425.87 2863087342.84  29076633087.83 29782367974.87 29965292900.87 30196181434.83 30401015406.84 30441106158.84 30518562691.83 31143001276.83 31144520558.83 31691922158.81 32651489978.82 33527122926.84 33532905180.78 33680001082.84 33890036527.82 34432420974.83 34775537831.88 35270809255.83 35289778563.88 35861935226.86 35988590.83    36115622446.83 36367760551.83 36635094629.91 36986663037.89 36986663037.93 36986663037.98 37153923388.84 37317216127.87 37365118958.84 37823857774.83 38333311882.76 38567244270.83 38915808562.98 38915808567.10138996969702.74 39003279726.83 39093924078.84 39832084206.83 39834151534.83 39932040893.88 39938772488.98 39938772490.99 39940869632.96 40091925676.81 40608002030.83 40653749742.87 40655079551.83 41834437230.88 42847154798.82 43061431595.72 43078501353.91 43102492671.83 43183609788.83 43528773102.81 43987951406.83 44158664835.84 44484923210.89 44484923210.93 44484923210.98 44524995199.84 44779572718.84 44833359747.83 45221239098.87 45415010670.83 4560351804.87  46046479982.82 46232973498.83 46234544622.84 46556098215.84 46812726894.83 48057003647.84 48825145582.83 49194402876.83 49257279598.82 49425192486.90 49724318719.82 50077211645.89 50077211645.93 50077211645.98 50487304575.83 50584888647.78 50674255854.84 51041686382.83 51458250794.95 51469190682.86 51678667183.82 52031133206.93 52076332701.96 52076332702.96 52198366190.87 52237318794.76 53373752302.84 53463187694.83 53494891374.82 53681773934.83 53767577775.82 53827994990.83 54261855034.84 54665582958.83 55090286.83    55222119100.83 55486849518.84 5555016302.83  56172400559.89 56172529599.81 56175235539.77 563227834.88   56712086766.83 56757832430.84 5684463747.87  57293592682.85 57522549927.81 57733900014.84 57745675194.83 58057019758.87 58170393966.83 58655119491.84 59314873579.77 59314873579.88 59314873579.89 59314873579.90 59314873579.92 59576986246.89 59907387523.84 59910875502.88 60468873383.83 60634079619.83 60797519086.88 60919923347.82 60976774461.89 60976774461.93 60976774461.98 60997568167.83 61230833468.83 61519228526.82 61798072430.83 61889459015.82 61917199023.82 61929802144.87 61929802406.89 61939782290.98 62067455854.83 6220318190.84  63045513727.88 63235321900.80 63903202542.83 63960920814.84 64302930659.76 64862446845.89 64862446845.93 64862446845.98 65458892654.83 65490594798.84 65805175866.84 65983638659.83 66028155702.81 66028155702.85 66028155702.93 66330498723.87 67215858474.87 67258535356.82 67510389213.89 67510389213.93 67510389213.98 68008320110.88 68034022143.83 68199404270.82 68714883566.87 7057573564.83  749971694.81   8172837742.83  8179223683.81  8278980118.84  8479284462.84  8583720762.83  8595948976.99  8595948983.101 8610795133.89  8610795133.93  8610795133.98  9182698862.83  9446047854.81  9610135226.83  9956545262.84  00000900=00I00R00S00W00g01701G01H01I01J01K01L01M01N01W01`01a01e01n02702<02H02I02J02S02\02e02n02o03803=03A03M03Q03]03f03j04304<04@04A04B04K04T04]04^04_04`04e04n05305405505605705@05D05E05a06=06Y06b06c06l07007107607707807907:07>07B07F07J07S07e08708;08G08H08I08R08[08_08h09109:09;09D09P09Q09T09Y09b09k09l0:00:90:B0:G0:P0:Q0:V0:Z0:c0:d0:e0:f0:g0;00;40;50;K0;X0;e0<20<60<B0<K0<T0<U0<^0<_0<`0<a0<j0=30=<0=E0=J0=T0=d0=i0=m0>60>?0>K0>T0>]0>a0>b0>n0?20?;0??0?@0?A0?B0?C0?O0?X0?Y0?^0?g0?k0@40@90@B0@C0@L0@X0@a0@e0@n0A20A>0AK0AX0Ae0B10B20B;0BD0BT0Bd0Bh0Bi0Bj0Bk0C40C50C>0CG0CP0CY0C]0Cf0Ck0D40D=0DA0DJ0DS0DT0DU0DV0D[0Dd0Dm0Dn0Do0E00E90E>0EG0EP0EQ0EX0F00F80F?0FL0FM0FN0FW0FX0FY0Fb0Fc0G00G=0GJ0GK0GO0GX0Ga0Gb0Gf0H80H>0HP0HY0Hb0Hn0I20I;0ID0IH0IU0Ib0Io0J80JA0JF0JG0JV0Je0K40K80K90K=0KJ0KW0Kd0Km0L90LB0LK0LO0LX0La0Lb0Lc0Ll0M10M20M30M@0MM0MZ0Mc0Ml0N10N:S4CEIL2LOS2HBS4CEIL2LO2C1S4CEIL2LOSS2LOS3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1SSSSSSSS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS3NSRS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS2LOS4CEIL2LO2C1S2HBS4CEIL2LO2C1S4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS2HBSSS4CEIL2LOS4CEIL2LOS4CEIL2LOFFFS3SPRS4CEIL2LOS3SPRFFFSS4CEIL2LOS2HBSS2HS2C02T03RZR4RLR02KS3Hsp1HS2HS2C02T03RZR4RLR02KS3Hsp1HS2HS2C02T03RZR4RLR02KS3Hsp1HS4CEIL2LOSS4CEIL2LOS2LOSS3SPRSSSSS2HBS2LOS2LOS2LOS4CEIL2LOS1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS2LOS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1SS1NS3SPRS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS3SPRS2LOS4CEIL2LOSSSFS4CEIL2LOS2LOSS2HS2T02T13RZR4RLR02KSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOSS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3NSRS4RLR03NSRS2NS3RZR3RSR3NSRS3RZRS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2LOFS4CEIL2LO2C1S2HBS4CEIL2LOS2LOSFFFS4CEIL2LO2C1S4CEIL2LOSS3SPRS4CEIL2LOS2HBS4CEIL2LOS3SPRS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS2HBS4CEIL2LOS2C0S4CEIL2LO2C1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOS2NS3RZR3RSR3NSRS2NS3RZR3RSR3NSRS2LOSFFS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSSS3SPRS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSS2HS2KSS2NS3RZR4RLR03RSR3NSR2KBS3NSR2KCS2KB2KDS2HS2T02KS2KESSS4CEIL2LOSSS4CEIL2LOFS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS2HBS4CEIL2LOS4CEIL2LOFS2LOS1N2NS3RZR3RSR3NSRS1N2KBS1N2NS3RZR3RSR3NSRS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S2LOS4CEIL2LOS4CEIL2LOS2HSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOSS2HBS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS3SPRSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LO".
carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_post. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
