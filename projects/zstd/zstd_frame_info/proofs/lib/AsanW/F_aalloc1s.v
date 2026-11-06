(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AModelFacts APrimFacts ASecFacts F_aunwind F_aalloc_s F_acache F_aalloc1 F_aalloc1b.
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
Definition allocA_pre_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x314cc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 0) (Z_to_bv 64 n)
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

#[using="Type"] Lemma allocA_pre_spec_sec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX -> is_primary n = false -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, AREQMAX, allocate_entry in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "04I0?10000179438.85 1046777916.88  10631675007.85 11016974190.87 11077664131.87 1162083375.86  11801586693.10211801586693.93 11801586693.97 11805467289.85 11805467289.86 11805467289.87 11805467289.88 11805467289.91 11805467289.92 12279985372.86 12391328750.87 12429510126.91 12546622119.88 12894873556.91 13078997820.85 13148467182.88 13153224558.87 13340275967.87 1351984962.90  14453557927.87 14761575534.92 14869235822.92 15138135406.88 15171934702.87 1533820803.87  15401314670.87 1579170362.85  15813913888.90 16518423935.88 16598865212.88 16872280319.87 17000728814.87 17776320431.86 18445402734.87 18694006766.87 19106585020.87 19239446934.92 19491992743.88 19809976814.87 2044177006.88  2067494638.91  20805333024.82 20805333024.86 20805333024.94 21155567546.87 2167481582.85  22163107130.88 22284289799.10222284289799.93 22284289799.97 22439364775.86 22544198510.88 22607575996.92 22675801219.88 22700267513.10322700267513.94 22700267513.98 22711797486.88 24266362535.91 24269065454.88 24559885231.86 2458073255.87  24630998586.87 24794926247.88 24972240369.89 24982576641.90 25029166211.87 25117511228.88 25348482085.82 25348482085.86 25348482085.94 25473289966.87 25787632170.81 25787632170.90 25878270254.87 25898482559.88 26278908583.87 26868428163.86 27017967214.87 27133822446.87 27408782894.87 27514742894.87 27981583342.87 28022296174.87 28355653425.91 2863087342.88  29076633087.87 29782367974.91 29965292900.91 30196181434.87 30401015406.88 30441106158.88 30518562691.87 31143001276.87 31144520558.87 31691922158.85 32651489978.86 33527122926.88 33532905180.82 33680001082.88 33890036527.86 34432420974.87 34775537831.92 35270809255.87 35289778563.92 35861935226.90 35988590.87    36115622446.87 36367760551.87 36635094629.95 36986663037.10236986663037.93 36986663037.97 37114577220.91 37153923388.88 37317216127.91 37365118958.88 37823857774.87 38333311882.80 38567244270.87 38915808562.10238915808567.10538996969702.78 39003279726.87 39093924078.88 39832084206.87 39834151534.87 39932040893.92 39938772488.10239938772490.10340091925676.85 40608002030.87 40653749742.91 40655079551.87 41834437230.92 42847154798.86 43061431595.76 43078501353.95 43102492671.87 43183609788.87 43528773102.85 43987951406.87 44030539416.62 44158664835.88 44484923210.10244484923210.93 44484923210.97 44524995199.88 44779572718.88 44833359747.87 45221239098.91 45415010670.87 4560351804.91  46046479982.86 46232973498.87 46234544622.88 46556098215.88 46812726894.87 47813310082.10248057003647.88 48825145582.87 49194402876.87 49257279598.86 49425192486.94 49724318719.86 50077211645.10250077211645.93 50077211645.97 50487304575.87 50584888647.82 50674255854.88 51041686382.87 51323987107.73 51458250794.99 51469190682.90 51678667183.86 52031133206.97 52076332701.10052076332702.10052198366190.91 52237318794.80 53373752302.88 53463187694.87 53494891374.86 53681773934.87 53767577775.86 53827994990.87 54261855034.88 54665582958.87 55090286.87    55222119100.87 55486849518.88 5555016302.87  56172400559.93 56172529599.85 56175235539.81 563227834.92   56712086766.87 56757832430.88 5684463747.91  57293592682.89 57508831501.91 57522549927.85 57733900014.88 57745675194.87 58057019758.91 58170393966.87 58655119491.88 59314873579.81 59314873579.92 59314873579.93 59314873579.94 59314873579.96 59576986246.93 59907387523.88 59910875502.92 60468873383.87 60634079619.87 60797519086.92 60919923347.86 60976774461.10260976774461.93 60976774461.97 60997568167.87 61230833468.87 61519228526.86 61798072430.87 61889459015.86 61917199023.86 61929802144.91 61929802406.93 61939782290.10262067455854.87 6220318190.88  63045513727.92 63235321900.84 63903202542.87 63960920814.88 64302930659.80 64862446845.10264862446845.93 64862446845.97 65458892654.87 65490594798.88 65805175866.88 65983638659.87 66028155702.85 66028155702.89 66028155702.97 66330498723.91 67215858474.91 67258535356.86 67510389213.10267510389213.93 67510389213.97 68008320110.92 68034022143.87 68199404270.86 68714883566.91 7057573564.87  749971694.85   8172837742.87  8179223683.85  8278980118.88  8479284462.88  8583720762.87  8595948976.103 8595948983.105 8610795133.102 8610795133.93  8610795133.97  9182698862.87  9446047854.85  9610135226.87  9956545262.88  00000900=00I00R00S00W00g01701G01H01I01J01K01L01M01N01W01`01a01f01j02302<02H02I02J02S02\02e02n02o03803=03A03M03Q03]03f03j04304<04@04A04B04K04T04]04^04_04`04e04n05305405505605705@05D05E05j06O07407=07>07G07K07L07Q07R07S07T07U07Y07]07a07e07n08108408808D08E08F08O08X08\08e08n09709809A09M09N09Q09V09_09h09i09m0:60:?0:D0:M0:N0:S0:W0:`0:a0:b0:c0:d0:m0;10;20;E0;R0;_0;l0<00<40<@0<I0<R0<S0<\0<]0<^0<_0<h0=10=:0=C0=U0=_0=m0>10>:0>C0>O0>X0>a0>e0>f0?20?60??0?C0?F0?G0?H0?I0?J0?V0?_0?`0?e0?n0@20@;0@@0@I0@J0@S0@a0@m0A60A:0AC0AG0AS0A`0Am0B:0BF0BG0BP0BY0BZ0B`0Bf0Bj0Bk0Bl0Bm0C60C70C@0CI0CR0C[0C_0Ch0Cm0D60D?0DC0DL0DU0DV0DW0DX0D]0Df0Do0E00E10E90E:0EC0EH0EQ0EZ0E[0Eb0Eh0F>0FD0FQ0FR0FS0F\0F]0F^0Fg0Fh0G50GB0GO0GP0GT0G]0Gf0Gg0Gk0Gn0H10H40H=0HF0HR0HV0H_0Hh0Hl0I90IF0IS0I\0Ie0Ij0Ik0J:0JI0JX0J\0J]0Ja0Jn0K;0KH0KQ0K]0Kf0Ko0L30L<0LE0LF0LG0LP0LU0LV0LW0Ld0M10M>0MG0MP0MU0M^S4CEIL2LOS2HBS4CEIL2LO2C1S4CEIL2LOSS2LOS3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1SSSSSSSS4CEIL2LOS4CEIL2LOSS3NSES2HBS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS2LOS4CEIL2LO2C1S2HBS4CEIL2LO2C1S4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS2HBSSS4CEIL2LOS4CEIL2LOS4CEIL2LOFFFS3SPRS4CEIL2LOS3SPRFFFSS4CEIL2LOS2HBSS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS4CEIL2LOSS4CEIL2LOS2LOSS3SPRSSSSS2HBS2LOS2LOS2LOS4CEIL2LOS1NS1NS2LOS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1SS1NS3SPRS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS3SPRS2LOS4CEIL2LOSSSFS4CEIL2LOS2LOSS1N2HS2T02T13MSB2KSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2RZS2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOSS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS1N2NB3RSE3RSR3NSES3RL74RLR0S1N2NB3RSE3RSRS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2LOFS4CEIL2LO2C1S2HBS4CEIL2LOS2LOS1NSFFFS4CEIL2LO2C1S4CEIL2LOSS3SPRS4CEIL2LOS2HBS4CEIL2LOS3SPRS4CEIL2LOSS4CEIL2LOS1N2NB3RSE3RSRS4CEIL2LO2C1S4CEIL2LOS2HBS4CEIL2LOS2C0S4CEIL2LO2C1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOSS1N2NBS1N2NBS2LOSFFS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSSS3SPRS4CEIL2LOS4CEIL2LOSSS2NB3RSRSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSS2HS2KSS1N2KBS1N3RSE3RSR3NSE3MSB2KCS1N2KDS2HS2T02KS2KESSS4CEIL2LOSSS4CEIL2LOFS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS2HBS4CEIL2LOS4CEIL2LOFS2LOS1NS1NS1NS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S2LOS4CEIL2LOS4CEIL2LOS2HSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOSS2HBS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS3SPRSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LO".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM0) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  pose proof (rz_log_big n NB) as RL7. assert (RLR0 : 0 <= rz_log n <= 7) by (rewrite RL7; lia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
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
  rewrite RZ.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (rounded_size n + 2048 <? 65537) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change (Z.land 1 0) with 0. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
  change (Z.land 18446744073709551615 2048) with 2048.
  setreg 19 (Z_to_bv 64 (needed_size n)) ltac:(f_equal; lia). setreg 20 (Z_to_bv 64 (rz_size n)) ltac:(f_equal; lia).
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_postS. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
