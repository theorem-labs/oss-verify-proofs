(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AModelFacts APrimFacts ASecFacts F_aunwind F_aalloc_s F_acache F_aalloc1 F_aalloc1b.
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
    ms' = MS (mkR (Z_to_bv 64 0x314d0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 0) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x356c4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells bsegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

#[using="Type"] Lemma allocA_pre_spec_sec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX -> is_primary n = false -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (allocA_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, AREQMAX, allocate_entry in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "04I0?10305251027.86 1046777916.88  10600373102.87 10631675007.85 11077664131.87 1162083375.86  11801586693.10211801586693.93 11801586693.97 11805467289.85 11805467289.86 11805467289.87 11805467289.88 11805467289.91 11805467289.92 11865194606.85 118736110.87   12145036526.88 12279985372.86 12334040174.92 12546622119.88 12744399342.87 12890777838.85 12894873556.91 13078997820.85 13340275967.87 1351984962.90  14453557927.87 14527015389.10214527015389.93 14527015389.97 14806281198.87 14993016302.87 15003893486.88 1533820803.87  1579170362.85  15813913888.90 16518423935.88 16598865212.88 16872280319.87 170773230.88   17141182446.87 17685336686.87 17776320431.86 18276986478.88 1899074286.86  19106585020.87 19415681262.87 19491992743.88 20292650734.88 20540342678.97 20603313390.88 20805333024.82 20805333024.86 20805333024.94 21155567546.87 21250035837.10221250035837.93 21250035837.97 21315116398.87 22163107130.88 22284289799.10222284289799.93 22284289799.97 22289517678.87 22439364775.86 22607575996.92 22675801219.88 22700267513.10322700267513.94 22700267513.98 24266362535.91 24346898045.10224346898045.93 24346898045.97 24559830510.91 24559885231.86 2458073255.87  24630998586.87 24794926247.88 24959150958.88 24972240369.89 24982576641.90 24991151882.80 25029166211.87 25099790446.87 25117511228.88 25234798574.88 25348482085.82 25348482085.86 25348482085.94 25634301166.85 25787632170.81 25787632170.90 25878270254.87 25898482559.88 26278908583.87 26868428163.86 26961506542.88 2728429678.92  27408782894.87 27523246446.87 27843469846.92 27872253706.80 28026153710.88 28355653425.91 28716985198.87 29076633087.87 29428725358.87 29782367974.91 29965292900.91 2997329262.88  30196181434.87 30396535790.87 30441442926.87 30518562691.87 30571528814.87 30832715758.87 31143001276.87 32651489978.86 3315427694.92  33532905180.82 33680001082.88 33890036527.86 34106874606.85 34775537831.92 35270809255.87 35289778563.92 36115622446.87 36367760551.87 36608995310.88 36635094629.95 37114577220.91 37124862062.86 37153923388.88 37317216127.91 38238797294.91 38915808562.10238915808567.10538996969702.78 39932040893.92 39938772488.10239938772490.10340059657198.91 40091925676.85 40238810222.87 40655079551.87 41330770158.87 41422295406.87 42522679662.87 42995994990.87 43061431595.76 43102492671.87 43183609788.87 43987951406.87 44030539416.62 44158664835.88 44253452910.92 44484923210.10244484923210.93 44484923210.97 44524995199.88 44545694830.92 44833359747.87 45221239098.91 45238050109.10245238050109.93 45238050109.97 45257912942.86 45314038894.87 45507666326.88 4560351804.91  45607773934.88 45657443310.88 46232973498.87 46556098215.88 47194525166.88 47813310082.10248057003647.88 48259303406.88 48654615790.92 48923332334.87 49123722493.10249123722493.93 49123722493.97 49194402876.87 4932169326.86  49425192486.94 49724318719.86 50487304575.87 50584888647.82 50946216942.88 51079938926.86 51323987107.73 51458250794.99 51469190682.90 51678667183.86 51820114670.88 51960277614.87 52076332701.10052076332702.10053072028142.88 53326475118.87 53767577775.86 54261855034.88 55207105262.88 55222119100.87 55661190638.85 55751247214.87 56172400559.93 56172529599.85 56175235539.81 56238753134.87 563227834.92   56582466030.91 56625144942.87 5684463747.91  57293592682.89 57508831501.91 57522549927.85 57745675194.87 58178897518.86 58360670702.88 58401687406.87 58622847598.88 58655119491.88 58945144430.87 59314873579.81 59314873579.92 59314873579.93 59314873579.94 59314873579.96 59378925678.87 59576986246.93 59907387523.88 60468873383.87 60471841134.91 60634079619.87 60965951726.87 60997568167.87 61230833468.87 61488250094.87 61889459015.86 61917199023.86 61929802144.91 61929802406.93 61939782290.10262019383790.87 62294762682.90 62801085934.88 63045513727.92 63075773422.88 63174103918.87 63235321900.84 63292612334.87 64302930659.80 64486602606.87 65805175866.88 65811741693.10265811741693.93 65811741693.97 65824677230.87 65983638659.87 66028155702.85 66028155702.89 66028155702.97 66330498723.91 67215858474.91 67258535356.86 67604033390.87 68034022143.87 68367824622.91 7057573564.87  7585226990.85  7671267822.87  8179223683.85  8583720762.87  8595948976.103 8595948983.105 9014700585.95  9610135226.87  00000100500>00J00K00O00_00o01?01@01A01B01C01D01E01N01W01`01a01j01k02402=02B02F02R02S02T02a02n03;03D03M03V03W03\03`03l04004<04E04N04W04[04d04m05105:05;05D05E05N05O05P05Q05V05c06006=06F06K06L06M06N06W06X06\06]07B07g08L08M08Z08g09409=09A09B09G09H09Q09R09S09T09U09^09b09k09o0:30:70:@0:C0:F0:J0:V0:W0:X0:a0:j0:n0;70;80;90;B0;C0;L0;X0;a0;b0;e0;n0<30<<0<E0<F0<O0<X0<\0<a0<j0<k0=00=40==0=>0=?0=@0=D0=E0=N0=a0=e0=n0>20>>0>G0>H0>I0>J0>\0>f0?40?=0?A0?J0?V0?_0?h0@10@:0@>0@J0@N0@R0@U0@V0@_0@`0@a0@b0@n0A70A80A=0AJ0AW0Ad0Am0B60B70B;0BD0BM0BR0BS0B\0Bj0C60C?0CH0CQ0C^0Ck0D80D<0DE0DI0DU0Da0Db0Dk0E40E50E;0EA0EE0EN0EW0EX0EY0Eb0Ek0Eo0F40F=0FA0FJ0FS0FT0FU0FV0F_0Fd0Fm0G60G70G80G@0GA0GF0GO0GX0Ga0Gj0Gk0H40H;0HA0HW0H]0Hj0I30I40I50I60I?0I@0II0IJ0IN0IW0IX0I\0I_0Ib0Ie0In0Io0J80JD0JM0JV0JZ0Jc0Jg0K00K50KB0KO0K\0Ke0Kf0L50LD0LS0LW0LX0L\0Le0M10M:0M>0MG0MP0MQ0MV0MW0MX0MY0M^FS2HBS4CEIL2LOS4CEIL2LO2C1SS2LOS3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1SSSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS3NSES2HBS4CEIL2LO2C1SSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS2LOS4CEIL2LO2C1S2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOSS4CEIL2LOSS4CEIL2LOFFFS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS3SPRFFFS4CEIL2LOSS2HBSS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS2LOSS3SPRSS4CEIL2LOSSSSS4CEIL2LOS2HBS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS1NS1NS2LOS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOSSS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOSS1NS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS3SPRS4CEIL2LOSS3SPRS2LOS4CEIL2LOSSSS2LOSS4CEIL2LOS1N2HS2T02T13MSB2KSS2RZS4CEIL2LOS2HBS4CEIL2LO2C1S4CEIL2LOSSSS1N2NB3RSE3RSR3NSES3RL74RLR0S1N2NB3RSE3RSRS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LO2C1S2HBS2LOS1NSS4CEIL2LOFFFS4CEIL2LO2C1S4CEIL2LOSS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LOS1N2NB3RSE3RSRS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS4CEIL2LOS2C0S4CEIL2LO2C1S4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOSS1N2NBS1N2NBS2LOS4CEIL2LOS4CEIL2LOFFS4CEIL2LOS4CEIL2LOS2LOS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSSS2NB3RSRSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2HS2KSS1N2KBS1N3RSE3RSR3NSE3MSB2KCS1N2KDS2HS2T02KS2KES4CEIL2LOSSSS4CEIL2LOSS4CEIL2LOSS2HBS4CEIL2LOFS2LOS1NS1NS1NS4CEIL2LOFS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS2HSS4CEIL2LOS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOSS2HBS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSS3SPRSSFS3SPR".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM0) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  pose proof (rz_log_big n NB) as RL7. assert (RLR0 : 0 <= rz_log n <= 7) by (rewrite RL7; lia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
