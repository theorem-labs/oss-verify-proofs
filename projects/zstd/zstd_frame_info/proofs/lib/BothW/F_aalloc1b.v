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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AModelFacts APrimFacts F_aunwind F_aalloc_s F_acache F_aalloc1.
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
    ms' = MS (mkR (Z_to_bv 64 0x314d0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
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

#[using="Type"] Lemma allocA_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n -> is_primary n = true -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (allocA_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  pose proof (prim_facts n N PRIM0) as (NS & RZR & RZE & RZM & RLR0 & RSR & RSM & NSR).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "04E0?10305251027.82 1046777916.84  10600373102.83 10631675007.81 11077664131.83 1162083375.82  11801586693.89 11801586693.93 11801586693.98 11805467289.81 11805467289.82 11805467289.83 11805467289.84 11805467289.87 11805467289.88 11865194606.81 118736110.83   12145036526.84 12279985372.82 12334040174.88 12546622119.84 12744399342.83 12890777838.81 13078997820.81 13201050402.87 13340275967.83 1351984962.86  14453557927.83 14527015389.89 14527015389.93 14527015389.98 14806281198.83 14993016302.83 15003893486.84 1533820803.83  1579170362.81  15813913888.86 16518423935.84 16598865212.84 16872280319.83 170773230.84   17141182446.83 17685336686.83 17776320431.82 18276986478.84 1899074286.82  19106585020.83 19415681262.83 19491992743.84 20292650734.84 20540342678.93 20603313390.84 20805333024.78 20805333024.82 20805333024.90 21155567546.83 21250035837.89 21250035837.93 21250035837.98 21315116398.83 22163107130.84 22284289799.89 22284289799.93 22284289799.98 22289517678.83 22439364775.82 22607575996.88 22675801219.84 22700267513.90 22700267513.94 22700267513.99 24266362535.87 24346898045.89 24346898045.93 24346898045.98 24559830510.87 24559885231.82 2458073255.83  24630998586.83 24794926247.84 24959150958.84 24972240369.85 24982576641.86 24991151882.76 25029166211.83 25099790446.83 25117511228.84 25234798574.84 25348482085.78 25348482085.82 25348482085.90 25634301166.81 25787632170.77 25787632170.86 25878270254.83 25898482559.84 26278908583.83 26868428163.82 26961506542.84 2728429678.88  27408782894.83 27523246446.83 27843469846.88 27872253706.76 28026153710.84 28355653425.87 28716985198.83 29076633087.83 29428725358.83 29782367974.87 29965292900.87 2997329262.84  30196181434.83 30396535790.83 30441442926.83 30518562691.83 30571528814.83 30832715758.83 31143001276.83 32651489978.82 3315427694.88  33532905180.78 33680001082.84 33890036527.82 34106874606.81 34775537831.88 35270809255.83 35289778563.88 36115622446.83 36367760551.83 36608995310.84 36635094629.91 37124862062.82 37153923388.84 37317216127.87 38238797294.87 38915808562.98 38915808567.10138996969702.74 39932040893.88 39938772488.98 39938772490.99 39940869632.96 40059657198.87 40091925676.81 40238810222.83 40655079551.83 41330770158.83 41422295406.83 42522679662.83 42995994990.83 43061431595.72 43102492671.83 43183609788.83 43987951406.83 44158664835.84 44253452910.88 44484923210.89 44484923210.93 44484923210.98 44524995199.84 44545694830.88 44833359747.83 45221239098.87 45238050109.89 45238050109.93 45238050109.98 45257912942.82 45314038894.83 45507666326.84 4560351804.87  45607773934.84 45657443310.84 46232973498.83 46556098215.84 47194525166.84 48057003647.84 48259303406.84 48654615790.88 48923332334.83 49123722493.89 49123722493.93 49123722493.98 49194402876.83 4932169326.82  49425192486.90 49724318719.82 50487304575.83 50584888647.78 50946216942.84 51079938926.82 51458250794.95 51469190682.86 51678667183.82 51820114670.84 51960277614.83 52076332701.96 52076332702.96 53072028142.84 53326475118.83 53767577775.82 54261855034.84 55207105262.84 55222119100.83 55661190638.81 55751247214.83 56172400559.89 56172529599.81 56175235539.77 56238753134.83 563227834.88   56582466030.87 56625144942.83 5684463747.87  57293592682.85 57522549927.81 57745675194.83 58178897518.82 58360670702.84 58401687406.83 58622847598.84 58655119491.84 58945144430.83 59314873579.77 59314873579.88 59314873579.89 59314873579.90 59314873579.92 59378925678.83 59576986246.89 59907387523.84 60468873383.83 60471841134.87 60634079619.83 60965951726.83 60997568167.83 61230833468.83 61488250094.83 61889459015.82 61917199023.82 61929802144.87 61929802406.89 61939782290.98 62019383790.83 62294762682.86 62801085934.84 63045513727.88 63075773422.84 63174103918.83 63235321900.80 63292612334.83 64302930659.76 64486602606.83 65805175866.84 65811741693.89 65811741693.93 65811741693.98 65824677230.83 65983638659.83 66028155702.81 66028155702.85 66028155702.93 66330498723.87 67215858474.87 67258535356.82 67604033390.83 68034022143.83 68367824622.87 7057573564.83  7585226990.81  7671267822.83  8179223683.81  8583720762.83  8595948976.99  8595948983.101 9014700585.91  9610135226.83  00000100500>00J00K00O00_00o01?01@01A01B01C01D01E01N01W01`01a01j01k02402=02A02F02R02S02T02a02n03;03D03M03V03W03\03`03l04004<04E04N04W04[04d04m05105:05;05D05E05N05O05P05Q05V05c06006=06F06K06L06M06N06W06X06\06]07907U08108208?08L08Y08b08f08g08l08m09609709809909:09C09G09P09T09X09\09e0:70:I0:M0:Y0:Z0:[0:d0:m0;10;:0;;0;<0;E0;F0;O0;[0;d0;e0;h0<10<60<?0<H0<I0<R0<[0<_0<d0<m0<n0=30=70=@0=A0=B0=C0=G0=H0=Q0=g0>00>40>@0>I0>J0>K0>L0>Q0>[0>k0?00?90?=0?F0?R0?[0?d0?m0@60@:0@F0@J0@N0@O0@X0@Y0@Z0@[0@g0A00A10A60AC0AP0A]0Af0Ao0B00B40B=0BF0BK0BL0BU0Ba0Bj0C30C<0CI0CV0Cc0Cg0D00D40D@0DL0DM0DV0D_0Do0E?0EC0EL0EU0EV0EW0E`0Ei0Em0F20F;0F?0FH0FQ0FR0FS0FT0F]0Fb0Fk0G40G50G60G70G<0GE0GN0GW0G`0Ga0Gj0H10HI0HQ0HX0He0Hn0Ho0I00I10I:0I;0ID0IE0II0IR0IS0IW0Ii0Io0JA0JJ0JK0JT0J`0Ji0K20K60K?0KC0KL0KQ0K^0Kk0L80LA0LB0LQ0L`0Lo0M30M40M80MA0MM0MV0MZ0Mc0Ml0Mm0N20N30N40N50N:FS2HBS4CEIL2LOS4CEIL2LO2C1SS2LOS3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1SSSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS3NSRS4CEIL2LO2C1SSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS2LOS4CEIL2LO2C1S2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOSS4CEIL2LOSS4CEIL2LOFFFS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS3SPRFFFS4CEIL2LOSS2HBSS2HS2C02T03RZR4RLR02KS3Hsp1HS2HS2C02T03RZR4RLR02KS3Hsp1HS2HS2C02T03RZR4RLR02KS3Hsp1HSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS2LOSS3SPRSS4CEIL2LOSSSSS4CEIL2LOS2HBS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS2LOS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOSSS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOSS1NS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS3SPRS4CEIL2LOSS3SPRS2LOS4CEIL2LOSSSS2LOSS4CEIL2LOS2HS2T02T13RZR4RLR02KSS4CEIL2LOS2HBS4CEIL2LO2C1S4CEIL2LOSSSS3NSRS4RLR03NSRS2NS3RZR3RSR3NSRS3RZRS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LO2C1S2HBS2LOSS4CEIL2LOFFFS4CEIL2LO2C1S4CEIL2LOSS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS4CEIL2LOS2C0S4CEIL2LO2C1S4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOS2NS3RZR3RSR3NSRS2NS3RZR3RSR3NSRS2LOS4CEIL2LOS4CEIL2LOFFS4CEIL2LOS4CEIL2LOS2LOS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSSSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2HS2KSS2NS3RZR4RLR03RSR3NSR2KBS3NSR2KCS2KB2KDS2HS2T02KS2KES4CEIL2LOSSSS4CEIL2LOSS4CEIL2LOSS2HBS4CEIL2LOFS2LOS1N2NS3RZR3RSR3NSRS1N2KBS1N2NS3RZR3RSR3NSRS4CEIL2LOFS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS2HSS4CEIL2LOS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOSS2HBS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSS3SPRSSFS3SPR".
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
