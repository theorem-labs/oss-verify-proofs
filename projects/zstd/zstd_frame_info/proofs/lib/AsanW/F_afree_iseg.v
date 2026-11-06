(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ F_aintal.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ficptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x52220) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 p)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x5220c) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x5220c) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x52264) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa2080, 0xa2080 + 0x81030); (0x130908, 0x130908 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x130908 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xa2080 (0xa2080 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa2088 + 8 * j) (le8 (Z_to_bv 64 0))).

#[using="Type"] Lemma ficptA_spec : forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
  rw_cells asegs m 0xa1b7c [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                             C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)] ->
  rw_cells asegs m 0x1329ca [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0x98e18 [C8 (Z_to_bv 64 0x130920)] -> rw_cells asegs m 0x130920 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK.
  unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa2080, 0xa2080 + 0x81030); (0x130908, 0x130908 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
  step.                                                          (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0340>10194049518.7011382190574.701162083360.89 1162083374.86 11647286254.7011658450183.8111716686062.6911805467289.6811805467289.6911805467289.7011805467289.7111805467289.8711805467289.8811805467289.9011944803374.8712844508569.7013390583683.6813401302801.821340665966.71 13993462363.8114010572455.8814253206403.7014472148348.8114698211132.7015005369198.6915600526930.8715600526930.9015819558015.8115835617411.881595966771.87 1595966771.90 16005734766.7016622434386.8716622434386.9017508180239.8717508180239.9017776320431.6918112172441.6918295418137.7019003817779.9020725798332.7022700267513.6822700267513.8422976515865.6823038706678.8523488737418.8023562950937.7024161039186.8724161039186.9024245873445.6224630998586.7024812739566.8824839773500.8125240764910.7025353615726.6825835920692.8725878270255.6926044510268.8126291562981.8126494647592.6826494647592.6926494647592.7026494647592.7126494647592.8726494647592.8826494647592.9026507015092.822665991228.71 26734508604.7027778003822.702779448302.71 27813070503.7028064746879.6128575982988.8128595780334.6828638459246.7029496748159.6229514832494.7029782367974.812993314286.70 30196181434.6830603927662.7031156070897.9031158168048.8131252939068.813141338350.70 32198681198.7032377744366.8832651489978.7132762210492.6932965887298.9233680001082.6933847179382.8533893304857.8834103819474.8734103819474.9034197713817.7034233151718.5934563363993.7034643237692.88348075025.80  3537628943.90 35973081767.6835979207534.7136115622447.6936654913774.6937845668334.8838748835203.7138773857693.8738773857693.9039219183342.7039617345646.8839631846169.7139782355367.7039833108633.6940005884953.7041635768124.8042267177992.8042309226734.7042488118638.7042831019478.8742831019478.9043061792393.5743268403504.8743268403504.9043987951406.7044021460374.784413803118.71 44697468441.6845141028272.9045221239098.8845273532441.7046217471676.8246356275438.694642516355.69 47169169795.7047469105018.7848538816594.8748538816594.9048687962964.7749166960472.8249360766237.9049432389714.6049750950894.8849878323996.8049921929014.6551219599470.7152040759708.8152074235540.9352118790567.6953746530983.7053767577775.6953853382510.6854300395630.7154452518048.8954465538982.7855916683929.7056064834414.7056170558594.61563227834.70  56721401731.7057745675194.7057878220782.6958440766190.8858618836718.7059266107886.7059349051708.6860492827805.8760492827805.9061359073817.7161439603310.7061778293102.6861917199020.6862003090710.7962236679847.7163131786862.7063235321900.6763267093326.936358563054.70 6405779422.93 64219115431.7064307395438.7064650279534.7064932245891.7066209555097.8866260016006.6866260016006.8467007713006.7068501319406.69698988910.68  742854766.68  7430352502.85 7605503698.87 7605503698.90 8583720762.70 8676799164.70 00000900B00F00J00S00T00]00^00_00`00a00b00c00d00h00i00j01701@01A01B01C01P01T01]01f01o02002102202302<02E02N02O02P02T02U02V02W02[02l03>03?03@03A03B03K03T03X03]03f04304<04E04F04J04W04X04Y04Z04[04\04]04^04_04l05005405=05F05G05H05W05`05i05j06306406=06B06K06O06S06`06i07207;07@07D07H07M07N07O07X07a07b07c07d07h08508608708@08D08M08V08W08X08Y08b08k08l08m08n08o09009509>09G09L09Q09U09Y09]09a09b09k09l0:00:50:60:70:@0:A0:B0:F0:O0:X0:\0:]0:^0:_0:h0:i0;80;A0;N0;O0;P0;Q0;U0;^0;g0;k0;l0;m0<60<70<<0<=0<B0<K0<T0<]0<f0<j0<k0<l0<m0=60=?0=C0=D0=E0=N0=R0=V0=_0=`0=a0=j0>30>40>50><0>D0>M0>V0>_0>h0>i0?20?;0?@0?DS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOFS4CEIL2LOSSSSSSSS2LOSSS4CEIL2LO3HspS4CEIL2LOSSSS4CEIL2LO3HspS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2LOSSSS2HBS4CEIL2LO2Hj2Hi1HS4CEIL2LO3Hj02Hi1HSSSSS4CEIL2LOS4CEIL2LOS2LOS3SPRS4CEIL2LOS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOSS2LOS4CEIL2LO3HspFSSSSSSSS4CEIL2LO3HspS2HBS2HBS4CEIL2LOS4CEIL2LOSSS4CEIL2LO3Hsp1HS4CEIL2LOS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS3SPRS4CEIL2LOS2PRS2PRS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS2HBS2JRS3SPRSSS4CEIL2LOS4CEIL2LOSSSS2HBS4CEIL2LO3HspSSS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOSSSSFS3SPRS4CEIL2LOS4CEIL2LOS3SPRS3SPRS2LOS2HBS2HBS2LOSS4CEIL2LOSS2HBS3SPRSFS4CEIL2LOSSS2PRS4CEIL2LOS4CEIL2LOS2PRSSSS4CEIL2LOSS4CEIL2LO3SPR1HS4CEIL2LOS4CEIL2LO3HspFSSS2LOS4CEIL2LOS4CEIL2LOS2LOSSS4CEIL2LOSS3SPRSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBSSSS4CEIL2LOS4CEIL2LOS2LOSSS4CEIL2LOS2LOS2JRS4CEIL2LOFSS4CEIL2LOS4CEIL2LOSSS2Hj2HiS3Hj02HiS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS3SPRS2HB".
carve_frame 2128%nat ST.
  cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (663688 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk asegs ?mm 663680 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells asegs ?mm 1247496 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.                                (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.   (* [comment removed for export] *)
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (663688 + 8 * j) with (663680 + j * 8 + 8) in RD by lia.
  step. clear RD.                              (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  clear Hj JR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.           (* [comment removed for export] *)
  step. sstep. step.                           (* [comment removed for export] *)
  step. step. lstep. step. step.               (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. lstep. step.                     (* [comment removed for export] *)
  step. step. lstep. step. step.               (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.             (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                       (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.        (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ficptA_post. do 10 eexists. exists (firstn 2040 (skipn 16 junk)). eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma ficptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v spv : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
  mem_inv asegs m ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x5227c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5227c) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00D0>13390583683.6814253206403.6817776320429.6718156171132.6220070138776.6125878270252.6830415381124.6236115622444.6838748835203.7043987951407.694642516355.68 47169169795.6949473387449.6353767577772.6856721401731.6958955648508.6261492862777.6361917199021.6763235321901.6764932245891.6900000100200600700800<00@00D00E00I00J00K00O00S00T00U00Y00]00a00bSSS2LOSSS2LOS2LOS2LOSS2LOSSS2LOS2LOSSS2LOS2LOS2LOS".
do 7 step. zstep. step.                                 (* [comment removed for export] *)
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. split; [|exact ST].
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
