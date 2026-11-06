(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AKitQ F_aintal.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ficptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x52224) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 p)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x52210) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x52210) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x52268) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa2240, 0xa2240 + 0x81030); (0x130ac8, 0x130ac8 + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' 0x130ac8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xa2240 (0xa2240 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xa2248 + 8 * j) (le8 (Z_to_bv 64 0))).

#[using="Type"] Lemma ficptA_spec : forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
  rw_cells bsegs m 0xa1d3c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                             C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)] ->
  rw_cells bsegs m 0x132b8a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0x98ff0 [C8 (Z_to_bv 64 0x130ae0)] -> rw_cells bsegs m 0x130ae0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK.
  unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa2240, 0xa2240 + 0x81030); (0x130ac8, 0x130ac8 + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
  step.                                                          (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0340>1162083360.89 1162083374.86 11658450183.8111805467289.6811805467289.6911805467289.7011805467289.7111805467289.8711805467289.8811805467289.9011850835729.82118736110.70  11944803374.8712334040174.7012608870894.7012844508569.701284870126.69 12909872956.8013342323729.8013390583683.6813993462363.8114010572455.8814253206403.7014698211132.7015280047342.7015819558015.8115835617411.881595966771.87 1595966771.90 16033677678.6816452877038.6816506041710.7017141182446.7017508180239.8717508180239.9017508353724.8217776320431.6918112172441.6918295418137.7018712044988.8119003817779.9019007305966.691901476206.68 20725798332.7021750412114.8721750412114.9022700267513.6822700267513.8422976515865.6823310670236.8123488737418.8023562950937.7023814431342.7023847006446.6923921527484.8124245873445.6224559830510.8824630998586.7025358857070.7025656252822.7925835920692.8725878270255.6926291562981.8126494647592.6826494647592.6926494647592.7026494647592.7126494647592.8726494647592.8826494647592.9026507015092.822665991228.71 26734508604.7027487025262.8827813070503.7028064746879.6128575982988.8129496748159.6229782367974.8130196181434.6831156070897.9031158168048.8132651489978.7132762210492.6932965887298.9233680001082.6933893304857.8834197713817.7034233151718.5934563363993.7034613502574.7034643237692.883537628943.90 35973081767.6836115622447.6936936768494.8838467863406.6938748835203.7138773857693.8738773857693.9039631846169.7139782355367.7039833108633.6940005884953.7042267177992.8042831019478.8742831019478.9042995994990.7043061792393.5743183854972.8143268403504.8743268403504.9043987951406.7044021460374.7844697468441.6845141028272.9045221239098.8845273532441.7045751589358.7046242528466.8746242528466.904642516355.69 47169169795.7047469105018.7848111625070.7148687962964.7748781039854.6948804778094.714932169326.71 49360766237.9049432389714.6049878323996.8049921929014.655012112366.88 50176460632.8250565006190.705191233902.68 52074235540.9352118790567.6953746530983.7053767577775.6954011733842.8754011733842.9054452518048.8954465538982.7855207105262.6955916683929.7056013230830.8856170558594.6156199689966.70563227834.70  56721401731.7056851286510.7057745675194.70578361838.70  58536729426.8758536729426.9059028845166.7059349051708.6859366507502.7159368190966.8559748865774.7060492827805.8760492827805.9060679622738.8760679622738.9061264814446.7061359073817.7161872782326.8561874979822.8861917199020.6862236679847.7163174103918.6863235321900.6763267093326.936405779422.93 64182077138.8764182077138.9064219115431.7064556005486.7164588566254.7064829717820.8164932245891.706536339054.70 65531314038.8566209555097.8866260016006.6866260016006.8466443298926.7167047510126.687720336238.70 8054831726.70 8583720762.70 8676799164.70 8773384430.70 8967238126.70 00000400800900:00;00<00=00>00?00@00M00V00Z00c00l00m01601701D01E01F01G01H01L01U01V01W01X01Y01b01k02402=02>02?02@02D02E02F02S02T02]02f02j03303<03M03_03`03m03n03o04804A04N04R04[04`04i04j04k04o05005105205305405505605705D05H05L05U05V05W05f05g05h05m06106506:06>06B06G06H06I06J06K06T06X06Y06Z06^06g07007107207307407507607707<07A07F07O07S07`07d07h07l07m07n08208708808A08J08S08T08U08Y08b08f08o09809A09B09C09D09S09\09]09f09o0:00:10:20:60:?0:H0:L0:M0:V0:W0:`0:a0:j0:o0;00;90;>0;G0;P0;Y0;b0;f0;o0<00<90<:0<;0<D0<M0<V0<W0<X0<a0<e0<f0<o0=30=70=80=A0=J0=K0=T0=]0=j0=k0>40>50>60>=0>E0>N0>W0>`0>i0>n0?20?;0?DS2LOS2LOFSSSSSSSS4CEIL2LO3HspS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOFS4CEIL2LO3HspSSSSS2HBS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSFS2LOSSS4CEIL2LO3HspSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LO2Hj2Hi1HS4CEIL2LO3Hj02Hi1HSS4CEIL2LO3HspSSS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS2LOS4CEIL2LOS3SPRS4CEIL2LOSSS2LOFSSSSSSSS4CEIL2LO3HspS2HBS2HBS4CEIL2LOSSS4CEIL2LO3Hsp1HSSS3SPRS2PRS2PRS3SPRS2HBS2JRS3SPRSSSSS4CEIL2LOS2HBSSS2LOS4CEIL2LOS4CEIL2LOSSSSSSSS3SPRS3SPRS3SPRS4CEIL2LOS2LOS4CEIL2LO3HspS2HBS2HBS2LOSSS2HBS3SPRSS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2PRS4CEIL2LOS2PRS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS4CEIL2LO3SPR1HS4CEIL2LOSS4CEIL2LOS4CEIL2LOFSSS2LOS4CEIL2LOS4CEIL2LOS2LOSS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS3SPRSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS2LOSS4CEIL2LOS2LOS2JRFS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspSS4CEIL2LOSSS2Hj2HiS3Hj02HiS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS2HBS4CEIL2LOS4CEIL2LO".
carve_frame 2128%nat ST.
  cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs mm (664136 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk bsegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk bsegs ?mm 664128 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells bsegs ?mm 1247944 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at bsegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.                                (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.   (* [comment removed for export] *)
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (664136 + 8 * j) with (664128 + j * 8 + 8) in RD by lia.
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
  stk bsegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
  mem_inv bsegs m ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x52280) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52280) fc None m (seg_rom bsegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00D0>13390583683.6814253206403.6817776320429.6718156171132.6220070138776.6125878270252.6830415381124.6236115622444.6838748835203.7043987951407.694642516355.68 47169169795.6949473387449.6353767577772.6856721401731.6958955648508.6261492862777.6361917199021.6763235321901.6764932245891.6900000100200600700800<00@00D00E00I00J00K00O00S00T00U00Y00]00a00bSSS2LOSSS2LOS2LOS2LOSS2LOSSS2LOS2LOSSS2LOS2LOS2LOS".
do 7 step. zstep. step.                                 (* [comment removed for export] *)
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. split; [|exact ST].
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
