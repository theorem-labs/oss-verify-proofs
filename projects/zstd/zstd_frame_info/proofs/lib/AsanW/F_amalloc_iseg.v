(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition icptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x52380) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x5236c) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x5236c) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x523c4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma icptA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xa1b58 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa1b7c [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                             C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)] ->
  rw_cells asegs m 0x1329ca [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x520d0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "02O0>10194049518.6511016974190.631162083361.67 1162083375.65 11805467289.6311805467289.6411805467289.6511805467289.6611805467289.6711805467289.6811944803375.6512844508569.6513390583683.631340665966.66 13997492006.5914010572455.6614253206403.6514698211132.6514869235822.6515005369198.6415815196930.5915835617411.661595966771.66 1595966771.68 16005734766.6516622434386.6616622434386.6716622434386.6816856728066.5917000728814.6517508180239.6617508180239.6817721832112.6717776320431.6418112172441.6418295418137.6519003817779.6820725798332.6522976515865.6323492967905.5823562950937.6524630998586.6525240764910.6525835920692.6625878270255.642665991228.66 26734508604.652779448302.66 27813070503.6527981583342.6528060516446.5528496379187.6728595780334.6328638459246.6529501105410.5629514832494.6530032995318.6430196181434.633141338350.65 32198681198.6532377744366.6632651489978.6632762210492.6433680001082.6433893304857.6634103819474.6634103819474.6734103819474.6834197713817.6534233151718.5434563363993.6534643237692.663537628943.68 35973081767.6335979207534.66360322319.67  36115622447.6438748835203.6638773857693.6638773857693.6738773857693.6839219183342.6539617345646.6639631846169.6639782355367.6539833108633.6440005884953.6540613224310.6542263017827.5842831019478.6642831019478.6742831019478.6842847154798.6642976005733.5943059266230.5243268403504.6643268403504.6843987951406.6544490584985.6644697468441.6345141028272.6845221239098.6645273532441.654569555623.66 46356275438.644642516355.64 47169169795.6547933512623.6649228402294.6449360766237.6749360766237.6849426064712.5449874034295.5851818863747.6652074235540.7252118790567.6453719345964.6553746530983.6553767577775.6453827994990.6554452518049.6755916683929.6556064834414.65563227834.65  56538540882.6656538540882.6756538540882.6856721401731.6557733900014.6457745675194.6557878220782.6458440766190.6658879845244.5859266107886.6559349051708.6360492827805.6660492827805.6760492827805.6860616668387.5761359073817.6661917199020.6362236679847.6663131786862.6563235321900.626358563054.65 64219115431.6564932245891.6565263019168.5966209555097.6668714883566.66698988910.63  7219832892.66 742854766.63  7605503698.66 7605503698.67 7605503698.68 8583720762.65 8676799164.65 9288527478.64 00000;00F00J00N00O00P00Q00R00S00T00X00Y00Z00e00f00g00h00l01701B01C01D01E01F01Q01\01g02202602A02B02C02G02K02L02M02N02R02S02T02U02Z02e02f02j02n03203=03>03I03J03K03V03a03b03m03n04304>04I04T04Y04]04b04c04n05905D05E05F05G05K05L05M05X05Y05]05^05_05`05a05l06706806906:06;06<06A06F06K06P06[06\06`06d06h06l06m06n07207707807907D07E07F07J07K07L07M07N07O07P07Q07R07V07W07[07f07j07k08608;08F08Q08\08]08h08m09809C09D09O09S09T09U09V09Z09[09_09`09k09o0::0:;0:<0:=0:>0:I0:T0:X0:c0:n0;90;D0;I0;M0;NS4CEIL2LO1HS4CEIL2LO1HS2LOS2LOSSSSSSS2LOSSS4CEIL2LO1HSSSS2HBS4CEIL2LO1HS4CEIL2LO1HSSSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HSSS2HBS2LOSSSS2HBSSSS3SPRS4CEIL2LO1HSS2LOS2HBS2HBS4CEIL2LO1HSS4CEIL2LO1HSSS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HSS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRS2HBS3SPRSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSSS2HBSSS4CEIL2LO1HSS2LOSSSSS4CEIL2LO1HS4CEIL2LO1HSSSSSS3SPRS3SPRS3SPRS3SPRS4CEIL2LO1HSS2LOS2HBS2HBS2LOSSS2HBS3SPRSSS4CEIL2LO1HSSS2LOSSSSSSFSS2LOSS2LOS4CEIL2LO1HS2LOSS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS2HBSSSS2LOSS2LOSS4CEIL2LO1HS2LOS4CEIL2LO1HSSSSS4CEIL2LO1HS4CEIL2LO1HS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRS2HBS".
carve_frame 2128%nat ST.
  (* [comment removed for export] *)
  cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2128).
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  step. sstep. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. lstep. step.                                       (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.                               (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.                          (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold icptA_post. do 10 eexists. exists (firstn 2040 (skipn 16 junk)). eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icptB_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0v : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x523d8) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  s0v s1
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x311f8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x523d8)].

#[using="Type"] Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  s1 = Z_to_bv 64 n ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x523c8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "00>0>11805467289.5511805467289.5717721832112.5728496379187.57360322319.57  42831019478.5742976005733.4845221239098.554569555623.55 47933512623.5651818863747.5553719345964.5460619012633.467219832892.55 00000100200600700800=00>00C00D00H00I00M00Q00USSS2HBSSS3SPRSS3SPRSS2LOSS2LOS2LOS2HB".
carve_frame 16%nat ST.
  do 3 step.                                                     (* [comment removed for export] *)
  do 7 step.                                                     (* [comment removed for export] *)
  apply evtF_done. unfold icptB_post, AINSTANCE. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma icptC_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  0 < UB < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x523d8)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x311fc) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x311fc) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "00M0>13390583683.7114253206403.7216856789792.6517776320428.7118156171132.6420070138776.6325878270252.7126397653890.6530415381124.64360322319.72  36115622444.7137645959030.7038748835203.7343987951407.724642516355.71 47169169795.7247933512620.7149473387449.6551818863747.7153719345965.7053767577772.7156721401731.7258879845244.6458955648508.6459308628179.6561492862777.6561917199021.7063235321901.7064932245891.7200000100200600:00;00<00@00E00I00J00N00O00P00T00U00V00Z00^00_00c00g00h00i00j01201601:01>01?SSS2LOS2LOSSS2LOS3UBRS2LOSS2LOSSS2LOSSS2LOS2LOSS2LOS2LOSSSS3UBR2K0S2LOS2LOS2LOS".
if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  do 4 step.                                                     (* [comment removed for export] *)
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
