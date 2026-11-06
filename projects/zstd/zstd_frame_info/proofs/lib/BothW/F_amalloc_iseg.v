(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2.
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
    ms' = MS (mkR (Z_to_bv 64 0x52384) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x52370) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x52370) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x523c8) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma icptA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells bsegs m 0xa1d18 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xa1d3c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                             C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)] ->
  rw_cells bsegs m 0x132b8a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x520d4) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "02O0>1162083361.67 1162083375.65 11805467289.6311805467289.6411805467289.6511805467289.6611805467289.6711805467289.6811944803375.6512608870894.6512844508569.651284870126.64 13390583683.6313997492006.5914010572455.6614253206403.6514698211132.6515280047342.6515815196930.5915835617411.661595966771.66 1595966771.68 16033677678.6316452877038.6316506041710.6516856728066.5917508180239.6617508180239.6817721832112.6717776320431.6418112172441.6418295418137.6519003817779.6819007305966.6419415681262.6520725798332.6521982102518.6422976515865.6323492967905.5823562950937.6523814431342.6524630998586.6525835920692.6625878270255.642665991228.66 26734508604.652728429678.65 27487025262.6627813070503.6528060516446.5528496379187.6729501105410.5629676826486.6430196181434.6330396535790.6532651489978.6632762210492.6433680001082.6433893304857.6634197713817.6534233151718.5434563363993.6534613502574.6534643237692.663537628943.68 35973081767.63360322319.67  36115622447.6438467863406.6438748835203.6638773857693.6638773857693.6738773857693.6839631846169.6639782355367.6539833108633.6440005884953.6542263017827.5842831019478.6642831019478.6742831019478.6842976005733.5943059266230.5243268403504.6643268403504.6843987951406.6544395637586.6644395637586.6744395637586.6844490584985.6644697468441.6345141028272.6845221239098.6645257912942.6645273532441.6545607773934.644569555623.66 45751589358.6546242528466.6646242528466.6746242528466.684642516355.64 47169169795.6547933512623.6648111625070.6649360766237.6749360766237.6849426064712.5449874034295.585012112366.66 50565006190.6551818863747.6652074235540.7252118790567.6453719345964.6553746530983.6553767577775.6453961827318.6454452518049.6755916683929.6556013230830.6656238753134.65563227834.65  56582466030.6656721401731.6556851286510.6557745675194.6558536729426.6658536729426.6758536729426.6858879845244.5859190426614.6559349051708.6359366507502.6659748865774.6560492827805.6660492827805.6760492827805.6860616668387.5761264814446.6561359073817.6661917199020.6362236679847.6663235321900.6264182077138.6664182077138.6764182077138.6864219115431.6564556005486.6664932245891.6565263019168.596536339054.65 66209555097.6667047510126.6367604033390.637219832892.66 8583720762.65 8676799164.65 8773384430.65 00000400800900:00;00<00=00>00B00M00N00Y00Z00[00\00]00a00l00m00n00o01001;01F01Q01U01V01W01[01_01`01a01b01m02802<02=02>02?02@02K02P02Q02U02Y02]02h03303403503603703803=03H03M03Q03V03W03X03Y03Z03e03i03j03k03l04004;04<04=04>04?04@04A04B04C04H04M04R04W04X04\04`04d04h05305>05I05J05K05O05T05_05`05k05l06706B06M06X06Y06Z06^06i06j06k06l06m07807C07D07E07F07J07K07O07P07T07U07`07k08008;08<08G08L08W08b08m08n08o09309>09I09J09K09L09P09[09\09`09a09e0:00:;0:F0:G0:R0:S0:T0:_0:`0:k0;60;:0;?0;C0;NS2LOS2LOSSSSSSS2LOS4CEIL2LO1HSS4CEIL2LO1HSSSSS2HBS4CEIL2LO1HSSSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOSSS2HBS2LOSSSS4CEIL2LO1HS4CEIL2LO1HS2HBSSSSS4CEIL2LO1HS3SPRSS2LOS2HBS2HBS4CEIL2LO1HS4CEIL2LO1HSSSSSS3SPRS4CEIL2LO1HS3SPRS2HBS3SPRSSSSS4CEIL2LO1HS2HBSSSS2LOS4CEIL2LO1HSSSSSSSSS3SPRS3SPRS3SPRS3SPRSS2LOS2HBS2HBS2LOS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS2HBS3SPRS4CEIL2LO1HSS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS2LOS4CEIL2LO1HSSSSS4CEIL2LO1HS4CEIL2LO1HSFSS2LOSS2LOSS2LOSS4CEIL2LO1HS4CEIL2LO1HS3SPRS4CEIL2LO1HSS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS2HBS4CEIL2LO1HS4CEIL2LO1HSSSS2LOS4CEIL2LO1HSS2LOSS2LOS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HSSS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS2HBS3SPRS2HBS4CEIL2LO1H".
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
    ms' = MS (mkR (Z_to_bv 64 0x523dc) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  s0v s1
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x311fc) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x523dc)].

#[using="Type"] Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk bsegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv bsegs m ->
  s1 = Z_to_bv 64 n ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x523cc) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
  stk bsegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv bsegs m ->
  0 < UB < 2^64 ->
  rw_cells bsegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x523dc)] ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x31200) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x31200) fc None m (seg_rom bsegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "00M0>13390583683.7114253206403.7216856789792.6517776320428.7118156171132.6420070138776.6325878270252.7126397653890.6530415381124.64360322319.72  36115622444.7138748835203.7343987951407.724642516355.71 47169169795.7247933512620.7149473387449.6551818863747.7153719345965.7053767577772.7156231386102.7056721401731.7258879845244.6458955648508.6459308628179.6561492862777.6561917199021.7063235321901.7064932245891.7200000100200600:00;00<00@00E00I00J00N00O00S00T00U00Y00]00^00b00f00g00h00i00j01201601:01>01?SSS2LOS2LOSSS2LOS3UBRS2LOSS2LOSS2LOSSS2LOS2LOSS2LOS2LOSSSSS3UBR2K0S2LOS2LOS2LOS".
if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  do 4 step.                                                     (* [comment removed for export] *)
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
