(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Image Tac InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit FsKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASYSCONF : Z := 0x87ee4.
Definition AGETPAGESIZE : Z := 0x64838.
Definition AGETMMAPGRAN : Z := 0x64fcc.

Definition sysconf30_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 544, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma sysconf30_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (canary : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 544 ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0x5f4010 [C8 canary] ->
  rw_cells bsegs m 0x5f4290 [C8 (Z_to_bv 64 4096)] ->
  a0 = Z_to_bv 64 30 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASYSCONF) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros MI ST CEIL LO RR CAN PGS -> RIMG RSTK.
  unfold ASYSCONF, ARELRO_LO, ARELRO_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (GCAN : rw_cells bsegs m 0x99cc0 [C8 (Z_to_bv 64 0x5f4010)]).
  { Local Ltac2 Set LiaHints.tbl := fun () => "01B0>10457177710.6311716686062.6311805467289.6311805467289.6511805467289.6612852200949.5914775942285.5115525371630.6315685060272.651569239581.68 1569239581.69 17221588796.6317776320431.6417776320431.6518497754962.6519006120615.6623230285244.6524161039186.6524812739566.6625435258127.6525435258127.6625566553219.6625566553219.6826506338798.6627302814958.6527679091076.5429071941542.6629594874646.5033680001082.6334170545134.6634290115814.543674242326.51 37774167030.6637916837325.5238806986883.6338806986883.6638847153746.6539939243268.5841564619544.5741988149419.6841988149419.6942831019478.6543061415347.5243913974254.6643987951406.6543987951406.6745221239098.6645254569351.5246358764173.5047472103150.6347921494998.6847921494998.6948165869806.635180980284.66 52970898030.6553767577775.6453767577775.6653860909166.6554552649625.6354618151079.6555104759171.6555104759171.6755716167292.58563227834.65  59178106163.6559308634368.1 59450265349.6760812923602.656166287527.63 62542160161.6663235321900.6263235321900.6563299176018.6564650279534.6565181327726.6668142785748.676878511574.52 7030286105.65 7753591367.56 8900878237.65 9188011161.66 9595551854.65 00000900B00C00D00E00I00J00S00W00X00Y00]00a00e00n00o01301<01E01F01G01H01I01R01[01_01`01a01e01n01o02002102202302402=02A02B02C02D02H02L02U02Y02]02a02e02f02o03003103:03>03G03K03O03X03Y03Z03[03\03]03a03b03f03g04004104204604:04C04L04U04V04W04X04Y04Z04[04dS4CEIL2LOS4CEIL2LOSSSS2LOSS4CEIL2LOS2HBFFS2HBS2LOS2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS2LOFSS2HBS4CEIL2LOSSSSSSS4CEIL2LOS2LOSFFS2HBS2LOS4CEIL2LOS2LOS2LOS2HBS2HaSS4CEIL2LOFFS4CEIL2LOS2HBS4CEIL2LOS2LOS2LOS4CEIL2LOSSSSSS2HBSS2KaFS4CEIL2LOSFS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFSSSSSS4CEIL2LO".
eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0x99cc0 (le8 (Z_to_bv 64 0x5f4010)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  (* [comment removed for export] *)
  assert (ROV : ro_cells bsegs m 0x213d4 [CB 2 [Z_to_bv 8 4; Z_to_bv 8 255]]).
  { apply (ro_cells_image bsegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  assert (ROJ : ro_cells bsegs m 0x21370 [CB 4 [Z_to_bv 8 136; Z_to_bv 8 109; Z_to_bv 8 6; Z_to_bv 8 0]]).
  { apply (ro_cells_image bsegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  carve_frame 32%nat ST. carve_frame 512%nat ST.
  do 4 zstep.               (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep. zstep.             (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka; lia|].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep. if_lit.            (* [comment removed for export] *)
  zstep. zstep. if_lit.     (* [comment removed for export] *)
  zstep. zstep. zstep. if_lit.   (* [comment removed for export] *)
  zstep. zstep. if_lit.     (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_lit.   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep. zstep. zstep.      (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  zstep. zstep. zstep.      (* [comment removed for export] *)
  zstep. zstep.             (* [comment removed for export] *)
  zstep. if_cases Kc; [zify_cond Kc; exfalso; apply Kc; reflexivity|].            (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32). release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma getmmapgran_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (canary : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 544 ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0x5f4010 [C8 canary] ->
  rw_cells bsegs m 0x5f4290 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AGETMMAPGRAN) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros MI ST CEIL LO RR CAN PGS RIMG RSTK. unfold AGETMMAPGRAN.
  zstep. zstep.             (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  eapply sysconf30_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; reflexivity.
Qed.
End CANSEC1.
