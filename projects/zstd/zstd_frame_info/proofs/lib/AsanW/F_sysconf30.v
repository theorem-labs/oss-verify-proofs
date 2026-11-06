(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Image Tac InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit FsKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASYSCONF : Z := 0x87d08.
Definition AGETPAGESIZE : Z := 0x64834.
Definition AGETMMAPGRAN : Z := 0x64fc8.

Definition sysconf30_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 544, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma sysconf30_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (canary : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 544 ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0x5f3e50 [C8 canary] ->
  rw_cells asegs m 0x5f40d0 [C8 (Z_to_bv 64 4096)] ->
  a0 = Z_to_bv 64 30 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASYSCONF) fc None m (seg_rom asegs)).
Proof.
  intros until canary. intros MI ST CEIL LO RR CAN PGS -> RIMG RSTK.
  unfold ASYSCONF, ARELRO_LO, ARELRO_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (GCAN : rw_cells asegs m 0x99ae8 [C8 (Z_to_bv 64 0x5f3e50)]).
  { Local Ltac2 Set LiaHints.tbl := fun () => "01B0>11805467289.6311805467289.6511805467289.6612010504302.6512852200949.5913110419182.6315685060272.6517221588796.6317776320431.6417776320431.6518040096338.6519006120615.6619624768029.6819624768029.6923230285244.6524091386350.6625435258127.6525435258127.6625566553219.6625566553219.6827202436054.6827202436054.6927679091076.5429071941542.6631423336146.6531781556718.6632087252941.5133680001082.6334290115814.5435930198638.6536428006994.6537587267666.6538782755822.6638806986883.6338806986883.6639939243268.5841564619544.5742831019478.6543061415347.5243987951406.6543987951406.6745221239098.6645254569351.5246058767598.6548781039854.6349848832982.5149891118830.6351433373806.655180980284.66 52780046574.6353042915222.5253767577775.6453767577775.6654552649625.6354618151079.6554965499405.5055104759171.6555104759171.6755234994189.5255716167292.58563227834.65  59028845166.6559178106163.6559308634368.1 59450265349.6760679622738.656166287527.63 61874979822.6662542160161.6662891835758.6663235321900.6263235321900.6563971070123.6863971070123.6966442393718.6668142785748.677030286105.65 7753591367.56 8163491438.63 8900878237.65 9188011161.66 9909486998.50 00000100200300<00@00I00M00Q00U00Y00b00c00d00e00i01201301401501601701801<01=01F01O01P01T01U01^01g02002902:02;02?02@02D02H02L02P02T02X02a02j02k03403=03A03J03K03O03S03T03U03V03W03X03Y03Z03^03g03h03l03m04604704@04A04J04N04R04S04T04U04V04W04X04a04b04c04dSSSS4CEIL2LOS2LOS4CEIL2LOS2HBS2HBS2LOS2LOS4CEIL2LOSFFS2HBS4CEIL2LOSSSSFFS2LOFS4CEIL2LOS4CEIL2LOSS2HBSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2LOSS2HBS2LOS2LOS2LOS2HBS2HaS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOSS2LOS2LOSSSSSSSS2HBS4CEIL2LOSS2KaFS4CEIL2LOSS4CEIL2LOFS4CEIL2LOS2LOS2LOFFSFSSS4CEIL2LOSSS".
eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0x99ae8 (le8 (Z_to_bv 64 0x5f3e50)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  (* [comment removed for export] *)
  assert (ROV : ro_cells asegs m 0x213d4 [CB 2 [Z_to_bv 8 4; Z_to_bv 8 255]]).
  { apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  assert (ROJ : ro_cells asegs m 0x21370 [CB 4 [Z_to_bv 8 172; Z_to_bv 8 107; Z_to_bv 8 6; Z_to_bv 8 0]]).
  { apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
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
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 544 ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0x5f3e50 [C8 canary] ->
  rw_cells asegs m 0x5f40d0 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AGETMMAPGRAN) fc None m (seg_rom asegs)).
Proof.
  intros until canary. intros MI ST CEIL LO RR CAN PGS RIMG RSTK. unfold AGETMMAPGRAN.
  zstep. zstep.             (* [comment removed for export] *)
  zstep.                    (* [comment removed for export] *)
  eapply sysconf30_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; reflexivity.
Qed.
End CANSEC1.
