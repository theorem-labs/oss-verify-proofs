(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Export AF_atexit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.
Definition RSTDIN : Z := 0x9df18.
Definition stdin_cells : list cell :=
[C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x8e660); C8 z64; C8 z64; C8 z64; C8 z64;
C8 (Z_to_bv 64 0x8e68c); C8 z64; C8 (Z_to_bv 64 0x8e7a4); C8 (Z_to_bv 64 0x5f5f28); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].
Section StdioExitStatement2.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Definition stdio_exit_spec_stmt2 : Prop :=
forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x5f56a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells asegs m 0x5f5b08 [C8 z64] ->
rw_cells asegs m 0x9e000 [C8 (Z_to_bv 64 RSTDIN)] ->
rw_cells asegs m RSTDIN stdin_cells ->
rw_cells asegs m 0x9df10 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells asegs m 0x9de20 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
mem_inv asegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
(bv_unsigned sp < 2^47)%Z ->
implAM RNG (stdout_exit_flush get_so set_so) s
(stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ed8c) fc None m (seg_rom asegs)).
End StdioExitStatement2.
End CANSEC1.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma a_Exit_specM : forall {St : Type} RNG (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem),
mem_inv asegs m ->
a0 = Z_to_bv 64 code ->
implAM RNG (msys (NExit code) dec_exit) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8906c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI ->.
apply implAM_sys; [exact I|]. do 2 zstep. step_ecall.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>10780409500.4013661623673.40000001002FF".
split; [ at_nodeA_solve | intros rsp a H; cbn in H; discriminate H ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition MDTOR_DEPTH : Z := 1024.
Definition MDTOR_W : list (Z * Z) :=
[(0x9edc0, 0x9edc8); (0x9fd30, 0x9fd38); (0x7fffc1c4, 0x7fffc428); (0x8000bc06, 0x8000bdb6)]%Z.
Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9edc0, 0x9edc8); (0x9fd30, 0x9fd38);
(0x7fffc1c4, 0x7fffc428); (0x8000bc06, 0x8000bdb6)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).
Definition module_dtor_stmt (PRE : mem -> Prop) : Prop :=
forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
PRE m ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
mem_inv asegs m ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
evtF asegs RNG (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8162c) fc None m (seg_rom asegs)).
Definition afuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5460, 0x5f5461); (0x5f5468, 0x5f546c); (0x5f5470, 0x5f5478)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).
#[using="Type"] Lemma afuncs_on_exit_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
atx_stateA reg m ->
rw_cells asegs m 0x5f56a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
mem_inv asegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
evtF asegs RNG (afuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x890b8) fc None m (seg_rom asegs)).
Proof.
intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF) LIBC MI LO KH RSTK RIMG.
unfold APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5460, 0x5f5461); (0x5f5468, 0x5f546c); (0x5f5470, 0x5f5478)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
Ltac a_lock := hstep; hstep; hstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); if_true; hstep.
Ltac a_unlock := hstep; (try replace (sx32 z64) with z64 by (vm_compute; reflexivity)); nlit; astep; hstep.
Local Ltac2 Set LiaHints.tbl := fun () => "02V0>10234336261.6710345787758.7511613074542.7411624100237.7711624100237.8112077381045.7613219133678.7613564410042.7613675852790.7514965928558.7415032614711.6515032614711.6615401314670.7516460732597.7617072082362.7617324619706.7617440010734.7317776320417.7517776320428.731800609155.75 18472172602.7718472172602.8118694006766.7318739900433.6618878608314.7619487559098.7619622476014.7619715914222.731994914414.74 20358894318.7621462605678.7522389541692.7322474082317.7623207695043.6623515987130.7623806169710.7423847006446.7624336903790.7624638473347.7524638473347.7725792608750.7327717157230.7527911298325.6627919346106.7628232702966.7228417259964.7528794186938.7629193796462.7529531591534.7529870281326.7430652851130.7630740307312.7730740307312.8130876851182.7531378308326.6631688326330.7631747197942.7432152641518.7532307613550.7332716547054.7533680001082.7634430152252.7634826175214.7434862521530.7635904081082.7636115622432.7636115622447.743622303802.77 3622303802.81 36936768494.7537514381363.6637813712954.7737813712954.8140457739452.7440647629038.7640653749742.7542864621754.7643059266230.6443299019630.7543864983022.7543987951392.7643987951406.7543988483203.7343988483203.7544051174384.7644147925946.7644590757434.7744590757434.8145221239098.7545848756903.7346134254574.7546468661564.7547201393082.7647974685754.7747974685754.8148712801850.7748712801850.814890470458.77 4890470458.81 49440506222.7349649769127.7650263849454.7350317564526.7451004059630.7351612054330.7751612054330.8151711223320.6552105090727.7552118254702.765227822010.76 52567164907.7352567164907.7452567164907.7552567164907.7652567164907.7752567164907.8153767577774.7453767577775.7454243526019.7454243526019.7654722921710.7456072045370.7756072045370.81563227834.74  56573624373.7756573624373.8156757832430.7656840378606.7657400943598.7557745675194.7558148933562.7658512233326.7558545717488.7659368190966.7259415204078.765953130734.76 60668852342.7360858483367.7561471961921.6662245250030.7562569894766.7562704248302.7563235321900.7263235321902.7463305555623.7464318125073.6664997134979.7664997134979.7765048273910.7265088762478.7465097823086.7565284019386.766642473454.73 67943285742.7568008320110.7468011150522.7668096078318.7368644094966.75761403661.76  7720336238.75 7764618426.76 8054831726.74 8583720762.73 8736766010.77 8736766010.81 8967238126.73 00000100900A00B00C00K00S00T00U00]00^00_00g00o01001101901=01A01B01C01D01L01M01N01O01W01_01g01o02702;02<02=02>02F02N02V02W02X02`02h02l02m02n03203303;03C03K03L03M03N03V03W03X03Y03a03i04104604:04B04C04D04H04L04M04N04V04W04X04Y04]04e04m04n05205:05B05F05J05K05L05M05N05O05P05U05V05^05b05c05d05e05f05g05h05i06106206:06B06J06K06L06M06N06V06W06X06Y06Z06[06\06]06a06e06f06g06o07007107607>07F07N07V07^07c07d07l07m07n08608>08?08@08A08I08Q08Y08]08a08b08c08d08e08f08n09609709?09G09O09P09X09Y09Z09b09c09k0:00:10:20::FS2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'SSS2LO3KH'FFS2LO3KH'S2LO3KH'SSS2LO3KH'S2LOS2LOSSSS2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBSFSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LOSSS2HBSS2LO3KH'S2LO3KH'S2LO3KH'SSSS2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S3RSPS2HBS2LO3KH'SSS2LOS2LOSSS2LO3KH'FSSS2HBS2LO3KH'S2LO3KH'SS2LOS2LO3KH'S2LO3KH'S2LOS2LOSSSSSSS3RSPSS2LO3KH'S2HBSSSSSSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSSSS2LO3KH'SSSSSSSS2LOS2LOSSS2LO3KH'SSS3RSPS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S3RSPSS2LO3KH'SSS2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S2LOS2LOSSSSSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SSS2LO3KH'SS2LO3KH'S3RSPSSS2LO3KH'".
carve_frame 48%nat ST.
steps_to 0x93380%Z. a_lock.
astep. astep.
destruct reg; cbn [negb andb orb] in *.
-
hstep. nlit. hstep. hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
hstep. hstep. hstep. hstep. hstep. hstep. hstep.
a_unlock.
hstep. hstep. hstep.
hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
hstep. hstep. a_lock.
hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
hstep. hstep. hstep. hstep. hstep. hstep. hstep.
a_unlock.
hstep. hstep. hstep.
hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
hstep. hstep. a_lock.
hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
hstep. hstep. hstep. hstep. hstep. hstep. astep.
steps_to 0x89178%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
a_unlock.
unfold afuncs_on_exit_post. sys_finish.
-
hstep. nlit. hstep. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
hstep. hstep. hstep. hstep. hstep. hstep. hstep.
a_unlock.
hstep. hstep. hstep.
hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
hstep. hstep. a_lock.
hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
hstep. hstep. hstep. hstep. hstep. hstep. astep.
steps_to 0x89178%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
a_unlock.
unfold afuncs_on_exit_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
[(sp - 48 - MDTOR_DEPTH, sp); (0x5f5680, 0x5f5684); (0x5f5460, 0x5f5461); (0x5f5468, 0x5f546c); (0x5f5470, 0x5f5478); (0x9ee10, 0x9ee11)]%Z.
Definition AEXIT_W (sp : Z) : list (Z * Z) := AEXIT_W1 sp ++ MDTOR_W.
Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x89308) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ed8c) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (0x5f5680, 0x5f5684); (0x5f5460, 0x5f5461); (0x5f5468, 0x5f546c);
(0x5f5470, 0x5f5478); (0x9ee10, 0x9ee11);
(0x9edc0, 0x9edc8); (0x9fd30, 0x9fd38); (0x7fffc1c4, 0x7fffc428); (0x8000bc06, 0x8000bdb6)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -16)
/\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ rw_cells asegs m' 0x5d5368 [C4 (Z_to_bv 64 t)]
/\ rw_cells asegs m' 0x5f5680 [C4 (Z_to_bv 64 t)]
/\ rw_cells asegs m' 0x9ee10 [C1 (Z_to_bv 8 1)].
Section Prefix.
Variable PRE : mem -> Prop.
Hypothesis MDTOR : module_dtor_stmt PRE.
Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.
#[using="MDTOR PRE_frame"] Lemma aexit_prefix_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso : word),
PRE m ->
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x5d5368 [C4 (Z_to_bv 64 t)] ->
rw_cells asegs m 0x5f5680 [C4 z64] ->
rw_cells asegs m 0x5f56a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_stateA reg m ->
rw_cells asegs m 0x9a440 [C8 (Z_to_bv 64 0x99218); C8 (Z_to_bv 64 0x99208)] ->
rw_cells asegs m 0x99208 [C8 (Z_to_bv 64 0x8162c); C8 (Z_to_bv 64 0x31314)] ->
rw_cells asegs m 0x9ee10 [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0x99750 [C8 (Z_to_bv 64 0x89180); C8 z64] ->
rw_cells asegs m 0x9b480 [C8 dso] ->
mem_inv asegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
evtF asegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8929c) fc None m (seg_rom asegs)).
Proof.
intros until dso. intros HPRE ST TID EXL LIBC AX GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
destruct AX as ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF). unfold APAEF_INCB, ACOV_FLAG, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. pose proof KH as KHI. unfold KHIGH in KH.
pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "03O0?10345787758.87 10558322770.90 10558322770.99 11352265753.97 11658450183.94 11742836854.96 12524706234.82 13161002319.11313161002319.94 13219133678.95 13285247418.82 1343986644.113 1343986644.94  13863029690.82 14054347474.90 14793086774.94 14944246202.82 16157959664.10316837903350.96 17776320430.11417776320430.96 18136077224.10618289765306.82 19049469500.97 19139940946.90 19139940946.99 19942487194.90 20433961190.80 20474933061.90 2105339983.113 2105339983.94  21462605678.87 21750412114.90 22398839631.11322398839631.94 22465273151.10622882010094.87 22882010094.97 22882010094.98 23250158093.10323446526574.97 24638473347.11624638473347.98 25314760359.97 25878270252.96 26210429109.82 26406216634.82 26993921178.87 27075805806.97 27911298325.10627923971379.99 28116497845.10329545175216.99 30225150802.90 30876851182.87 31521058898.90 31672869045.10331791172943.11331791172943.94 32600174396.87 32716547054.87 3321256686.95  33680001082.95 33924000758.97 34145311854.97 34169650127.11334169650127.94 34430152252.95 34673264466.90 3525607222.75  35811162350.95 35930198638.97 36115622433.11536115622433.97 36438299669.90 36630883559.81 36641385327.82 36654913774.95 36899703738.82 36936768494.87 36944450135.81 37258164461.81 37429491794.90 37587267666.90 37587267666.99 37823627923.88 38084277946.10338508687005.99 38782755822.87 38782755822.97 38782755822.98 39521875765.71 39998025810.90 40201484047.90 40292163822.95 40457739452.97 40653749742.87 40737376082.90 40737376082.99 41387167214.87 41387167214.97 41387167214.98 42046568378.82 42273372099.89 42777245626.82 42831019478.90 42831019478.99 43059266230.78 43104399792.90 43124198553.95 43271993786.82 43667128060.10543836933870.95 43864983022.87 43987951404.11243987951404.94 45221239098.87 45221239098.97 45221239098.98 45473410746.10345752853946.82 46134254574.87 46468661564.98 47586416750.97 47737464762.82 47909047994.10348316456345.97 48429240188.89 48538816594.90 48538816594.99 4866047897.97  4866047897.98  48909296622.87 48909296622.97 48909296622.98 49649769127.95 49750950894.87 49750950894.97 49750950894.98 50667478351.11350667478351.94 51255250618.10351425718543.99 51468013242.10351481786499.97 51678667182.98 52567164907.10352567164907.82 52567164907.87 52567164907.90 52567164907.95 52567164907.97 52567164907.98 52567164907.99 52579502455.11352579502455.94 52780046574.95 52994560594.90 53386120174.87 53386120174.97 53386120174.98 53391726517.10353605654098.90 53605654098.99 53767577774.89 54164510851.87 54243526019.11554243526019.97 54404701703.11354636957394.90 54817786350.87 54817786350.97 54817786350.98 55972696470.90 5610575698.90  56170333721.90 56172233139.71 563227834.97   57400943598.87 58148456595.86 58658194106.10358668948922.82 58865697174.10958871667702.95 59314923118.82 60858483367.98 61439603310.97 62245250030.87 62583080755.90 63235321900.86 63305555623.97 63779719325.99 64311140434.90 64311140434.99 6446801648.82  6491058798.97  64997134979.11364997134979.95 65088762478.97 65823634362.82 66307532356.90 66309513997.82 66747928658.90 66747928658.99 67081926311.87 67476598335.88 67759509071.11367759509071.94 67943285742.87 67943285742.97 67943285742.98 721185103.113  721185103.94   7311899066.82  7488583.88     7681401786.82  8268688502.111 8520501178.82  8800126135.114 8800126135.92  8800126135.95  9775356142.95  9841059514.103 00000700>00E00F00G00H00I00T00_00f00g00h00i00j01101>01?01@01A01E01I01J01K01O01V01]01^01_01`01k02602=02D02O02Z02[02b02i03003103803903:03;03?03F03G03H03O03S03T03[03_03f03m04404;04F04Q04U04\04c04h04i05005;05F05J05Q05^05e05l06006406806<06@06G06H06O06S06T06[06b06i06m06n06o07607=07D07H07O07P07W07[07b07i08008708>08E08F08M08N08S08X08\08`08a08b08c08j09109509909>09C09H09I09J09Q09U09\09]09^09_09`09g09n09o0:00:70:>0:E0:F0:M0:T0:[0:f0;10;20;30;40;50;90;:0;;0;<0;=0;>0;?0;@0;A0;L0;W0;^0;e0;l0<30<:0<A0<H0<O0<S0<T0<U0<V0<W0<^0<e0<l0=30=40=;0=<0==0=B0=I0=M0=N0=O0=P0=Q0=W0=X0=_0=f0=g0=k0=l0=m0>40>;0><0>C0>D0>E0>L0>M0>N0>O0>V0>]0>^0>_0>j0?50?<0?C0?J0?U0?`0?a0?b0?c0?d0?e0@20@50@B0@I0@JS2LO2KHS2LO2KHS2LO2KHSFSSS2LO2KH3HspS2LO2KH3HspS2LO2KHSFFSS2LO2KHS2LO2KH3RSP1HSSSS2LOS2LOFSS2HBS2LO2KHS2LO2KHFSFS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspFS2LO2KHS2LO2KHS2LO2KHSS2LO2KHSSSS2LOS2LO2KHSFS2LO2KHS2LOSS2LO2KHS2HBS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspS2HBS2LO2KHS2LO2KHS3RSPSS2LO2KHS2LO2KH3HspS2LO2KH3HspS2HBS2LO2KHS2LO2KH3RSP1HS2LO2KHS2LO2KHS2LOS2LOS2LOS2HtS2HtS2LO2KHSS2LO2KHS2HtFS2LO2KHS2LO2KHS2LO2KHS2LOSSS2LO2KHS2LO2KHS2LO2KHS2LOS2LO2KHSS2LO2KHS2HBS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSS2LO2KHSS3RSPS3RSPS2LOS2HBSSSS2LO2KHS2LO2KHS2LOS2LOS3RSPS3RSPS3RSPSSS2LO2KHS2HBS2LO2KHSSSSS2LO2KHS2LO2KHSSS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspSSSSS2LOSSSSSSSSS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LOSSSFS2LO2KHS2LO2KHS2LO2KHS2LO2KHSS2LO2KHSSS3RSPS2LO2KHS2LOSSSSS2Ht1KSS2LO2KHS2LO2KHSS2LOSSS2LO2KHS2LO2KHSS2LO2KHSSS2LO2KHSSSS2LO2KHS2LO2KHSFS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspSSSSSS2LO2KH3Hsp1HS1HS2LO2KH3Hsp1HS2LO2KHS".
carve_frame 16%nat ST.
do 6 hstep.
replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
hstep. hstep.
sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
astep. sort_lits. amo_step. astep.
hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. astep.
hstep. hstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AX : atx_stateA reg mx) by (exact (conj (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 X9)))))))) (conj CB CF))) end.
clear X1 X2 X3 X4 X5 X6 X7 X8 X9 CB CF.
call_sp (afuncs_on_exit_spec reg RNG);
try (first [ exact AX | hyp_by_addr | exact KHI | exact RIMG | (eapply rng_sub'; [exact RSTK | lia]) | lia ]).
clear AX. match goal with S : stk _ _ lo _ |- _ => rename S into ST end.
hstep. carve_frame 32%nat ST.
steps_to 0x31314%Z.
carve_frame 16%nat ST.
hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
steps_to 0x89180%Z. hstep.
steps_to 0x313a0%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
astep. astep. hstep. hstep. hstep.
match goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mc _) =>
pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH, KHIGH; lia) MU WM) as HPRE1;
assert (MU2 : munch (AEXIT_W (bv_unsigned sp)) m mc)
by (eapply munch_weaken; [| exact MU]; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH, sub_fp; cbn [outside app]; intros; lia);
clear MU; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH in MU2; cbn [app] in MU2
end.
call_sp (MDTOR RNG); try first [ exact HPRE1 | eassumption | unfold MDTOR_DEPTH; lia | unfold KHIGH; lia | exact RW ].
1:{ eapply rng_sub'; [exact RSTK | lia]. }
astep. astep. hstep. hstep. hstep. hstep.
match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
hstep. hstep.
hstep.
unfold aexit_prefix_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Prefix.
Section ExitProof.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable PRE : mem -> Prop.
Hypothesis MDTOR : module_dtor_stmt PRE.
Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.
Hypothesis stdio_exit_spec : stdio_exit_spec_stmt2 get_so set_so.
#[using="MDTOR PRE_frame stdio_exit_spec"] Lemma aexit_spec : forall (reg : bool) RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
PRE m ->
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x5d5368 [C4 (Z_to_bv 64 t)] ->
rw_cells asegs m 0x5f5680 [C4 z64] ->
rw_cells asegs m 0x5f56a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_stateA reg m ->
rw_cells asegs m 0x9a440 [C8 (Z_to_bv 64 0x99218); C8 (Z_to_bv 64 0x99208)] ->
rw_cells asegs m 0x99208 [C8 (Z_to_bv 64 0x8162c); C8 (Z_to_bv 64 0x31314)] ->
rw_cells asegs m 0x9ee10 [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0x99750 [C8 (Z_to_bv 64 0x89180); C8 z64] ->
rw_cells asegs m 0x9b480 [C8 dso] ->
rw_cells asegs m 0x5f5b08 [C8 z64] -> rw_cells asegs m 0x9e000 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
rw_cells asegs m 0x9df10 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x9de20 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
mem_inv asegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
(bv_unsigned sp < 2^47)%Z ->
implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8929c) fc None m (seg_rom asegs)).
Proof.
intros until guard. intros HPRE ST TID EXL LIBC AX GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF GG GU MI -> -> Ht LO KH RSTK RIMG RW RG0 SP47.
pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
unfold file_cells in SOF1, SEF1. unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
unfold Driver.exit_model.
eapply (implAM_bind RNG _ _ s
(fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
ms' = MS (mkR (Z_to_bv 64 0x89308) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x89308) fc None m' (seg_rom asegs) /\ mem_inv asegs m')).
-
change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
apply implAM_from_evt.
Local Ltac2 Set LiaHints.tbl := fun () => "00N0?10429640106.11713161002319.11613161002319.1181343986644.116 15103023515.11616826702739.13918634102223.11820175941839.1182105339983.118 21510966599.1162168467805.117 22398839631.1172260382799.118 28696517455.11828751370288.11728994763729.11731791172943.11731913181519.11834169650127.1173525607222.120 42148696048.11743549400527.11850667478351.11752085204047.11855288767055.11856172531244.11763002406865.11866920267471.11867759509071.118721185103.118  00000400<00D00E00F00G00O00W00_00`00f00g00o01701801@01H01P01X01g01l02402<02D02L02M02U02]02^02fS2LOS2LO3KH'S2LO3KH'FFSS2LO3KH'S2LO3KH'S2LO3KH'FS4SP47FS2LO3KH'S2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO4SP473KH'1HS3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'FS2LO3KH'".
call (aexit_prefix_spec PRE MDTOR PRE_frame reg RNG);
try first [ exact HPRE | eassumption | reflexivity | unfold MDTOR_DEPTH; lia | exact KH | exact RW ].
all: try (lazymatch goal with |- rng _ _ _ => first [exact RSTK | exact RIMG] end).
name_sp sp (-16)%Z.
pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt2, got_ssp, ssp_guard, GLOBALS_TOP, RSTDIN, stdin_cells in SE.
apply evtF_done. eapply implAM_mono; [eapply (SE RNG)|].
all: lazymatch goal with
| |- forall _, _ =>
intros [] s' ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
replace (ret_pc (Z_to_bv 64 0x89308)) with (Z_to_bv 64 0x89308) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
do 30 eexists; split; [cbv delta [mkR]; reflexivity | destruct PO as (_ & _ & MIq & _); exact MIq]
| |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
| |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
| |- rng _ _ _ => unname_sp; first [ eapply rng_sub'; [exact RSTK | lia] | exact RIMG ]
| |- rng0 _ => exact RG0
| |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia | assumption ]
end.
-
clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
intros [] s' ms' PO. destruct_exs PO. destruct PO as [-> MI'].
apply implAM_from_evt. zstep. zstep. apply evtF_done.
apply a_Exit_specM; [exact MI' | reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ExitProof.
End CANSEC2.
