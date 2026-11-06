(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Export AF_atexit.
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
Definition RSTDIN : Z := 0x9e0a8.
Definition stdin_cells : list cell :=
[C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x8e7f0); C8 z64; C8 z64; C8 z64; C8 z64;
C8 (Z_to_bv 64 0x8e81c); C8 z64; C8 (Z_to_bv 64 0x8e934); C8 (Z_to_bv 64 0x5f5fe8); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].
Section StdioExitStatement2.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Definition stdio_exit_spec_stmt2 : Prop :=
forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x5f5760 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells bsegs m 0x5f5bc8 [C8 z64] ->
rw_cells bsegs m 0x9e190 [C8 (Z_to_bv 64 RSTDIN)] ->
rw_cells bsegs m RSTDIN stdin_cells ->
rw_cells bsegs m 0x9e0a0 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells bsegs m 0x9dfb0 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->
mem_inv bsegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
(bv_unsigned sp < 2^47)%Z ->
implAM RNG (stdout_exit_flush get_so set_so) s
(stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ef1c) fc None m (seg_rom bsegs)).
End StdioExitStatement2.
End CANSEC1.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma a_Exit_specM : forall {St : Type} RNG (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem),
mem_inv bsegs m ->
a0 = Z_to_bv 64 code ->
implAM RNG (msys (NExit code) dec_exit) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x891fc) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI ->.
apply implAM_sys; [exact I|]. do 2 zstep. step_ecall.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>10780409500.4013661623673.40000001002FF".
split; [ at_nodeA_solve | intros rsp a H; cbn in H; discriminate H ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition MDTOR_DEPTH : Z := 1024.
Definition MDTOR_W : list (Z * Z) :=
[(0x9ee80, 0x9ee88); (0x9fdf0, 0x9fdf8); (0x7fffc1cc, 0x7fffc40c); (0x8000bc38, 0x8000bdd0)]%Z.
Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9ee80, 0x9ee88); (0x9fdf0, 0x9fdf8);
(0x7fffc1cc, 0x7fffc40c); (0x8000bc38, 0x8000bdd0)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp).
Definition module_dtor_stmt (PRE : mem -> Prop) : Prop :=
forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
PRE m ->
stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
mem_inv bsegs m ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
evtF bsegs RNG (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x81544) fc None m (seg_rom bsegs)).
Definition afuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5520, 0x5f5521); (0x5f5528, 0x5f552c); (0x5f5530, 0x5f5538)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp).
#[using="Type"] Lemma afuncs_on_exit_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
stk bsegs m lo (bv_unsigned sp) ->
atx_stateA reg m ->
rw_cells bsegs m 0x5f5760 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
mem_inv bsegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
evtF bsegs RNG (afuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x89248) fc None m (seg_rom bsegs)).
Proof.
intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF) LIBC MI LO KH RSTK RIMG.
unfold APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5520, 0x5f5521); (0x5f5528, 0x5f552c); (0x5f5530, 0x5f5538)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
Ltac a_lock := hstep; hstep; hstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); if_true; hstep.
Ltac a_unlock := hstep; (try replace (sx32 z64) with z64 by (vm_compute; reflexivity)); nlit; astep; hstep.
Local Ltac2 Set LiaHints.tbl := fun () => "02V0>10136806254.7510471563706.7613164008890.7613768071406.7613970248890.7614159447534.7514328636398.7515032614711.6515032614711.661586831214.73 16238530166.7516394845038.7516438264558.7416733534830.7417776320417.7517776320428.731800609155.75 18140285936.7618739900433.661931560046.74 2067820398.75 21916162286.7622192655290.7622389541692.7322793452142.7423207695043.6623570233326.7323742962798.7424282274821.6724638473347.7524638473347.7727911298325.6628417259964.7529950340078.7530958998586.7730958998586.8131068521070.7431378308326.6631423754298.7731423754298.8131662557237.7731662557237.8132531853370.7732531853370.8132595612014.7532638908656.7632877577146.7633510318702.7433680001082.7634170545134.7534202051574.7234430152252.7634454534638.7334773204922.7635002504378.7635012330478.7536115622432.7636115622447.7437364793838.7337514381363.6637815856058.763852219578.76 39208223342.7439482238446.7540235527098.7640457739452.7440463905978.7640531229166.7340583097326.7540584289006.764068500334.75 41023668493.7641589340654.7342426800622.734262819002.76 43040747578.7743040747578.8143059266230.6443175993206.7543941322990.7643987951392.7643987951406.7543988483203.7343988483203.754454318318.76 44588913006.7344804625134.7645221239098.7545572931770.7645745840622.7345848756903.7346058767598.7446396466030.7546468661564.7546891393006.7547262450798.7648165869806.764829287792.77 4829287792.81 48680735162.7649557673146.7649649769127.7651459583162.7651711223320.6551890444685.7751890444685.8152105090727.7552567164907.7352567164907.7452567164907.7552567164907.7652567164907.7752567164907.8152970898030.7453767577774.7453767577775.7454243526019.7454243526019.7654394415470.7554893195322.7754893195322.8155201985594.7755201985594.8155881596341.76563227834.74  57745675194.755808028474.77 5808028474.81 59176389614.7559714667374.7560277514421.766062692974.74 60858483367.756134792378.76 61471961921.6662044555194.7662138158710.7362577245174.7262751043597.7662891835758.7563046200890.7763046200890.8163235321900.7263235321902.7463305555623.7463692445114.7663894255854.7664101751662.7564318125073.6664710317242.7664997134979.7664997134979.7766161370682.7766161370682.8166766799342.7367105489134.766736605166.73 68030567414.7468205640558.7568644094966.728163491438.76 8246623034.77 8246623034.81 8264524782.75 8583720762.73 9939242478.75 00000800900:00B00C00K00S00T00U00]00^00f00n01601:01>01?01@01A01I01Q01Y01Z01^01f01g01o02702802902:02>02B02J02K02L02T02U02V02W02_02g02h02i03103203303;03@03H03I03M03U03V03W03_03c03g03o04004104204:04B04C04G04H04P04X04`04h04i05105905:05;05<05@05A05I05M05Q05R05S05[05c05k06006106906:06B06J06N06V06^06f06g06h06i06j06k06l06m06n06o07007107207307407507607>07B07F07G07H07P07Q07R07S07T07\07a07f07g07h08008808@08H08I08J08K08L08M08N08O08W08X08Y08]08a08b08c08k09309409509609709809909A09I09Q09R09Z09[09c09d09e09m0:20::S2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'FFS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LOS2LOSSSS2LO3KH'S2LO3KH'S2LO3KH'SS2HBS2LO3KH'FS2LO3KH'S2LO3KH'FSSS2LOS2HBS2LO3KH'SSS2LO3KH'SSSS2LO3KH'S2LO3KH'SSS2LO3KH'SSS2LO3KH'S3RSPS2LO3KH'SS2HBS2LO3KH'SSS2LO3KH'S2LOS2LOS2LO3KH'FSSS2LO3KH'S2LO3KH'SS2HBSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SSSS2LOSS2LO3KH'S2LOS2LOSSS2LO3KH'S2LO3KH'S2LO3KH'S3RSPSS2LO3KH'SS2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'SSSSSSSSSSSSSSSSS2LO3KH'S2LOS2LOSSS2LO3KH'SSSSS2LO3KH'S3RSPS3RSPSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSSSSSSS2LO3KH'SSS2LOS2LOSSS2LO3KH'S2LO3KH'SSSSSSS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'SSS2LO3KH'S3RSPS2LO3KH'".
carve_frame 48%nat ST.
steps_to 0x93510%Z. a_lock.
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
steps_to 0x89308%Z.
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
steps_to 0x89308%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
a_unlock.
unfold afuncs_on_exit_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
[(sp - 48 - MDTOR_DEPTH, sp); (0x5f5740, 0x5f5744); (0x5f5520, 0x5f5521); (0x5f5528, 0x5f552c); (0x5f5530, 0x5f5538); (0x9eed0, 0x9eed1)]%Z.
Definition AEXIT_W (sp : Z) : list (Z * Z) := AEXIT_W1 sp ++ MDTOR_W.
Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x89498) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ef1c) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (0x5f5740, 0x5f5744); (0x5f5520, 0x5f5521); (0x5f5528, 0x5f552c);
(0x5f5530, 0x5f5538); (0x9eed0, 0x9eed1);
(0x9ee80, 0x9ee88); (0x9fdf0, 0x9fdf8); (0x7fffc1cc, 0x7fffc40c); (0x8000bc38, 0x8000bdd0)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -16)
/\ rw_cells bsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ rw_cells bsegs m' 0x5d5428 [C4 (Z_to_bv 64 t)]
/\ rw_cells bsegs m' 0x5f5740 [C4 (Z_to_bv 64 t)]
/\ rw_cells bsegs m' 0x9eed0 [C1 (Z_to_bv 8 1)].
Section Prefix.
Variable PRE : mem -> Prop.
Hypothesis MDTOR : module_dtor_stmt PRE.
Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> PRE m'.
#[using="MDTOR PRE_frame"] Lemma aexit_prefix_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso : word),
PRE m ->
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x5d5428 [C4 (Z_to_bv 64 t)] ->
rw_cells bsegs m 0x5f5740 [C4 z64] ->
rw_cells bsegs m 0x5f5760 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_stateA reg m ->
rw_cells bsegs m 0x9a5d0 [C8 (Z_to_bv 64 0x993a8); C8 (Z_to_bv 64 0x99398)] ->
rw_cells bsegs m 0x99398 [C8 (Z_to_bv 64 0x81544); C8 (Z_to_bv 64 0x31200)] ->
rw_cells bsegs m 0x9eed0 [C1 (Z_to_bv 8 0)] ->
rw_cells bsegs m 0x998e0 [C8 (Z_to_bv 64 0x89310); C8 z64] ->
rw_cells bsegs m 0x9b610 [C8 dso] ->
mem_inv bsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
evtF bsegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8942c) fc None m (seg_rom bsegs)).
Proof.
intros until dso. intros HPRE ST TID EXL LIBC AX GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
destruct AX as ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF). unfold APAEF_INCB, ACOV_FLAG, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. pose proof KH as KHI. unfold KHIGH in KH.
pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
pose proof (wmono_refl bsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "03O0?10047693422.97 11187370938.82 11352265753.97 11658450183.94 12018219118.97 1299361973.82  1343986644.113 1343986644.94  1355623354.82  13665692054.90 1415401029.90  14159447534.87 14328636398.87 14552611770.82 14793086774.94 15865176174.97 17776320430.11417776320430.96 18039553618.90 18039553618.99 18497754962.90 18589389294.87 18589389294.97 18589389294.98 19049469500.97 19174530798.95 19251685870.87 19251685870.97 19251685870.98 19317809487.11319317809487.94 19552102719.10619916546158.97 19942487194.90 20433961190.80 20609531986.90 2067820398.87  21916162286.95 22029590458.82 24125903290.82 24638473347.11624638473347.98 25314760359.97 25358937786.10325449023214.95 25878270252.96 27431799738.82 27716857426.90 27716857426.99 27911298325.10627922131438.87 27922131438.97 27922131438.98 27923971379.99 27971003322.82 28754851922.90 29545175216.99 29950340078.87 31423336146.90 32600174396.87 32735658066.90 32735658066.99 3281461173.103 32931238842.82 3362501458.90  33680001082.95 34170545134.87 34430152252.95 3454168506.82  35012330478.87 35012330478.97 35012330478.98 3525607222.75  35730135792.82 36115622433.11536115622433.97 36351020662.96 36438299669.90 36551235151.11336551235151.94 36630883559.81 36641385327.82 36944450135.81 37258164461.81 37823627923.88 37856381709.82 38072106319.11338072106319.94 38508687005.99 39093924078.95 39208223342.97 39521875765.71 40201484047.90 40457739452.97 40583097326.87 41502848698.10341834437230.97 42273372099.89 42709615183.11342709615183.94 42732709998.97 42831019478.90 42831019478.99 43059266230.78 43104399792.90 43124198553.95 43493603410.90 43493603410.99 43609253714.90 43667128060.10543987951404.11243987951404.94 43991364538.82 45221239098.87 45221239098.97 45221239098.98 45455842800.10346468661564.98 46732000693.10347647952826.82 47762024973.10348316456345.97 48429240188.89 4866047897.97  4866047897.98  48781039854.95 49245040366.95 49649769127.95 49896851182.95 50012503994.82 50286274741.10351138747382.97 51274276282.82 51384740047.11351384740047.94 51425718543.99 51468150458.10351481786499.97 51678667182.98 52198366190.87 52198366190.97 52198366190.98 52565071546.10352567164907.10352567164907.82 52567164907.87 52567164907.90 52567164907.95 52567164907.97 52567164907.98 52567164907.99 52579502455.11352579502455.94 53431880694.96 53767577774.89 54164510851.87 54243526019.11554243526019.97 54404701703.11354471188922.82 56020217919.88 56170333721.90 56172233139.71 56276506042.82 563227834.97   56795746746.82 56885027538.90 57240568302.87 57240568302.97 57240568302.98 58148456595.86 582374735.113  582374735.94   5853766638.87  5853766638.97  5853766638.98  59028845166.97 59176389614.87 59314923118.82 59368190966.95 59377953174.10959922101071.11359922101071.94 60280114806.11160679622738.90 60679622738.99 60858483367.98 61445037647.11361445037647.94 61479303406.95 61581656914.90 61581656914.99 61874979822.87 61874979822.97 61874979822.98 61892124754.90 61892124754.99 62583080755.90 62891835758.87 63235321900.86 63305555623.97 63779719325.99 64997134979.11364997134979.95 66017866578.90 66307532356.90 66364210874.10367081926311.87 67923310760.10668303855698.90 7260242362.82  7488583.88     8006446778.103 8090913178.87  8264524782.87  8510236346.103 861906514.90   861906514.99   8726975058.90  8800126135.114 8800126135.92  8800126135.95  9939242478.87  00000700800900:00A00H00I00J00K00L00M00T00[00\00i01001401801?01F01M01T01[01b01f01m02402;02B02M02X02Y02`02a02b02i03003703803903:03;03<03=03D03H03I03P03W03[03b03i04004104204904=04D04K04O04V04]04d04e04l05105805<05=05D05K05R05_05`05d05h05i05m06806C06G06K06O06P06T06U06`06k06l07307:07>07?07C07J07K07R07Y07d07o08608;08@08D08H08I08P08W08^08_08c08g08h08m09209709809<09C09D09E09F09G09H09I09P09W09X09_09`09g09h09i0:40:?0:@0:A0:B0:F0:M0:T0:[0:\0:]0:^0:_0:`0:a0:b0:c0:d0:o0;:0;;0;?0;@0;A0;B0;C0;D0;E0;F0;G0;H0;M0;N0;U0;\0;c0;j0;n0<90<D0<K0<R0<Y0<`0<g0<m0<n0<o0=:0=E0=F0=M0=T0=U0=`0=k0>20>90>@0>G0>N0>U0>\0>c0>d0>k0>o0?00?10?20?30?:0?;0?<0?=0?>0?E0?F0?G0?H0?I0?P0?Q0?X0?_0?f0@30@60@C0@JS2LO2KHSSFS2LO2KHS2LO2KHFFSSFS2LO2KHS2LO2KHSS2LO2KH3RSP1HS2LO2KHS2LOS2LOS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2HBS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspFS2LO2KHFSS2LO2KHS2LO2KHS2LO2KHSSSSSSS2LO2KHS2LOSS2LO2KHS2LO2KHS2LOS2LO2KHS2LO2KHS2LO2KHSSS2LO2KHS2HBS2LO2KHS2LO2KHS2HBS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS3RSPS2LO2KHS2HBSS2LO2KHS2LO2KHS2LO2KHS2LO2KH3RSP1HSS2LOS2LOSS2LOS2LO2KH3HspS2LO2KH3HspS2HtS2HtS2HtFS2LOSS2LO2KH3HspS2LO2KH3HspSS2LO2KHS2LO2KHS2LOSS2HBS2LO2KHSS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspS2LO2KHS3RSPS3RSPS2LOS2HBSS2LO2KHS2LO2KHS2LO2KHSS2LOS2LOSS3RSPS3RSPS3RSPSS2HBS2LO2KHSSSSSSS2LO2KHS2LO2KHSS2LO2KHSS2LO2KHSSS2LO2KH3HspS2LO2KH3HspSSSS2LOS2LO2KHS2LO2KHS2LO2KHSSSSSSSSSS2LO2KH3HspS2LO2KH3HspSS2LOSSSFSFSSSS3RSPSS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LOS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2Ht1KSSS2LO2KH3HspS2LO2KH3HspSS2LO2KHS2LO2KHSS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2LOSSSSS2LO2KHSSSFS2LO2KHSSSFS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LO2KH3Hsp1HS1HS2LO2KH3Hsp1HS2LO2KH".
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
steps_to 0x31200%Z.
carve_frame 16%nat ST.
hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
steps_to 0x89310%Z. hstep.
steps_to 0x3128c%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
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
Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> PRE m'.
Hypothesis stdio_exit_spec : stdio_exit_spec_stmt2 get_so set_so.
#[using="MDTOR PRE_frame stdio_exit_spec"] Lemma aexit_spec : forall (reg : bool) RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
PRE m ->
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x5d5428 [C4 (Z_to_bv 64 t)] ->
rw_cells bsegs m 0x5f5740 [C4 z64] ->
rw_cells bsegs m 0x5f5760 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_stateA reg m ->
rw_cells bsegs m 0x9a5d0 [C8 (Z_to_bv 64 0x993a8); C8 (Z_to_bv 64 0x99398)] ->
rw_cells bsegs m 0x99398 [C8 (Z_to_bv 64 0x81544); C8 (Z_to_bv 64 0x31200)] ->
rw_cells bsegs m 0x9eed0 [C1 (Z_to_bv 8 0)] ->
rw_cells bsegs m 0x998e0 [C8 (Z_to_bv 64 0x89310); C8 z64] ->
rw_cells bsegs m 0x9b610 [C8 dso] ->
rw_cells bsegs m 0x5f5bc8 [C8 z64] -> rw_cells bsegs m 0x9e190 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells bsegs m RSTDIN stdin_cells ->
rw_cells bsegs m 0x9e0a0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells bsegs m 0x9dfb0 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->
mem_inv bsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
(bv_unsigned sp < 2^47)%Z ->
implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8942c) fc None m (seg_rom bsegs)).
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
ms' = MS (mkR (Z_to_bv 64 0x89498) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x89498) fc None m' (seg_rom bsegs) /\ mem_inv bsegs m')).
-
change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
apply implAM_from_evt.
Local Ltac2 Set LiaHints.tbl := fun () => "".
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
replace (ret_pc (Z_to_bv 64 0x89498)) with (Z_to_bv 64 0x89498) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
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
