(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Export AF_atexit.      (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition RSTDIN : Z := 0x9d5f0.
Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x8dd14); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0x8dd40); C8 z64; C8 (Z_to_bv 64 0x8de58); C8 (Z_to_bv 64 0x5f4928); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].

(* [comment removed for export] *)
Section StdioExitStatement2.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Definition stdio_exit_spec_stmt2 : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk asegs m lo (bv_unsigned sp) ->
      rw_cells asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells asegs m 0x5f4508 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells asegs m 0x9d6d8 [C8 (Z_to_bv 64 RSTDIN)] ->                           (* [comment removed for export] *)
      rw_cells asegs m RSTDIN stdin_cells ->                                           (* [comment removed for export] *)
      rw_cells asegs m 0x9d5e8 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells asegs m 0x9d4f8 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->   (* [comment removed for export] *)
      mem_inv asegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
      (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
      implAM RNG (stdout_exit_flush get_so set_so) s
            (stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x8e440) fc None m (seg_rom asegs)).
End StdioExitStatement2.

(* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma a_Exit_specM : forall {St : Type} RNG (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 code ->
  implAM RNG (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x88720) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI ->.
  apply implAM_sys; [exact I|]. do 2 zstep. step_ecall.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>10780409500.4013661623673.40000001002FF".
split; [ at_nodeA_solve | intros rsp a H; cbn in H; discriminate H ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MDTOR_DEPTH : Z := 1024.
(* [comment removed for export] *)
Definition MDTOR_W : list (Z * Z) :=
  [(0x9d7c0, 0x9d7c8); (0x9e730, 0x9e738); (0x7fffc1a8, 0x7fffc1b8); (0x8000bae2, 0x8000baf2)]%Z.

Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9d7c0, 0x9d7c8); (0x9e730, 0x9e738);
              (0x7fffc1a8, 0x7fffc1b8); (0x8000bae2, 0x8000baf2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition module_dtor_stmt (PRE : mem -> Prop) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
    mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF asegs RNG (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81d78) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f3e60, 0x5f3e61); (0x5f3e68, 0x5f3e6c); (0x5f3e70, 0x5f3e78)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma afuncs_on_exit_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  atx_stateA reg m ->
  rw_cells asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->    (* [comment removed for export] *)
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF asegs RNG (afuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8876c) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF) LIBC MI LO KH RSTK RIMG.
  unfold APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG in *. pose proof KH as KH'. unfold KHIGH in KH'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f3e60, 0x5f3e61); (0x5f3e68, 0x5f3e6c); (0x5f3e70, 0x5f3e78)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
  Ltac a_lock := hstep; hstep; hstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); if_true; hstep.
  Ltac a_unlock := hstep; (try replace (sx32 z64) with z64 by (vm_compute; reflexivity)); nlit; astep; hstep.
  Local Ltac2 Set LiaHints.tbl := fun () => "02V0>11361371254.7211875767022.7612578924813.7613761980858.7613945626606.7514118943342.7414521171130.7615002254522.7615025058286.7315032614711.6515032614711.6615442153454.7316834310006.7517776320417.7517776320428.731800609155.75 18645511354.7618739900433.6619622476014.7620578639034.7621459134830.7522389541692.7322856607214.7522994020538.7623207695043.6623433232781.7723433232781.8123847006446.7624638473347.7524638473347.7725792608750.7327133822446.7527301385206.7327778003822.7527867550830.7627911298325.6628417259964.7528568521786.7728568521786.8129531591534.7529870281326.7429874910138.762993314286.73 30401015406.7630543425082.7730543425082.8130970512821.7631114877370.7631233491310.7331378308326.6631856720366.7332194692666.7732194692666.8132440122478.7432716547054.7532720823226.7632795189110.7232804079546.7633680001082.7633781268846.7534110508400.7734110508400.8134293717005.7634430152252.7635364219061.7635811162350.7635930198638.7436115622432.7636115622447.7436654913774.7636936768494.7537514381363.6638567244270.7338782755822.7538848536430.7539093924078.7640457739452.7440871484270.7541540547438.7541834437230.7443000880110.7543059266230.644365912122.77 4365912122.81 43987951392.7643987951406.7543988483203.7343988483203.7544466451258.7744466451258.8144762256494.7445221239098.7545848756903.7346468661564.7546865726906.7647429895152.7647749021114.7648909296622.7549649769127.7649750950894.755087518190.75 50885881018.7651340875834.7751340875834.8151711223320.6552083213430.7552105090727.7552198366190.7552567164907.7352567164907.7452567164907.7552567164907.7652567164907.7752567164907.8152780046574.7653767577774.7453767577775.7454038547642.7654243526019.7454243526019.7654755617850.7754755617850.81563227834.74  56327961070.7357000382702.7657045163194.7657745675194.7558057019758.7558068748346.7758068748346.8158264183534.7459400225594.7759400225594.8159691043770.7660281899194.7660797519086.7460858483367.7561012565946.7661439603310.7461471961921.6661932712176.7661975105398.7461983425722.766253858422.72 62682870638.7562826138350.7663235321900.7263235321902.7463305555623.7464318125073.666491058798.74 64997134979.7664997134979.7765427817477.6765458892654.7365941320634.7666400913390.736747295797.77 6747295797.81 68107765818.7768107765818.817720336238.75 8054831726.74 8172837742.75 8583720762.73 8967238126.73 00000100900:00;00C00K00L00M00U00V00W00_00`00d00h00i00j00k01301401<01@01H01I01J01K01L01T01U01V01^01f01g01o02702;02?02@02A02I02Q02R02Z02b02c02d02l02m03503603>03?03@03H03P03Q03R03S03X03`03a03b03c03g03o04704?04C04G04O04W04X04`04h05005805<05D05L05T05\05`05a05b05f05j05k05l05m05n06606;06<06@06A06B06C06K06L06T06\06]06^06_06`06a06b06j06k06l06m06n06o07007807<07@07A07B07C07D07E07J07R07Z07[07`07h07i07j08208308408508608>08?08@08H08I08J08K08L08M08U08]08a08e08f08g08o09009109209:09;09C09K09S09T09U09]09e09m0:20::SS2LO3KH'SSS2LO3KH'S2LO3KH'SSS2LO3KH'FFS2LO3KH'SS2LOS2LOSSSS2LO3KH'SS2LO3KH'S2HBS2LO3KH'SFSSS2LO3KH'SSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LOS2HBSSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'SS2LO3KH'SSS2LO3KH'S2LO3KH'SSSS3RSPS2LO3KH'SSSS2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LOS2LOS2LO3KH'S2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LOSSS2LOS2LOSSSSS2LO3KH'S3RSPSS2HBSSSS2LO3KH'SS2LO3KH'S2LO3KH'SSSSSSS2LO3KH'SSSSSSS2LO3KH'S2LOS2LOSSSSSS3RSPS2LO3KH'S2LO3KH'SS3RSPS2LO3KH'SSS2LO3KH'SSSSS2LO3KH'SSS2LO3KH'SSSSSS2LO3KH'S2LO3KH'S2LOS2LOSSS2LO3KH'SSFS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S3RSPS2LO3KH'".
carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x92a34%Z. a_lock.
  (* [comment removed for export] *)
  astep. astep.
  destruct reg; cbn [negb andb orb] in *.
  - (* [comment removed for export] *)
    hstep. nlit. hstep. hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    a_unlock.
    (* [comment removed for export] *)
    hstep. hstep. hstep.
    hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
    (* [comment removed for export] *)
    hstep. hstep. a_lock.
    hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    a_unlock.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    hstep. hstep. a_lock.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    steps_to 0x8882c%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep.
    a_unlock.
    unfold afuncs_on_exit_post. sys_finish.
  - (* [comment removed for export] *)
    hstep. nlit. hstep. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    a_unlock.
    hstep. hstep. hstep.
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. hstep. a_lock.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    steps_to 0x8882c%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep.
    a_unlock.
    unfold afuncs_on_exit_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
  [(sp - 48 - MDTOR_DEPTH, sp); (0x5f4080, 0x5f4084); (0x5f3e60, 0x5f3e61); (0x5f3e68, 0x5f3e6c); (0x5f3e70, 0x5f3e78); (0x9d810, 0x9d811)]%Z.
Definition AEXIT_W (sp : Z) : list (Z * Z) := AEXIT_W1 sp ++ MDTOR_W.

(* [comment removed for export] *)
Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x889bc) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8e440) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (0x5f4080, 0x5f4084); (0x5f3e60, 0x5f3e61); (0x5f3e68, 0x5f3e6c);
              (0x5f3e70, 0x5f3e78); (0x9d810, 0x9d811);
              (0x9d7c0, 0x9d7c8); (0x9e730, 0x9e738); (0x7fffc1a8, 0x7fffc1b8); (0x8000bae2, 0x8000baf2)]%Z m m'
                                                                  (* [comment removed for export] *)
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x5d3d68 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m' 0x5f4080 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m' 0x9d810 [C1 (Z_to_bv 8 1)].

Section Prefix.
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  (* [comment removed for export] *)
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.

  #[using="MDTOR PRE_frame"] Lemma aexit_prefix_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso : word),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x5d3d68 [C4 (Z_to_bv 64 t)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x5f4080 [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
    atx_stateA reg m ->                                                               (* [comment removed for export] *)
    rw_cells asegs m 0x99b18 [C8 (Z_to_bv 64 0x988d0); C8 (Z_to_bv 64 0x988c0)] -> (* [comment removed for export] *)
    rw_cells asegs m 0x988c0 [C8 (Z_to_bv 64 0x81d78); C8 (Z_to_bv 64 0x300a4)] ->  (* [comment removed for export] *)
    rw_cells asegs m 0x9d810 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x98e08 [C8 (Z_to_bv 64 0x88834); C8 z64] ->                   (* [comment removed for export] *)
    rw_cells asegs m 0x9ab58 [C8 dso] ->                                             (* [comment removed for export] *)
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF asegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x88950) fc None m (seg_rom asegs)).
  Proof.
    intros until dso. intros HPRE ST TID EXL LIBC AX GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
    (* [comment removed for export] *)
    destruct AX as ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF). unfold APAEF_INCB, ACOV_FLAG, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. pose proof KH as KHI. unfold KHIGH in KH.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl asegs m) as WM.
    Local Ltac2 Set LiaHints.tbl := fun () => "03O0?11352265753.97 11658450183.94 12018219118.97 13088407226.1031343986644.113 1343986644.94  14201864274.90 14201864274.99 14290588398.95 14793086774.94 15442756538.82 17094381263.11317094381263.94 17424134738.90 17737863790.97 17776320430.11417776320430.96 17794849359.11317794849359.94 18039553618.90 18039553618.99 18516799094.96 19049469500.97 19251685870.87 19251685870.97 19251685870.98 19308892685.10319544954352.1031980106478.95  19912767669.82 19942487194.90 19953839802.1032004949074.90  2004949074.99  20433961190.80 21750412114.90 21816722869.10322263194970.87 22288337850.82 22712646074.82 22856607214.87 23955338831.11323955338831.94 2395583510.109 2405740150.95  24638473347.11624638473347.98 24938556479.88 25271559662.87 25271559662.97 25271559662.98 25301904978.90 25301904978.99 25314760359.97 25375207605.10325878270252.96 25941858234.82 26472748474.82 2658730222.95  26631534418.90 26631534418.99 27134262970.10327810329426.90 27911298325.10627923971379.99 27992010170.82 28042496442.82 28478010358.11128948218862.87 28948218862.97 28948218862.98 29009273786.82 29545175216.99 29854969274.82 30301260421.90 31521058898.90 31768715240.10632570464186.82 32600174396.87 32638227566.97 32716547054.87 33680001082.95 33940205650.90 33940205650.99 34430152252.95 34783684282.1033525607222.75  35671420790.97 36115622433.11536115622433.97 36438299669.90 36630883559.81 36641385327.82 36654913774.95 36769380282.82 36936768494.87 36944450135.81 37258164461.81 37587267666.90 37789560506.10337823627923.88 38508687005.99 38761854802.90 38782755822.87 38848536430.87 39521875765.71 40054548974.87 40054548974.97 40054548974.98 40201484047.90 40321951854.97 40457739452.97 40737376082.90 41291922255.11341291922255.94 42273372099.89 42831019478.90 42831019478.99 43000880110.87 43059266230.78 43091392750.95 43104399792.90 43124198553.95 43493603410.90 43667128060.10543913974254.87 43913974254.97 43913974254.98 43987951404.11243987951404.94 4516797370.82  45221239098.87 45221239098.97 45221239098.98 4607114938.103 46162087634.90 46468661564.98 47085660085.10347472103150.95 48316456345.97 48429240188.89 48538816594.90 48538816594.99 4866047897.97  4866047897.98  48909296622.87 49649769127.95 49750950894.87 49750950894.97 49750950894.98 49896851182.95 50667478351.11350667478351.94 5087518190.87  51425718543.99 51481786499.97 51678667182.98 52198366190.87 52567164907.10352567164907.82 52567164907.87 52567164907.90 52567164907.95 52567164907.97 52567164907.98 52567164907.99 52579502455.11352579502455.94 5289036218.82  53763180367.11353763180367.94 53767577774.89 54078018550.96 54164510851.87 54243526019.11554243526019.97 54404701703.11354532700782.97 56170333721.90 56172233139.71 56185332718.87 56185332718.97 56185332718.98 563227834.97   57378835438.87 57378835438.97 57378835438.98 57486588142.95 58057019758.87 58148456595.86 58205633466.82 59314923118.82 59547203903.1066054978158.97  60695562682.82 60858483367.98 61439603310.97 61445037647.11361445037647.94 62368248589.82 62583080755.90 62623540922.10362785554362.82 63235321900.86 63299176018.90 63299176018.99 63305555623.97 63779719325.99 64583586514.90 64778507194.82 64997134979.11364997134979.95 65023939312.82 66307532356.90 67081926311.87 6863291727.113 6863291727.94  7488583.88     8393561110.90  8800126135.114 8800126135.92  8800126135.95  9595551854.97  00000100200900:00;00<00C00J00Q00^00_00j01501<01C01G01K01V01a01h01o02002402;02B02I02J02K02R02Y02Z02[02b02i02j03103803903:03;03B03M03X03Y03Z03[03\03]03d03k04204904@04A04H04L04M04N04U04\04c04d04k04o05005105205305:05A05H05I05M05N05O05V05W05X05\05c05j05o06606=06A06B06O06P06T06X06\06`06d06k06l07307707807?07@07D07E07L07S07Z07^07e07l08308408;08?08F08Q08\08c08h08m09409809?09C09D09K09L09S09Z09a09e09i09j09o0:40:90::0:A0:E0:L0:S0:T0:U0:\0:c0:d0:e0:l0:m0;40;;0;B0;I0;T0;_0;f0;g0;h0;l0<30<40<50<60<70<80<90<:0<;0<F0<Q0<R0<]0<h0<l0<m0<n0<o0=00=10=80=90=:0=A0=H0=O0=T0=[0=b0=i0>00>70>;0><0>B0>C0>J0>K0>L0>S0>^0>i0>j0>k0>l0>m0?10?80??0?@0?A0?H0?I0?J0?K0?L0?M0?N0?Y0?d0?e0?f0@30@60@C0@JSFS2LO2KHSFFS2LO2KHS2LO2KHS2LO2KHS2LO2KH3RSP1HSS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHS2LOS2LOS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KHSS2HBS2LO2KHS2LO2KHS2LO2KHSSS2LO2KHS2LO2KHFSS2LO2KHS2LO2KHSS2LO2KHS2LO2KHFSSS2LO2KHS2LO2KH3HspS2LO2KH3HspSSSSFS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2LOSSS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2LOSSSSS2LO2KHS2LO2KHS2LO2KHSS2HBSFS2LO2KHFSS2HBS2LO2KHS2LO2KHS3RSPS2LO2KHS2LO2KHS2HBSS2LO2KH3RSP1HSS2LOS2LOS2LOS2HtS2HtS2LO2KHSS2LO2KHS2HtFS2LO2KHSS2LOSS2LO2KHS2LO2KHS2LO2KHS2LOS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2HBS2LO2KHS2LO2KH3HspS2LO2KH3HspS2LO2KHS3RSPS3RSPS2LO2KHS2LOS2LO2KHS2HBSS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LOS2LOSS3RSPS3RSPS3RSPSS2LO2KHS2HBS2LO2KHS2LO2KHSSS2LO2KHS2LO2KHSSS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KH3HspS2LO2KH3HspS2LO2KHSSS2LOS2LO2KHSSSSSSSSS2LO2KH3HspS2LO2KH3HspSS2LO2KH3HspS2LO2KH3HspS2LOSSSSFS2LO2KHSSS2LO2KHS2LO2KHS2LO2KHS3RSPS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LOSS2Ht1KFS2LO2KHSSS2LO2KHS2LO2KH3HspS2LO2KH3HspSSSSS2LOS2LO2KHS2LO2KHSSS2LO2KHSSSSSSS2LO2KH3HspS2LO2KH3HspSSS2LO2KH3Hsp1HS1HS2LO2KH3Hsp1HS2LO2KH".
carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    (* [comment removed for export] *)
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    astep. sort_lits. amo_step. astep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. astep.
    hstep. hstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AX : atx_stateA reg mx) by (exact (conj (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 X9)))))))) (conj CB CF))) end.
    clear X1 X2 X3 X4 X5 X6 X7 X8 X9 CB CF.
    call_sp (afuncs_on_exit_spec reg RNG);
      try (first [ exact AX | hyp_by_addr | exact KHI | exact RIMG | (eapply rng_sub'; [exact RSTK | lia]) | lia ]).
    clear AX. match goal with S : stk _ _ lo _ |- _ => rename S into ST end.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x300a4%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0x88834%Z. hstep.
    steps_to 0x30130%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep.
    match goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH, KHIGH; lia) MU WM) as HPRE1;
      assert (MU2 : munch (AEXIT_W (bv_unsigned sp)) m mc)
        by (eapply munch_weaken; [| exact MU]; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH, sub_fp; cbn [outside app]; intros; lia);
      clear MU; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH in MU2; cbn [app] in MU2
    end.
    call_sp (MDTOR RNG); try first [ exact HPRE1 | eassumption | unfold MDTOR_DEPTH; lia | unfold KHIGH; lia | exact RW ].
    1:{ eapply rng_sub'; [exact RSTK | lia]. }
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep. hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
    hstep. hstep.
    hstep.
    unfold aexit_prefix_post. sys_finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Prefix.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt2 get_so set_so.     (* [comment removed for export] *)

  #[using="MDTOR PRE_frame stdio_exit_spec"] Lemma aexit_spec : forall (reg : bool) RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x5d3d68 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x5f4080 [C4 z64] ->
    rw_cells asegs m 0x5f40a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    atx_stateA reg m ->
    rw_cells asegs m 0x99b18 [C8 (Z_to_bv 64 0x988d0); C8 (Z_to_bv 64 0x988c0)] ->
    rw_cells asegs m 0x988c0 [C8 (Z_to_bv 64 0x81d78); C8 (Z_to_bv 64 0x300a4)] ->
    rw_cells asegs m 0x9d810 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x98e08 [C8 (Z_to_bv 64 0x88834); C8 z64] ->
    rw_cells asegs m 0x9ab58 [C8 dso] ->
    (* [comment removed for export] *)
    rw_cells asegs m 0x5f4508 [C8 z64] -> rw_cells asegs m 0x9d6d8 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
    rw_cells asegs m 0x9d5e8 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x9d4f8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x88950) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros HPRE ST TID EXL LIBC AX GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF GG GU MI -> -> Ht LO KH RSTK RIMG RW RG0 SP47.
    pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1. unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    unfold Driver.exit_model.
    eapply (implAM_bind RNG _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x889bc) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x889bc) fc None m' (seg_rom asegs) /\ mem_inv asegs m')).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      apply implAM_from_evt.
      Local Ltac2 Set LiaHints.tbl := fun () => "00N0?10429640106.11712319647183.1181343986644.116 17094381263.11717794849359.11721014659151.11821510966599.1162168467805.117 23955338831.11825218221843.13928751370288.11732617356379.1163525607222.120 35850771151.11838072106319.11841031678929.11741291922255.11742148696048.11744386577743.11848990548559.11850667478351.11753763180367.11855989238223.11856172531244.11759221632975.11861445037647.11865196339153.11867759509071.1186863291727.116 6863291727.118 00000400<00=00E00M00U00V00\00d00e00f00g01601>01F01N01O01T01\01d01l02402<02=02E02F02N02V02^02fS2LOS2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'FS4SP47S2LO3KH'SFFS2LO4SP473KH'1HS2LO3KH'S2LO3KH'S2LO3KH'FS3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'".
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
               replace (ret_pc (Z_to_bv 64 0x889bc)) with (Z_to_bv 64 0x889bc) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               do 30 eexists; split; [cbv delta [mkR]; reflexivity | destruct PO as (_ & _ & MIq & _); exact MIq]
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- rng _ _ _ => unname_sp; first [ eapply rng_sub'; [exact RSTK | lia] | exact RIMG ]
           | |- rng0 _ => exact RG0
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia | assumption ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. destruct PO as [-> MI']. 
      apply implAM_from_evt. zstep. zstep. apply evtF_done.
      apply a_Exit_specM; [exact MI' | reflexivity].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ExitProof.
End CANSEC2.
