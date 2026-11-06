(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Export AF_atexit.      (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition RSTDIN : Z := 0x9d7c8.
Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x8def0); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0x8df1c); C8 z64; C8 (Z_to_bv 64 0x8e034); C8 (Z_to_bv 64 0x5f4ae8); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].

(* [comment removed for export] *)
Section StdioExitStatement2.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Definition stdio_exit_spec_stmt2 : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk bsegs m lo (bv_unsigned sp) ->
      rw_cells bsegs m 0x5f4260 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells bsegs m 0x5f46c8 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells bsegs m 0x9d8b0 [C8 (Z_to_bv 64 RSTDIN)] ->                           (* [comment removed for export] *)
      rw_cells bsegs m RSTDIN stdin_cells ->                                           (* [comment removed for export] *)
      rw_cells bsegs m 0x9d7c0 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells bsegs m 0x9d6d0 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->   (* [comment removed for export] *)
      mem_inv bsegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
      (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
      implAM RNG (stdout_exit_flush get_so set_so) s
            (stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x8e61c) fc None m (seg_rom bsegs)).
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
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 code ->
  implAM RNG (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x888fc) fc None m (seg_rom bsegs)).
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
  [(0x9d980, 0x9d988); (0x9e8f0, 0x9e8f8); (0x7fffc1a8, 0x7fffc1b8); (0x8000bb1c, 0x8000bb2c)]%Z.

Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9d980, 0x9d988); (0x9e8f0, 0x9e8f8);
              (0x7fffc1a8, 0x7fffc1b8); (0x8000bb1c, 0x8000bb2c)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition module_dtor_stmt (PRE : mem -> Prop) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
    mem_inv bsegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF bsegs RNG (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81f38) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f4020, 0x5f4021); (0x5f4028, 0x5f402c); (0x5f4030, 0x5f4038)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma afuncs_on_exit_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  atx_stateA reg m ->
  rw_cells bsegs m 0x5f4260 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->    (* [comment removed for export] *)
  mem_inv bsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (afuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88948) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF) LIBC MI LO KH RSTK RIMG.
  unfold APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG in *. pose proof KH as KH'. unfold KHIGH in KH'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f4020, 0x5f4021); (0x5f4028, 0x5f402c); (0x5f4030, 0x5f4038)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
  Ltac a_lock := hstep; hstep; hstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); if_true; hstep.
  Ltac a_unlock := hstep; (try replace (sx32 z64) with z64 by (vm_compute; reflexivity)); nlit; astep; hstep.
  Local Ltac2 Set LiaHints.tbl := fun () => "02V0>100583406.73  10600373102.7511382190574.7311716686062.7613651802606.7314290588398.7614993016302.7515032614711.6515032614711.6615398494062.7515552782733.7715552782733.811677124334.74 17399173998.7517440010734.7317737863790.7417776320417.7517776320428.7317962199098.7717962199098.811800609155.75 18276986478.7618366784949.7618739900433.6618831516858.7619250787318.7519715914222.731994914414.74 20148087866.7720148087866.8120313996398.7420625069046.7521659337070.7522133345850.7722133345850.8122389541692.7322758394037.7623207695043.6623778567173.6723806169710.7424638473347.7524638473347.7724766024890.7624812739566.7524955856954.7724955856954.812499852730.76 25271559662.7525358857070.7525836868538.7625862056950.7226086432750.7526423752717.7626561879482.7626961506542.7627361570160.7727361570160.8127911298325.6628232702966.7228417259964.7530876851182.7531378308326.6632638227566.743309735918.73 33680001082.7634430152252.7634466450490.7734466450490.8136115622432.7636115622447.7437514381363.6638230178030.7639999968366.7640059657198.7540457739452.7440647629038.7640680825840.7641130902458.7641317949302.7342377136570.7642930927674.7742930927674.8143059266230.6443091392750.7643299019630.7543374297454.734360033082.77 4360033082.81 43959694190.7543987951392.7643987951406.7543988483203.7343988483203.7544195543534.7344253452910.7445221239098.7545848756903.7346468661564.754692183309.76 47905320122.7648635215034.7648654615790.7448781039854.7649197989050.7649649769127.7650693720814.7651324249070.7551606948026.7651633900730.7651711223320.6552105090727.7552567164907.7352567164907.7452567164907.7552567164907.7652567164907.7752567164907.8152604583866.7653326475118.7353767577774.7453767577775.7453886442938.7654030706746.7754030706746.8154243526019.7454243526019.7655166996720.7656185332718.75563227834.74  57745675194.75578361838.73  58170940602.7658487837626.7659028845166.7459368190966.7259415204078.7660437097402.7660471841134.7560805654074.7760805654074.8160858483367.7561471961921.6661674577390.7561874979822.7562013604854.7462019383790.7362245250030.7562879821877.7762879821877.8162953577658.7663235321900.7263235321902.7463305555623.7464307395438.7564318125073.6664650279534.7464997134979.7664997134979.7765097823086.7566419189946.7667826950970.7767826950970.817240705978.76 8583720762.73 8901816942.74 9333008750.75 00000800@00H00P00X00`00h00i00j01201301401<01D01L01T01X01\01]01^01_01g01o02002102202:02B02C02D02L02M02U02V02W02[02c02d02e02m02n02o03003803903:03;03C03K03L03M03U03V03W03_03`03a03e03f03j04204304;04C04H04L04M04N04R04V04W04_04g04o05305;05<05=05>05?05@05A05E05M05U05]05^05_05g05k05o06006106906A06F06G06K06L06M06N06V06^06_06`06h07007107207307407507607707807907:07;07C07G07K07L07M07N07O07P07Q07Y07^07c07k07l07m08508608>08?08G08H08I08J08K08S08[08\08d08l09409<09=09A09E09F09N09O09W09X09Y09a09b09c09d09e09j0:20::S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'FFS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LOS2LOSSSS2LO3KH'S2LO3KH'SSSS2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'SSS2HBS2LO3KH'FFS2LO3KH'SSSS2LO3KH'SSSS2LO3KH'S2LO3KH'SSS2LO3KH'SSS2LO3KH'SSS2LOSS2HBS2LO3KH'SS2LO3KH'S2LO3KH'S3RSPS2HBSSS2LOS2LOFS2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'SSSSSSS2LOS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LOS2LOSSS2LO3KH'S2LO3KH'S3RSPSS2HBSSSS2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'SSSSSSSSSSSS2LO3KH'S2LOS2LOSSSSSSS2LO3KH'S3RSPS3RSPS2LO3KH'SSS2LO3KH'SS2LO3KH'SS2LO3KH'SSSSS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LOS2LOSS2LO3KH'SS2LO3KH'SSS2LO3KH'SSSSS3RSPS2LO3KH'S2LO3KH'".
carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x92c10%Z. a_lock.
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
    steps_to 0x88a08%Z.
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
    steps_to 0x88a08%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep.
    a_unlock.
    unfold afuncs_on_exit_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
  [(sp - 48 - MDTOR_DEPTH, sp); (0x5f4240, 0x5f4244); (0x5f4020, 0x5f4021); (0x5f4028, 0x5f402c); (0x5f4030, 0x5f4038); (0x9d9d0, 0x9d9d1)]%Z.
Definition AEXIT_W (sp : Z) : list (Z * Z) := AEXIT_W1 sp ++ MDTOR_W.

(* [comment removed for export] *)
Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x88b98) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8e61c) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (0x5f4240, 0x5f4244); (0x5f4020, 0x5f4021); (0x5f4028, 0x5f402c);
              (0x5f4030, 0x5f4038); (0x9d9d0, 0x9d9d1);
              (0x9d980, 0x9d988); (0x9e8f0, 0x9e8f8); (0x7fffc1a8, 0x7fffc1b8); (0x8000bb1c, 0x8000bb2c)]%Z m m'
                                                                  (* [comment removed for export] *)
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells bsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells bsegs m' 0x5d3f28 [C4 (Z_to_bv 64 t)]
    /\ rw_cells bsegs m' 0x5f4240 [C4 (Z_to_bv 64 t)]
    /\ rw_cells bsegs m' 0x9d9d0 [C1 (Z_to_bv 8 1)].

Section Prefix.
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  (* [comment removed for export] *)
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> PRE m'.

  #[using="MDTOR PRE_frame"] Lemma aexit_prefix_spec : forall (reg : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso : word),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m 0x5d3f28 [C4 (Z_to_bv 64 t)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x5f4240 [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x5f4260 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
    atx_stateA reg m ->                                                               (* [comment removed for export] *)
    rw_cells bsegs m 0x99cf0 [C8 (Z_to_bv 64 0x98aa8); C8 (Z_to_bv 64 0x98a98)] -> (* [comment removed for export] *)
    rw_cells bsegs m 0x98a98 [C8 (Z_to_bv 64 0x81f38); C8 (Z_to_bv 64 0x300a8)] ->  (* [comment removed for export] *)
    rw_cells bsegs m 0x9d9d0 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x98fe0 [C8 (Z_to_bv 64 0x88a10); C8 z64] ->                   (* [comment removed for export] *)
    rw_cells bsegs m 0x9ad30 [C8 dso] ->                                             (* [comment removed for export] *)
    mem_inv bsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF bsegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x88b2c) fc None m (seg_rom bsegs)).
  Proof.
    intros until dso. intros HPRE ST TID EXL LIBC AX GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
    (* [comment removed for export] *)
    destruct AX as ((X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) & CB & CF). unfold APAEF_INCB, ACOV_FLAG, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. pose proof KH as KHI. unfold KHIGH in KH.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl bsegs m) as WM.
    Local Ltac2 Set LiaHints.tbl := fun () => "03O0?11352265753.97 11432636941.10311658450183.94 12771348661.10312779238896.1031343986644.113 1343986644.94  14793086774.94 14869079534.87 14869079534.97 14869079534.98 1518605069.82  15398494062.87 17439338734.95 17776320430.11417776320430.96 19049469500.97 19317809487.11319317809487.94 19622476014.95 19942487194.90 20335457722.82 20433961190.80 21428112826.82 22244383342.97 23111766312.10624065322682.10324161039186.90 24638473347.11624638473347.98 2474928570.82  24812739566.87 24954805690.82 25271559662.87 25314760359.97 25878270252.96 26323796050.90 26323796050.99 26493902277.90 26631534418.90 27294894486.90 27297791862.11127911298325.10627923971379.99 28361529274.82 28607055698.90 28696517455.11328696517455.94 29545175216.99 29592705978.82 29870281326.97 30080170938.82 30170357434.10330225150802.90 3070178032.82  30876851182.87 31361185874.90 31521058898.90 31521058898.99 31625319706.87 31979994175.88 32499718325.82 32600174396.87 32716547054.87 32716547054.97 32716547054.98 33680001082.95 33940205650.90 3439967214.87  3439967214.97  3439967214.98  34430152252.95 34498709429.10335146564538.82 3525607222.75  35850771151.11335850771151.94 36115622433.11536115622433.97 3640025710.97  36438299669.90 36630883559.81 36641385327.82 36944450135.81 37222180794.82 37258164461.81 37823627923.88 38072106319.11338072106319.94 38508687005.99 38647586490.1033888239342.95  39093924078.95 39521875765.71 39949608786.90 39949608786.99 39998025810.90 40059657198.87 40201484047.90 40457739452.97 41072247790.87 41072247790.97 41072247790.98 41161757422.95 41834437230.97 42273372099.89 42283207062.10942310800374.95 42831019478.90 42831019478.99 43059266230.78 43104399792.90 43124198553.95 43493603410.90 43493603410.99 43667128060.10543987951404.11243987951404.94 44507231930.10345221239098.87 45221239098.97 45221239098.98 45577070266.10346468661564.98 46609450959.11346609450959.94 48316456345.97 48429240188.89 48577040082.90 4866047897.97  4866047897.98  48781039854.95 49649769127.95 49952102226.90 49952102226.99 50362574674.90 50362574674.99 51324249070.87 51327670714.82 51425718543.99 51481786499.97 51678667182.98 52024118390.96 52136437230.87 52136437230.97 52136437230.98 52198366190.87 52198366190.97 52198366190.98 52311803630.95 52567164907.10352567164907.82 52567164907.87 52567164907.90 52567164907.95 52567164907.97 52567164907.98 52567164907.99 52579502455.11352579502455.94 5300105810.90  5321489999.113 5321489999.94  53710956986.82 53767577774.89 54164510851.87 54243526019.11554243526019.97 54404701703.11354605059791.11354605059791.94 55067441390.95 55074817722.10355583907258.82 55705332543.10656170333721.90 56172233139.71 56181959098.82 56185332718.87 563227834.97   5644302266.82  58148456595.86 59028845166.97 5907136082.90  5907136082.99  59314923118.82 59989976054.96 60471841134.87 60679622738.90 60679622738.99 60858483367.98 61674577390.87 61874979822.87 61874979822.97 61874979822.98 62245250030.87 62583080755.90 62987396431.11362987396431.94 63235321900.86 63305555623.97 63779719325.99 64997134979.11364997134979.95 65098116726.97 65530721210.82 66102116794.82 66307532356.90 67003974766.97 67081926311.87 68596889710.97 68699702202.82 7119268334.87  7119268334.97  7119268334.98  7488583.88     7923331770.103 7986041554.90  8684881006.97  8800126135.114 8800126135.92  8800126135.95  9212863925.103 00000100200300:00;00<00=00J00Q00X00_00`00g00n01201601:01E01P01W01X01Y01Z01[01b01c01d01k01l01m01n02502602=02>02B02I02P02Q02X02Y02Z02^02_02`02g03203=03A03B03I03J03K03R03S03Z03a03h03o04004104804<04C04J04Q04V04]04d04k05205605=05>05K05V05a05e05i06006406806<06@06A06B06F06Q06\06]06^06e06l07007707>07E07L07M07Q07X07_07f07m08408;08<08=08B08G08K08O08P08W08^08_08c08g08h08m09209709809<09G09R09S09T09[09\09]09d09e09l0:30::0:A0:H0:I0:J0:K0:O0:P0:W0:^0:e0:l0;30;:0;A0;B0;C0;D0;E0;F0;G0;H0;I0;T0;_0;f0<10<<0<=0<A0<B0<C0<D0<E0<P0<[0<b0<c0<d0<e0<f0<g0<h0<o0=40=50=90=@0=G0=N0=T0=U0=\0=c0=j0=k0>20>90>@0>G0>N0>O0>Z0>e0>i0>j0>k0>l0>m0>n0>o0?00?10?80?90?@0?A0?H0?O0?V0?W0?X0?_0?f0@30@60@C0@JSSFS2LO2KHSFFS2LO2KH3RSP1HS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2LO2KHS2LOS2LOS2HBS2LO2KH3HspS2LO2KH3HspS2LO2KHFSSSS2LO2KHFSS2LO2KHSSSS2LO2KHSS2LO2KHSS2LOS2LO2KHS2LO2KHFS2LO2KHSSS2LOSSS2LO2KHS2LO2KH3HspS2LO2KH3HspS2HBSS2LO2KHSSS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LO2KHFFS2LO2KHS2HBS2LO2KHS2LO2KHS2LO2KHS3RSPS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2HBS2LO2KHSS2LO2KH3RSP1HS2LO2KH3HspS2LO2KH3HspS2LOS2LOS2LO2KHS2LOS2HtS2HtS2HtSFS2LOS2LO2KH3HspS2LO2KH3HspSSS2LO2KHS2LO2KHS2LOS2LO2KHS2LO2KHS2LO2KHS2LO2KHSS2HBS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSSS3RSPS3RSPS2LOS2HBSS2LO2KHS2LO2KHSS2LOS2LOSS3RSPS3RSPS3RSPSS2HBS2LO2KH3HspS2LO2KH3HspSSS2LO2KHSSS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSSSS2LOSS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSSSSSSSSS2LO2KH3HspS2LO2KH3HspS2LO2KHS2LO2KH3HspS2LO2KH3HspSS2LOSSSFS2LO2KH3HspS2LO2KH3HspS2LO2KHSSFSSSS2LO2KHS3RSPSS2LOS2LO2KHS2LO2KHS2LO2KHS2Ht1KSS2LO2KHS2LO2KHS2LO2KHSS2LO2KHS2LO2KHS2LO2KHS2LO2KHS2LO2KHSS2LO2KH3HspS2LO2KH3HspS2LOSSSSSSSSS2LO2KHSS2LO2KHSS2LO2KHS2LO2KHS2LO2KHSSS2LO2KHS2LO2KHS2LO2KH3Hsp1HS1HS2LO2KH3Hsp1HS2LO2KH".
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
    steps_to 0x300a8%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0x88a10%Z. hstep.
    steps_to 0x30134%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
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
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> PRE m'.
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt2 get_so set_so.     (* [comment removed for export] *)

  #[using="MDTOR PRE_frame stdio_exit_spec"] Lemma aexit_spec : forall (reg : bool) RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m 0x5d3f28 [C4 (Z_to_bv 64 t)] ->
    rw_cells bsegs m 0x5f4240 [C4 z64] ->
    rw_cells bsegs m 0x5f4260 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    atx_stateA reg m ->
    rw_cells bsegs m 0x99cf0 [C8 (Z_to_bv 64 0x98aa8); C8 (Z_to_bv 64 0x98a98)] ->
    rw_cells bsegs m 0x98a98 [C8 (Z_to_bv 64 0x81f38); C8 (Z_to_bv 64 0x300a8)] ->
    rw_cells bsegs m 0x9d9d0 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x98fe0 [C8 (Z_to_bv 64 0x88a10); C8 z64] ->
    rw_cells bsegs m 0x9ad30 [C8 dso] ->
    (* [comment removed for export] *)
    rw_cells bsegs m 0x5f46c8 [C8 z64] -> rw_cells bsegs m 0x9d8b0 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells bsegs m RSTDIN stdin_cells ->
    rw_cells bsegs m 0x9d7c0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells bsegs m 0x9d6d0 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->
    mem_inv bsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x88b2c) fc None m (seg_rom bsegs)).
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
                 ms' = MS (mkR (Z_to_bv 64 0x88b98) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x88b98) fc None m' (seg_rom bsegs) /\ mem_inv bsegs m')).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      apply implAM_from_evt.
      Local Ltac2 Set LiaHints.tbl := fun () => "00N0?10429640106.1171343986644.116 13861454031.11814700187727.11817094381263.11819317809487.11721510966599.1162168467805.117 26608136145.11828696517455.11728751370288.1173525607222.120 35850771151.11736098240795.11637234421199.11838072106319.11738072106319.11842148696048.11746609450959.1185321489999.118 54605059791.11855985279891.13956128028111.11856172531244.11761445037647.11861603222095.11862987396431.11662987396431.11866956803025.11768459972047.11800000400500=00E00M00U00V00\00d00e00f01501=01>01F01N01V01[01c01d01l01m02502602>02F02N02V02^02fS2LOFS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'FS4SP47S2LO3KH'FFS2LO4SP473KH'1HS2LO3KH'FS2LO3KH'S2LO3KH'S2LO3KH'S3KH'S2LO3KH'FS2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'".
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
               replace (ret_pc (Z_to_bv 64 0x88b98)) with (Z_to_bv 64 0x88b98) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
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
