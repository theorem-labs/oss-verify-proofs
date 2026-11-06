(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition sysret_entry := 0x88e84%Z.
Definition read_entry := 0x97a44%Z.
Definition close_entry := 0x97964%Z.
Definition open_entry := 0x88da0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

#[using="Type"] Lemma sysret_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  mem_inv bsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  evtF bsegs RNG (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88e84) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>13162791137.6613328991197.6314260848499.5320433961190.5125071629079.6025071629079.6325071629079.6726504924688.492821730166.64 29023867535.6731399144472.5232600174396.603832199072.53 40201484047.6340201484047.6542831019478.6342831019478.6743059746780.4943104399792.6345221239098.6053767577760.6253769674920.6454164510851.6054164510851.6562445010544.6762583080755.6362631338201.6063235321902.5963237419048.6463779719325.6764310411571.6765917833157.5367081926311.6000000100600>00?00@00A00B00F00G00H00M00Q00Y00Z00[00_00c00g00k00o01301701801901=01>01C01G01K01P01Q01Y01ZSS3SEPS2Hc3Ra0SSSSS2HcSSS3Ra0S2HBS2LO3Ra0SSS2HBS2HBS2LOS2HBS2HBS2LOS2LOSSS2TPSS3SEPS2LOS2LOS3SEPSS2Hc3Ra0S".
rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells bsegs m' B [CB n junk]
                    /\ rw_cells bsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells bsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

#[using="Type"] Lemma read_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (bv_unsigned a1 + count <= 2^47)%Z ->                 (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  rng RNG (bv_unsigned a1) count ->
  implA bsegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epostF (read_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x97a44) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP RSTK RERR RDST.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply implF_enode.
  Local Ltac2 Set LiaHints.tbl := fun () => "00^0>10464971335.7912428150072.7912528832645.6312975952027.6114442746792.5918592857425.5920433961190.5823652920060.5925076071819.7925076071819.8026494647592.6526507342608.6331399144472.613187352862.61 32600174396.6533506546962.5934237669365.5937038156647.623824981359.75 3830199799.62 3832491140.62 42160541851.6543059266230.564442029274.63 45221239098.6546534209988.5946930574496.7547786637509.6352110790085.6352220997238.6854164510851.6554164510851.695449153110.61 57384956810.5957622410744.805764142568.80 5904775314.59 62619160405.7562631338201.6563235321900.6463235321900.6867081926311.6567905458627.7567909738204.6367909786197.639293543967.75 00000100200N00R00S00X00Y00]01101J01K01X01Y01_01c01i01n02302702;02?02S02W02[02_02`02j03<03X03Y03Z03[03_03`03c03i03j03n04404804<04=04G04T04a04eFFS3CNT4SEP14SEP24SEP34Hlen2HBS2TPFS3CNTSS2FDS3CNT4SEP14SEP24SEP3S3CNT4SEP14SEP24SEP34HlenSS3CNT4Hlen2HBSS4SEP1S2HBS4CNT2S3CNTS3CNTS2HeS2LOS2LOS3CNT4SEP14SEP24SEP3S2LOS2HBS2HBFS3CNT4HlenS3CNT4CNT24Hlen2HBS3CNT4SEP14SEP24SEP34Hlen2HBSSSS2LOFS1HS4SEP1FS2HeS4SEP1S2LOS2LOSS3CNT4HlenS3CNT4Hlen2HBS3CNT4Hlen2HBS2He".
carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_read_Some in Hdec as [ci Hdec]; [|lia].
  destruct ans as [e|bs].
  - destruct Hdec as [-> He]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    finish; lia.
  - destruct Hdec as [-> Hlen]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    finish; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Proof.
  intros e He. Local Ltac2 Set LiaHints.tbl := fun () => "00:0=10904838341.518932449448.522558107161.523086697931.531208808405.535499739364.555973457752.563846358525.565318618767.59281348460.3 00000:00;00?00@00D00E00H00I00O00SS2He3Hne1nSS2HeSS2HeSS1lSS2He1lS2He".
rewrite unsigned_errno_ret by lia.
  destruct (Z.eqb_spec e 4) as [->|Hne].
  - replace ((2 ^ 64 - 4 + 4) mod 18446744073709551616)%Z with 0%Z by reflexivity.
    cbn. reflexivity.
  - assert (Hnz : ((2 ^ 64 - e + 4) mod 18446744073709551616 <? 1)%Z = false).
    { apply Z.ltb_ge. destruct (Z.ltb_spec0 e 4).
      - replace (2 ^ 64 - e + 4)%Z with ((4 - e) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hnz. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. unfold errno_ret. rewrite <- (Z_to_bv_minus_mod (18446744073709551616 - e)). f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 (close_errno a errv)].

#[using="Type"] Lemma close_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  implA bsegs RNG (enode (NClose fd) dec_close)
       (epostF (close_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x97964) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST ERR MI -> FD LO SEP1 TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply implF_enode.
  Local Ltac2 Set LiaHints.tbl := fun () => "00j0>12428150072.7412428150072.7612975165284.5312975835496.5515447086794.5515447429318.5315735287248.5315735958492.5516792795048.7516792795048.7720433961190.5121997767011.6922284289799.7422284289799.7623652920060.5225071629079.5825076071819.7525076071819.7731399144472.6631399144472.6731399144472.6932600174396.583525607222.57 3525607222.59 35916362628.633830115332.67 3830115332.68 3832295799.70 39339135284.6143059266230.4945221239098.5847357332149.5551517989270.7051517989270.7252074235542.6552074235542.6752607845368.5254164510851.5854164510851.7454164510851.7554164510851.7954289615862.5856172355148.5556172795968.5357622410744.7557622410744.7759020524184.6759020524184.6862631338201.5863235321900.5763235321900.7363235321900.7463235321902.7867081926311.5868030567414.5968030567414.619279252460.70 9281348460.55 00000100200600:00>00B00H00N00X00b00c00h00i00j00n00o01901C01D01E01F01J01S01\01]01a01e01i01j01n02202602702802902:02;02<02=02>02?02@02A02B02N02Z02[02\02b02f02j02n03203303403503903=FFS2TPS2TPS2LOS2LOS4SEP1S4SEP1S4SEP13HspS4SEP13HspSS3HneFFS2FDSS4SEP13HspS4SEP13HspSSSS2HBS2LO1H2H0S2LO1H2H0FS2LOS2LOS2LOSS2LOS2HBS2HeSSFFFSSSSSSSS4SEP13Hsp1HS4SEP13Hsp1HSSS4SEP1S2LOS2LOS2LOS2LOSSSS2HeS2He".
carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *.
    destruct (Z.eqb_spec e 4) as [->|Hne].
    + rewrite errno_of_lit in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. rewrite Z.eqb_refl. finish.
    + rewrite errno_of_errno_ret in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. replace (e =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). finish.
  - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x99cc0%Z.
Definition ssp_guard := 0x5f4010%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at bsegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells bsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells bsegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

#[using="Type"] Lemma open_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  bytes_at bsegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells bsegs m ssp_guard [C8 canary] ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  path_has_slash path = false ->                        (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length path) + 1) ->
  rng_aimg RNG ->
  implA bsegs RNG (enode (NOpen path) dec_open)
       (epostF (open_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x88da0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST SRC ERR GOT SSP MI -> NUL NSL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP RSTK RERR RSRC RIMG.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply implF_enode.
  Local Ltac2 Set LiaHints.tbl := fun () => "02J0>11076189219.9011076189219.9211382190574.711162083360.92 1162083374.73 1162083374.92 11716686062.7412038600686.7412352412732.7412428150072.8912428150072.9112712509603.9012712509603.9212975835496.6812984225256.701423997812.74 15525371630.7416740655320.8416792795048.9016792795048.9217151130279.7417776320431.7217826350070.7417826350070.7617995455655.7318363204284.7318628173017.7419970277031.7320163737475.7320163737475.9220475430715.6520918232942.732124193155.73 21735729902.7322163107130.7422284289799.8922284289799.9124358849780.7324390924092.7324630998586.7425071629079.7125071629079.7325071629079.7425076071819.9025076071819.9225353615726.7325878270252.7025878270252.9025878270254.9026216087156.7427032929881.7328370640551.7328558912116.7328953805038.7430196181434.7330403814844.7330840919662.73315996476.74  32127996803.7332225056601.7332651489978.7332716586478.7433680001082.7435205357699.7435205357699.9336068309337.7336115622446.7336180999398.6436914069924.653812382191.81 39027678318.7339282922457.7439934790638.7140091925665.9140091925679.7240091925679.9140150930599.7440318426646.8540318426646.8741272171651.7141272171651.9141481574516.7442250564406.7242250564406.7443059580201.624339538087.74 43984724152.6543987951406.7344950045500.744496656560.82 4496656560.84 46232973498.7347357332149.6849961420788.7350131542183.7350975666620.735114850435.74 51219599470.7351678667169.9151678667183.7251678667183.9152707631992.6552932610323.6553711996362.6853720383818.7053767577775.7253860909166.7354880082292.7155575700569.7356087804133.6556172355148.6856180742860.70563227834.73  56986461756.7157622410744.9057622410744.9257745675194.7357966400220.6857974789724.7058715251188.7358788101849.7159192637571.7360511600900.8260511600900.8461305990311.7361917199023.7262181856437.7062190324166.8462302209411.7362623338453.8163014048956.7363235321903.726326792124.73 63568978676.7363980343257.7364307395438.7364650279534.7364772824451.7364772824451.9265805175866.7367007713006.7467278875246.7367664121070.7367800019075.7467823595993.747130566823.73 7486304935.71 7508761433.73 8583720762.71 9198351348.73 9281010335.82 945059608.81  945059608.83  9540386158.73 00000G00^00d00h00o01301901?01E01F01G01h02I02M02Q02Z02`02j03K03l04004704804904=04C04L04P04T04U04V04\04`04f04j04k04l05505;05?05@05A05B05c06D06J06Q06U06Y06b06k06o07807>07B07H07N07T07X07a07e07k07o08308408=08D08H08I08M08S08\08b08f08m09109509609709;09<09E09M09U09\09`09a09h09n09o0:00:40:80:A0:E0:K0:O0:U0:Y0:`0:d0:e0:f0:j0:n0;50;;0;D0;M0;Q0;R0;S0;W0;]0<@0<c0<g0=00=90=B0=K0=O0=S0=W0=[0=b0=l0>60>:0>>0>D0>K0>Q0>Z0>c0>i0>o0?30?40?80?>0?D0?J0?N0?W0?[0?_0?h0?l0@50@90@:0@;0@AS4SEP14SEP44SEP62BP3HspS4SEP14SEP44SEP62BP3HspS4SEP4S2LOS2LO2BPS2LOS4SEP4S4SEP4S4SEP4FFS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS2TPS2TPS4SEP22BPS4SEP4S4Hfd33HfdS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS2BPS2LO2BPSSS2BPS4SEP4S4SEP12BPS2BPS2BPSFS4SEP4S2BPS4SEP4S2HBFFS4SEP22BPS4SEP4S2HBSSSS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP4S2LO2BPS2LOS2LOS4SEP22BPS4SEP12BPS2BPS4SEP22BPS4SEP4S2HBS4SEP4S4SEP4S4SEP4S2BPS4SEP12BPS2HBS4SEP4S2HBS2BPSS4SEP12BPS2LO2BPS2BPFS2HeS4SEP4S4SEP12BPS4SEP4S2LOS2LO2BPS2LOS2BPSSS2BPSS4SEP22BPS4SEP41HS4SEP41HS2LO2BPS2BPFS2LO2BPS4SEP4SSS2HBS2HeS4SEP22BPS2BPS4SEP4S2BPS4SEP4S2LOS2LO2BPS2LOFFS2LOS2LOS2LO2BPS4SEP4S4SEP22BPS4SEP12BPS2BPSSS2HBS4SEP4S4SEP14SEP24SEP34SEP44SEP52BP3Hsp1HS4SEP14SEP24SEP34SEP44SEP52BP3Hsp1HS2HBS4SEP12BPS4SEP12BPS4SEP22BPS4SEP12BPS2BPS2LOS2LOS2BPS2LO2BPS4Hfd33HfdS4Hfd33HfdS2BPS2HeS4SEP4S2LO2BPS4SEP4S4SEP22BPS4SEP12BPS4SEP4S4SEP4S2BPSS2HBS4SEP4S4SEP4S4SEP4S2BPS4SEP12BPS2BPS2BPS4SEP12BPS2HBS4SEP22BPS2HeSSS4SEP4".
carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
