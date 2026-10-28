(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes SysStep.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope bv_scope.

Definition sysret_entry := 0x14350%Z.
Definition read_entry := 0x1bbe4%Z.
Definition close_entry := 0x1bb84%Z.
Definition open_entry := 0x14204%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt usegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14350) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. Local Ltac2 Set LiaHints.tbl := fun () => "00L0>13328991197.5914260848499.4920433961190.4725071629079.5625071629079.5925071629079.6326504924688.4529023867535.6331399144472.4832600174396.563832199072.49 40201484047.5940201484047.6142831019478.5942831019478.6343059746780.4543104399792.5945221239098.5654164510851.5654164510851.6160357415926.6062445010544.6362583080755.5962631338201.5663779719325.6364310411571.6365917833157.4967081926311.5600000500=00>00?00@00A00E00F00K00O00W00X00Y00]00a00e00i00m00n00o01001401501:01?01@01H01IS3SEPS2Hc3Ra0SSSSS2HcSS3Ra0S2HBS2LO3Ra0SSS2HBS2HBS2LOS2HBS2HBSSSS2TPSS3SEPS3SEPSS2Hc3Ra0S".
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

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells usegs m' B [CB n junk]
                    /\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells usegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells usegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Lemma read_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (bv_unsigned a1 + count <= 2^47)%Z ->                 (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1bbe4) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  apply impl_enode.
  Local Ltac2 Set LiaHints.tbl := fun () => "00Z0>10464971335.7412428150072.7412528832645.5812975952027.5614442746792.5418592857425.5420433961190.5323652920060.5425076071819.7425076071819.7526494647592.6026507342608.5831399144472.563187352862.56 32600174396.6033506546962.5434237669365.5437038156647.573824981359.70 3830199799.57 3832491140.57 42160541851.6043059266230.514442029274.58 45221239098.6046534209988.5446930574496.7047786637509.5852110790085.5854164510851.6054164510851.645449153110.56 57622410744.755764142568.75 62619160405.7062631338201.6065531314038.6367081926311.6067905458627.7067909738204.5867909786197.589293543967.70 00000100200N00R00S00X00Y00]01101J01K01X01Y01_01c01i01n02302702;02?02S02W02[02_02`02j03<03X03Y03Z03^03a03g03k04104204304=04J04W04[FFS3CNT4SEP14SEP24SEP34Hlen2HBS2TPFS3CNTSS2FDS3CNT4SEP14SEP24SEP3S3CNT4SEP14SEP24SEP34HlenSS3CNT4Hlen2HBSS4SEP1S2HBS4CNT2S3CNTS3CNTS2HeS2LOS2LOS3CNT4SEP14SEP24SEP3S2LOS2HBS2HBFS3CNT4HlenS3CNT4CNT24Hlen2HBS3CNT4SEP14SEP24SEP34Hlen2HBSSS2LOS1HS4SEP1S2HeS4SEP1SSS3CNT4HlenS3CNT4Hlen2HBS3CNT4Hlen2HBS2He".
carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_read_Some in Hdec as [ci Hdec]; [|lia].
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
Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Proof.
  intros e He. Local Ltac2 Set LiaHints.tbl := fun () => "00:0=10904838341.418932449448.422558107161.423086697931.431208808405.435499739364.455973457752.463846358525.465318618767.49281348460.2 00000:00;00?00@00D00E00H00I00O00SS2He3Hne1nSS2HeSS2HeSS1lSS2He1lS2He".
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

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (close_errno a errv)].

Lemma close_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1bb84) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST ERR MI -> FD LO SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  apply impl_enode.
  Local Ltac2 Set LiaHints.tbl := fun () => "00c0>12428150072.7012428150072.7212975165284.4912975835496.5115447086794.5115447429318.4915735287248.4915735958492.5116792795048.7116792795048.7320433961190.4721997767011.6522284289799.7022284289799.7222357826550.5423652920060.4825071629079.5425076071819.7125076071819.7325850720662.6625850720662.6831399144472.6231399144472.6331399144472.6532600174396.543525607222.53 3525607222.55 35916362628.593830115332.63 3830115332.64 3832295799.66 39339135284.5743059266230.4545221239098.5447357332149.5151524615158.5551524615158.5752074235542.6152074235542.6354164510851.5454164510851.7054164510851.7154164510851.7557622410744.7157622410744.7359020524184.6359020524184.6462631338201.5467081926311.549279252460.66 9281348460.51 00000100200600:00>00B00H00N00X00b00c00h00i00j00k00o01001:01D01E01F01G01H01I01M01V01_01`01d01h01l01m02102502902:02;02<02=02>02?02@02A02M02Y02Z02[02a02b02f02jFFS2TPS2TPS2LOS2LOS4SEP1S4SEP1S4SEP13HspS4SEP13HspSS3HneFFSS2FDSS4SEP13HspS4SEP13HspSSSSSS2HBS2LO1H2H0S2LO1H2H0FS2LOS2LOS2LOSS2LOS2HBS2HeSSFFSSSSS4SEP13Hsp1HS4SEP13Hsp1HSSS4SEP1SS2HeS2He".
carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
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
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x1ccb8%Z.
Definition ssp_guard := 0x4e298%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at usegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells usegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells usegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Lemma open_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells usegs m ssp_guard [C8 canary] ->
  mem_inv usegs m ->
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
  impl usegs (at_node usegs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x14204) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST SRC ERR GOT SSP MI -> NUL NOSL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply impl_enode.
  Local Ltac2 Set LiaHints.tbl := fun () => "0230>11875767022.6812352412732.6812428150072.8312428150072.8512975835496.6212984225256.641423997812.68 15442153454.6516629598702.6816740655320.7816792795048.8416792795048.8617151130279.6817995455655.6718363204284.6718628173017.6819415681262.6819970277031.6720163737475.6720163737475.8620475430715.592124193155.67 22163107130.6822284289799.8322284289799.8524358849780.6724390924092.6724630998586.6825071629079.6525071629079.6725071629079.6825076071819.8425076071819.8626216087156.6827032929881.672728429678.67 28370640551.6728558912116.6730196181434.6730396535790.6530403814844.67315996476.68  32127996803.6732225056601.6732651489978.6733680001082.6833781268846.6735205357699.6835205357699.8736068309337.6736180999398.5837360254574.673812382191.75 39282922457.6840150930599.6841272171651.6541272171651.8541481574516.6842250564406.6642250564406.6843059580201.564339538087.68 4461167854.68 44762256494.6744950045500.684496656560.76 4496656560.78 45257912942.6745607773934.6846232973498.6746690875510.6846690875510.7047357332149.6249961420788.6750131542183.6750975666620.675114850435.68 51820114670.6752707631992.5952932610323.5953711996362.6253720383818.6454880082292.6555575700569.6756020583278.6756238753134.67563227834.67  5646517998.67 56625144942.6756986461756.6557622410744.8457622410744.8657745675194.6757966400220.6257974789724.6458715251188.6758788101849.6559192637571.6759586984046.675972701590.79 5972701590.81 59959517475.8459959517475.8660511600900.7660511600900.7861305990311.6762181856437.6462190324166.7862302209411.6762623338453.7562801085934.6863014048956.676326792124.67 63568978676.6763980343257.6764772824451.6764772824451.8665805175866.6767604033390.6767800019075.6867823595993.687130566823.67 7486304935.65 7508761433.67 7835469603.84 7835469603.86 8583720762.65 9198351348.67 9281010335.76 945059608.75  945059608.77  00000600<00=00>00B00F00O00U00[00e01F01g01k01o02502>02D02H02L02M02N02R02V02W02X02a02g02k02l02m02n03O04004904B04H04L04U04Y04_04e04k04o05805<05@05F05J05K05T05X05^05b05k05o06306406=06E06M06T06X06^06d06j06k06l07207807<07=07>07B07K07O07U07Y07_07`07a07e07i08208;08A08G08K08Q08W08]09@09c09g0:00:90:B0:K0:O0:U0:V0:W0:n0;E0;I0;M0;Q0;[0;e0;i0;m0<30<90<?0<H0<Q0<U0<V0<Z0<`0<d0<m0=10=50=>0=_0>@0>D0>M0>Q0>R0>SS4SEP4S4SEP4FFS2TPS2TPS4SEP22BPS4SEP4S4SEP4S4Hfd33HfdS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS2BPS2BPS4SEP4S4SEP12BPS4SEP4S2BPS2BPSFS2BPS2HBFFS4SEP22BPS4SEP4S2HBSSSS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP22BPS4SEP12BPS4SEP4S2BPS4SEP22BPS2HBS4SEP4S4SEP4S4SEP4S2BPS4SEP12BPS2HBS2HBS4SEP4S2BPSS4SEP12BPS2BPS4SEP4S2HeS4SEP12BPS2BPS2BPSS4SEP22BPS4SEP41HS4SEP41HS2LO2BPS2BPS4SEP4S4SEP4S4SEP4SSS4SEP4S4SEP4S2HBSSS2HeS4SEP22BPS2BPS4SEP4S2BPS4SEP4FFS2LOS2LOS4SEP22BPS4SEP12BPS4SEP4S4SEP4S2HBS4SEP4S4SEP4S4SEP4S4SEP14SEP24SEP34SEP44SEP52BP3Hsp1HS4SEP14SEP24SEP34SEP44SEP52BP3Hsp1HS2HBS4SEP12BPS4SEP12BPS4SEP22BPS4SEP12BPS2BPS4SEP4SSS4SEP14SEP44SEP62BP3HspS4SEP14SEP44SEP62BP3HspS2LOS2LOS2BPS4Hfd33HfdS4Hfd33HfdS2BPS2HeS4SEP4S4SEP4S4SEP4S4SEP22BPS4SEP12BPS2BPSS2HBS4SEP4S2BPS4SEP12BPS2BPS2BPS4SEP12BPS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS2HBS4SEP22BPS2HeSS".
carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
