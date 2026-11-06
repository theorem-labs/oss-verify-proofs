(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
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

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
#[using="Type"] Lemma sysret_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(errv : word) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
(lo <= bv_unsigned sp - 16)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (errno_addr tp) 4 ->
evtF asegs RNG (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x895f4) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST ERR MI LO SEP TP RSTK RERR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
do 3 step. if_cases Hc; zify_cond Hc.
-
step. unfold sysret_post, sysret_val, sysret_errno. Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>13162791137.6613328991197.6314260848499.5320433961190.5125071629079.6025071629079.6325071629079.6726504924688.4929023867535.6731399144472.5232600174396.603832199072.53 39377301110.6440201484047.6340201484047.6542831019478.6342831019478.6743059746780.4943104399792.6345221239098.6053767577760.6253769674920.6454164510851.6054164510851.6562445010544.6762583080755.6362631338201.6063235321902.5963237419048.6463779719325.6764310411571.6765917833157.5367081926311.6000000100600>00?00@00A00B00F00G00L00P00X00Y00Z00[00_00c00g00k00o01301701801901=01>01C01G01K01P01Q01Y01ZSS3SEPS2Hc3Ra0SSSSS2HcSS3Ra0S2HBS2LO3Ra0SSSS2HBS2HBS2LOS2HBS2HBS2LOS2LOSSS2TPSS3SEPS2LOS2LOS3SEPSS2Hc3Ra0S".
rewrite (errno_of_small a0) by lia. finish.
- carve_frame 16%nat ST.
do 14 step.
pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
rewrite negw_errno in ERR by lia.
unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
release_frame FR ST (bv_unsigned sp).
finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition read_ret (a : read_ans) : word :=
match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.
Definition read_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
(a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ match a with
| RdErr e => rw_cells asegs m' B [CB n junk]
/\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
| RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
/\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
end.
#[using="Type"] Lemma read_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(fd count : Z) (junk : list byte) (errv : word) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
(3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
(bv_unsigned a1 + count <= 2^47)%Z ->
(lo <= bv_unsigned sp - 16)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
(bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
(164 <= bv_unsigned tp)%Z ->
rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (errno_addr tp) 4 ->
rng RNG (bv_unsigned a1) count ->
implA asegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
(epostF (read_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x981b4) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP RSTK RERR RDST.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
(errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
apply implF_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "00^0>10464971335.7912428150072.7912528832645.6312975952027.6114442746792.5918592857425.5920433961190.5823652920060.5925076071819.7925076071819.8026494647592.6526507342608.6331399144472.613187352862.61 32600174396.6533506546962.5934237669365.5937038156647.623824981359.75 3830199799.62 3832491140.62 38350421878.6842160541851.6543059266230.564442029274.63 45221239098.6546534209988.5946930574496.7547786637509.6352110790085.6354164510851.6554164510851.695449153110.61 57384956810.5957622410744.805764142568.80 5904775314.59 62619160405.7562631338201.6563235321900.6463235321900.6867081926311.6567905458627.7567909738204.6367909786197.639293543967.75 00000100200N00R00S00X00Y00]01101J01K01X01Y01_01c01i01n02302702;02?02@02T02X02\02`02a02k03=03Y03Z03[03_03`03c03i03j03n04404804<04=04G04T04a04eFFS3CNT4SEP14SEP24SEP34Hlen2HBS2TPFS3CNTSS2FDS3CNT4SEP14SEP24SEP3S3CNT4SEP14SEP24SEP34HlenSS3CNT4Hlen2HBSS4SEP1S2HBS4CNT2S3CNTS3CNTS2HeS2LOS2LOSS3CNT4SEP14SEP24SEP3S2LOS2HBS2HBFS3CNT4HlenS3CNT4CNT24Hlen2HBS3CNT4SEP14SEP24SEP34Hlen2HBSSS2LOFS1HS4SEP1FS2HeS4SEP1S2LOS2LOSS3CNT4HlenS3CNT4Hlen2HBS3CNT4Hlen2HBS2He".
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
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (close_errno a errv)].
#[using="Type"] Lemma close_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(fd : Z) (errv : word) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
(lo <= bv_unsigned sp - 32)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (errno_addr tp) 4 ->
implA asegs RNG (enode (NClose fd) dec_close)
(epostF (close_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x980d4) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST ERR MI -> FD LO SEP1 TP RSTK RERR.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
apply implF_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "00j0>12428150072.7412428150072.7612975165284.5312975835496.5515447086794.5515447429318.5315735287248.5315735958492.5516792795048.7516792795048.7720433961190.5121997767011.6922284289799.7422284289799.7623652920060.5225071629079.5825076071819.7525076071819.7728467194262.7028467194262.7231399144472.6631399144472.6731399144472.6932600174396.583525607222.57 3525607222.59 35916362628.633830115332.67 3830115332.68 3832295799.70 39339135284.6143059266230.4945221239098.5847357332149.5552074235542.6552074235542.6752607845368.5254164510851.5854164510851.7454164510851.7554164510851.7956172355148.5556172795968.5357622410744.7557622410744.7759020524184.6759020524184.6861955427318.5961955427318.6162631338201.5862770004982.5863235321900.5763235321900.7363235321900.7463235321902.7867081926311.589279252460.70 9281348460.55 00000100200600:00>00B00H00N00X00b00c00h00i00j00n00o01901C01D01E01F01G01H01L01U01^01_01c01g01k01l02002402802902:02;02<02=02>02?02@02A02M02Y02Z02[02\02]02c02d02h02l03003403503903=FFS2TPS2TPS2LOS2LOS4SEP1S4SEP1S4SEP13HspS4SEP13HspSS3HneFFS2FDSS4SEP13HspS4SEP13HspSSSSSS2HBS2LO1H2H0S2LO1H2H0FS2LOS2LOS2LOSS2LOS2HBS2HeFFFSSSSSSS4SEP13Hsp1HS4SEP13Hsp1HSSSSS4SEP1SS2LOS2LOS2LOS2LOSS2HeS2He".
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
Definition got_ssp := 0x9a410%Z.
Definition ssp_guard := 0x5f5450%Z.
Definition open_ret (a : sret) : word :=
match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.
Definition open_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint)
: machine_state -> Prop :=
fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (open_errno a errv)]
/\ bytes_at asegs m' P (path ++ [Z_to_bv 8 0])
/\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
/\ rw_cells asegs m' ssp_guard [C8 canary]
/\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.
#[using="Type"] Lemma open_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(path : list byte) (errv canary : word) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
bytes_at asegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
rw_cells asegs m ssp_guard [C8 canary] ->
mem_inv asegs m ->
a1 = Z_to_bv 64 0 ->
~ In (Z_to_bv 8 0) path ->
path_has_slash path = false ->
(lo <= bv_unsigned sp - 112)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
(ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
(errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
(got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
(164 <= bv_unsigned tp)%Z ->
rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (errno_addr tp) 4 ->
rng RNG (bv_unsigned a0) (Z.of_nat (length path) + 1) ->
rng_aimg RNG ->
implA asegs RNG (enode (NOpen path) dec_open)
(epostF (open_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x89510) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST SRC ERR GOT SSP MI -> NUL NSL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP RSTK RERR RSRC RIMG.
unfold got_ssp, ssp_guard in *.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
apply implF_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "02J0>100583406.71  1162083360.92 1162083374.73 1162083374.92 12352412732.7412428150072.8912428150072.9112975835496.6812984225256.7014086840430.731423997812.74 15617080686.7315704552726.8515704552726.8716740655320.8416792795048.9016792795048.9217151130279.7417416023030.7417416023030.7617776320431.7217995455655.7318363204284.7318628173017.7418909637614.7119970277031.7320163737475.7320163737475.9220313996398.7320475430715.652124193155.73 21585288942.7422163107130.7422284289799.8922284289799.9124358849780.7324390924092.7324630998586.7425067826030.7325071629079.7125071629079.7325071629079.7425076071819.9025076071819.9225878270252.7025878270252.9025878270254.9026216087156.7426982344558.7327032929881.7327453056622.7327804035822.7328370640551.7328558912116.7330196181434.7330274919918.7430403814844.73315996476.74  32127996803.7332225056601.7332651489978.7333680001082.7435022110958.7435205357699.7435205357699.9336068309337.7336115622446.7336180999398.6436914069924.653734855790.73 3812382191.81 38903098019.9038903098019.9239282922457.7440091925665.9140091925679.7240091925679.9140150930599.7441272171651.7141272171651.9141481574516.7442250564406.7242250564406.7443059580201.624339538087.74 43984724152.6543987951406.7344950045500.744496656560.82 4496656560.84 46232973498.7346270630510.7347357332149.6849961420788.7350131542183.7350693720814.7450975666620.735114850435.74 51678667169.9151678667183.7251678667183.9152707631992.6552932610323.6553711996362.6853720383818.7053767577775.7254880082292.7155575700569.7356087804133.6556172355148.6856180742860.70563227834.73  56986461756.7157622410744.9057622410744.9257637878894.7357745675194.7357839090926.7457966400220.6857974789724.7058715251188.7358788101849.7159192637571.7360511600900.8260511600900.8461305990311.7361917199023.7262181856437.7062190324166.8462302209411.7362623338453.8163014048956.7363235321903.726326792124.73 63568978676.7363980343257.7364772824451.7364772824451.9265518452462.7365805175866.7367800019075.7467823595993.747130566823.73 7486304935.71 7508761433.73 7779942894.74 8583720762.71 9198351348.73 9281010335.82 9317568675.90 9317568675.92 9333008750.73 945059608.81  945059608.83  00000600:00A00E00K00L00M00Q00U00[00d00j00k00l01601W02802<02=02>02E02I02O02X02^02b02f02g02m02n03203803<03=03>03G03M03Q03W03X03Y03Z04;04\04c04g04k05405:05C05I05O05S05\05`05f05l06206606?06C06G06M06Q06R06[06b06f06g06m07107H07_07h07l08308708;08?08@08I08Q08Y08`08d08e08l09209309409809>09B09K09O09U09[09_09c09j09n09o0:00:40:80:?0:H0:Q0:U0:V0:W0:[0:a0;D0;g0;m0<10<70<@0<I0<R0<[0<_0<c0<g0<k0=20=<0=F0=J0=N0=T0=[0=a0=j0>30>70>80>>0>B0>F0>O0>S0>W0>`0>f0>j0?30?70?X0@90@?0@@0@AS4SEP4S2LOS2LO2BPS2LOS4SEP4FFS2TPS2TPS4SEP4S4SEP22BPS4SEP4SSS4Hfd33HfdS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS2BPSSS2LO2BPS2BPS4SEP4S4SEP12BPS4SEP4S2BPS2BPSS4SEP4FS2BPS4SEP4S2HBFFS4SEP22BPS4SEP4S2HBS4SEP4SSSS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS2LO2BPS2LOS2LOS4SEP22BPS4SEP4S4SEP12BPS4SEP4S4SEP4S2BPS4SEP22BPS2HBS4SEP4S4SEP4S4SEP4S2BPS4SEP12BPS2HBS2HBS4SEP4S2BPSS4SEP12BPS2LO2BPS2BPFS4SEP4S2HeS4SEP14SEP44SEP62BP3HspS4SEP14SEP44SEP62BP3HspS4SEP12BPS2LOS2LO2BPS2LOS2BPS2BPSS4SEP22BPS4SEP41HS4SEP41HS2LO2BPS2BPFS2LO2BPS4SEP4SSS2HBS4SEP4S2HeS4SEP22BPS2BPS4SEP4S4SEP4S2BPS2LOS2LO2BPS2LOFFS2LOS2LOS2LO2BPS4SEP22BPS4SEP12BPS2BPSSS2HBS4SEP4S4SEP14SEP24SEP34SEP44SEP52BP3Hsp1HS4SEP14SEP24SEP34SEP44SEP52BP3Hsp1HS4SEP4S2HBS4SEP4S4SEP12BPS4SEP12BPS4SEP22BPS4SEP12BPS2BPS2LOS2LOS2BPS2LO2BPS4Hfd33HfdS4Hfd33HfdS2BPS2HeS4SEP4S2LO2BPS4SEP4S4SEP22BPS4SEP12BPS2BPSS4SEP4S2HBS2BPS4SEP12BPS2BPS2BPS4SEP12BPS4SEP4S2HBS4SEP22BPS2HeS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP14SEP24SEP34SEP44SEP52BP3HspS4SEP4SS".
carve_frame 96%nat ST.
do 18 step. if_false. do 3 step. if_false. do 2 step.
do 8 step. do 8 step.
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
