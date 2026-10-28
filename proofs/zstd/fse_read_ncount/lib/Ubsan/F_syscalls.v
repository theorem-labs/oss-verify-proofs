(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes SysStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope bv_scope.
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
F (Z_to_bv 64 0x15170) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST ERR MI LO SEP TP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
do 3 step. if_cases Hc; zify_cond Hc.
-
step. unfold sysret_post, sysret_val, sysret_errno. Local Ltac2 Set LiaHints.tbl := fun () => "00L0>13328991197.5914260848499.4920433961190.4725071629079.5625071629079.5925071629079.6326504924688.4529023867535.6331399144472.4832600174396.563832199072.49 40201484047.5940201484047.6142831019478.5942831019478.6343059746780.4543104399792.5945221239098.5654164510851.5654164510851.6159190426614.6062445010544.6362583080755.5962631338201.5663779719325.6364310411571.6365917833157.4967081926311.5600000500=00>00?00@00A00E00F00K00O00W00X00Y00]00a00e00i00m00n00o01001401501:01?01@01H01IS3SEPS2Hc3Ra0SSSSS2HcSS3Ra0S2HBS2LO3Ra0SSS2HBS2HBS2LOS2HBS2HBSSSS2TPSS3SEPS3SEPSS2Hc3Ra0S".
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
(bv_unsigned a1 + count <= 2^47)%Z ->
(lo <= bv_unsigned sp - 16)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
(bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl usegs (at_node usegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
(epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1cad8) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
(errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "00^0>10464971335.7412428150072.7412528832645.5812975952027.5614442746792.5418592857425.5420364309523.7420364309523.7520433961190.5323652920060.5425076071819.7525703619574.6326494647592.6026507342608.5831399144472.563187352862.56 32600174396.6033506546962.5434237669365.5437038156647.573824981359.70 3830199799.57 3832491140.57 40190575097.7542160541851.6043059266230.514442029274.58 45221239098.6046534209988.5446930574496.7047786637509.5852110790085.5854164510851.6054164510851.645449153110.56 5764142568.75 62619160405.7062631338201.6062900777713.7563897388522.7463897388522.7567081926311.6067905458627.7067909738204.5867909786197.589293543967.70 00000100200D00H00I00N00X00g00h00l00m00n00o01<01=01C01G01M01R01W01[01_01c01d01n02202602:02;02E02W02i02j02k02o03503903?03B03L03[03\03f04304@04DFFS3CNT4SEP34Hlen2HBS2TPFS3CNTS3CNT4SEP3S3CNT4SEP34HlenSS2FDFSSS3CNT4Hlen2HBSS4SEP1S2HBS4CNT2S3CNTS3CNTS2HeS2LOS2LOFS3CNT4SEP2S2LOS2HBS2HBFS3CNT4HlenS3CNT4CNT24Hlen2HBS3CNT4SEP24Hlen2HBSSS2LOS4SEP1S2HeS4SEP1S1HS3CNT4SEP2S3CNT4SEP24HlenSS3CNT4HlenS3CNT4Hlen2HBS3CNT4Hlen2HBS2He".
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
F (Z_to_bv 64 0x1ca78) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST ERR MI -> FD LO SEP1 TP.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "00i0>11714716182.6611714716182.6812428150072.7012428150072.7212951406312.7112951406312.7312975165284.4912975835496.5115447086794.5115447429318.4915735287248.4915735958492.5116792795048.7116792795048.7320433961190.4721997767011.6522284289799.7022284289799.7223652920060.4825071629079.5425076071819.7125076071819.7331399144472.6231399144472.6331399144472.6532600174396.5432795189110.5532795189110.573525607222.53 3525607222.55 35916362628.5937645959030.543830115332.63 3830115332.64 3832295799.66 39339135284.5740097498809.7140097498809.7340190575097.7140190575097.7343059266230.4545221239098.5447357332149.5152074235542.6152074235542.6354164510851.5454164510851.7054164510851.7154164510851.7559020524184.6359020524184.6462631338201.5462900777713.7162900777713.7367081926311.549279252460.66 9281348460.51 00000100200300400900>00B00F00J00N00T00Z00d00n00o01401501601:01;01<01=01>01?01@01D01E01F01O01X01Y01Z01^01b01f01g01m02302402502902=02A02B02C02D02E02F02G02H02I02O02V02]02^02b02fSSFFS3HspS3HspS2TPS2TPS2LOS2LOS4SEP1S4SEP1S4SEP13HspS4SEP13HspSS3HneFFS2FDSFFSSSS2HBSSS2LO1H2H0S2LO1H2H0FSS2LOS2LOS2LOSS4SEP1S4SEP1FFS2LOS2HBS2HeFFSSSSSSS4SEP1S3Hsp1HS3Hsp1HSS2HeS2He".
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
Definition got_ssp := 0x1dbb0%Z.
Definition ssp_guard := 0x4f1a0%Z.
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
impl usegs (at_node usegs) (enode (NOpen path) dec_open)
(epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15024) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST SRC ERR GOT SSP MI -> NUL NOSL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
unfold got_ssp, ssp_guard in *.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "02A0>11041912942.6712352412732.6812428150072.8312428150072.8512975835496.6212984225256.641423997812.68 15776184302.6516740655320.7816792795048.8416792795048.8617040090734.6717151130279.6817836644758.7917836644758.8117995455655.6718363204284.6718628173017.6819970277031.6720163737475.6720163737475.8620430848892.8420430848892.8620475430715.592124193155.67 21262406894.6722163107130.6822284289799.8322284289799.8522666764398.6724358849780.6724390924092.6724630998586.6825071629079.6525071629079.6725071629079.6825076071819.8425076071819.8626216087156.6826757167854.6827032929881.6727557601256.8427557601256.8628316868590.6828370640551.6728558912116.6730196181434.6730403814844.6731450648822.8431450648822.86315996476.68  32127996803.6732225056601.6732651489978.6733647749998.6733680001082.6833885744366.6835205357699.6835205357699.8736068309337.6736180999398.583640025710.67 3812382191.75 38822420342.6838822420342.7039282922457.6839512420078.6740150930599.6840190575097.8440190575097.8641272171651.6541272171651.8541481574516.6842250564406.6642250564406.6843059580201.564339538087.68 44950045500.684496656560.76 4496656560.78 45604733294.6746232973498.6746600235374.6746985772561.8446985772561.8647357332149.6248490912238.6549961420788.6750131542183.6750491175406.6850975666620.675114850435.68 52707631992.5952932610323.5952982799889.8452982799889.8653711996362.6253720383818.6454880082292.6555067441390.6855575700569.67563227834.67  56986461756.6557581223022.6757745675194.6757966400220.6257974789724.6458715251188.6758788101849.6559192637571.6759587477102.6760511600900.7660511600900.7861305990311.6761816451513.8461816451513.8662181856437.6462190324166.7862302209411.6762473508590.6862623338453.7562900777713.8462900777713.8663014048956.676326792124.67 63568978676.6763980343257.6764309385462.8464309385462.8664762703525.8464762703525.8664772824451.6764772824451.8665782973294.6765805175866.6767800019075.6867823595993.687130566823.67 7486304935.65 7508761433.67 8583720762.65 9198351348.67 9281010335.76 945059608.75  945059608.77  00000600<00=00>00B00F00O00U00_00i01301901=01>01?01C01I01O01S01W01X01a01j01k01o02502902:02;02A02J02P02T02U02V02W02X02Y02b02h02n03303803>03B03K03O03U03[03a03g03k04104504;04?04E04I04J04P04T04Z04^04_04`04f04l05005105205605705@05H05P05W05[05a05b05c05i05m06306=06G06K06Q06Z06^06d06j06n06o07007:07D07H07L07U07[07a07e07k08108508;08A08J08P08T08Z08^08b08f08l09209<09F09J09P09T09[09b09h09n0:70:=0:C0:I0:V0:c0:g0:h0:n0;20;60;<0;@0;D0;J0;N0;W0;[0;\0;]S4SEP4S4SEP4FFS2TPS2TPS4SEP22BPS4SEP4S4Hfd33HfdS4SEP13HspS4SEP13HspS4SEP4S2BPSSS2BPS4SEP4S4SEP1S2BPS2BPSS4SEP32BPS4SEP32BPFS2BPS4SEP4S2HBFFS4SEP4S4SEP22BPS4SEP4S2HBSSSFFS4SEP22BPS4SEP4S4SEP1S3HspS3HspS4SEP4S2BPS4SEP22BPS2HBS4SEP4S4SEP5S4SEP5S4SEP4S2BPS4SEP1S2HBS4SEP4S2HBS4SEP4S2BPSS4SEP1S2BPS4SEP4S2HeSSS4SEP1S4SEP4S2BPFFS2BPSS4SEP22BPS4SEP41HS4SEP41HS2LO2BPS2BPS4SEP4SSS4SEP4S2HBS4SEP4S4SEP43HspS4SEP43HspS2HeS4SEP4S4SEP22BPS2BPS4SEP4S4SEP4S2BPFFS4SEP43HspS4SEP43HspS2LOS2LOS4SEP22BPS4SEP4S4SEP1S2HBS4SEP4S4SEP4S2HBS4SEP1S4SEP1S4SEP22BPS4SEP1S2BPS4SEP4S2LOS2LOS2BPS4SEP1S4SEP1S4Hfd33HfdS4Hfd33HfdS2BPS4SEP4S2HeS3Hsp1HS3Hsp1HS4SEP4S4SEP4S4SEP22BPS4SEP1S4SEP6S4SEP6S4SEP22BP3HspS4SEP22BP3HspS2BPSS4SEP4S2HBS2BPS4SEP1S2BPS2BPS4SEP1S2HBS4SEP22BPS2HeSS".
carve_frame 96%nat ST.
do 18 step. if_false. do 3 step. if_false. do 2 step.
do 8 step. do 8 step.
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
