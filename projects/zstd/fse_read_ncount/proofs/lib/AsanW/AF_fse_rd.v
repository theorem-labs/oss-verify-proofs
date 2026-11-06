(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AF_fse_rd_iface
AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_loop AF_fse_rd_hdr AF_fse_rd_seg AF_fse_rd_asm.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac boxH H := lazymatch type of H with ?T => change T with (bx T) in H end.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma zsize_c8 : forall c, Z.of_nat (cells_size [C8 c]) = 8. Proof. reflexivity. Qed.
#[using="Type"] Lemma zsize_c4 : forall c, Z.of_nat (cells_size [C4 c]) = 4. Proof. reflexivity. Qed.
Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0R : stack_malloc_0r_stmt AI fflag rng_fs.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Definition rd_body8A_stmt : Prop :=
forall (L : alayout) (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
(SPV NC MSVP TLP BUF : Z) (rt0 rt buf : list Z) (msv0 msv tl n lo : Z) (tl0 : word),
AHEAP AI L RNG st LB m -> fake0_le1 LB ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
u8arr asegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
rw_cells asegs m MSVP [C4 (Z_to_bv 64 msv0)] -> rw_cells asegs m TLP [C4 tl0] ->
bytes_at asegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
read_ncount_body8 buf (msv0 + 1) rt0 = Ok (rt, msv, tl, n) ->
0 <= msv0 <= 255 -> 8 <= zlen buf <= 65536 -> zlen rt0 <= 65536 ->
fcellA m LB NC (2 * zlen rt0) -> NC mod 8 = 0 -> shullA RNG m LB NC (2 * zlen rt0) ->
fcellA m LB MSVP 4 -> MSVP mod 4 = 0 -> fcellA m LB TLP 4 -> TLP mod 4 = 0 ->
bufA m LB BUF (zlen buf) -> ablk BUF (BUF + zlen buf) -> BUF mod 8 = 0 ->
(NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
(NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
(MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
(MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - RD8_STACK ->
SPV + 16 < al_top L -> SPV mod 16 = 0 ->
mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (nshad (2 * zlen rt0)) ->
rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 -> rng RNG TLP 4 -> rng RNG (shad TLP) 1 ->
rng RNG BUF (zlen buf) -> rng RNG (shad BUF) (nshad (zlen buf)) ->
evtF asegs RNG (fse_read_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 rt msv tl n lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
(Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom asegs)).
#[using="fflag FFLAG FREL SM0R"] Theorem rd_body8A : rd_body8A_stmt.
Proof.
unfold rd_body8A_stmt.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF rt0 rt buf
msv0 msv tl n lo tl0
AH LE1 LBH ARR HMSV HTL HBUF FBY RB HM0 H8 HRT FCN N8 HULL FCM M4 FCT T4 BFA BBK B8 SNM SNT SNB SMT SMB STB ST BOT LO SPT SP16 MI TP
RSTK RI RFS RN RNS RM RMS RT RTS RBf RBS.
pose proof atop_range as ATR.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
unfold RD8_STACK, SM0R_STACK in LO.
pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
Local Ltac2 Set LiaHints.tbl := fun () => "00P0?11423978205.4  12270355462.4  1387517820.4   14100427596.15015000377476.5  16073428041.11716244895032.7  16437443255.18316817704085.18217986879152.4  18361226889.18320935316357.5  25521682176.3  2570613437.4   29199660172.11 29782367974.4  34345818009.3  3456505237.7   37944222770.18141597280153.3  42878255082.4  46028828505.2  4635839732.182 48088141008.39 54929060281.11656170431935.4  57386783433.5  60025627831.6  61522184623.1816338257984.190 66149329549.25 8952163448.5   00000400=00F00J00Q00U00b00f00j00o01301<01@01D01P01Q01U01b01f01j02202802<02^02b02g02n03503903=03P03^S2HaS2LO4SPABS3SPT3LY3S2H8S2M12M2S2H8S3BOT2LO4SPABS2T2S2M1S3BOTS2T1S3AR33AR4S2LOS2HaS2FH1H2H02H4SS2HaS3BOT2LO4SPABS2N2S2HaS3AR22HrS4SPABS2M2S2H32H41H2H02H62H73H113H123H163H21S2H8S3SPTS2T12T2S2N12N2S2N1S2H8S2H32H41H2H02H63H11S3SPT3LY34SPAB".
assert (AR1 : ATOP <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR2 : SPAz SPV + 160 <= SPV) by (clear - SPAB; lia).
assert (AR3 : ATOP + 4096 <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR4 : SPAz SPV + 56 <= 2^47) by (clear - SPAB SPT LY3; lia).
assert (LOA : lo <= SPAz SPV - 2224) by (clear - LO SPAB; lia).
assert (SPK : SPV + 16 < KEND) by (clear - SPT LY3; unfold KEND; lia).
assert (LOC : ATOP <= lo) by (clear - BOT; lia).
assert (LO' : lo <= SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; clear - LO; lia).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
destruct (read_body8_inv buf (msv0 + 1) rt0 rt msv tl n ltac:(lia) RB) as (HM1 & _).
lazymatch goal with |- evtF _ _ ?P _ =>
eapply evtF_cut; [eapply (rd_open AI fflag rng_fs SM0R L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m st LB SPV NC MSVP TLP BUF (zlen buf) lo (evtF asegs RNG P));
[first [assumption| lia] .. | ]
| intros ms' Hms; exact Hms ] end.
intros FF m3 j48 junk x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x28 x29 x30 x31
F64 FH FC RFF RSFF FFD AH3 MG3 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3.
replace (7 <? zlen buf) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
set (C := mkRDA gp tp FR fc m3 SPV FF NC MSVP TLP BUF lo rt0 buf msv0).
assert (ESPA : a_SPA C = SPAz SPV) by reflexivity.
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (clear - FH; apply ablk_lin in FH; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
boxH SNM. boxH SNT. boxH SNB. boxH SMT. boxH SMB. boxH STB.
pose proof FCN as [(cN & FAN & FNN & HbN & N1 & N2 & N3 & N5) _].
pose proof FCM as [(cM & FAM & FNM & HbM & M1 & M2 & M3 & M5) _].
pose proof FCT as [(cT & FAT & FNT & HbT & T1 & T2 & T3 & T5) _].
destruct (bufA_block m LB BUF (zlen buf) BFA) as (bB & HbB & B1 & B2).
assert (ABN : ablk NC (NC + 2 * zlen rt0)) by (eapply ablk_sub; [exact N3| lia| lia]).
assert (ABM : ablk MSVP (MSVP + 4)) by (eapply ablk_sub; [exact M3| lia| lia]).
assert (ABT : ablk TLP (TLP + 4)) by (eapply ablk_sub; [exact T3| lia| lia]).
assert (HPs : forall a', in_fake LB a' -> aclient_addr CI LB SPV (shad a')) by (intros a' Ha'; apply cl_shadow; right; right; exact Ha').
pose proof H8 as [H8a H8b]. pose proof HM0 as [HM0a HM0b].
assert (OKC : rd_okA C).
{ unfold rd_okA. rewrite ESPA. unfold C; cbn [a_buf a_msv0 a_rt0 a_SP a_lo a_NC a_MSVP a_TLP a_BUF a_FF]. unfold RDA_CALLEE.
repeat split; assumption. }
assert (SHC : rd_shA C).
{ unfold rd_shA, C; cbn [a_m a_NC a_rt0 a_MSVP a_TLP a_BUF a_buf].
split; [exact (proj2 (fcellA_mg _ _ _ _ _ _ MG3 HPs FCN))|].
split; [exact (proj2 (fcellA_mg _ _ _ _ _ _ MG3 HPs FCM))|].
split; [exact (proj2 (fcellA_mg _ _ _ _ _ _ MG3 HPs FCT))|].
eapply (bufA_unpoisoned AI L RNG st (FB0 FF :: LB) m3); [exact AH3| | lia].
eapply bufA_mono; [eapply bufA_mg; [exact MG3| exact HPs| exact BFA]| intros b Hb; right; exact Hb]. }
assert (RNGC : rd_rngA C RNG).
{ unfold rd_rngA, C; cbn [a_lo a_SP a_NC a_rt0 a_MSVP a_TLP a_BUF a_buf].
split; [assumption|]. split; [eapply rng_sub'; [exact RSTK| clear - SPT; lia]|]. repeat (split; [assumption|]). assumption. }
assert (ARR3 : u8arr asegs m3 NC (u16s (map (Z_to_bv 64) rt0))).
{ eapply u8arr_mg; [exact MG3| exact ARR|]. rewrite u16s_length, length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ NC (2 * zlen rt0) HbN); cbn [ab_addr ab_size]; [exact N1| exact N2| clear - Ha; lia]. }
assert (HMSV3 : rw_cells asegs m3 MSVP [C4 (Z_to_bv 64 msv0)]).
{ eapply rw_cells_magree; [exact MG3| exact HMSV|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ MSVP 4 HbM); cbn [ab_addr ab_size]; [exact M1| exact M2| clear - Ha; lia]. }
assert (HTL3 : rw_cells asegs m3 TLP [C4 tl0]).
{ eapply rw_cells_magree; [exact MG3| exact HTL|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ TLP 4 HbT); cbn [ab_addr ab_size]; [exact T1| exact T2| clear - Ha; lia]. }
assert (HBUF3 : bytes_at asegs m3 BUF (map (Z_to_bv 8) buf)).
{ eapply bytes_at_magree; [exact MG3| exact HBUF|]. rewrite length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ BUF (zlen buf) HbB); [exact B1| exact B2| clear - Ha; lia]. }
pose proof (shullA_mg _ _ _ _ _ _ _ MG3 HPs HULL) as (hc & HFA & HFN & HbH & H1 & H2 & H3 & H4 & H5 & H6 & HW & HR).
assert (EH : shad (HFA + HFN) - shad HFA = HFN / 8) by (clear - H3 H4; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (HH : HFA <= NC /\ NC + 2 * zlen rt0 <= HFA + HFN /\ HFA mod 64 = 0 /\ (HFA + HFN) mod 64 = 0 /\ 0 <= HFA /\ HFA + HFN <= KEND).
{ split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [clear - H3 H4; Z.div_mod_to_equations; lia|]. split; [exact H5| exact H6]. }
pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC. unfold artcells in RTC.
destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
eapply evtF_cut.
{ eapply (rd_mainA C RNG OKC SHC RNGC rt msv tl n tl0 j48 HFA (HFA + HFN));
first [exact ARR3| exact HMSV3| exact HTL3| exact HBUF3| exact FRA3| exact STL3| exact MI3| exact GOT| exact RIC| exact SHB
| exact INI| exact LAY| exact REAL| exact RB| exact HH| rewrite EH; exact HW| rewrite EH; exact HR]. }
cbv beta. intros ms' (m4 & z6 & z10 & z12 & z13 & z14 & z15 & z16 & z17 & z19 & z23 & z30 & -> & INV).
destruct INV as (ARR4 & LNC4 & HBUF4 & HMSV4 & HTL4 & (j16 & FRM4) & STL4 & MU4 & WM4 & MI4).
clear C0 GOT RIC REAL SHB SUA INI LAY.
assert (AH4 : AHEAP AI L RNG st (FB0 FF :: LB) m4).
{ eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. unfold rd_WA. rewrite ESPA. unfold C; cbn [a_NC a_rt0 a_MSVP a_TLP].
constructor; [cbn; right; left; exists (mkABlock (ABFake cN) FAN FNN); split; [right; exact HbN| cbn; clear - N1 N2; lia]|].
constructor; [cbn; right; left; exists (mkABlock (ABFake cM) FAM FNM); split; [right; exact HbM| cbn; clear - M1 M2; lia]|].
constructor; [cbn; right; left; exists (mkABlock (ABFake cT) FAT FNT); split; [right; exact HbT| cbn; clear - T1 T2; lia]|].
constructor; [cbn; left; left; unfold RDA_CALLEE; clear - AR3 AR4; lia| constructor]. }
assert (MG4 : magree asegs (PAG AI LB SPV NC MSVP TLP rt0) m m4).
{ eapply magree_munch_step; [eapply magree_mono; [exact MG3| intros a HP; destruct HP as (Ha & _); exact Ha]| exact MU4| exact WM4|].
intros a HP. destruct HP as (Ha & HN & HM & HT). unfold rd_WA. rewrite ESPA. unfold C; cbn [a_NC a_rt0 a_MSVP a_TLP outside].
unfold RDA_CALLEE.
split; [exact HN|]. split; [exact HM|]. split; [exact HT|]. split; [| exact I].
intros Hr. exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH AR1 ltac:(clear - Hr AR2; lia) Ha). }
destruct (frame_WA C FF ABN (blk_sepF FF NC (2 * zlen rt0) FAN FNN N1 N2 (FFD _ HbN))
ABM (blk_sepF FF MSVP 4 FAM FNM M1 M2 (FFD _ HbM))
ABT (blk_sepF FF TLP 4 FAT FNT T1 T2 (FFD _ HbT))
FH (proj1 BSF) (proj2 BSF) ltac:(rewrite ESPA; unfold RDA_CALLEE; exact AR1) ltac:(rewrite ESPA; cbn [a_SP C]; exact AR2))
as (DS & DF & DR & DG).
pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU4 WM4 DS) as SHF4.
pose proof (rw_cells_transport _ _ _ _ _ _ FFC3 MU4 WM4 DF) as FFC4.
pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU4 WM4 DR) as FRB4.
assert (STG4 : stk asegs m4 (SPAz SPV + 56) (SPV + -104))
by (eapply stk_transport; [exact STG3| exact MU4| exact WM4| intros x Hx; left; apply DG; rewrite ESPA; exact Hx]).
destruct (rffhdr_split m4 FF (fflag L 0 FF) junk FFC4) as [FF04 FF564].
unfold rd_lstA. rewrite ESPA. unfold C; cbn [a_gp a_tp a_F a_fc a_SP a_FF a_NC a_MSVP a_TLP a_BUF a_lo a_rt0 a_buf a_msv0].
eapply (rd_close AI fflag FFLAG FREL L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV NC MSVP TLP lo FF rt0 rt msv tl n
(Z_to_bv 64 0x41b58ab3) (FRA_main C j16));
first [exact AH4| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MG4| exact MI4| exact SHF4
| exact FF04| exact FF564| exact FRB4| exact FRM4| reflexivity| exact STL4| exact STG4| exact BOT| exact RSTK| exact ARR4
| exact HMSV4| exact HTL4| exact LNC4| exact FCN| exact FCM| exact FCT| exact SP16| exact LO'| exact SPT].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="fflag FFLAG FREL SM0R"] Theorem rd_smallA : forall (L : alayout) (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
(SPV NC MSVP TLP BUF : Z) (p : aptr) (rt0 rt buf : list Z) (msv0 msv tl n lo : Z) (tl0 : word),
AHEAP AI L RNG st LB m ->
(forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
u8arr asegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
rw_cells asegs m MSVP [C4 (Z_to_bv 64 msv0)] -> rw_cells asegs m TLP [C4 tl0] ->
bytes_at asegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) ->
0 <= msv0 <= 255 -> zlen buf < 8 -> zlen rt0 <= 65536 ->
fcellA m LB NC (2 * zlen rt0) -> NC mod 8 = 0 -> shullA RNG m LB NC (2 * zlen rt0) ->
fcellA m LB MSVP 4 -> MSVP mod 4 = 0 -> fcellA m LB TLP 4 -> TLP mod 4 = 0 ->
In (mkABlock (ABHeap p) BUF (zlen buf)) LB ->
(NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
(MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - FSE_READ_STACK_A ->
SPV + 16 < al_top L -> SPV mod 16 = 0 ->
mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (nshad (2 * zlen rt0)) ->
rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 -> rng RNG TLP 4 -> rng RNG (shad TLP) 1 ->
evtF asegs RNG (fse_read_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 rt msv tl n lo m)
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
(Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom asegs)).
Proof.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF p rt0 rt buf
msv0 msv tl n lo tl0
AH NOF LBH ARR HMSV HTL HBUF FBY RN HM0 H8 HRT FCN N8 HULL FCM M4 FCT T4 HBB SNM SNT SMT ST BOT LO SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS.
pose proof atop_range as ATR.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
unfold FSE_READ_STACK_A in LO.
pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
Local Ltac2 Set LiaHints.tbl := fun () => "01f0?11910807144.5  11910871016.3  12656316497.4  1328287416.3   1353714310.281 13647548426.16 1387517820.4   14922313372.4  15045128145.32215173394556.4  15368781294.3  16216422631.27116244895032.7  16434987658.4  16815682600.3  1750090398.3   17835752075.2  1789991534.3   17986879152.4  18086183040.3  18359479861.3  19614730921.52 19614731429.40 20935316357.5  21469252055.27121821313523.2  22706556809.8  22706556809.9  2476896450.2   24869205307.30525351589538.1  25453336226.2  25464949579.5  25521682176.3  2570613437.4   26507246098.8  26822851774.2  28573892092.10 29126943203.16 29199660172.11 29782367974.4  29788642184.28229788740056.31429790736738.27129790753113.25429926317891.5  29971687518.5  30619540277.2  30682412847.4  31281399278.27231283498337.27132100692746.3  32775280396.3  34329646136.17 34339027045.6  34341079406.5  34345818009.3  3456505237.7   34750417625.25434894035453.4  35275475455.16 35507916949.2803668948108.323 37280869577.4  3748619754.121 37944157234.5  38522995511.31 38791659505.7  38807667984.13 38920596583.2  40161347186.13 4030593391.322 4032691428.7   40573248581.27140575347914.27241597280153.3  41690886119.2  42878255082.4  43083164090.2  44603709907.4  46023873379.3  46028828505.2  4638012616.4   46607015759.1  47365148506.3  48785955651.27149507265123.5  49989610512.16 50214402296.13 51451730144.32251755794159.11852539013619.2  53144815218.13 53880447441.5  53882577365.6  54847176891.3  54847178794.3  56185111867.4  58441668457.2  59312301922.5  59890914555.2  60477223755.32661524216116.3  63368326909.32263368326909.32363698612035.4  64025876735.16 6431003755.1   65412001441.13 66151427842.16 66718732212.1  67510821534.2  67642815997.3237714730308.3   8140018179.23  8952163448.5   936935958.4    9606237278.2   00000100600700<00]00a00j01001Q01V01[02<02I02M02Q02U02Y02^02c02h02l02m02n03703X03Y03j04;04A04b04c04h04l05005405J05K05`05m06906:06[07<07]08>08G08K08Q08R09309T09Y09]09j09k0:30:70:D0:e0:j0;70;X0<90<C0<[0<_0=:0=H0=S0=Y0=d0>G0>T0?50?V0?Z0?[0?c0?i0@20@70@=0@A0@B0@F0@k0@l0A40A80AY0A\0Aa0Al0B10B20B60B:0B@0BE0BN0BR0C30C80CY0D:0D?0DL0DM0DQ0Dh0Di0Dj0EK0EP0Ec0F10F:0F?FS3HB8SS3HB8S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S2HXS3SPT3LY3S4BR1dS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3DNFS3DMFS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3BOT2LO4SPABS2T2S2M1S2HaS2H8S3DTFS3BOTS3SPTS2T1FFS3AR33AR4S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5SS3ATR3AR14BSF22HxS3ATR3LOC4BSF22HxS4BSF2S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5SS3FHdS2HaS2LOS2HaS3ATR3AR13AR23FHc4BSF2SS3ATR3AR13FHc4BSF22HxS3AR14ABNc2HXS2FH1H2H02H4SS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3AR13AR2S2N2S4BSF1SS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3HB8S2HrS3F641H2H02H4FS3NLE2N1S2HaS3BOT2LO4SPABS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3AR1S3AR14ABTc2HXS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3SPT4SPABS3ATR3LY13LY43AR23AR32HcS2N2S3F641H2H02H42H52H93H103H14S3ATR4BR1c3HL6S3DNF2D02DKS4BR1aS3DMF2D02DKS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL51HS3ATR4BSF22HAS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S2HaSS3AR22HrS4BR1bS2LO4SPABS3LO8S4SPABS2M2SS2HaS3LRT4ABNb4ABMb4ABTb3FHb3FHd4BR1b3HL5SS3SPK2HYS2D0S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S1HS3AR2S3DTF2D02DKS3DFBFS2HrS2HaS4STOPS3AR2S3AR13AR2S2H8S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3N1'S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3LB'S3AR14ABMc2HXSS2DKS5SPA321H2H02H43BR43F64SSS3LRT4ABNb4ABMb4ABTb3FHb4BR1b3HL5S3HB8S3F641H2H02H42H52H9S3SPT3LY34SPABS3HM03HM1S3AR2".
assert (AR1 : ATOP <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR2 : SPAz SPV + 160 <= SPV) by (clear - SPAB; lia).
assert (AR3 : ATOP + 4096 <= SPAz SPV - 2224) by (clear - LO BOT SPAB; lia).
assert (AR4 : SPAz SPV + 56 <= 2^47) by (clear - SPAB SPT LY3; lia).
assert (LOC : ATOP <= lo) by (clear - BOT; lia).
assert (LO8 : lo <= SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; clear - LO; lia).
assert (LOI : lo <= SPAz SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; clear - LO SPAB; lia).
assert (SPTI : SPAz SPV + 16 < al_top L) by (clear - SPAB SPT; lia).
assert (SPI16 : SPAz SPV mod 16 = 0) by (clear - SPA32; Z.div_mod_to_equations; lia).
assert (STOP : SPV <= al_top L) by (clear - SPT; lia).
assert (SPK : SPV + 16 < KEND) by (clear - SPT LY3; unfold KEND; lia).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
boxH SNM. boxH SNT. boxH SMT.
set (hb := zlen buf) in *. set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))).
assert (HB8 : 0 <= hb < 8) by (subst hb; clear - H8; lia).
assert (HB64 : 0 <= hb < 2^64) by (clear - HB8; lia).
assert (RB : read_ncount_body8 buf' (msv0 + 1) rt0 = Ok (rt, msv, tl, n) /\ n <= hb).
{ pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'. fold hb in RN'.
replace (hb <? 8) with true in RN' by (symmetry; apply Z.ltb_lt; clear - HB8; lia). fold buf' in RN'.
destruct (read_ncount_body8 buf' (msv0 + 1) rt0) as [[[[nc1 msv1'] tl1] cs]| | |]; cbn [bind] in RN'; try discriminate RN'.
destruct (Z.ltb_spec hb cs); [discriminate RN'|]. injection RN' as <- <- <- <-. split; [reflexivity| lia]. }
destruct RB as [RB NLE].
assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; clear - H8; lia).
assert (FB' : Forall (fun c => 0 <= c < 256) buf').
{ subst buf'. apply Forall_app. split; [exact FBY|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia. }
destruct (read_body8_inv buf' (msv0 + 1) rt0 rt msv tl n ltac:(clear - LB'; lia) RB) as (HM1 & _).
assert (NR : 1 <= n /\ length rt = length rt0).
{ destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; clear - LB'; lia)
ltac:(unfold FseNCount.Zlength; clear - HM1 HM0; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & L2 & _ & _ & _ & N2 & _) | (e & E2)];
rewrite RB in E2; [injection E2 as <- <- <- <-; split; [clear - N2; lia| exact L2]| discriminate E2]. }
destruct NR as [N1 LRT].
pose proof FCN as [(cN & FAN & FNN & HbN & N1' & N2 & N3 & N5) _].
pose proof FCM as [(cM & FAM & FNM & HbM & M1 & M2 & M3 & M5) _].
pose proof FCT as [(cT & FAT & FNT & HbT & T1 & T2 & T3 & T5) _].
assert (ABN : ablk NC (NC + 2 * zlen rt0)) by (eapply ablk_sub; [exact N3| clear - N1'; lia| clear - N2; lia]).
assert (ABM : ablk MSVP (MSVP + 4)) by (eapply ablk_sub; [exact M3| clear - M1; lia| clear - M2; lia]).
assert (ABT : ablk TLP (TLP + 4)) by (eapply ablk_sub; [exact T3| clear - T1; lia| clear - T2; lia]).
pose proof (ablk_lin _ _ ABN) as (ABNa & ABNb & ABNc & ABNd). pose proof (ablk_lin _ _ ABM) as (ABMa & ABMb & ABMc & ABMd).
pose proof (ablk_lin _ _ ABT) as (ABTa & ABTb & ABTc & ABTd).
assert (HPs : forall a', in_fake LB a' -> aclient_addr CI LB SPV (shad a')) by (intros a' Ha'; apply cl_shadow; right; right; exact Ha').
lazymatch goal with |- evtF _ _ ?P _ =>
eapply evtF_cut; [eapply (rd_open AI fflag rng_fs SM0R L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m st LB SPV NC MSVP TLP BUF hb lo (evtF asegs RNG P));
[first [assumption| exact (fake0_le1_none LB NOF)] .. | ]
| intros ms' Hms; exact Hms ] end.
intros FF m3 j48 junk x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x28 x29 x30 x31
F64 FH FC RFF RSFF FFD AH3 MG3 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3.
replace (7 <? hb) with false by (symmetry; apply Z.ltb_ge; clear - HB8; lia). cbv iota.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (clear - FH; apply ablk_lin in FH; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
destruct BSF as [BSF1 BSF2].
destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 (or_intror HBB))
as (HBN & (BR1 & BR2 & BR3 & BR4) & RBUF & RSB & SHBB & WRB & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RLR & RLW)).
pose proof (ablk_lin _ _ BR1) as (BR1a & BR1b & BR1c & BR1d).
destruct (block_hullR RNG m3 BUF hb RLO RHI ltac:(clear - HB8; lia) RL1 RL2 RL3 RL4 ltac:(unfold AIMG_HI in BR1a; clear - BR1a; lia) RLR RLW)
as (HR1 & HW1 & HL1 & HL2 & HL3 & HL4 & HL5 & HL6).
assert (UB3 : unpoisoned m3 BUF (BUF + hb))
by (apply ablock_unpoisonedR; [exact SHBB| clear - BR4; Z.div_mod_to_equations; lia| clear - BR1b; lia| clear - HB8; lia| clear - BR1d; lia]).
assert (HBUF3 : bytes_at asegs m3 BUF (map (Z_to_bv 8) buf)).
{ eapply bytes_at_magree; [exact MG3| exact HBUF|]. rewrite length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ BUF hb HBB); cbn [ab_addr ab_size]; clear - Ha; lia. }
pose proof (AI_rtcells AI _ _ _ _ _ AH3) as RTC. unfold artcells in RTC.
destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
pose proof (FFD _ HBB) as DFB. cbn [ab_addr ab_size] in DFB.
eapply (rd_small1 gp tp FR fc SPV lo);
first [exact HB8| exact FBY| exact HBUF3| exact FFC3| exact SHF3| exact MI3| exact STL3| exact GOT| exact RIC| exact SHB| exact INI
| exact LAY| exact REAL| exact UB3| exact FH| exact FC| exact F64| exact DFB| exact BR1| exact RFF| exact RSFF| exact RBUF
| exact SP16| exact RI| exact HW1| exact HR1| exact LOC| exact SPK
| apply ablk_app_blk; [exact BR1| clear - HB8; lia]
| split; [exact HL1|]; split; [exact HL2|]; split; [exact HL3|]; split; [exact HL4|]; split; [exact HL5| unfold KEND; clear - HL6 BR1c ATR; lia]
| eapply rng_sub'; [exact RSTK| clear - STOP; lia]
| unfold RD8_STACK, SM0R_STACK in LO8; clear - LO8; lia
| lazymatch goal with |- BUF + _ <= FF \/ FF + 64 <= BUF => clear - DFB; lia end
| idtac].
intros m5 rs j16 y5 y6 y7 y16 y17 y28 y29 y30 y31 MU5 WM5 MI5 STL5 FFC5 SHF5 HBUF5.
clear C0 GOT RIC REAL SHB SUA INI LAY.
assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
{ eapply (AI_frame AI); [exact AH3| exact MU5| exact WM5|].
constructor; [cbn; left; left; clear - AR3 AR4; lia|].
constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
change (2 ^ 3) with 8; unfold ASHOFF; clear - F64 FHb; Z.div_mod_to_equations; lia]| constructor]. }
assert (MG5 : magree asegs (aclient_addr CI LB SPV) m m5).
{ eapply magree_munch_step; [exact MG3| exact MU5| exact WM5|]. intros a Ha. cbn.
split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV - 2224) a HCI HCI0 LBH AR1 ltac:(clear - Hr AR2; lia) Ha)|].
split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(clear - AR1 AR2; lia) LBH FFD ltac:(clear - Hr; lia) Ha)|].
split; [intros Hr; refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(clear - AR1 AR2; lia) LBH FFD _ Ha);
unfold shad, ASHOFF; clear - Hr; lia| exact I]. }
destruct (rffhdr5_split m5 FF rs _ j16 (fflag L 0 FF) FFC5) as (FF05 & FB5 & FF565).
pose proof rd_body8A as RB8. unfold rd_body8A_stmt in RB8.
assert (IARR : u8arr asegs m5 NC (u16s (map (Z_to_bv 64) rt0))).
{ eapply u8arr_mg; [exact MG5| exact ARR|]. rewrite u16s_length, length_map.
intros a Ha. apply (cl_range_block CI LB SPV _ NC (2 * zlen rt0) HbN); cbn [ab_addr ab_size]; [exact N1'| exact N2| clear - Ha; lia]. }
assert (IHMSV : rw_cells asegs m5 MSVP [C4 (Z_to_bv 64 msv0)]).
{ eapply rw_cells_magree; [exact MG5| exact HMSV|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ MSVP 4 HbM); cbn [ab_addr ab_size]; [exact M1| exact M2| clear - Ha; lia]. }
assert (IHTL : rw_cells asegs m5 TLP [C4 tl0]).
{ eapply rw_cells_magree; [exact MG5| exact HTL|]. cbn [cells_size csize Nat.add].
intros a Ha. apply (cl_range_block CI LB SPV _ TLP 4 HbT); cbn [ab_addr ab_size]; [exact T1| exact T2| clear - Ha; lia]. }
assert (IHBUF : bytes_at asegs m5 (FF + 32) (map (Z_to_bv 8) buf')).
{ destruct FB5 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
assert (ILE : fake0_le1 (FB0 FF :: LB)) by (apply fake0_le1_cons; exact NOF).
assert (ILBH : forall b, In b (FB0 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b)).
{ intros b [<-|Hb]; [exact FH| exact (LBH b Hb)]. }
assert (INCL : forall b, In b LB -> In b (FB0 FF :: LB)) by (intros b Hb; right; exact Hb).
assert (IFCN : fcellA m5 (FB0 FF :: LB) NC (2 * zlen rt0)) by (eapply fcellA_mono; [eapply fcellA_mg; [exact MG5| exact HPs| exact FCN]| exact INCL]).
assert (IFCM : fcellA m5 (FB0 FF :: LB) MSVP 4) by (eapply fcellA_mono; [eapply fcellA_mg; [exact MG5| exact HPs| exact FCM]| exact INCL]).
assert (IFCT : fcellA m5 (FB0 FF :: LB) TLP 4) by (eapply fcellA_mono; [eapply fcellA_mg; [exact MG5| exact HPs| exact FCT]| exact INCL]).
assert (IHULL : shullA RNG m5 (FB0 FF :: LB) NC (2 * zlen rt0)) by (eapply shullA_mono; [eapply shullA_mg; [exact MG5| exact HPs| exact HULL]| exact INCL]).
assert (IBFA : bufA m5 (FB0 FF :: LB) (FF + 32) (zlen buf')).
{ right. rewrite LB'. split.
- exists 0, FF, 64. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact FH| clear - F64; Z.div_mod_to_equations; lia].
- apply c1z_unpoisonedR; [| clear - F64; Z.div_mod_to_equations; lia| lia| lia| lia].
replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + 4).
+ exact (rffsh0_byte4 _ _ SHF5).
+ rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F64. Z.div_mod_to_equations. lia. }
assert (IBBK : ablk (FF + 32) (FF + 32 + zlen buf')) by (rewrite LB'; eapply ablk_sub; [exact FH| lia| lia]).
assert (IB8 : (FF + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
pose proof (blk_sepF FF NC (2 * zlen rt0) FAN FNN N1' N2 (FFD _ HbN)) as DNF.
pose proof (blk_sepF FF MSVP 4 FAM FNM M1 M2 (FFD _ HbM)) as DMF.
pose proof (blk_sepF FF TLP 4 FAT FNT T1 T2 (FFD _ HbT)) as DTF.
assert (ISNB : NC + 2 * zlen rt0 <= FF + 32 \/ FF + 32 + zlen buf' <= NC) by (rewrite LB'; clear - DNF; lia).
assert (ISMB : MSVP + 4 <= FF + 32 \/ FF + 32 + zlen buf' <= MSVP) by (rewrite LB'; clear - DMF; lia).
assert (ISTB : TLP + 4 <= FF + 32 \/ FF + 32 + zlen buf' <= TLP) by (rewrite LB'; clear - DTF; lia).
boxH DNF. boxH DMF. boxH DTF. boxH ISNB. boxH ISMB. boxH ISTB.
assert (IH8 : 8 <= zlen buf' <= 65536) by (rewrite LB'; lia).
assert (IRBf : rng RNG (FF + 32) (zlen buf')) by (rewrite LB'; eapply rng_sub'; [exact RFF| lia]).
assert (IRBS : rng RNG (shad (FF + 32)) (nshad (zlen buf'))).
{ rewrite LB'. eapply rng_sub'; [exact RSFF|]. rewrite !shad_div. unfold nshad. rewrite Z.shiftr_div_pow2 by lia.
change (2^3) with 8. clear - F64 FHb. Z.div_mod_to_equations. lia. }
replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen buf')) by (rewrite LB'; reflexivity).
eapply evtF_cut.
{ eapply (RB8 L RNG (Z_to_bv 64 0x81ef4) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) (Z_to_bv 64 0) y16 y17
(Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb) (Z_to_bv 64 (FF + 32))
(Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) s11 y28 y29 y30 y31 FR fc m5 st (FB0 FF :: LB)
(SPAz SPV) NC MSVP TLP (FF + 32) rt0 rt buf' msv0 msv tl n lo tl0
AH5 ILE ILBH IARR IHMSV IHTL IHBUF FB' RB HM0 IH8 HRT IFCN N8 IHULL IFCM M4 IFCT T4 IBFA IBBK IB8 SNM SNT ISNB SMT ISMB ISTB
STL5 BOT LOI SPTI SPI16 MI5 TP RSTK RI RFS RNc RNS RM RMS RT RTS IRBf IRBS). }
cbv beta. intros ms' PO.
destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m7 & -> & MI7 & ST7 & MG7 & AH7 & ARR7 & HMSV7 & HTL7).
rd_retlit.
assert (SPAV : SPAz SPV <= SPV) by (clear - AR2; lia).
assert (SHF7 : rw_cells asegs m7 (Z.shiftr FF 3 + 2147450880) RFFSH0).
{ eapply rw_cells_magree; [exact MG7| exact SHF5|]. change (Z.of_nat (cells_size RFFSH0)) with 8.
intros a Ha. apply (pag_shadowR AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 0 FF 64 (or_introl eq_refl));
[clear - F64; Z.div_mod_to_equations; lia| reflexivity| exact FHb| clear - FHd; lia| exact ABN| exact ABM| exact ABT|].
change (64 / 8) with 8. unfold shad, ASHOFF. clear - Ha. lia. }
eapply (rd_small2 gp tp FR fc SPV lo);
first [exact SHF7| exact MI7| exact FH| exact F64| exact RSFF| exact SP16| exact LOC| exact SPK
| eapply rng_sub'; [exact RSTK| clear - STOP; lia]
| unfold RD8_STACK, SM0R_STACK in LO8; clear - LO8; lia
| lazymatch goal with |- 0 <= n <= hb => clear - N1 NLE; lia end
| lazymatch goal with |- hb < 8 => clear - HB8; lia end
| idtac].
intros m6 z10 z12 MU6 WM6 MI6 SHF6.
assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
{ eapply (AI_frame AI); [exact AH7| exact MU6| exact WM6|].
constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
change (2 ^ 3) with 8; unfold ASHOFF; clear - F64 FHb; Z.div_mod_to_equations; lia]| constructor]. }
assert (MG6 : magree asegs (PAG AI LB SPV NC MSVP TLP rt0) m m6).
{ eapply magree_trans; [eapply magree_mono; [exact MG5| intros a HP; destruct HP as (Ha & _); exact Ha]|].
eapply magree_munch_step; [eapply magree_mono; [exact MG7|]| exact MU6| exact WM6|].
- intros a HP. destruct HP as (Ha & HN & HM & HT). split; [eapply aca_monoA; [exact Ha| exact INCL| exact SPAV]|].
split; [exact HN|]. split; [exact HM| exact HT].
- intros a HP. destruct HP as (Ha & _). cbn. split; [| exact I].
intros Hr. refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(clear - AR1 AR2; lia) LBH FFD _ Ha).
unfold shad, ASHOFF. clear - Hr. lia. }
unfold bx in DNF, DMF, DTF.
assert (PFF : forall k, 0 <= k -> forall d, 0 <= d -> d + k <= 64 ->
forall a, FF + d <= a < FF + d + k -> PAG AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 a).
{ intros k K0 d D0 DK. apply (pag_blockR AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 (FB0 FF) (FF + d) k (or_introl eq_refl));
cbn [ab_addr ab_size]; clear - K0 D0 DK DNF DMF DTF; lia. }
assert (PST : forall X Y, SPAz SPV <= X -> Y <= SPV -> forall a, X <= a < Y -> PAG AI (FB0 FF :: LB) (SPAz SPV) NC MSVP TLP rt0 a).
{ intros X Y HX HY. apply pag_stackR; clear - HX HY SPK AR1 ABNc ABMc ABTc; unfold KEND in SPK; lia. }
assert (DW6 : forall A k, ablk A (A + k) -> disjoint_from [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] A k).
{ intros A k HA. cbn [disjoint_from]. split; [| exact I].
destruct (app_vs_shadow A k (Z.shiftr FF 3 + 2147450880 + 4) 1 HA ltac:(clear - BSF1; lia) ltac:(clear - BSF2; lia)); lia. }
assert (DW6s : forall A k, ATOP <= A -> disjoint_from [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] A k).
{ intros A k HA. cbn [disjoint_from]. split; [| exact I]. clear - HA BSF2 ATR. lia. }
assert (FF06 : rw_cells asegs m6 FF [C8 (Z_to_bv 64 0x41b58ab3)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| rewrite zsize_c8; apply DW6; eapply ablk_sub; [exact FH| clear; lia| clear; lia]].
eapply rw_cells_magree; [exact MG7| exact FF05|]. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 0x41b58ab3)])) with 8.
intros a Ha. apply (PFF 8 ltac:(lia) 0 ltac:(lia) ltac:(lia)). clear - Ha. lia. }
assert (FF566 : rw_cells asegs m6 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| rewrite zsize_c8; apply DW6; eapply ablk_sub; [exact FH| clear; lia| clear; lia]].
eapply rw_cells_magree; [exact MG7| exact FF565|]. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (fflag L 0 FF))])) with 8.
intros a Ha. apply (PFF 8 ltac:(lia) 56 ltac:(lia) ltac:(lia)). clear - Ha. lia. }
assert (FRB6 : rw_cells asegs m6 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| apply DW6s; clear - AR1 AR2; lia].
eapply rw_cells_magree; [exact MG7| |].
- eapply rw_cells_transport; [exact FRB3| exact MU5| exact WM5|]. change (Z.of_nat (cells_size (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))) with 104.
cbn [disjoint_from]. clear - AR1 AR2 FHc BSF2 ATR. lia.
- change (Z.of_nat (cells_size (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))) with 104.
apply PST; clear - AR2; lia. }
assert (FRA6 : rw_cells asegs m6 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| apply DW6s; clear - AR1; lia].
eapply rw_cells_magree; [exact MG7| |].
- eapply rw_cells_transport; [exact FRA3| exact MU5| exact WM5|]. change (Z.of_nat (cells_size [CB 48 j48; C8 (Z_to_bv 64 FF)])) with 56.
cbn [disjoint_from]. clear - AR1 AR2 FHc BSF2 ATR. lia.
- change (Z.of_nat (cells_size [CB 48 j48; C8 (Z_to_bv 64 FF)])) with 56. apply PST; clear - AR2; lia. }
assert (STG6 : stk asegs m6 (SPAz SPV + 56) (SPV + -104)).
{ eapply stk_transport; [| exact MU6| exact WM6| intros x Hx; left; cbn; clear - Hx AR1 BSF2 ATR; lia].
eapply stk_magree; [exact MG7| | apply PST; clear - AR2; lia].
eapply stk_transport; [exact STG3| exact MU5| exact WM5| intros x Hx; left; cbn; clear - Hx AR1 AR2 FHc BSF2 ATR; lia]. }
assert (ST6 : stk asegs m6 lo (SPAz SPV)).
{ eapply stk_transport; [exact ST7| exact MU6| exact WM6| intros x Hx; left; cbn; clear - Hx LOC BSF2 ATR; lia]. }
assert (LNC : Z.of_nat (length (u16s (map (Z_to_bv 64) rt))) = 2 * zlen rt0) by (rewrite u16s_length, length_map, LRT; lia).
assert (ARR6 : u8arr asegs m6 NC (u16s (map (Z_to_bv 64) rt))).
{ eapply u8arr_transport; [exact ARR7| exact MU6| exact WM6|]. rewrite LNC. apply DW6. exact ABN. }
assert (HMSV6 : rw_cells asegs m6 MSVP [C4 (Z_to_bv 64 msv)]) by (eapply rw_cells_transport; [exact HMSV7| exact MU6| exact WM6| rewrite zsize_c4; apply DW6; exact ABM]).
assert (HTL6 : rw_cells asegs m6 TLP [C4 (Z_to_bv 64 tl)]) by (eapply rw_cells_transport; [exact HTL7| exact MU6| exact WM6| rewrite zsize_c4; apply DW6; exact ABT]).
eapply (rd_close AI fflag FFLAG FREL L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m6 st LB SPV NC MSVP TLP lo FF rt0 rt msv tl n
(Z_to_bv 64 0x41b58ab3) [CB 48 j48; C8 (Z_to_bv 64 FF)]);
first [exact AH6| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact MG6| exact MI6| exact SHF6
| exact FF06| exact FF566| exact FRB6| exact FRA6| reflexivity| exact ST6| exact STG6| exact BOT| exact RSTK| exact ARR6
| exact HMSV6| exact HTL6| exact LRT| exact FCN| exact FCM| exact FCT| exact SP16| exact LO8| exact SPT].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="fflag FFLAG FREL SM0R"] Theorem fse_read_proofA : fse_read_stmtA AI rng_fs.
Proof.
unfold fse_read_stmtA.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF p
rt0 rt buf msv0 msv tl n lo tl0
AH NOF LBH ARR HMSV HTL HBUF FBY RN HM0 HBL HRT FCN N8 HULL FCM M4 FCT T4 HBB SNM SNT SNB SMT SMB STB ST BOT LO SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS E0 E1 E2 E3 E4.
subst a0 a1 a2 a3 a4.
unfold AFSE_RD_ENTRY.
zstep. zstep.
destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
- eapply (rd_smallA L RNG ra gp tp t0 t1 t2 s0 s1 _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF p
rt0 rt buf msv0 msv tl n lo tl0
AH NOF LBH ARR HMSV HTL HBUF FBY RN HM0 LT HRT FCN N8 HULL FCM M4 FCT T4 HBB SNM SNT SMT ST BOT LO SPT SP16 MI TP
RSTK RI RFS RNc RNS RM RMS RT RTS).
- assert (RB : read_ncount_body8 buf (msv0 + 1) rt0 = Ok (rt, msv, tl, n)).
{ unfold read_ncount in RN. unfold FseNCount.Zlength in RN.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25521682176.3 53811710888.3 54941529998.2 66151427842.1600000400<00@00MS2LOS3HBL2GES2GES3BR41H2H02H4".
replace (zlen buf <? 8) with false in RN by (symmetry; apply Z.ltb_ge; clear - GE; lia). exact RN. }
destruct (AI_block AI _ _ _ _ _ _ _ _ AH HBB) as (HBN & (BR1 & BR2 & BR3 & BR4) & RBUF & RSB & _).
assert (BFA : bufA m LB BUF (zlen buf)) by (left; exists p, BUF, (zlen buf); split; [exact HBB| split; apply Z.le_refl]).
assert (B8 : BUF mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
assert (LO8 : lo <= SPV - RD8_STACK) by (unfold RD8_STACK, SM0R_STACK; unfold FSE_READ_STACK_A in LO; clear - LO; lia).
assert (H8 : 8 <= zlen buf <= 65536) by (clear - GE HBL; lia).
eapply (rd_body8A L RNG ra gp tp t0 t1 t2 s0 s1 _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF
rt0 rt buf msv0 msv tl n lo tl0
AH (fake0_le1_none LB NOF) LBH ARR HMSV HTL HBUF FBY RB HM0 H8 HRT FCN N8 HULL FCM M4 FCT T4 BFA BR1 B8
SNM SNT SNB SMT SMB STB ST BOT LO8 SPT SP16 MI TP RSTK RI RFS RNc RNS RM RMS RT RTS RBUF RSB).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
End CANSEC1.
