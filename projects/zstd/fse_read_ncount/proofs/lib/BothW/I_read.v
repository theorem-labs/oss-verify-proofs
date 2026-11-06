(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells ShadowTac F_syscalls F_tryinit F_rip.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Section CANSEC1. Context {rc : runConstT}.
Definition read_i_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
(a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ match a with
| RdErr e => rw_cells bsegs m' B [CB n junk]
/\ rw_cells bsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
| RdData bs => rw_cells bsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
/\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
end.
Section Proofs.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
(fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z).
Notation B := (bv_unsigned a1).
Notation W := [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (errno_addr tp, errno_addr tp + 4)]%Z.
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis LAY : rt_layout m.
Hypothesis REAL : rt_real_read m.
Hypothesis DST : rw_cells bsegs m B [CB (Z.to_nat count) junk].
Hypothesis ERR : rw_cells bsegs m (errno_addr tp) [C4 errv].
Hypothesis A0 : a0 = Z_to_bv 64 fd.
Hypothesis A2 : a2 = Z_to_bv 64 count.
Hypothesis FD : (3 <= fd < 2^32)%Z.
Hypothesis CNT : (1 <= count <= 16777216)%Z.
Hypothesis BHI : (0x5f7000 <= B \/ (0x5c4b90 <= B /\ B + count <= 0x5d4b90 /\ B + count <= errno_addr tp))%Z.
Hypothesis SEPD : (B + count <= lo)%Z.
Hypothesis SEPE : (0xa3740 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f7000)%Z.
Hypothesis TP : (164 <= bv_unsigned tp)%Z.
Hypothesis APPD : app_blk B (B + count).
Hypothesis UDST : unpoisoned m B (B + count).
Hypothesis R2 : (RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
Hypothesis WR2 : wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RERR : rng RNG (errno_addr tp) 4.
Hypothesis RD : rng RNG B count.
Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Notation POST := (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m).
Definition INV2 (bs : list byte) (mc : word -> option byte) : Prop :=
(exists jk, rw_cells bsegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
/\ stk bsegs mc lo (bv_unsigned sp + -2128)
/\ munch W m mc
/\ wmono bsegs m mc /\ mem_inv bsegs mc
/\ rt_got mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_read mc
/\ unpoisoned mc B (B + count)
/\ wr_at bsegs mc (shad RLO2) (shad RHI2 - shad RLO2)
/\ rw_cells bsegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
/\ rw_cells bsegs mc (errno_addr tp) [C4 errv]
/\ (length bs <= Z.to_nat count)%nat.
Definition BND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 1 <= count <= 16777216
/\ 0x5c4b90 <= B /\ (0x5f7000 <= B \/ B + count <= 0x5d4b90 /\ B + count <= errno_addr tp) /\ B + count <= lo /\ B + count + 8 <= KEND
/\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
/\ 0 <= Z.shiftr B 3 < 2^44
/\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
/\ RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
/\ 0xa3740 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f7000)%Z.
#[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BND_ok : BND.
Proof.
unfold BND. destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
pose proof R2 as R2'. unfold sf_hide in R2'.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>29786661831.75000001S".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac acc_facts Bf ::= pose proof BND_ok as Bf; unfold BND, KHIGH, KEND in Bf.
Definition BL : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 1 <= count <= 16777216 /\ 0x5c4b90 <= B /\ (0x5f7000 <= B \/ B + count <= 0x5d4b90 /\ B + count <= errno_addr tp) /\ B + count <= lo
/\ B + count + 8 <= 2^47 /\ 0 <= Z.shiftr B 3 < 2^44
/\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
/\ 0xa3740 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f7000)%Z.
#[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62898626424.7200000IS2LO3CNT3BHI4SEPD4SEPE2Bf".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac inv_open H :=
let jk := fresh "jk" in
destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21 & BUF1 & ERR1 & LENB).
Ltac prep IV :=
pose proof IV as IV0; inv_open IV;
let Bl := fresh "BL" in pose proof BL_ok as Bl; unfold BL in Bl;
assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in ERR; change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
#[using="ST LO KLO CNT BHI SEPD SEPE APPD UDST R2 WR2"] Lemma inv2_of : forall bs mc jk,
rw_cells bsegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk bsegs mc lo (bv_unsigned sp + -2128) ->
munch W m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
rt_got mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_read mc ->
rw_cells bsegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] ->
rw_cells bsegs mc (errno_addr tp) [C4 errv] -> (length bs <= Z.to_nat count)%nat ->
INV2 bs mc.
Proof.
intros bs mc jk FR ST1 MU1 WM1 MI1 G1 G3 G4 G5 G6 BUF1 ERR1 LENB. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf.
split; [exists jk; exact FR|]. repeat (split; [assumption|]).
assert (SS : (shad (B + count - 1) + 1 <= 17594333495296 /\ 2147450880 <= shad B /\
(B + count <= shad B \/ shad (B + count - 1) + 1 <= B))%Z).
{ pose proof APPD as [_ AD]. unfold KLOW, KHIGH, KEND in AD. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0020?26494383029.89 38818841286.13100000G00fS3CNT3BHI2R24LENB2Bf2SSS3CNT3BHI4LENB2Bf2AD1H2H02H42H5".
lia. }
split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. lia. }
split. { eapply wr_at_transport; eassumption. }
repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO CNT BHI SEPD SEPE APPD R2 RSTK"] Lemma LX : forall bs mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
INV2 bs mc ->
evtF bsegs RNG (POST (RdData bs) RNG)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x44574) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00@0?15498737820.1181807322596.118 25820099228.11928053229631.11035378896924.11835854634524.1193602932068.118 37031752369.11046703417572.11849475153977.11150221378407.11752415237221.11958390049052.12066138656668.1196922740008.110 7944451815.117 00000600<00B00H00N00T00Z00d00j01401:01@01F01L01U01[S4LENBS4LENBS4LENBS4LENBS4LENBS4LENBS4LENBS3CNT4LENBS4LENBS4LENB3BL0S4LENBS4LENBS4LENBS4LENBS2LO4LENBS4LENB".
prep IV.
do 9 zstep.
release_frame FR ST1 (bv_unsigned sp). unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO CNT BHI SEPD SEPE APPD R2 RSTK RSH2"] Lemma LSL : forall bs mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
Z.to_nat (shad (B + Z.of_nat (length bs) - 1) - c) = k -> (shad B <= c < shad (B + Z.of_nat (length bs) - 1))%Z ->
evtF bsegs RNG (POST (RdData bs) RNG)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
(Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x446d8) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00<0?13708355367.11613732943226.11624120772675.11640339170391.12144092989940.12157132210400.11457930470673.11159308585478.11159308627018.1  60888476447.1166732576738.142 6922740008.110 00000@00]01701R01S01_01o02?02C02Z03;03GS3CNT4LENB2Hk2HcS3CNT3BHI4LENB3BL02Hk2Hc2SL1KS3CNT4LENB3BL02SM2Hk2Hc2SLS3CNT3BHI4LENB3BL02SM2Hk2HcFS4LENB2Hk2HcS3CNT4LENB2Hk2HcS3CNT4LENB2Hk2HcS2K'S3CNT4LENB3BL02SM2Hk2HcS3CNT3BHI4LENB2N13BL02Hk2Hc2H42H5S2LO4LENB2Hk".
prep IV.
pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
assert (SL : (shad (B + Z.of_nat (length bs) - 1) = 2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)%Z)
by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd bsegs mc B (B + count) c UD1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO CNT BHI SEPD SEPE APPD R2 RSTK RSH2"] Lemma LSS : forall bs mc x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
evtF bsegs RNG (POST (RdData bs) RNG)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
(Z_to_bv 64 (2147450880 + Z.shiftr B 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3))
(Z_to_bv 64 (B + Z.of_nat (length bs) + -1)) x14 x15 x16 x17
x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x446bc) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00D0?15389206808.13019033648638.13419482125347.12424122881528.11424991237561.12428034943372.17628442431488.13429782203372.12029784416728.11436641402764.10943610543400.10946022211192.15652076332689.12052523015483.12253364399459.10853510313881.12457930470673.10759308629082.1  59949010196.1096922740008.106 00000900B00[00e00k01X01n02402:02D02J03<03Q03W03`03f04004404=04FS4LENB2H0S4LENB2H0S3CNT3BHI4LENB2N13BL03CK2S4LENB3BL0S4LENBS3CNT3BHI4LENB2N13BL01B1H2H02H42H52H93H103H34S3CNT3BHI4LENB3BL03CK2S4LENBS4LENBS3CNT4LENBS4LENBS3CNT3BHI4LENB2N13BL02K61H2H02H42H52H93H103H143H15S3CNT3BHI4LENB2N13BL0S4LENBS4LENB2N1S4LENBS3CNT4LENBS2K7S4LENB2N1S2LO4LENB".
prep IV.
pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
pose proof (shad_mono B (B + Z.of_nat (length bs) - 1) ltac:(lia)) as SM2.
destruct (unpoisoned_check_rd bsegs mc B (B + count) (B + Z.of_nat (length bs) + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. do 5 zstep.
rewrite land7_mod. rewrite (aip_zero ((B + Z.of_nat (length bs) + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
zstep. if_cases K6; zify_cond K6.
- zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
eapply LX; eassumption.
- eapply LSL; [exact IV0 | assumption | reflexivity |].
unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO CNT BHI SEPD SEPE APPD UDST R2 WR2 RI RSTK RSH2"] Lemma LC : forall bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
INV2 bs mc ->
evtF bsegs RNG (POST (RdData bs) RNG)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x44514) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00i0?11447729195.17811447729323.19114336930838.13416073429258.11916075443317.11616075584073.11423009804051.11623260809484.11823260842252.11624115025141.12724122799997.11627923696028.12629782203372.12829782203372.1292996087336.121 30010325480.11631885183527.1193210808038.129 36200770684.12639547979280.11839677217177.11640243440868.12841055186995.11341123052556.11642148695032.11643374880621.11246186857798.10946300107345.20646766805368.19 47018790687.11847019085599.11647803503873.11648325108386.11649852543712.11649852904160.11849921929014.12051845486909.11452074235542.12852735198782.11752735198782.11956172530212.11657307948242.12757880736640.12957915647498.1155876716948.115 59308628179.1  59308628304.11459308628695.1  62348280136.11962348288512.14762839777234.12763407398368.11663407889888.11864368761933.11664659114050.11668313605590.2196922740008.108 00000100e00k01801E01R01[01d01m02702A02N02T02Z02f02l03H03I03O03d03m03n04@04U04_04h05205h06806A06J06T06^06o07@07P07b08708A08K08Q08W08X08a08b08f09709;09<09=09C09P09]09c09m0;L0;UFS3CNT3BHI4LENB3BL01H2H02H42H52H93H103H143H153H193H20S4LENBS3CNT4LENB2RrS3CNT4LENB2RrS3CNT4LENB2RrS4LENB2RrS2R24LENBS2R24LENBS4LENB3BL0S4LENB3BL0S3CNT4LENB2RrS4LENBS4LENBS4LENB2KZ2N1S4LENBS3CNT3BHI4LENB3BL03R1'2K22SMFS4LENBS3CNT3BHI2R24LENB3R1'S4LENB2RrFS3CNT3BHI4LENB3BL0S3CNT3BHI2R24LENB3R1'S4LENB3BL0S4LENB2KZS3CNT4LENBS3CNT3BHI4LENB3BL01B1H2H02H42H52H93H103H143H153H193H34S3BL02Rr2K21H2H0S2R24LENBS2R24LENBS3CNT4LENBS4LENB3BL0S3CNT3BHI2R24LENBS3CNT3BHI2R24LENBS3CNT4LENB3BL01HS3CNT3BHI4LENB3BL0S3CNT3BHI4LENB3R1'2K1S4LENB3BL0S4LENB3BL0S4LENBS4LENBFS4LENB2RrFS2K0S3CNT4LENB3BL02K1S2K4FFS4LENBS3CNT2R24LENBS3CNT2R24LENBS4LENBS3CNT4LENBS3CNT3BHI4LENB3BL02Rr3R1'2K22N11B1H2H02H42H52H93H103H143H153H193H203H243H253H293H393H443H593H60S2LO4LENB".
prep IV.
assert (Rr : (0 <= Z.of_nat (length bs) <= count)%Z) by lia.
zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
zstep. if_cases KZ; zify_lts KZ.
{ eapply LX; eassumption. }
assert (R1' : (1 <= Z.of_nat (length bs))%Z) by lia.
zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
zstep. zstep. zstep. if_cases K2; zify_cond K2.
-
do 4 zstep.
unfold sf_hide in DST.
pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
| zsimp; eapply app_blk_sub; [exact APPD | lia | lia | lia]
| zsimp; eapply unpoisoned_sub; [exact UD1 | lia | lia]
| zsimp; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
do 3 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply LX; eapply inv2_of; eassumption.
-
assert (N1 : (Z.of_nat (length bs) <= 64)%Z) by (clear - K2 Rr R1' BL0; Z.div_mod_to_equations; lia).
do 11 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R2.
destruct (shadow_probe8 bsegs mc RLO2 RHI2 B WR21 ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
destruct (shadow_probe8 bsegs mc RLO2 RHI2 (B + Z.of_nat (length bs) + -1) WR21
ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LSS; [eassumption | lia].
+ eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="RLO2 RHI2 MI ST LO KLO GOT SHB INI LAY REAL DST ERR A0 A2 FD CNT BHI SEPD SEPE APPD UDST R2 WR2 RI RSTK RERR RD RSH2"] Lemma read_i_body :
implA bsegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
(epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x444c4) fc None m (seg_rom bsegs)).
Proof.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof BL_ok as BL0. unfold BL in BL0.
Local Ltac2 Set LiaHints.tbl := fun () => "00m0?12973736063.10015498737820.12415498737820.90 15642987184.91 162492479.82   1807322596.89  1807322599.121 21694748720.90 23654922526.10025820099228.12525820099228.90 27712824752.88 28055345289.1142845652246.100 3117223615.100 34233151718.81 34235665431.10035378896924.12435378896924.88 35854634524.12535854634524.90 3602932068.89  3602932074.124 36200770684.12937033835015.1143812400510.114 39815459250.11442149037413.82 43055369225.79 44368527500.10045735046704.90 46703417572.89 46703417578.12449460590346.11549921929014.10149921929014.86 50221378405.12350221378407.87 51077402219.75 51795196848.90 52415237221.90 52415237227.12553175635037.10056170256219.10056172315833.82 57603500076.12957813240112.90 58390049052.12658390049052.91 59308628179.1  59308633593.1  59430450874.10062623352644.11462697437393.10766138656668.12266138656668.90 6922740008.74  6950140022.105 7078002290.100 7944451812.89  7944451813.123 00000600700800900=00>00?00@00D00E00F00G00H00I00N00O00T00U00V00W00X00Y00Z00[00`00d00e00j00o01G01H01I01J01N01d02:02;02<02@02A02B02C02T02U02V02W02X02Y02Z02^02b02n03203303403503903:03M03N03OS4SEPESSSS2LOSSSS2FDSSSSSS3BL0SS3CNTSSSSSSSS3CNTS2HeSS3BL0S3LO'S2LO3CNT3BHI4SEPD2R23HspSSSS2LOS2LO3CNT3BHI4SEPD2R21HS2LO3CNT3BHI4SEPD2R21HSSS2LOSSSS3CNT3BHI4SEPE2R2SSSSSSS2K0S2KZS2R23BL03HspS2HeSSSS2LOSS2LO3CNT3BHI2R23HspSS".
assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
pose proof DST as DST0. change (?P) with (sf_hide P) in DST. pose proof ERR as ERR0. change (?P) with (sf_hide P) in ERR.
rewrite A0, A2.
iprefix.
carve_frame 2128%nat ST0.
do 9 zstep. do 3 zstep. zstep.
call_sp tryinit_spec; [ assumption | exact ST0 | lia | unfold KHIGH; lia | assumption | eapply rng_sub'; [exact RSTK | lia] | ].
do 6 zstep. zstep.
name_sp sp (-2128)%Z.
Local Ltac usp := match goal with H : bv_unsigned _ = (bv_unsigned sp + -2128)%Z |- _ => rewrite H end.
icallk read_spec;
[ usp; eassumption | eassumption | eassumption | assumption | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia
| usp; eapply rng_sub'; [exact RSTK | lia] | ].
ipost bsegs. unname_sp.
lazymatch goal with P : context [match ?a with RdErr _ => _ | RdData _ => _ end] |- _ => rename P into RP end.
destruct ans as [e|bs]; cbn [read_ret].
-
destruct RP as (BUFe & ERRe & He).
zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
zstep. if_cases KZ; zify_lts KZ. 2:{ exfalso. clear - KZ. lia. }
do 9 zstep.
lazymatch goal with ST2 : stk bsegs _ lo _ |- _ => release_frame FR ST2 (bv_unsigned sp) end.
unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish; lia.
-
destruct RP as (BUF1 & ERR1 & LENB).
eapply LC. eapply inv2_of; try eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.
#[using="Type"] Lemma read_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z),
mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_read m ->
rw_cells bsegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
rw_cells bsegs m (errno_addr tp) [C4 errv] ->
a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
(3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
(0x5f7000 <= bv_unsigned a1 \/ (0x5c4b90 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= 0x5d4b90 /\ bv_unsigned a1 + count <= errno_addr tp))%Z -> (bv_unsigned a1 + count <= lo)%Z ->
(0xa3740 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f7000)%Z -> (164 <= bv_unsigned tp)%Z ->
app_blk (bv_unsigned a1) (bv_unsigned a1 + count) ->
unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + count) ->
(RLO2 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (errno_addr tp) 4 -> rng RNG (bv_unsigned a1) count ->
rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
implA bsegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
(epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x444c4) fc None m (seg_rom bsegs)).
Proof. intros. eapply read_i_body; eassumption. Qed.
End CANSEC1.
