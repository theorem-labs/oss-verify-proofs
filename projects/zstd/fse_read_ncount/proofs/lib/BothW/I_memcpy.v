(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells ShadowTac F_memcpy F_rip.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
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
Definition memcpy_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at bsegs m' (bv_unsigned a1) src.
Section Proofs.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
(src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z).
Notation D := (bv_unsigned a0).
Notation S := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis RIC : rt_got_ric m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis LAY : rt_layout m.
Hypothesis REAL : rt_real_mem m.
Hypothesis SRC : bytes_at bsegs m S src.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis DST : rw_cells bsegs m D [CB (Z.to_nat n) junk].
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Hypothesis SEPS : (S + n <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= S)%Z.
Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
Hypothesis APPS : app_blk S (S + n).
Hypothesis APPD : app_blk D (D + n).
Hypothesis USRC : unpoisoned m S (S + n).
Hypothesis UDST : unpoisoned m D (D + n).
Hypothesis NSZ : (n <= 2^40)%Z.
Hypothesis R1 : (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z.
Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
Hypothesis WR1 : wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1).
Hypothesis WR2 : wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RS : rng RNG S n.
Hypothesis RD : rng RNG D n.
Hypothesis RSH1 : rng RNG (shad RLO1) (shad RHI1 - shad RLO1).
Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Notation POST := (memcpy_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m).
Definition INV (mc : word -> option byte) : Prop :=
(exists jk, rw_cells bsegs mc (bv_unsigned sp + -2160)
[CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
/\ stk bsegs mc lo (bv_unsigned sp + -2160)
/\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc
/\ wmono bsegs m mc /\ mem_inv bsegs mc
/\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
/\ unpoisoned mc S (S + n) /\ unpoisoned mc D (D + n)
/\ wr_at bsegs mc (shad RLO1) (shad RHI1 - shad RLO1) /\ wr_at bsegs mc (shad RLO2) (shad RHI2 - shad RLO2).
Definition BND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
/\ 0 <= S /\ S + n + 8 <= KEND /\ 0 <= D /\ D + n + 8 <= KEND
/\ 2147450880 <= shad RLO1 /\ shad RLO1 <= shad S /\ shad (S + n - 1) + 1 <= shad RHI1 /\ shad RHI1 <= KHIGH
/\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
/\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44
/\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
/\ shad RLO1 mod 8 = 0 /\ shad RHI1 mod 8 = 0 /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
/\ RLO1 <= S /\ S + n <= RHI1 /\ RLO2 <= D /\ D + n <= RHI2
/\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.
#[using="m src ST LO KLO LEN APPS APPD NSZ R1 R2"] Lemma BND_ok : BND.
Proof.
unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
destruct ST as (L0 & _). destruct APPS as [LES AS]. destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
pose proof R1 as R1'. pose proof R2 as R2'. unfold sf_hide in R1', R2'.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>29786661831.82000008S3LEN2Rn".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
first [clear -Rn L0 LO KLO NSZ LES AS LED AD R1' R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.
Definition BL : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= S /\ S + n + 8 <= 2^47 /\ 0 <= D /\ D + n + 8 <= 2^47
/\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44 /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
/\ 2147450880 <= shad RLO1 /\ shad RLO1 <= shad S /\ shad (S + n - 1) + 1 <= shad RHI1 /\ shad RHI1 <= 17594333495296
/\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
#[using="m src ST LO KLO LEN APPS APPD NSZ R1 R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62904913180.7500000>S2LO3LEN3NSZ1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac inv_open H :=
let jk := fresh "jk" in
destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1 & US1 & UD1 & WR11 & WR21).
Ltac prep IV :=
pose proof IV as IV0; inv_open IV;
let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]);
change (?P) with (sf_hide P) in SRC; change (?P) with (sf_hide P) in DST;
change (?P) with (sf_hide P) in SEP; change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in SEPD;
change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
#[using="src ST LO KLO LEN SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2"] Lemma inv_of : forall mc jk,
rw_cells bsegs mc (bv_unsigned sp + -2160) [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk bsegs mc lo (bv_unsigned sp + -2160) ->
munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
INV mc.
Proof.
intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
split; [exists jk; exact FR|]. repeat (split; [assumption|]).
assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
{ intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0020?11807744665.90 22714189854.15500000K00hS3LEN3SEP4SEPS4SEPD2R12R21BS3LEN3SEP4SEPS4SEPD1B2H21H2H0".
lia. }
split. { eapply unpoisoned_munch; [exact USRC | exact MU1 |]. cbn [disjoint_from]. pose proof (SS S (S + n)%Z). lia. }
split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
split; eapply wr_at_transport; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
INV mc ->
evtF bsegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x5292c) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00M0?11799456952.11511801535522.11614963958750.12415096019484.13217726993820.13218463327460.13218911011559.13120596453351.13122458203492.13222700267513.11923038706678.12527770204444.13328509638172.13335814319382.12537100524840.11446160525468.1334831066756.125 48376441407.12451311196007.13152637814885.13356162579484.13356978285031.13158793529244.13259136411879.13160968803940.13261296450716.13262658698084.13263910294172.1329978492700.134 00000H00`00e00j00o01401901>01C01J01O01T01Y01^01f01k02302802=02B02G02L02Q02V02[02`02e02j02oS3LEN3SEP4SEPS2R12R23BL0S3LEN3SEP4SEPD2R12R23BL0S3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN1HS3LENS3LENS3LENS3LENS2LO3LENS3LENS2LO3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN".
prep IV.
assert (SRC1 : bytes_at bsegs mc S src).
{ unfold sf_hide in *. eapply bytes_at_transport; [exact SRC | exact MU1 |]. rewrite LEN. cbn [disjoint_from]. lia. }
assert (DST1 : rw_cells bsegs mc D [CB (Z.to_nat n) junk]).
{ unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
zstep. zstep. zstep.
unfold sf_hide in SEPD.
apply (munch_weaken _ [(bv_unsigned sp + -2240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
2:{ unfold sub_fp; cbn [outside]; intros; lia. }
clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR11 WR21.
call memcpy_spec; [exact SRC1 | exact LEN | exact DST1 | unfold sf_hide in SEP; exact SEP | exact MI1 |].
do 13 zstep.
release_frame FR ST1 (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x16 x17 x18 x19 x23 x24 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
evtF bsegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
x18 x19 (Z_to_bv 64 (D + n + -1)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) x23 x24
s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52cb8) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13708355367.11813732943226.11824120772675.11824189877751.12437100524840.11340339170388.12441500211037.15850781112641.11659308585478.11359308627018.1  60888476447.11800000>00Q00]00^00i01;01O01Z01h01l02AS3LEN2N12Hk2HcS3LEN2N12Hk2Hc2SL1KS3LEN3BL02HkFS2LO3LEN2HkS3LEN2N13BL02Hk2HcS3LEN2N12Hk2Hc2H42H5S3LEN2Hk2HcS3LEN2N12Hk2HcS2K'S3LEN2N13BL02Hk2Hc2SL".
prep IV.
revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd bsegs mc D (D + n) c UD1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD RSH2"] Lemma LWS : forall mc x1 x5 x6 x7 x9 x15 x16 x17 x18 x19 x23 x24 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
evtF bsegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) x15 x16 x17
x18 x19 (Z_to_bv 64 (D + n + -1)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) x23 x24
s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52c9c) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?15389206936.14619033648510.15019482125344.12519482125358.12324122881528.11624991237562.12528034942977.21328442431616.15029782203372.12229784416728.11636004493144.11137100524840.11043614754995.11146022211061.16552076332689.12252523015476.12353510313876.12359308629082.1  68646946464.11100000800@00L00X00a00f01F01R01W01\01a01i01n02F02R02W02\02`02hS3LEN2H0S3LEN2H0S3LEN2N13CK2S3LEN2N13CK2S3LEN3BL0S3LENS3LEN2N11B1H2H02H42H52H93H103H59S3LEN2N13CK2S3LENS3LENS3LENS2LO3LENS3LENS3LEN2N12K62H42H52H93H10S3LEN2N13BL0S3LENS3LENS2K7S3LEN2N1".
prep IV.
destruct (unpoisoned_check_rd bsegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. do 5 zstep.
rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
zstep. if_cases K6; zify_cond K6.
- zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
eapply LX; eassumption.
- eapply LWL; [exact IV0 | assumption | reflexivity |].
unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH2"] Lemma LW : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x23 x24 x28 x29 x30 x31,
INV mc ->
evtF bsegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) x23 x24
s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x528e4) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00W0?11447729323.19013313378710.1331606916996.18  1725273741.153 1725281608.118 23260809484.11723260842252.11524115025143.12424122799997.11529782203372.12730010325480.11531885183527.1183210808038.127 34598411672.11537100524840.11139547979280.11742148837058.11546300108241.24647018790687.11747019085599.11549852543712.11549852904160.11751845486909.11352076332702.12552733105242.11652733105242.11855358375734.11956172410654.11557307948242.12657880736640.127585992346.116  5876716948.114 59308628304.11359308628695.1  62806329641.11262839777246.12263407398368.11563407889888.11764073056942.11500000100600C00D00E00M00U00^00g00l01101:01;01D01L01[01d02P02X02`02k03603?03K03T03]03h03m04204304:04;04G04K04T04Y04d04o05>FS3LENS3BL02K21H2H0FFS3LEN2R2S3LEN2R2S3LEN3BL0S3LEN3BL0S3LENS3LENS3LEN3BL0FS3LEN3BL0S2LO3LENS3LEN2R23BL02N1S3LEN3BL0S3LEN2N11B1H2H02H42H52H93H103H143H153H593H64S3LEN2R2S3LEN2R2S3LEN2R22N1S3LEN2R22N1S3LEN3BL0S3LEN3BL02N1S3LEN3BL0S3LEN3BL0S3LEN3BL01HS3LENS3LENFS3LEN1BFS3LEN3BL02K1S2K4S3LEN3BL0S3LENS3LEN2R22N1S3LEN2R22N1S3LEN2R23BL02N1".
prep IV.
zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
zstep. zstep. if_cases K2; zify_cond K2.
-
zstep. if_cases K3; zify_cond K3.
2:{ zstep. eapply LX; eassumption. }
do 5 zstep.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
| pose proof BND_ok as B; unfold BND in B; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply LX; eapply inv_of; eassumption.
-
assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
do 10 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R2.
destruct (shadow_probe8 bsegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
destruct (shadow_probe8 bsegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LWS; eassumption.
+ eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LRL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x23 x24 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
Z.to_nat (shad (S + n - 1) - c) = k -> (shad S <= c < shad (S + n - 1))%Z ->
evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 0) x16 x17
x18 (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) x23 x24
s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52bb8) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00<0?13708355367.11613732943226.11624120772675.11624189877750.12337100524840.11140339170389.12353039530994.15657132210400.11459308585478.11159308627018.1  60483825568.12360888476447.11600000>00Q00]00^00i00j01>01I01W01[01m02BS3LEN2N12Hk2HcS3LEN2N12Hk2Hc2SL1KS3LEN3BL02HkFS2LO3LEN2HkFS3LEN2N12Hk2Hc2H42H5S3LEN2Hk2HcS3LEN2N12Hk2HcS2K'S3LEN2N13BL02Hk2HcS3LEN2N13BL02Hk2Hc2SL".
prep IV.
revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
assert (SL : (shad (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd bsegs mc S (S + n) c US1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LW; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LRS : forall mc x5 x6 x7 x9 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) x15 x16 x17
x18 (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) x23 x24
s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52b9c) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00D0?15389206936.14419033648510.14819482125344.12319482125358.12124122881528.11424991237562.12328034942977.21228034943116.20528442431616.14829782203372.12129784416728.11437100524840.10843614754995.10946022211061.16348157833191.10952076332703.12252523015476.12153510313876.12159308629082.1  59961573519.10900000800@00L00X00a00f00g01G01S01X01]01e01j02B02G02S02X02]02a02iS3LEN2H0S3LEN2H0S3LEN2N13CK2S3LEN2N13CK2S3LEN3BL0S3LENFS3LEN2N11B1H2H02H42H52H93H103H44S3LEN2N13CK2S3LENS3LENS2LO3LENS3LENS3LEN2N12K62H42H52H93H10S3LENS3LEN2N13BL0S3LENS3LENS2K7S3LEN2N1".
prep IV.
destruct (unpoisoned_check_rd bsegs mc S (S + n) (S + n + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. do 5 zstep.
rewrite land7_mod. rewrite (aip_zero ((S + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
zstep. if_cases K6; zify_cond K6.
- zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
eapply LW; eassumption.
- eapply LRL; [exact IV0 | assumption | reflexivity |].
unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LR : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x24 x28 x29 x30 x31,
INV mc ->
evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (S + n)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) x22 x23 x24
s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52898) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00[0?11447729323.1891606916996.18  16224732650.11616225027562.1141725273741.152 1725281608.117 22625362435.11422625395203.11624115025143.12324122799997.11426844494028.11429782203372.12630010325480.11431782320794.11731885183527.11731885191650.1523210808038.126 34598411672.11437100524840.11041067758515.11142148837058.11443042078623.11443042373535.11646300108113.23146300108124.23846300108241.24546415450209.11546415450209.11751845486909.11252076332689.12155358375734.11856172410654.11457307948242.12557880736640.126585992346.115  5876716948.113 59308628304.11259308628695.1  62839777246.12165824578719.11665824677023.11468032931094.1329722591124.116 00000100>00F00N00O00P00X00`00i01201A01F01K01T01U01V01W01`01h02102:02E02P03703c03d03m04604?04K04V04[04`04a04h04i05505905>05I05T05Y05hFS3BL02K21H2H0S3LEN2R1S3LEN2R1FFS3LEN2R1S3LEN2R1S3LEN3BL0S3LEN3BL0S3LEN2R13BL02N1S3LENS3LENS3LEN3BL0FFFS3LEN3BL0S2LO3LENS3LEN3BL0S3LEN3BL0S3LEN2R12N1S3LEN2R12N1S3LEN2N11B2H42H52H93H103H143H153H193H44S3LEN2N11B1H2H02H42H52H93H103H143H153H243H49FS3LEN3BL0S3LEN3BL0S3LEN3BL0S3LEN3BL02N1S3LEN3BL01HS3LENS3LENFS3LEN1BFS3LEN3BL02K1S2K4S3LENS3LEN2R12N1S3LEN2R12N1S3LENS3LEN2R13BL02N1".
prep IV.
zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
zstep. zstep. zstep. if_cases K2; zify_cond K2.
-
zstep. if_cases K3; zify_cond K3.
2:{ zstep. eapply LW; eassumption. }
do 6 zstep.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPS | exact US1
| pose proof BND_ok as B; unfold BND in B; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply LW; eapply inv_of; eassumption.
-
assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
do 10 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R1.
destruct (shadow_probe8 bsegs mc RLO1 RHI1 S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
destruct (shadow_probe8 bsegs mc RLO1 RHI1 (S + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LRS; eassumption.
+ eapply LW; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk RLO1 RHI1 RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma memcpy_i_body :
evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x52838) fc None m (seg_rom bsegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof BL_ok as BL0. unfold BL in BL0.
Local Ltac2 Set LiaHints.tbl := fun () => "00X0>11476328624.9213145679078.8215096019484.8917494642224.9117726993820.9018463327460.9018911011559.8920596453351.8922458203492.9023554792368.8927770204444.9128509638172.9131824352478.9037100524840.7738067495472.9043061432073.8044119101360.9146160525468.9150103754032.9051311196007.8852637814885.915491675952.90 56155646640.9156162579484.9156978285031.8958793529244.9059136411879.8959308628179.1 59308628566.8860968803940.9061296450716.9062173853744.9062658698084.9063910294172.906431256683.78 64491632942.9068159522224.918929152288.87 8929152679.88 9978492700.92 00000500:00?00D00I00N00S00X00]00b00g00l01101901>01G01L01Q01V01[01`01e01j01o02402902>02B02Q02V02[02`02e02j03203703<03K03]03bS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS2LO3LENS3LENS3LEN3BL0S3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS2K0S3LEN3SEP2K22K3S3LENS3LENS3LENS3LENS3LENS2LO3LENS3LENS3LENS3LEN2R12R23BL0S3LEN2R12R23BL02K2S3LEN".
assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
assert (LO' : (lo <= bv_unsigned sp - 2160)%Z) by lia.
change (?P) with (sf_hide P) in SEP; change (?P) with (sf_hide P) in SEPS;
change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
change (?P) with (sf_hide P) in SRC; change (?P) with (sf_hide P) in DST.
pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
change (?P) with (sf_hide P) in WR1; change (?P) with (sf_hide P) in WR2.
carve_frame 2160%nat ST0.
do 13 zstep.
do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
do 4 zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (IV : INV m1) by (eapply inv_of; eassumption) end.
zstep. if_cases K1; zify_cond K1.
{ eapply LR; exact IV. }
zstep. if_cases K2; zify_cond K2.
{ eapply LR; exact IV. }
zstep. if_cases K3; zify_cond K3. { exfalso. unfold sf_hide in SEP. lia. }
eapply LR; exact IV.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.
#[using="Type"] Lemma memcpy_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
bytes_at bsegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
(bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
app_blk (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
(bv_unsigned a2 <= 2^40)%Z ->
(RLO1 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z ->
(RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF bsegs RNG (memcpy_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x52838) fc None m (seg_rom bsegs)).
Proof. intros. eapply memcpy_i_body; eassumption. Qed.
End CANSEC1.
