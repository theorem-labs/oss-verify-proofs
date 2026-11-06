(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells ShadowTac F_memcpy F_rip.
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
Definition asan_memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.
Section Proofs.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
(src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z).
Notation D := (bv_unsigned a0).
Notation S := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis RIC : rt_got_ric m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis LAY : rt_layout m.
Hypothesis REAL : rt_real_mem m.
Hypothesis SRC : bytes_at asegs m S src.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Hypothesis SEPS : (S + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= S)%Z.
Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
Hypothesis APPS : app_blk S (S + n).
Hypothesis APPD : app_blk D (D + n).
Hypothesis USRC : unpoisoned m S (S + n).
Hypothesis UDST : unpoisoned m D (D + n).
Hypothesis NSZ : (n <= 2^40)%Z.
Hypothesis R1 : (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z.
Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
Hypothesis WR1 : wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1).
Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RS : rng RNG S n.
Hypothesis RD : rng RNG D n.
Hypothesis RSH1 : rng RNG (shad RLO1) (shad RHI1 - shad RLO1).
Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Notation POST := (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m).
Definition INV (mc : word -> option byte) : Prop :=
(exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
[CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
/\ stk asegs mc lo (bv_unsigned sp + -2144)
/\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
/\ wmono asegs m mc /\ mem_inv asegs mc
/\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
/\ unpoisoned mc S (S + n) /\ unpoisoned mc D (D + n)
/\ wr_at asegs mc (shad RLO1) (shad RHI1 - shad RLO1) /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).
Definition BND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
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
(0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= S /\ S + n + 8 <= 2^47 /\ 0 <= D /\ D + n + 8 <= 2^47
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
assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
change (?P) with (sf_hide P) in SRC; change (?P) with (sf_hide P) in DST;
change (?P) with (sf_hide P) in SEP; change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in SEPD;
change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
#[using="src ST LO KLO LEN SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2"] Lemma inv_of : forall mc jk,
rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -2144) ->
munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
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
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
INV mc ->
evtF asegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52070) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00K0?11799456952.11411801535522.11514540549476.13116852238724.12417231150308.13117607716380.13219031052389.13222580318183.13022700267513.11824346829668.13125250094364.131260657820.131  27620275190.12427914623132.13135834628839.13035973911964.13237601013348.13138214514495.12338637523228.13245454594454.12447452071390.12353295060839.13053723688860.13157540799784.11366283099932.13268577416220.1338794126823.130 00000H00`00e00m01201701<01A01H01M01R01W01\01a01f01k02002502:02?02D02I02N02V02[02`02eS3LEN3SEP4SEPS2R12R23BL0S3LEN3SEP4SEPD2R12R23BL0S3LENS2LO3LENS3LENS3LENS3LENS3LENS3LEN1HS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS2LO3LENS3LENS3LENS3LEN".
prep IV.
assert (SRC1 : bytes_at asegs mc S src).
{ unfold sf_hide in *. eapply bytes_at_transport; [exact SRC | exact MU1 |]. rewrite LEN. cbn [disjoint_from]. lia. }
assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
{ unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
zstep. zstep. zstep.
unfold sf_hide in SEPD.
apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
2:{ unfold sub_fp; cbn [outside]; intros; lia. }
clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR11 WR21.
call memcpy_spec; [exact SRC1 | exact LEN | exact DST1 | unfold sf_hide in SEP; exact SEP | exact MI1 |].
do 12 zstep.
release_frame FR ST1 (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x16 x17 x18 x21 x23 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
evtF asegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
x18 (Z_to_bv 64 (D + n + -1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 (Z_to_bv 64 (n + -65)) x23
s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52398) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13708355367.11713732943226.11724120772675.11740339170388.12341500211037.15750781112641.11557540799784.11259308585478.11259308627018.1  60888476447.11762863995383.12300000>00Q00]00o01C01N01Y01g01k02@02AS3LEN2N12Hk2HcS3LEN2N12Hk2Hc2SL1KS3LEN3BL02HkS3LEN2N13BL02Hk2HcS3LEN2N12Hk2Hc2H42H5S3LEN2Hk2HcS2LO3LEN2HkS3LEN2N12Hk2HcS2K'S3LEN2N13BL02Hk2Hc2SLF".
prep IV.
revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD RSH2"] Lemma LWS : forall mc x1 x5 x6 x7 x9 x15 x16 x17 x18 x21 x23 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
evtF asegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) x15 x16 x17
x18 (Z_to_bv 64 (D + n + -1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 (Z_to_bv 64 (n + -65)) x23
s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x5237c) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?15389206936.14519033648510.14919482125344.12419482125358.12224122881528.11524991237562.12428034942977.21228442431616.14929782203372.12129784416728.11536004493144.11043614754995.11046022211061.16452076332703.12352523015476.12253510313876.12257540799784.10959308629082.1  68646946464.11000000800@00L00X00a00f01F01R01W01\01a01f02>02J02O02T02\02`02hS3LEN2H0S3LEN2H0S3LEN2N13CK2S3LEN2N13CK2S3LEN3BL0S3LENS3LEN2N11B1H2H02H42H52H93H103H59S3LEN2N13CK2S3LENS3LENS3LENS3LENS3LEN2N12K62H42H52H93H10S3LEN2N13BL0S3LENS3LENS2LO3LENS2K7S3LEN2N1".
prep IV.
destruct (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
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
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH2"] Lemma LW : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x28 x29 x30 x31,
INV mc ->
evtF asegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 (Z_to_bv 64 (n + -65)) x23
s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52028) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00W0?11146785174.13211447729323.1891606916996.18  19575182546.12523260809484.11623260842252.11424115025143.12324122799997.11429782203372.12630010325480.11431247978648.11431885183527.1173210808038.126 39547979280.11640131048926.12142148837058.11446300108241.24547018790687.11647019085599.11449852543712.11449852904160.11651845486909.11252076332689.12152733105242.11552733105242.11756172410654.11457540799784.11057880736640.126585992346.115  5876716948.113 59308628304.11259308628695.1  60274602806.11862806329641.11163407398368.11463407889888.11664073056942.1147744853832.117 7744861325.152 00000500600C00H00P00X00a00j00o01401=01F01G01V01[01d02P02X02`02k03603?03K03T03]03b03j03k04204304?04C04N04W04b04m05<05=05>S3LENFS3BL02K21H2H0S3LENS3LEN2R2S3LEN2R2S3LEN3BL0S3LEN3BL0S3LENS3LENS3LEN3BL0S3LEN3BL0FS3LEN2R23BL02N1S3LENS3LEN3BL0S3LEN2N11B1H2H02H42H52H93H103H143H153H593H64S3LEN2R2S3LEN2R2S3LEN2R22N1S3LEN2R22N1S3LEN3BL0S3LEN3BL02N1S3LEN3BL0S3LEN3BL0S3LENS2LO3LENFS3LEN1BFS3LEN3BL02K1S2K4S3LEN3BL01HS3LEN3BL0S3LEN2R22N1S3LEN2R22N1S3LEN2R23BL02N1FF".
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
destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LWS; eassumption.
+ eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LRL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x23 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
Z.to_nat (shad (S + n - 1) - c) = k -> (shad S <= c < shad (S + n - 1))%Z ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 0) x16 x17
x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (n + -65)) x23
s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x522f4) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00<0?13708355367.11513732943226.11524120772675.11540339170389.12253039530994.15557132210400.11357540799784.11059308585478.11059308627018.1  60483825568.12260888476447.11562863995382.12200000>00Q00]00^01201=01H01V01Z01l02A02BS3LEN2N12Hk2HcS3LEN2N12Hk2Hc2SL1KS3LEN3BL02HkFS3LEN2N12Hk2Hc2H42H5S3LEN2Hk2HcS2LO3LEN2HkS3LEN2N12Hk2HcS2K'S3LEN2N13BL02Hk2HcS3LEN2N13BL02Hk2Hc2SLF".
prep IV.
revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
assert (SL : (shad (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd asegs mc S (S + n) c US1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LW; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LRS : forall mc x5 x6 x7 x9 x15 x16 x17 x18 x23 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) x15 x16 x17
x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (n + -65)) x23
s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x522d8) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00D0?15389206936.14319033648510.14719482125344.12219482125358.12024122881528.11324991237562.12228034942977.21128034943116.20428442431616.14729782203372.12029784416728.11343614754995.10846022211061.16248157833191.10852076332702.12252523015476.12053510313876.12057540799784.10759308629082.1  59961573519.10800000800@00L00X00a00f00g01G01S01X01]01b02:02?02K02P02U02]02a02iS3LEN2H0S3LEN2H0S3LEN2N13CK2S3LEN2N13CK2S3LEN3BL0S3LENFS3LEN2N11B1H2H02H42H52H93H103H44S3LEN2N13CK2S3LENS3LENS3LENS3LEN2N12K62H42H52H93H10S3LENS3LEN2N13BL0S3LENS3LENS2LO3LENS2K7S3LEN2N1".
prep IV.
destruct (unpoisoned_check_rd asegs mc S (S + n) (S + n + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
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
#[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LR : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31,
INV mc ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (S + n)) x22 x23
s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x51fdc) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00[0?11447729323.1881606916996.18  16224732650.11516225027562.11319239446934.13119575182546.12422625362435.11322625395203.11524115025143.12224122799997.11326844494028.11329782203372.12530010325480.11331247978648.11331782320794.11631885183527.11631885191650.1513210808038.125 40131048926.12041067758515.11042148837058.11343042078623.11343042373535.11546300108113.23046300108124.23746300108241.24446415450209.11446415450209.11651845486909.11152076332703.12256172410654.11357540799784.10957880736640.125585992346.114  5876716948.112 59308628304.11159308628695.1  60274602806.11765824578719.11565824677023.1137744853832.116 7744861325.151 9722591124.115 00000100>00F00N00S00X00`00h01101:01I01N01S01\01e01f01g01h01m02602?02J02U03<03h03i04204;04D04P04U04]04^04e04f05205605A05L05W05X05Y05hFS3BL02K21H2H0S3LEN2R1S3LEN2R1S3LENS3LENS3LEN2R1S3LEN2R1S3LEN3BL0S3LEN3BL0S3LEN2R13BL02N1S3LENS3LENS3LEN3BL0S3LEN3BL0FFFS3LENS3LEN3BL0S3LEN3BL0S3LEN2R12N1S3LEN2R12N1S3LEN2N11B2H42H52H93H103H143H153H193H44S3LEN2N11B1H2H02H42H52H93H103H143H153H243H49FS3LEN3BL0S3LEN3BL0S3LEN3BL0S3LEN3BL02N1S3LENS2LO3LENFS3LEN1BFS3LEN3BL02K1S2K4S3LEN3BL01HS3LEN2R12N1S3LEN2R12N1FFS3LEN2R13BL02N1".
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
destruct (shadow_probe8 asegs mc RLO1 RHI1 S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
destruct (shadow_probe8 asegs mc RLO1 RHI1 (S + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LRS; eassumption.
+ eapply LW; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk RLO1 RHI1 RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma asan_memcpy_body :
evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f80) fc None m (seg_rom asegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof BL_ok as BL0. unfold BL in BL0.
Local Ltac2 Set LiaHints.tbl := fun () => "00U0>10499999408.8913879134430.9014540549476.9017231150308.9017607716380.9118486058859.7819031052389.9122537331120.9222580318183.8924346829668.9025250094364.89260657820.90  27914623132.9028521959216.9134540297392.9135834628839.8935973911964.9137601013348.9038637523228.9140600447536.9043061432073.8046586017712.9152637746480.9053295060839.8853723688860.9057540799784.7758622399152.9159308628179.1 59308628566.8861226359086.9063971998950.8264640737328.9066283099932.9168577416220.928794126823.89 8929152288.87 8929152679.88 00000500:00?00D00I00Q00V00[00`00e00j00o01401901>01C01H01M01R01W01`01e01j01o02402<02A02E02T02Y02^02c02h02m03203A03SS3LENS3LENS3LENS3LENS3LENS2LO3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN3BL0S3LENS3LENS3LENS3LENS2LO3LENS3LENS2K0S3LEN3SEP2K22K3S3LENS3LENS3LENS3LENS3LENS3LENS3LEN2R12R23BL0S3LEN2R12R23BL02K2".
assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
change (?P) with (sf_hide P) in SEP; change (?P) with (sf_hide P) in SEPS;
change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
change (?P) with (sf_hide P) in SRC; change (?P) with (sf_hide P) in DST.
pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
change (?P) with (sf_hide P) in WR1; change (?P) with (sf_hide P) in WR2.
carve_frame 2144%nat ST0.
do 12 zstep.
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
#[using="Type"] Lemma asan_memcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
(bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
app_blk (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
(bv_unsigned a2 <= 2^40)%Z ->
(RLO1 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z ->
(RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF asegs RNG (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f80) fc None m (seg_rom asegs)).
Proof. intros. eapply asan_memcpy_body; eassumption. Qed.
End CANSEC1.
