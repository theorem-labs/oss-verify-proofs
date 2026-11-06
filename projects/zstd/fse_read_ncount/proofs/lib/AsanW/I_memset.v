(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells ShadowTac F_memset F_rip.
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
Definition memset_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].
Section Proofs.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
(junk : list byte) (RLO2 RHI2 : Z).
Notation D := (bv_unsigned a0).
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
Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
Hypothesis APPD : app_blk D (D + n).
Hypothesis UDST : unpoisoned m D (D + n).
Hypothesis NSZ : (n <= 2^40)%Z.
Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RD : rng RNG D n.
Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
Notation POST := (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).
Definition INV (mc : word -> option byte) : Prop :=
(exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
[CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
/\ stk asegs mc lo (bv_unsigned sp + -2144)
/\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
/\ wmono asegs m mc /\ mem_inv asegs mc
/\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
/\ unpoisoned mc D (D + n)
/\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).
Definition BND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
/\ 0 <= D /\ D + n + 8 <= KEND
/\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
/\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
/\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
/\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.
#[using="m ST LO KLO APPD NSZ R2"] Lemma BND_ok : BND.
Proof.
unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
pose proof R2 as R2'. unfold sf_hide in R2'.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>29786661831.66000004S2Rn".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.
Definition BL : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
/\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
/\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
#[using="m ST LO KLO APPD NSZ R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62904913180.6200000:S2LO3NSZ1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac inv_open H :=
let jk := fresh "jk" in
destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21).
Ltac prep IV :=
pose proof IV as IV0; inv_open IV;
let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
#[using="ST LO KLO APPD UDST NSZ R2 WR2"] Lemma inv_of : forall mc jk,
rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -2144) ->
munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
INV mc.
Proof.
intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
split; [exists jk; exact FR|]. repeat (split; [assumption|]).
assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
{ intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0020?11807744665.77 22714190622.11400000600?S2R21BS2H21H2H0".
lia. }
split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
eapply wr_at_transport; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
INV mc ->
evtF asegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x526f0) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00H0?11799456952.98 14540549476.11416852238724.10717231150308.11417607716380.11519031052389.11520217284830.10622580318183.11322700267513.10125250094364.114260657820.114  27914623132.11435834628839.11335973911964.11537601013348.11438214514495.10650345689494.10753295060839.11353723688860.11454078910070.10757540799784.97 66283099932.11568577416220.1168794126823.113 00000=00>00B00C00D00E00F00G00J00K00L00M00N00O00P00Q00R00S00T00U00Y00Z00[00\S4SEPD2R23BL0SS2LOSSSSSS1HSSSSSSSSSSSS2LOSSS".
prep IV.
assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
{ unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
zstep. zstep. zstep.
unfold sf_hide in SEPD.
apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
2:{ unfold sub_fp; cbn [outside]; intros; lia. }
clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
call memset_spec; [exact DST1 | exact MI1 |].
do 11 zstep.
release_frame FR ST1 (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52824) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13708355367.10213732943226.10224120772675.10240339170390.10641500211165.12850781112641.10057540799784.97 59308585478.97 59308627018.1  60888476447.10262863995381.10600000700C00K00V00c00j01101801<01J01KS2Hk2HcS2Hk2Hc2SL1KS3BL02HkS3BL02Hk2HcS2Hk2Hc2H42H5S2Hk2HcS2LO2HkS2Hk2HcS2K'S3BL02Hk2Hc2SLF".
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
#[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
INV mc -> (1 <= n <= 64)%Z ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
(Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
(Z_to_bv 64 (D + n + -1)) x16 x17
x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52808) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?15389206808.11519033648638.11919482125344.10819482125345.10724122881528.99 24991237562.10828034943372.16028442431488.11929782203372.10429784416728.99 36004493144.94 43614754995.94 46022211189.13452076332689.10552523015476.10653510313883.10757540799784.93 59308629082.1  68646946464.94 00000400800=00B00G00H00d00i00j00k00l00m01>01F01G01H01L01P01TS2H0S2H0S3CK2S3CK2S3BL0SS2N11B1H2H02H42H52H93H103H34S3CK2SSSSS2K62H42H52H93H10S2N13BL0SSS2LOS2K7S2N1".
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
#[using="junk ST LO KLO DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
INV mc ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x52698) fc None mc (seg_rom asegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00Y0?11447729195.1611606916996.15  19575182546.11123260809484.10223260842252.10024115025142.11024122799997.10029782203372.11129782203372.11230010325480.10031247978648.10031885183527.1033210808038.112 38128246294.11839547979280.10240131048914.11142148837058.10046300107345.18946300107356.19547018790687.10247019085599.10049852543712.10049852904160.10251845486909.98 52076332702.11052733105242.10152733105242.10356172410654.10057540799784.96 57880736640.112585992346.101  5876716948.99  59308628304.98 59308628695.1  60274602806.10462806329641.97 63407398368.10063407889888.10264073056942.1007744853832.103 7744861197.124 00000100>00?00C00G00L00Q00R00S00T00Y00^00_00`00k00l01101T02<02@02D02H02L02Q02Y02^02c02d02h02i02l02m03503903@03E03I03M03X03Y03ZFS3BL02K21H2H0SS2R2S2R2S3BL0S3BL0SSSS3BL0S3BL0FSS2R23BL02N1SS3BL0S2N11B2H42H52H93H103H143H153H193H34S2N11B1H2H02H42H52H93H103H143H153H243H39S2R2S2R2S2R2S2R2S3BL0S3BL02N1S3BL0S3BL0SS2LOFS1BFS3BL02K1S2K4S3BL01HS3BL0S2R2S2R2S2R23BL02N1FF".
prep IV.
zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
zstep. zstep. zstep. if_cases K2; zify_cond K2.
-
zstep. if_cases K3; zify_cond K3.
2:{ zstep. eapply LX; exact IV0. }
do 5 zstep.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
| pose proof BND_ok as B; unfold BND in B; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply LX; eapply inv_of; eassumption.
-
assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
do 11 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R2.
destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LWS; eassumption.
+ eapply LX; exact IV0.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="junk RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma memset_i_body :
evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5265c) fc None m (seg_rom asegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof BL_ok as BL0. unfold BL in BL0.
Local Ltac2 Set LiaHints.tbl := fun () => "00O0>10499999408.7613879134430.7714540549476.7717231150308.7717607716380.7818486058859.6519031052389.7822537331120.7922580318183.7625250094364.76260657820.77  27914623132.7728521959216.7834540297392.7835834628839.7635973911964.7837601013348.7740600447536.7743061432073.6746586017712.7852637746480.7753295060839.7553723688860.7757540799784.6459308628179.1 61226359086.7763971998950.6964640737328.7766283099932.7868577416220.798794126823.76 00000100200300400500900:00;00<00=00>00?00@00A00B00C00D00E00J00K00L00M00N00R00V00W00X00Y00Z00[00\SSSSSS2LOSSSSSSSSSSSSS3BL0SSSSS2LOS2K0SSSSSS".
assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
change (?P) with (sf_hide P) in R2;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
change (?P) with (sf_hide P) in DST.
pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
carve_frame 2144%nat ST0.
do 11 zstep.
do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
eapply LB. eapply inv_of; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.
#[using="Type"] Lemma memset_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
(bv_unsigned a2 <= 2^40)%Z ->
(RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF asegs RNG (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5265c) fc None m (seg_rom asegs)).
Proof. intros. eapply memset_i_body; eassumption. Qed.
End CANSEC1.
