(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells ShadowTac F_rip F_tryinit F_memchr I_printf_lib.
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
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Ltac iprem :=
lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => first [assumption | eassumption]
| |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
| |- stk _ _ _ _ => first [assumption | eassumption]
| |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
| |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
| |- bytes_at _ _ _ _ => first [assumption | eassumption]
| |- unpoisoned _ _ _ => first [assumption | eassumption]
| |- memchr_ok _ _ _ _ => first [assumption | eassumption]
| |- wr_at _ _ _ _ => first [assumption | eassumption]
| |- app_blk _ _ => first [assumption | eassumption]
| |- Forall _ _ => first [assumption | eassumption]
| |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
| |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end ]
| |- _ => unfold KHIGH, sf_hide in *; first [assumption | lia]
end.
Ltac unland K :=
change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
change (2 ^ 64)%Z with 18446744073709551616%Z in K.
Notation rt_real_memchr m := (rw_cells bsegs m 0x9b638 [C8 (Z_to_bv 64 0x92b44)]).
Notation rt_real_strnlen m := (rw_cells bsegs m 0x9b720 [C8 (Z_to_bv 64 0x934cc)]).
Section CANSEC1. Context {rc : runConstT}.
Definition hitlen (c n : Z) (buf : list byte) : Z :=
match find_byte c (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.
Definition memchr_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S cc n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res S cc n buf)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2208, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp) /\ bytes_at bsegs m' S buf.
Section MEMCHR.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z).
Notation S := (bv_unsigned a0).
Notation cc := (bv_unsigned a1 mod 256)%Z.
Notation n := (bv_unsigned a2).
Notation N := (hitlen cc n buf).
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis LAY : rt_layout m.
Hypothesis RMC : rt_real_memchr m.
Hypothesis BUF : bytes_at bsegs m S buf.
Hypothesis OK : memchr_ok S cc n buf.
Hypothesis SEPB : (S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z.
Hypothesis SPOS : (0 < S)%Z.
Hypothesis APP : app_blk S (S + N).
Hypothesis UNP : unpoisoned m S (S + N).
Hypothesis NSZ : (N <= 2^40)%Z.
Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RB : rng RNG S (Z.of_nat (length buf)).
Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
Notation POST := (memchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc n buf lo m).
Notation RES := (memchr_res S cc n buf).
Definition INV (mc : word -> option byte) : Prop :=
rw_cells bsegs mc (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk bsegs mc lo (bv_unsigned sp + -2128) /\ stk bsegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
/\ munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc
/\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
/\ unpoisoned mc S (S + N) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at bsegs mc S buf.
Definition BND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= n < 2^64
/\ 0 <= S /\ S + N + 8 <= KEND
/\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
/\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
/\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
/\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
#[using="a0 RLO RHI R1"] Lemma hitlen_range : (0 <= N <= n)%Z.
Proof.
unfold hitlen. pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>60075379046.6565176764200.6400000800;S2R11R1ES1R".
destruct (find_byte cc (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="m ST LO KLO SPOS APP NSZ R1"] Lemma BND_ok : BND.
Proof.
unfold BND. destruct ST as (L0 & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
pose proof (bv_unsigned_in_range 64 a2) as NR. unfold bv_modulus in NR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in NR.
pose proof hitlen_range as HR.
Local Ltac2 Set LiaHints.tbl := fun () => "0020?29784462332.68 62900828075.14500000101`SS2LO3KLO4SPOS3NSZ2R13LES2AS3SPR2NR2HR1H2H02H42H52H93H103H143H153H193H203H243H253H343H353H393H403H443H453H493H50".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.
Definition BL : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N <= n /\ N <= 2^40 /\ n < 2^64
/\ 0 <= S /\ S + N + 8 <= 2^47
/\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
/\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
#[using="m ST LO KLO SPOS APP NSZ R1"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. pose proof hitlen_range. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62905010198.6400000AS2LO4SPOS3NSZ1B1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac inv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & BUF1).
Ltac hide_all :=
change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
change (?P) with (sf_hide P) in RMC; change (?P) with (sf_hide P) in BUF; change (?P) with (sf_hide P) in OK.
Ltac prep IV :=
pose proof IV as IV0; inv_open IV;
let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
hide_all.
#[using="ST LO KLO BUF SEPB SPOS APP UNP NSZ R1 WR1"] Lemma inv_of : forall mc,
rw_cells bsegs mc (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk bsegs mc lo (bv_unsigned sp + -2128) -> stk bsegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ->
munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
rt_got mc -> rt_shbase mc -> rt_layout mc -> INV mc.
Proof.
intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
repeat (split; [assumption|]).
Local Ltac2 Set LiaHints.tbl := fun () => "0020?11805731844.74 22714190609.11500000@00HS2R11B4SEPB4SPOSS1B1H2H0".
assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
split. { eapply wr_at_transport; eassumption. }
eapply bytes_at_transport; [exact BUF | exact MU1 |]. cbn [disjoint_from]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition mregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
a0 a1 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31.
#[using="ST LO KLO SPOS APP NSZ R1 RSTK"] Lemma LX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31, INV mc ->
evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x44038) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?17305236855.10617676671814.1001807322596.105 21879957789.99 22437836862.10030232449436.10633334826102.98 3602932068.105 39480921372.1054203475740.106 46703417572.10546970229916.10750221378407.10451188481948.10552415237221.10656185171996.10663123389028.1056922740008.97  7944451815.104 00000100200300800900:00?00@00A00B00C00D00E00F00G00H00I00M00NSSSS3BL0SSS3BL0SSSSSSSSSSS2LOS".
prep IV.
do 10 zstep.
pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
apply evtF_done. unfold memchr_i_post.
replace (bv_unsigned sp - 2208)%Z with (bv_unsigned sp + -2208)%Z by lia.
do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO SPOS APP NSZ R1 RSTK RSH1"] Lemma LL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x21 x28 x29 x30 x31,
INV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
evtF bsegs RNG POST (MS (mregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 RES) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
(Z_to_bv 64 (bv_unsigned sp + -2128)) x21 x28 x29 x30 x31)
F (Z_to_bv 64 0x44148) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. unfold mregs. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13714642969.10013739240004.10024122881917.10044092989943.10650781112641.98 57313722740.13359308585478.95 59308627018.1  60890567713.10064507443219.1066922740008.95  00000700D00L00M00T00b00i00m01;01F01MS2Hk2HcS2Hk2Hc2SL2K1S3BL02HkFS2Hk2HcS2Hk2Hc2H93H10S2Hk2HcS2K'S3BL02Hk2Hc2SLS3BL02Hk2HcS2LO2Hk".
prep IV.
revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
assert (SL : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd bsegs mc S (S + N) c UNP1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO SPOS APP NSZ R1 RSTK RSH1"] Lemma LE : forall mc x1 x5 x6 x7 x14 x15 x16 x17 x21 x28 x29 x30 x31, INV mc -> (1 <= N <= 64)%Z ->
evtF bsegs RNG POST (MS (mregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 RES) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
(Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 x28 x29 x30 x31)
F (Z_to_bv 64 0x4412c) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1. unfold mregs. Local Ltac2 Set LiaHints.tbl := fun () => "00B0?15389206805.12019033648627.12419482125347.10724122881528.97 24991237561.10728034943233.16728442431501.12429782203372.10429784416728.97 30459532252.92 43614754995.92 46022211192.13952076332689.10352523015483.10553510313881.10759308629082.1  68646946464.92 6922740008.91  00000400800E00J00K00g00l00m00n00o01001A01N01O01P01T01X01\S2H0S2H0S4SPOS2N13CK2S3BL0SS2N11B1H2H02H42H52H93H103H39S3CK2SSSSS2K62H42H52H93H10S4SPOS2N13BL0SSS2K7S2N1S2LO".
prep IV.
destruct (unpoisoned_check_rd bsegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. do 5 zstep.
rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
zstep. if_cases K6; zify_cond K6.
- zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
eapply LX; eassumption.
- eapply (LL mc); [exact IV0 | exact N1 | reflexivity |].
unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO BUF SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma LC : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31, INV mc ->
x9 = Z_to_bv 64 N -> x10 = Z_to_bv 64 RES ->
evtF bsegs RNG POST (MS (mregs x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 x28 x29 x30 x31)
F (Z_to_bv 64 0x43ff0) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV -> ->. unfold mregs. Local Ltac2 Set LiaHints.tbl := fun () => "00\0?11447729195.15811912587876.96 13478728930.98 16232768748.10018185049160.98 18185344072.96 18443040858.25 24115025141.10724122799997.96 26552522358.97 26552522358.99 29782203372.10829782203372.10930010325480.96 3210808038.109 35497698603.96 35497698988.95 3705762087.24  38959952907.98 38960247819.96 42148918724.97 45029014839.98 45029506359.96 46300107345.18646300107356.19248324795550.97 49921929014.10152074235542.10856172459032.97 57307948242.10757880736640.1095876716948.95  59308628695.1  61937741491.97 61937790389.96 61939863024.10062348280136.10062348288512.12862472604513.98 62473096033.96 62839777234.10766146829846.11566684767264.98 6922740008.93  00000100=00I00N00R00V00g00l01101601;01<01=01>01?01@01A01O01S01W01\01`01d02L03403803B03O03P03Q03R03S03W03`03i04204304404804<04=04>04C04GFS4SPOS2R12N1S4SPOS2R12N1S3BL0S2R1S2R1S3BL02K22K32H42H5S3BL0S3BL0S3BL0S3BL0SSSFSSS3BL02K22H42H5S2R1S2R1S3BL0S2R1S2R1S2N11B1H2H02H42H52H93H103H143H153H243H39S2N11B1H2H02H42H52H93H103H143H153H293H44S2LOS3BL01H2H0S4SPOS3BL02N1SSFFS2K4S3NSZ3BL0S3NSZ3BL0S3NSZ3BL0FFS2R1S2R1SSS3NSZS2LO".
prep IV.
zstep. zstep. zstep. if_cases K2; zify_cond K2.
-
zstep. if_cases K3; zify_cond K3.
2:{ zstep. eapply LX; eassumption. }
assert (N1 : (64 < N)%Z) by (unland K2; clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
zstep. zstep. zstep. zstep.
unfold sf_hide in LO.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
| zsimp; exact APP | zsimp; exact UNP1
| zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply LX. eapply inv_of; eassumption.
-
assert (N1 : (1 <= N <= 64)%Z) by (unland K2; clear - K2 BL0; Z.div_mod_to_equations; lia).
do 11 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R1.
destruct (shadow_probe8 bsegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
destruct (shadow_probe8 bsegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply LE; eassumption.
+ eapply LX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="RLO RHI MI ST LO KLO GOT SHB INI LAY RMC BUF OK SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma memchr_i_body :
evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x43f7c) fc None m (seg_rom bsegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof BL_ok as BL0. unfold BL in BL0.
Local Ltac2 Set LiaHints.tbl := fun () => "00d0?13078519495.86 14684412918.84 14972603573.78 162492479.78   17305236855.86 1807322599.84  1889508528.86  19628484135.11419943966000.84 22325994321.11330232449436.86 33320343373.76 3602932068.85  39480921372.85 4203475740.86  43055384156.74 46058061009.10346568687280.85 46703417572.85 46970229916.87 49921929014.82 50221378407.83 51188481948.84 51845487163.11351845487163.11452415237221.86 53510313876.86 54553403622.76 55910501615.86 56172315833.78 56185171996.85 58604970416.85 59308628179.1  59308628304.1  59308628433.1  59308628433.14 59308628566.12 59308628566.13 60334541206.96 62804018190.11262804018190.11363123389028.85 64623284016.86 6519901054.78  65622283570.10865869203986.78 6922740008.65  6950140022.101 7941138992.87  7944451815.84  8929152288.114 8937270825.124 00000100200300700800900:00J00K00V00W00\00]00^00_00d00e00f00g00h01201301401D01T01U01V01W01X01Y01Z01[01_01c01g02002;02F02G02W02g02h02i02j02k02l03003103203303C03SSSFS2LOSSSS4SPOS2R13BL02ENSS2R13BL02ENSS3BL0SSSS3BL0SSSSS3BL01H2H0SSS4SPOS2R13BL02HRS4SPOS2R13BL02ENSSSSSSSS2K0S2K1S2K2S4SPOS2K2S3BL02EN2K3S3BL02EN2K3SS4SPOS2R13BL02HRS4SPOS2R13BL02ENSSFSFS2LOSSSS4SPOS2R13BL02ENS4SPOS2R13BL02EN".
assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
pose proof LAY as LAYc. pose proof RMC as RMCc.
assert (BUFc : bytes_at bsegs m S buf) by exact BUF.
hide_all.
carve_frame 56%nat ST0.
destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
do 13 zstep.
zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
zstep. call_sp tryinit_spec. all: iprem.
do 6 zstep. zstep.
unfold sf_hide in OK.
call memchr_spec. all: iprem.
zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
pose proof hitlen_range as HR.
destruct (find_byte cc (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
-
assert (ER : RES = (S + Z.of_nat j)%Z) by (unfold memchr_res; rewrite FB; reflexivity).
assert (EN : N = (Z.of_nat j + 1)%Z) by (unfold hitlen; rewrite FB; reflexivity).
rewrite ER. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear -K2 BL0 HR EN SPOS. lia. } clear K2.
do 5 zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 HR EN. lia. } clear K3.
eapply LC; [eapply inv_of; eassumption | f_equal; lia | rewrite ER; reflexivity].
-
assert (ER : RES = 0%Z) by (unfold memchr_res; rewrite FB; reflexivity).
assert (EN : N = n) by (unfold hitlen; rewrite FB; reflexivity).
rewrite ER. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 BL0 HR EN. lia. } clear K3.
eapply LC; [eapply inv_of; eassumption | rewrite EN; symmetry; apply Z_to_bv_bv_unsigned | rewrite ER; reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End MEMCHR.
#[using="Type"] Lemma memchr_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z),
let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let n := bv_unsigned a2 in let N := hitlen cc n buf in
mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_memchr m ->
bytes_at bsegs m S buf -> memchr_ok S cc n buf ->
(S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
(RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length buf)) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
evtF bsegs RNG (memchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x43f7c) fc None m (seg_rom bsegs)).
Proof. intros. eapply memchr_i_body; eassumption. Qed.
End CANSEC1.
Notation rt_isl m := (rw_cells bsegs m 0x134160 [C8 (Z_to_bv 64 72340172838076673)]).
Section CANSEC2. Context {rc : runConstT}.
Definition strnlen_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 4384, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp) /\ bytes_at bsegs m' S buf.
Section STRNLEN.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z).
Notation S := (bv_unsigned a0).
Notation n := (bv_unsigned a1).
Notation N := (hitlen 0 n buf).
Notation L0 := (strnlen_res n buf).
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 4384)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis LAY : rt_layout m.
Hypothesis RMC : rt_real_memchr m.
Hypothesis RSL : rt_real_strnlen m.
Hypothesis ISL : rt_isl m.
Hypothesis BUF : bytes_at bsegs m S buf.
Hypothesis OK : memchr_ok S 0 n buf.
Hypothesis SEPB : (S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z.
Hypothesis SPOS : (0 < S)%Z.
Hypothesis APP : app_blk S (S + N).
Hypothesis UNP : unpoisoned m S (S + N).
Hypothesis NSZ : (N <= 2^40)%Z.
Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RB : rng RNG S (Z.of_nat (length buf)).
Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
Notation POST := (strnlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S n buf lo m).
Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition SINV (mc : word -> option byte) : Prop :=
rw_cells bsegs mc (bv_unsigned sp + -64) SAVES
/\ stk bsegs mc lo (bv_unsigned sp + -2144) /\ stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
/\ munch [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc
/\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
/\ unpoisoned mc S (S + N) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at bsegs mc S buf.
#[using="a0 RLO RHI R1"] Lemma hitlen_range2 : (0 <= N <= n)%Z.
Proof.
unfold hitlen. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>37069349879.677092301823.66 00000800;S2R11R1ES1R".
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="a0 RLO RHI R1"] Lemma hitlen_strnlen : N = Z.min (L0 + 1) n.
Proof.
unfold hitlen, strnlen_res. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>16444534670.6651103915881.6700000600>S2R11RS2R11R1E".
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition SBND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 4384 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= n < 2^64
/\ 0 <= S /\ S + N + 8 <= KEND
/\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
/\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
/\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
/\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
#[using="m ST LO KLO SPOS APP NSZ R1"] Lemma SBND_ok : SBND.
Proof.
unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
pose proof (bv_unsigned_in_range 64 a1) as NR. unfold bv_modulus in NR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in NR.
pose proof hitlen_range2 as HR.
Local Ltac2 Set LiaHints.tbl := fun () => "0020?29784462332.70 62900827686.14000000101`SS2LO3KLO4SPOS3NSZ2R13LES2AS3SPR2NR2HR1H2H02H42H52H93H103H143H153H193H203H243H253H293H303H343H353H393H403H443H45".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.
Definition SBL : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 4384 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N <= n /\ N <= 2^40 /\ n < 2^64
/\ 0 <= S /\ S + N + 8 <= 2^47
/\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
/\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
#[using="m ST LO KLO SPOS APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. pose proof hitlen_range2. unfold SBL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62905010198.6600000AS2LO4SPOS3NSZ1B1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & BUF1).
Ltac shide_all :=
change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
change (?P) with (sf_hide P) in RMC; change (?P) with (sf_hide P) in RSL; change (?P) with (sf_hide P) in ISL;
change (?P) with (sf_hide P) in BUF; change (?P) with (sf_hide P) in OK.
Ltac sprep IV :=
pose proof IV as IV0; sinv_open IV;
let B := fresh "BL" in pose proof SBL_ok as B; unfold SBL in B;
assert (RSTK' : rng RNG (bv_unsigned sp + -4384) 4384) by (eapply rng_sub'; [exact RSTK| lia]);
shide_all.
#[using="ST LO KLO BUF SEPB SPOS APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
rw_cells bsegs mc (bv_unsigned sp + -64) SAVES ->
stk bsegs mc lo (bv_unsigned sp + -2144) -> stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
munch [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
Proof.
intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
repeat (split; [assumption|]).
Local Ltac2 Set LiaHints.tbl := fun () => "0020?11805731844.76 22714190620.11000000@00HS2R11B4SEPB4SPOSS1B1H2H0".
assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
split. { eapply wr_at_transport; eassumption. }
eapply bytes_at_transport; [exact BUF | exact MU1 |]. cbn [disjoint_from]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition sregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
a0 a1 (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x134068) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31.
#[using="ST LO KLO SPOS APP NSZ R1 RSTK"] Lemma SX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x42c44) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00E0?12302439452.10914122173212.10817865510902.10136425667485.10239992552262.10341279188892.10941989626981.10943270609767.10744881826460.10946264218599.10748451966364.10849343541694.10351586824420.1085163216412.110 56578273576.10060119267940.10864017296868.10865813004644.10866208007911.10767169600375.1088699793692.109 00000100200700<00=00>00?00@00A00B00C00D00E00F00J00K00L00M00N00O00PSSS3BL0S3BL0SSSSSSSSSSS2LOSSSSSS".
sprep IV.
do 11 zstep.
pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
apply evtF_done. unfold strnlen_i_post.
replace (bv_unsigned sp - 4384)%Z with (bv_unsigned sp + -4384)%Z by lia.
do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO SPOS APP NSZ R1 RSTK RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x22 x28 x29 x30 x31,
SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 L0) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
x22 x28 x29 x30 x31)
F (Z_to_bv 64 0x42d18) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1 Hk Hc. unfold sregs. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13714642969.10213739240004.10224122881917.10236772856310.10944094519847.12850783209802.10056578273576.97 59308585478.97 59308627018.1  60890567713.10264507443218.10900000700E00M00N00[00b00i01001401C01NS2Hk2HcS2Hk2Hc3SLE2K1S3BL02HkFS2Hk2Hc2H42H5S2Hk2HcS2LO2HkS2Hk2HcS2K'S3BL02Hk2Hc3SLES3BL02Hk2Hc".
sprep IV.
revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd bsegs mc S (S + N) c UNP1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply SX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO SPOS APP NSZ R1 RSTK RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x14 x15 x16 x17 x22 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 L0) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
(Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 x22 x28 x29 x30 x31)
F (Z_to_bv 64 0x42cfc) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV N1. unfold sregs. Local Ltac2 Set LiaHints.tbl := fun () => "00B0?15389206808.11516578645250.94 19033648638.11919482125347.10924122881528.99 24991237561.10928034943372.16328442431488.11929782203372.10729784416728.99 43614754995.94 46022211189.13452076332689.10552523015483.10753510313881.10956578273576.93 59308629082.1  68646946464.94 00000400500900F00K00L00h00m00n00o01001A01N01O01P01T01X01\S2H0SS2H0S4SPOS2N13CK2S3BL0SS2N11B1H2H02H42H52H93H103H34S3CK2SSSS2K62H42H52H93H10S4SPOS2N13BL0SSS2LOS2K7S2N1".
sprep IV.
destruct (unpoisoned_check_rd bsegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. do 5 zstep.
rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
zstep. if_cases K6; zify_cond K6.
- zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
eapply SX; eassumption.
- eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO BUF SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31, SINV mc -> x9 = Z_to_bv 64 N ->
evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31)
F (Z_to_bv 64 0x42bfc) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV ->. unfold sregs. Local Ltac2 Set LiaHints.tbl := fun () => "00\0?11447730086.15311912587876.98 13478728930.10016232768748.10217567724938.17 18185049160.10018185344072.98 21217492798.10024115025141.10924122799997.98 26552522358.10126552522358.99 29591526682.16 29782203372.11029782203372.11130010325480.98 31248028574.99 3210808038.111 35497698603.98 35497698988.97 38959952907.10038960247819.98 42148918724.99 45029014839.10045029506359.98 46300107345.18746300107740.18152074235542.11055836803597.12355836811592.10256172459032.99 56578273576.95 57307948242.10957880736640.1115876716948.97  59052953946.10259055042847.98 59055092249.99 59308628695.1  60274602806.10362472604513.10062473096033.98 62839777234.1099261986838.117 00000100=00I00N00^00b00f00k01001501:01?01L01M01N01O01S01T01U01V01Z01^01c01g01k02S03;03H03I03J03K03O03P03Q03R03[03d03m04104;04?04C04D04EFS4SPOS2R12N1S4SPOS2R12N1S3BL0S3BL02K22K31H2H0S2R1S2R1S3NSZS3BL0S3BL0S3BL0S3BL0S3BL02K21H2H0SSSS2LOFSSS2R1S2R1S3BL0S2R1S2R1S2N11B1H2H02H42H52H93H103H143H153H243H39S2N11B1H2H02H42H52H93H103H143H153H193H34S4SPOS3BL02N1FFSS2LOSFFS3NSZ3BL0S3NSZ3BL0S3NSZ3BL0S2K4S3BL01H2H0S2R1S2R1SS".
sprep IV.
zstep. zstep. zstep. if_cases K2; zify_cond K2.
-
zstep. if_cases K3; zify_cond K3.
2:{ zstep. eapply SX; eassumption. }
assert (N1 : (64 < N)%Z) by (unland K2; clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
zstep. zstep. zstep. zstep.
unfold sf_hide in LO.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
| zsimp; exact APP | zsimp; exact UNP1
| zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply SX. eapply sinv_of; eassumption.
-
assert (N1 : (1 <= N <= 64)%Z) by (unland K2; clear - K2 BL0; Z.div_mod_to_equations; lia).
do 11 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R1.
destruct (shadow_probe8 bsegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
destruct (shadow_probe8 bsegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. if_cases K5; zify_cond K5.
+ eapply SE; eassumption.
+ eapply SX; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="a0 RLO RHI SPOS R1"] Lemma L0_range : (0 <= L0 <= n)%Z /\ N = Z.min (L0 + 1) n.
Proof.
pose proof hitlen_strnlen as HS. unfold strnlen_res in *. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>32067164085.6732067164085.6800000>00NS4SPOS2R12HS1RS4SPOS2R11E2HS1R".
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO ISL BUF SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma SJ : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, SINV mc -> (L0 + 1 < 2^64)%Z -> x10 = Z_to_bv 64 L0 ->
evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 1) x10 x11 x12 x13 x14 x15 x16 x17
a0 a1 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x42bd0) fc None mc (seg_rom bsegs)).
Proof.
intros until x31. intros IV L1 ->. pose proof L0_range as [LR HS]. Local Ltac2 Set LiaHints.tbl := fun () => "00>0?10651012160.99 18319861645.5  19628484000.10019628484135.1014006481375.107 46227753327.10747290164840.99 51845487163.10156578273576.97 59308628179.1  59308628304.1  59308628566.12 61753526832.10162804130354.10000000500<00C00J00K00L00M00`00d00h00l01:01A01TS3BL0S2HS2K2S2L12LRS2L12LRSSSS4SPOS3BL02K22LR2HSS2LOS2K0S2K1S2HS3BL02K22K3S2HS2K2S4SPOS3BL02K22LR2HS".
sprep IV.
assert (ISL1 : rw_cells bsegs mc 0x134160 [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]).
{ unfold sf_hide in ISL. pose proof ISL as ISL'.
eapply rw_cells_transport in ISL'; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
recell ISL' 0%nat 1%nat [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]. exact ISL'. }
zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
zstep. zstep. if_cases K2; zify_cond K2.
-
zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 LR HS K2. lia. }
assert (EN : N = n) by (clear -HS K2 LR; lia).
eapply SC; [exact IV0 |]. rewrite EN. symmetry. apply Z_to_bv_bv_unsigned.
-
zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 BL0 LR HS K2. lia. }
eapply SC; [exact IV0 |]. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="RLO RHI MI ST LO KLO GOT SHB INI LAY RMC RSL ISL BUF OK SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strnlen_i_body :
evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x42b80) fc None m (seg_rom bsegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof SBL_ok as BL0. unfold SBL in BL0. pose proof L0_range as [LR HS].
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
Local Ltac2 Set LiaHints.tbl := fun () => "01B0?10692747071.88 10873507702.11311803386017.8  12302439452.96 13316380976.96 13351392165.14814122173212.94 14972603573.88 14976486804.10617646078182.86 17854827725.86 18030760519.10519534904793.11523427917212.11323427917212.16123427917212.1622386425949.149 30149303810.10330188231019.15430190181064.15332838660918.11034976036807.95 35693770006.10636494662430.10637370542899.10637374523922.88 38547629084.11538547629084.16338547629084.16439864294064.96 40774967580.11240774967580.16040774967580.16141279188892.96 41989626981.96 43061756892.84 43270609767.93 44881826460.95 45133556400.11245882632240.95 46264218599.94 48451966364.95 48506519986.12551586824420.95 5163216412.97  51935442352.96 53504345874.12253506393489.10653945548306.15456172315833.88 56185144728.10656580371994.70 57204409776.11557919931184.95 59308628304.1  59308628304.15 60119267940.95 60274602806.92 60668852342.15960668852342.16060749751065.10663189062448.11363971692720.94 64017296871.94 6515395167.106 6519901054.88  65813004644.95 66208007911.94 67169600375.95 68372036967.11168372036967.15968372036967.1607263570864.97  7943836388.112 7943836388.160 7943836388.161 8699793692.96  8929152417.155 8935173664.168 9739449962.114 9739449962.162 9739449962.163 00000400500:00;00<00@00A00B00C00D00I00J00K00L00M00Q00R00V01001G01[01\01]01a01b01c01d01e01i01j01k01l02002102202702802902:02;02<02=02>02?02@02A02B02C02]02^02_02c02d02e02i03803903C03D03H03N03O03P03Q03R03S03T03U03V03W03X03\03]03^03_03c03d04>04X04Y04Z04^S2LOSS3BL0SSS2LOSFFSS3BL0SSSSS2FJSS2LOS4SPOS2R13BL02HS3R1c2EL2FJS4SPOS2R13BL02HS3R1c2ELS2R13BL02LR2HS3R1c1HSSS2LOFFSSS2FJSSSS2FJSSS3BL0SSSSSSSSSSSSS4SPOS2R13BL02HS3R1c2EL2FJSSS2LOSSS2K1S4SPOS2EL2FJ2K1SS3BL01H2H0SS2FJS4SEPBSSSFFSSSSSS2FJSSSS2FJSS4SPOS2R13BL02HS3R1c2EL2FJS4SPOS2R13BL02HS3R1c2EL2FJSSS2FJ".
assert (RSTK' : rng RNG (bv_unsigned sp + -4384) 4384) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
pose proof LAY as LAYc. pose proof RMC as RMCc. pose proof RSL as RSLc.
pose proof APP as APPc. pose proof WR1 as WR1c. pose proof R1 as R1c.
assert (BUFc : bytes_at bsegs m S buf) by exact BUF. assert (OKc : memchr_ok S 0 n buf) by exact OK.
shide_all.
carve_frame 64%nat ST0.
destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
do 13 zstep. zstep.
call_sp tryinit_spec. all: iprem.
do 5 zstep. zstep.
match goal with H : stk bsegs _ lo (bv_unsigned sp + -2144) |- _ => carve_frame 32%nat H end.
do 8 zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
assert (UNP1 : unpoisoned m1 S (S + N)) by (unfold sf_hide in UNP; eapply unpoisoned_munch; [exact UNP | exact MU1 |]; cbn [disjoint_from]; clear -BL0; lia)
end end.
call_sp memchr_i_spec. all: iprem.
rewrite ?unsigned_lit in * by lia. change ((0 mod 256)%Z) with 0%Z in *.
try rename POST into RTI9.
assert (TAIL : forall mc x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 jk,
rw_cells bsegs mc (bv_unsigned sp + -2176) [CB 8 jk; C8 (Z_to_bv 64 1); C8 sp; C8 (Z_to_bv 64 0x42bd0)] ->
rw_cells bsegs mc (bv_unsigned sp + -64) SAVES ->
stk bsegs mc lo (bv_unsigned sp + -2176) -> stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
munch [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
rt_got mc -> rt_shbase mc -> rt_layout mc ->
evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 0x934f0) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp x5 x6 x7 a1 a0
(Z_to_bv 64 (memchr_res S 0 n buf)) x11 x12 x13 x14 x15 x16 x17
a0 a1 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x934f0) fc None mc (seg_rom bsegs))).
{ intros until jk. intros FRS FR9 ST2 STM9 MU9 WM9 MI9 G1 G2 G3.
assert (IV : SINV mc).
{ pose proof (stk_release _ _ _ _ _ ST2 FRS ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
replace (bv_unsigned sp + -2176 + Z.of_nat 32)%Z with (bv_unsigned sp + -2144)%Z in ST3 by lia.
eapply sinv_of; eassumption. }
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
- assert (ER : memchr_res S 0 n buf = (S + Z.of_nat j)%Z) by (unfold memchr_res; rewrite FB; reflexivity).
assert (EL : L0 = Z.of_nat j) by (unfold strnlen_res; rewrite FB; reflexivity).
pose proof (find_byte_Some _ _ _ FB) as [FJ _]. rewrite firstn_length in FJ.
rewrite ER. zstep. if_cases K1; zify_cond K1. { exfalso. unland K1. clear -K1 BL0 LR HS EL SPOS FJ. Z.div_mod_to_equations; lia. } clear K1.
do 6 zstep. zstep.
eapply SJ; [exact IV | lia | f_equal; lia].
- assert (ER : memchr_res S 0 n buf = 0%Z) by (unfold memchr_res; rewrite FB; reflexivity).
assert (EL : L0 = n) by (unfold strnlen_res; rewrite FB; reflexivity).
unfold sf_hide in OK. pose proof OK as OK'. unfold memchr_ok in OK'. rewrite FB in OK'.
rewrite ER. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1. cbv in K1. lia. } clear K1.
do 5 zstep. zstep.
eapply SJ; [exact IV | lia | rewrite EL; symmetry; apply Z_to_bv_bv_unsigned]. }
eapply TAIL; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End STRNLEN.
#[using="Type"] Lemma strnlen_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z),
let S := bv_unsigned a0 in let n := bv_unsigned a1 in let N := hitlen 0 n buf in
mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4384)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_memchr m -> rt_real_strnlen m -> rt_isl m ->
bytes_at bsegs m S buf -> memchr_ok S 0 n buf ->
(S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
(RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length buf)) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
evtF bsegs RNG (strnlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x42b80) fc None m (seg_rom bsegs)).
Proof. intros. eapply strnlen_i_body; eassumption. Qed.
End CANSEC2.
