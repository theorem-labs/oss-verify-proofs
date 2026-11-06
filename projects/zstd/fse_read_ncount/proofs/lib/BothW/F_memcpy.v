(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StrwF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
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
Section CANSEC1. Context {rc : runConstT}.
Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at bsegs m' (bv_unsigned a1) src.
Section Proofs.
Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Hypothesis RS : rng RNG S n.
Hypothesis RD : rng RNG D n.
Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at bsegs m1 S src /\ u8arr bsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv bsegs m1 /\ munch W m m1 /\ wmono bsegs m m1.
Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
Ltac inv_tac :=
lazymatch goal with
| |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.
Ltac fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite LEN in DST
end;
finish2.
Tactic Notation "use" uconstr(L) :=
eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x93000 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>14960463391.6315007238884.6617614059739.6817627789829.7118461681647.8221378083199.7927137092668.6935854508628.6835854985538.6837460500211.7137460828367.694095858866.79 41440498486.8041440498487.7948425388885.7948425388890.7653519152272.6455911282436.6556033789200.665670485634.71 58422563556.6958424662383.7059310683863.6560319515480.7160372992323.7764943576677.6867361222914.7267363322505.738471139633.66 8471139633.69 8471139760.64 8701968733.68 9537802130.68 00000800I00Q00m01B01T01i02E02^02l03=03R03d04504G04X04]04o05D05L05Q05V05^05c06506G06L06Q06V06[06`06h06mS3LEN2RrS3LEN2HP2Hr2Rr2K1S3LEN2HPS3LEN2AB3SEP2HP2Hr2Rr3Hl42K1S3LEN2HP2Hr2Rr3Hl42K1S3LEN2HP2Hr2Rr3Hl4S3LEN2HP2Hr2Rr3Hl42K1S3LEN2AB3SEP2HP2Hr2Rr3Hl42K1S3LEN2AB3SEP2HP2Hr2Rr3Hl4S3LEN2HP2Hr2RrS3LEN2HP2Hr2Rr2K1S3LEN2HP2Hr2Rr3Hl42K1S3LEN2HP2Hr2Rr3Hl4S3LEN2HP2Hr2Rr2K1S3LEN2HP2Hr2Rr3Hl4S3LEN2HP2Hr2Rr2K1S3LENS3LEN2HP2Hr2Rr3Hl4S3LEN2AB2Hr2Rr3Hl42K1S3LEN2HPS3LENS3LENS3LEN2K2S3LENS3LEN2HP2Hr2Rr3Hl4S3LEN2HP2Hr2Rr3Hl4S3LENS3LENS3LENS3LENS3LENS3LEN2HPS3LEN".
rewrite land_bit_2 by lia.
zstep. if_cases K2; zify_cond K2.
-
destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
window P 2%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat.
zstep. zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ zstep. fin.
+ window (P + 2)%Z 1%nat HW1.
ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
- destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
+ zstep. fin.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92fd4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
Local Ltac2 Set LiaHints.tbl := fun () => "00K0>13229325859.7715232684526.6817614059739.6818461681646.8021378083198.8022209901305.7022212000114.6930652131693.683174382116.68 35854508628.6835854985538.684095858876.78 41440498485.8143819961571.6848425388893.7152585647649.6855913543746.6358422563556.6958424662383.7058990801936.7860321612658.6860372992323.7767361222914.6967363322505.7068039493266.688701968733.68 9537802130.68 00000>00F00N00\00j00o01401901>01S01h02602D02R02`02n03<03A03F03T03Y03g03l04104604>04CS3LEN2HP2Hr2RrS3LEN2HPS3LEN2HPS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LEN2AB3SEP2HP2Hr2RrS3LEN2AB3SEP2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LEN2HPS3LEN".
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92fcc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.631954409626.65 39327911311.6452585996226.6553512850223.6459308586639.657486163061.65 00000800@00E00V00[00b013S3LEN2RrS3LEN2HPS3LENS3LEN2HP2Hr2Rr2HlS3LENS3LEN1KS3LEN2HP2Hr2Rr2Hl".
rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92f80 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
Local Ltac2 Set LiaHints.tbl := fun () => "00_0>13229325859.8114887710883.7217614059739.7218461681646.8421378083197.8522209901305.7422212000114.7328933012513.7231172317970.723174232370.72 331373769.74  333469506.73  33947626002.7235854508628.7235854985538.7236956519214.8436981015021.7238143086867.8139872627390.8440553280942.724095858876.82 41159228708.7241442595646.8641878318348.8242519607010.7342521705833.744379120953.74 4381220530.73 48425388893.7548806683649.8154345795443.8155913543746.6358422563556.7358424662383.7458990801936.8259048792025.7459050886226.7360321612658.7260372992323.8163453960940.8267361222914.7367363322505.7468039493266.728701968733.72 8767047774.84 933003762.72  9537802130.72 00000>00L00T00b01001501:01H01M01R01W01\01a02602K02Y02^02l03:03B03P03U03c04104604;04@04E04S04a04o05=05B05G05U05Z05_05d06206@06E06J06O06W06e06j06oS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HPS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LEN2AB3SEP2HP2Hr2RrS3LEN2AB3SEP2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HPS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LEN2HPS3LEN2HP2Hr2RrS3LENS3LEN".
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92ca8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.631954409626.65 39327911311.6452585996226.6553512850223.6459308586639.657486163061.65 00000800@00E00V00[00b013S3LEN2RrS3LEN2HPS3LENS3LEN2HP2Hr2Rr2HlS3LENS3LEN1KS3LEN2HP2Hr2Rr2Hl".
rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92f78 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.631954409626.65 21589288373.6528933189058.6553512850223.6459308586639.658599378191.64 00000800@00Q00b00g00n013S3LEN2RrS3LEN2HPS3LEN2HP2Hr2Rr2HlS3LEN2HP2Hr2Rr2HlS3LENS3LEN1KS3LEN".
rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92ca0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.631954409626.65 21589288373.6528933189058.6553512850223.6459308586639.658599378191.64 00000800@00Q00b00g00n013S3LEN2RrS3LEN2HPS3LEN2HP2Hr2Rr2HlS3LEN2HP2Hr2Rr2HlS3LENS3LEN1KS3LEN".
rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92eec m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
Local Ltac2 Set LiaHints.tbl := fun () => "01H0>10123188876.9011876150401.8913229325859.8914124842244.8014831506370.8114833604681.8217614059739.8018461681646.9221378083197.9322060137616.9022209901305.8222212000114.8122591487219.8924858419934.9225467773476.8028617768652.902908411198.92 31172317970.8031698834028.903174232370.80 331373769.82  333469506.81  33947626002.8034542207534.8035828976930.8135831072425.8235854508628.8035854985538.8036956519214.9237417757316.8038143086867.8938919300617.8238921399682.8139872627390.9240521388254.924095858876.90 41061126204.9041159228708.8041442595646.9441878318348.9042519607010.8142521705833.8243789150489.824379120953.82 43791245970.814381220530.81 47056395501.8048425388893.8348806683649.8950193414060.9050245381742.9250705750049.8051026294307.8052273755634.8152275854969.8253166764541.9354345795443.8955687891801.8255689986258.8155913543746.6358422563556.8158424662383.8258990801936.9059048792025.8259050886226.8159669457796.8060321612658.8060372992323.8962098688838.9463275709282.8163277807849.8263453960940.906388747923.89 65081149156.8065297434404.8065797790514.8165799884985.8267361222914.8167363322505.8268039493266.8068107253092.8068714759086.927849922052.80 8701758027.80 8701968733.80 8767047774.92 933003762.80  9537802130.80 00000>00L00Z00_00d00i01101?01M01[01`01e02302A02F02T02b02g03503:03?03D03I03Q03V03[04004E04S04X04f04k05005>05L05Z05h05m06;06I06N06S06X06]06b06g06l07:07H07V07d08208@08E08J08X08f08k09009>09C09H09V09[09`09e09j0:80:F0:K0:P0:^0:l0;10;60;;0;@0;E0;J0;O0;T0;b0;g0;o0<70<E0<J0<OS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LEN2HPS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LEN2HPS3LENS3LENS3LEN2AB3SEP2HP2Hr2RrS3LEN2AB3SEP2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LEN2HP2Hr2RrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LEN2HPS3LEN2HPS3LEN2HP2Hr2RrS3LENS3LEN".
window P 16%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
zstep.
st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
zstep.
st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
zstep.
use (mc_a04 _ _ (P + 16)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92dbc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00?0>14960463391.6315232684526.7317614059739.701954409626.65 23669985285.8427291075718.8530652131693.733174382116.73 35856676733.7339327911311.6452585647649.7353512850223.6455913379676.6559308586639.657486163061.65 00000800D00L00T00i01>01G01P01l02102F02K02\02c034S3LEN2RrS3LEN2HP3Lq0S3LEN2HPS3LEN2HPS3LEN2HP2Hr2Rr2Hl3Lq0S3LEN2HP2Hr2Rr2Hl3Lq0S3LEN3Lq0S3LEN3Lq0S3LEN2AB3SEP2HP2Hr2Rr2Hl3Lq0S3LENS3LEN2HP2Hr2Rr2Hl3Lq0S3LENS3LEN2HP2Hr2Rr2HlS3LEN1KS3LEN2HP2Hr2Rr2Hl".
rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92d9c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00G0>1739602051.88 17614059739.731954350798.64 21589299169.6423669985285.8727291075718.912766356686.86 28606789727.9028933012513.7929010566698.6429010765213.7930652198372.8030654293615.8131478707699.793172197403.76 35854985538.7935856676734.7936981015021.7940553280942.7941159228708.7955913389320.6468515850823.718699810932.76 00000F00N00V00W00i01?01]02302402<02L02Y02f03<03E03b04?04L04\04i05705M05YS3LEN2HP2Hr2K83Lq03Lq1S3LEN2HPS3LEN2HPFS3LEN2HP2Hr2K83Lq0S3LEN2HP2Hr2K83Lq03Lq1S3LEN2HP2Hr2Rr2K83Lq03Lq11H2H0S3LEN2HP2Hr2K83Lq03Lq1FS3LEN2RrS3LEN2Rr3Lq03Lq1S3LEN3Lq03Lq1S3LEN3Lq03Lq1S3LEN2HP2Hr2K83Lq03Lq1S3LEN3Lq0S3LEN2AB3SEP2HP2Hr2K83Lq03Lq1S3LEN2AB3SEP2HP2Hr2K83Lq03Lq1S3LEN3Lq03Lq1S3LEN2HP3Lq03Lq1S3LEN3Lq03Lq1S3LEN2HP2Hr2K8S3LEN2HP2Hr2Rr2K81H2H0S3LEN2HP3Lq0".
if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92d6c m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00R0?1739602060.96  17614059739.80 23669985295.88 25467319239.93 27291075718.10428606789726.10430413233184.93 30629262582.93 30652198372.93 30654293615.94 3172197403.83  34542670797.93 3525611882.93  35854985538.92 35856676728.92 35986998188.93 38334802883.98 38705000451.10141160876824.86 42332822672.93 47055932686.93 49618201255.93 55913379906.63 60395700433.10160736276752.10261589165561.94 61591264882.93 65299093785.89 67728738874.93 8699810932.83  8699810934.89  8699810935.86  9468518585.94  9470618418.93  00000F00Q00c01;01Y02702R02j03B03Z03f04A04f05K06006Q06k07I07Y08:08R09009>09\0::0:R0:j0;>0;V0;e0<<0<O0<g0=?S3LEN2HK2HP2Hr3Lq03Lq1S3LEN2HK2HPS3LEN2HK2HP2Hr3Lq0S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq32KlS3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq0S3LEN2HK2HP3Lq03Lq13Lq23Lq3S3LEN2AB3SEP2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2AB3SEP2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2AB3SEP2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq32KlS3LEN2HK2HP2Hr3Lq03Lq13Lq2S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq1S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq32KlS3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK2Hr3Lq03Lq13Lq23Lq32KlS3LEN2HK2HP2HrS3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq2S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK2HP3Lq0S3LEN2HK2HP3Lq03Lq13Lq2S3LEN2HK2HP3Lq03Lq1S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3".
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92d60 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0050>1952252736.61 23620210391.6133001337551.6146756385821.618528200964.61 00000800=00F00R00aS3LEN2HPS3LENS3LEN3K16S3LEN2HP3K16S3LEN2AB3SEP2HP".
if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92ce4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using AB LEN SEP RS RD.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00e0?11682182573.10012052116205.10314939502105.10914939502106.10815532809353.10915532809354.10816246187601.64 17625870649.98 17627852546.98 17799441610.10725465216029.10027291075718.11028450517914.86 28606789726.11030629262582.99 30652198372.99 30654293615.1003207237953.99  34540583959.10034949646288.1073523526320.100 3525611882.99  35986998188.99 37371927852.99 42330731338.10042332822672.99 42778715608.85 42778738477.99 44141951062.95 45238635437.99 45494427840.99 47055932686.99 47058035412.10047747482048.85 48646401325.10649018563173.11150707785240.10051430137632.85 54463712011.99 5668449992.86  5670546306.89  5670546307.92  5670546308.95  59059322704.89 60395700446.11060736276766.11061025648849.92 61589165561.10061591264882.99 65019182622.1007503760135.99  9468518585.100 9470618418.99  00000E00^00_00`00a00b01001X02@02m03H03i04404U05005K05f06D06b07L07m08U09909T0:90:]0:h0;F0;]0;^0<<0<W0=20=:0=W0>80>90>A0>\0>j0?<0?R0?l0@;0@\0A=0AP0Ak0BF0BG0Bb0C=0CXS3LEN2HK2HP2Hr2Lw3Lq1S3LEN2HK2HP2Hr2Lw3Lq13Lq2FFFFS3LEN2HK2HP2HrS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2LwS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K161H2H0S3LEN2HK2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K16S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2HPS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq3FS3LEN2HK2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HKS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq3S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4FS3LEN2HKS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2LwS3LEN2HK2HP2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq1S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq2S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4".
window (P - 2)%Z 20%nat HW.
pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92cc8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>11445594946.681954168185.68 1954412143.67 21378083199.7923207601716.6824496052053.6832189479286.6735854578228.6835854985538.6837961114563.6841440498486.8047747482048.6747747893974.6855913381321.6257481181359.6857716083907.6858422563556.6958424662383.7064329521941.688712226349.68 00000;00F00N00\00d00l01101F01[01i02702<02D02O02W02b02j03203303;S3LEN2HP2LwS3LEN2HP2LwS3LEN2HPS3LEN2HP2Hr2LwS3LEN2LwS3LEN2LwS3LENS3LEN2AB3SEP2HP2Hr2LwS3LEN2AB3SEP2HP2Hr2LwS3LEN2HP2Hr2LwS3LEN2HP2Hr2LwS3LENS3LEN2LwS3LEN2HP2HrS3LEN2LwS3LEN2Hr2LwS3LEN2LwS3LEN2LwFS3LEN2Lw".
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92dec m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using AB LEN SEP RS RD.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00e0?14939502105.10914939502106.10816246187601.64 17799441610.10725465216029.10027291075718.11027869909680.99 28606789726.11028902232586.86 29547073601.92 30629262582.99 30652198372.99 30654293615.1003130479241.109 3130479242.108 32871115528.85 32871133693.99 34239283936.85 34540583959.10034949646288.1073523526320.100 3525611882.99  35986998188.99 37057556349.10338442233144.86 38444329074.89 38444329075.92 38444329076.95 41527505799.99 42330731338.10042332822672.99 42608138941.10645238635437.99 46717093062.95 47055932686.99 47058035412.10047747482048.85 50707785240.1005270709493.111 54463712011.99 56355875692.99 5638810941.100 57286117777.99 60395700446.11060736276766.11061589165561.10061591264882.99 61736020672.89 63927126121.98 63929341522.98 65019182622.1009468518585.100 9470618418.99  00000100200@00m01H01i02G02h03303F03a04<04W04X04Y04d05B05J05h06R07307[08?08X08f09809N09h0:C0:h0;L0;i0;j0<A0<\0=70=?0=@0=a0><0>W0>l0?J0?k0@L0@g0AB0AQ0B90Ba0Bb0C=0CXFFS3LEN2HK2HP2HrS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2LwS3LEN2HK2Lw3Lq13Lq2S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FFS3LEN2HK2HPS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HKS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K161H2H0S3LEN2HK2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2HP2Hr2Lw3Lq13Lq2S3LEN2HK2HP2LwS3LEN2HK2HP2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K16S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq3FS3LEN2HK2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HKFS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq1S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4FS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4".
window (P - 1)%Z 20%nat HW.
pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92dd8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>1954168185.68 1954412143.67 32189479286.6735854578228.6841440498493.7347575940095.6847747482048.6747747893974.6849684669621.6855495042850.6855913381321.6258422498925.6860842786339.6861231522292.6864329521941.6800000;00C00H00]00k01301801@01H01S01^01f02102902:S3LEN2HP2LwS3LEN2HPS3LENS3LEN2AB3SEP2HP2Hr2LwS3LEN2HP2Hr2LwS3LEN2LwS3LENS3LEN2LwS3LEN2LwS3LEN2HP2LwS3LEN2HP2HrS3LEN2LwS3LEN2Hr2LwS3LEN2LwF".
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92e80 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using AB LEN SEP RS RD.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00e0?13559082540.99 14939502105.10914939502106.10815142433245.10616246187601.64 17799441610.10720461994225.99 25465216029.10025516933792.89 27291075718.11027324926471.99 28606789726.11029060250920.85 29060294621.99 30629262582.99 30652198372.99 30654293615.10034540583959.10034949646288.1073523526320.100 3525611882.99  35986998188.99 36029045281.92 39837713106.89 39837713107.92 39837713108.95 39839811480.86 42330731338.10042332822672.99 43927186569.10943927186570.10845238635437.99 45838477930.86 46528672533.11146896642141.10047055932686.99 47058035412.10047747482048.85 48411116489.98 48412876274.98 49862951696.99 50707785240.10051556470438.95 54463712011.99 60395700446.11060736276766.11061589165561.10061591264882.99 65019182622.1007338841760.85  9468518585.100 9470618418.99  9566550941.103 00000K00L00M00j01801e02C02^02m03N03i04J04U05305N05i06D06b07O08008X09<09O09a0:70:Q0:_0;D0;h0;i0;j0;k0<60<W0<l0=G0=b0=j0>R0?:0?X0?Y0@00@K0@l0AM0Ah0BC0BD0BL0Bg0CB0C[S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FFS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq3S3LEN2HK2HP2HrS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq1S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HPS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq13Lq23Lq3S3LEN2HK2HP2LwS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K16S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlFFFS3LEN2HK2LwS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq1S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HKS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq42KlFS3LEN2HK2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FS3LEN2HKS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq2".
window (P - 3)%Z 20%nat HW.
pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ use (mc_978 _ _ (P + 16)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92e5c m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00G0>12904082803.6818461681647.7919265887139.681954168185.68 1954412143.67 21378083199.7922593628578.6830723275572.6832189479286.6735854578228.6835854985538.6841440498486.8043772821919.6847747482048.6747747893974.6851735867829.6852099707821.6855913381321.6258422563556.6958424662383.7064329521941.6867361222914.6967363322505.7000000>00L00W00b00j01801C01K01P01e02:02H02P02U02]02e02m03803@03H03I03Q03YS3LEN2HP2Hr2LwS3LEN2HP2Hr2LwS3LEN2Hr2LwS3LEN2HP2LwS3LEN2HPS3LEN2HP2Hr2LwS3LEN2HP2LwS3LEN2LwS3LENS3LEN2AB3SEP2HP2Hr2LwS3LEN2AB3SEP2HP2Hr2LwS3LEN2HP2Hr2LwS3LEN2LwS3LENS3LEN2LwS3LEN2LwS3LEN2LwS3LEN2HP2HrS3LEN2LwS3LEN2LwFS3LEN2LwS3LEN2Lw".
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92cb4 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00=0>17614059739.661954349123.70 1954350020.71 23669985294.7332189484253.7132189484890.7046067125452.7046067126091.7147747445867.7147747446764.7055913379906.6159836705152.7059836705287.7100000800D00P00_00h01101=01I01R01[01f01g01hS3LEN2HPS3LEN2HP3Lq0S3LEN2HP3Lq0S3LEN2HP2Hr3Lq0S3LEN3Lq0S3LEN3Lq0S3LEN2Hr3Lq0S3LEN2Hr3Lq0S3LEN3Lq0S3LEN3Lq0S3LEN2HP2HrFF".
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92c90 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>1952251972.61 1952252736.62 34949646288.6941711908335.6246069222603.6150707785240.6258165550833.698528200964.62 8528201216.61 00000800@00U00V00_00`01101=01LS3LEN2HPS3LEN2HPS3LEN2HP3K323K161H2H0FS3LEN3K32FS3LEN2HP3K161H2H0S3LEN2HP3K32S3LEN2AB3SEP2HP".
if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evtF bsegs RNG POST (ST 0x92c88 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP RS RD.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>14527800125.6155713077998.618539203201.63 00000800=00>S3LEN2HPS3LENF".
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evtF bsegs RNG POST (ST 0x92c58 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using AB LEN SEP RS RD.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00B0>15007267655.6117614059739.6319620497067.7235854508628.6335987008627.6539332109038.6441440498488.7343984391875.6544096333846.6544098420809.6448425388888.6949682117334.6449684208265.6558422962257.6558425049102.648530298113.65 9535722215.64 9537829560.65 00000;00F00G00Y00d00l01701?01M01X01c01k02302;02C02U02]02eS3LEN2HK2HPS3LEN2HK2HPFS3LEN2AB3SEP2HK2HPS3LEN2HK2HPS3LEN2HKS3LEN2HK2HPS3LEN2HKS3LEN2HK2HP2K1S3LEN2HK2HPS3LEN2HK2HPS3LEN2HKS3LEN2HKS3LEN2HKS3LEN2HKS3LEN2AB3SEP2HK2HPS3LEN2HKS3LEN2HK".
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma memcpy_body : forall junk,
rw_cells bsegs m D [CB (Z.to_nat n) junk] -> bytes_at bsegs m S src -> mem_inv bsegs m ->
evtF bsegs RNG POST (ST 0x92c40 m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using AB LEN SEP RS RD.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>21981031364.4925708206614.6525708207259.5825708256798.5125712457666.5135283523713.5135296064472.5835296064853.6535296112989.5139334206190.5039334206190.5143545014749.5143549202433.5155163157952.515960583647.65 5960585042.58 5960601047.51 5964801035.51 8385880958.51 00000500600700800900:00;00<00=00B00G00O00Z00_00`00a00b00c00hS3LENFFFFFFFFS3LENS3LENS3LEN2ABS3LEN2AB2K0S3LENFFFFS3LEN".
pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
change 0%nat with (Z.to_nat 0) in CP. clear DST0.
zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
-
zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
+ use (mc_71c m junk 0%Z).
+ use (mc_7ec m junk 0%Z).
- zstep. if_cases K0; zify_cond K0.
+ zstep. use (mc_714 m junk 0%Z).
+ zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.
#[using="Type"] Lemma memcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at bsegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv bsegs m ->
rng RNG (bv_unsigned a1) (bv_unsigned a2) ->
rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
evtF bsegs RNG (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x92c40) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI RS RD.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32139438783.4800000<S3LEN1B2B21R".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
