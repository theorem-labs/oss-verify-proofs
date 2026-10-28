(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope bv_scope.
Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at usegs m' (bv_unsigned a1) src.
Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at usegs m1 S src /\ u8arr usegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv usegs m1 /\ munch W m m1 /\ wmono usegs m m1.
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
evt usegs POST (ST 0x1c4f0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00I0>14960463391.5915007238884.6217614059739.6417627789829.6727137092668.6535854508628.6435854985538.6437460500211.6737460828367.6553519152272.6055911282436.6156033789200.625670485634.67 58422563556.6558424662383.6659310683863.6160319515480.6764943576677.6467361222914.6867363322505.698471139633.62 8471139633.65 8471139760.60 8701968733.64 9537802130.64 00000800I00Q00m01B01^02702H02Y02Z02i03>03F03K03P03X03]03l04104604;04@04A04I04NS3LEN2RrS3LEN2HP2Hr2Rr2K1S3LEN2HPS3LEN2AB3SEP2HP2Hr2Rr3Hl42K1S3LEN2HP2Hr2Rr3Hl42K1S3LEN2AB3SEP2HP2Hr2Rr3Hl42K1S3LEN2AB3SEP2HP2Hr2Rr3Hl4S3LEN2HP2Hr2Rr2K1S3LEN2HP2Hr2Rr2K1SS3LEN2HP2Hr3Hl4S3LEN2AB2Hr2Rr3Hl42K1S3LEN2HPS3LENS3LENS3LEN2K2S3LENS3LEN2HP2Hr3Hl4S3LENS3LENS3LENS3LENSS3LEN2HPS3LEN".
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
evt usegs POST (ST 0x1c4c4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>15232684526.6417614059739.6422209901305.6622212000114.6530652131693.643174382116.64 35854508628.6435854985538.6443819961571.6452585647649.6455913543746.5958422563556.6558424662383.6660321612658.6467361222914.6567363322505.6668039493266.648701968733.64 9537802130.64 00000800@00E00J00O00T00i01>01F01N01\01a01f01k02002502:02B02GS3LEN2HPS3LEN2HPS3LENS3LENS3LENS3LENS3LEN2AB3SEP2HP2Hr2RrS3LEN2AB3SEP2HP2Hr2RrS3LEN2HPS3LEN2HrS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HPS3LEN".
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c4bc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.591954409626.61 39327911311.6052585996226.6153512850223.6059308586639.617486163061.61 00000800@00A00R00S00Z00kS3LEN2RrS3LEN2HPSS3LEN2HP2Hr2Rr2HlSS3LEN1KS3LEN2HP2Hr2Rr2Hl".
rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c470 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
Local Ltac2 Set LiaHints.tbl := fun () => "00O0>14887710883.6817614059739.6822209901305.7022212000114.6928933012513.6831172317970.683174232370.68 331373769.70  333469506.69  33947626002.6835854508628.6835854985538.6836981015021.6840553280942.6841159228708.6842519607010.6942521705833.704379120953.70 4381220530.69 55913543746.5958422563556.6958424662383.7059048792025.7059050886226.6960321612658.6867361222914.6967363322505.7068039493266.688701968733.68 933003762.68  9537802130.68 00000800@00E00J00R00W00\00a00f00k01@01U01Z01b01g01l02102602;02I02N02S02X02]02b02g02l03103903>03CS3LEN2HPS3LEN2HPS3LENS3LENS3LEN2HrS3LENS3LENS3LENS3LENS3LENS3LEN2AB3SEP2HP2Hr2RrS3LEN2AB3SEP2HP2Hr2RrS3LENS3LEN2HPS3LENS3LENS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HPS3LENS3LEN".
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
evt usegs POST (ST 0x1c198 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.591954409626.61 39327911311.6052585996226.6153512850223.6059308586639.617486163061.61 00000800@00A00R00S00Z00kS3LEN2RrS3LEN2HPSS3LEN2HP2Hr2Rr2HlSS3LEN1KS3LEN2HP2Hr2Rr2Hl".
rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c468 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.591954409626.61 21589288373.6128933189058.6153512850223.6059308586639.618599378191.60 00000800@00Q00b00c00j00kS3LEN2RrS3LEN2HPS3LEN2HP2Hr2Rr2HlS3LEN2HP2Hr2Rr2HlSS3LEN1KS".
rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c190 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>14960463391.591954409626.61 21589288373.6128933189058.6153512850223.6059308586639.618599378191.60 00000800@00Q00b00c00j00kS3LEN2RrS3LEN2HPS3LEN2HP2Hr2Rr2HlS3LEN2HP2Hr2Rr2HlSS3LEN1KS".
rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c3dc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
Local Ltac2 Set LiaHints.tbl := fun () => "00h0>14124842244.7614831506370.7714833604681.7817614059739.7622209901305.7822212000114.7725467773476.7631172317970.763174232370.76 331373769.78  333469506.77  33947626002.7634542207534.7635828976930.7735831072425.7835854508628.7635854985538.7637417757316.7638919300617.7838921399682.7741159228708.7642519607010.7742521705833.7843789150489.784379120953.78 43791245970.774381220530.77 47056395501.7650705750049.7651026294307.7652273755634.7752275854969.7855687891801.7855689986258.7755913543746.5958422563556.7758424662383.7859048792025.7859050886226.7759669457796.7660321612658.7663275709282.7763277807849.7865081149156.7665297434404.7665797790514.7765799884985.7867361222914.7767363322505.7868039493266.7668107253092.767849922052.76 8701758027.76 8701968733.76 933003762.76  9537802130.76 00000500:00?00G00L00Q00V00[00`00e00j00o01701<01A01V01k02002502:02?02D02I02N02S02X02]02b02j03203703<03A03F03T03Y03^03c03h03m04204704<04A04F04K04P04U04Z04_04d04i05105905>05CS3LENS3LENS3LENS3LEN2HPS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HPS3LENS3LENS3LEN2AB3SEP2HP2Hr2RrS3LEN2AB3SEP2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HrS3LEN2HPS3LENS3LENS3LENS3LENS3LEN2HP2Hr2RrS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HPS3LEN2HPS3LENS3LEN".
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
evt usegs POST (ST 0x1c2ac m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00=0>14960463391.5915232684526.6917614059739.661954409626.61 30652131693.693174382116.69 35856676733.6939327911311.6052585647649.6953512850223.6055913379676.6159308586639.617486163061.61 00000800D00L00T00]00f01B01C01X01Y01g01n02?S3LEN2RrS3LEN2HP3Lq0S3LEN2HPS3LEN2HPS3LEN3Lq0S3LEN3Lq0S3LEN2AB3SEP2HP2Hr2Rr2Hl3Lq0SS3LEN2HP2Hr2Rr2Hl3Lq0SS3LEN2HP2Hr2HlS3LEN1KS3LEN2HP2Hr2Rr2Hl".
rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c28c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>17614059739.691954350798.60 21589299169.602766356686.82 28933012513.7529010566698.6029010765213.7530652198372.7630654293615.7731478707699.753172197403.72 35854985538.7535856676734.7536981015021.7540553280942.7541159228708.7555913389320.6068515850823.678699810932.72 00000800@00A00_00`00h01801E01R01h02102N02k03803H03U03c04904ES3LEN2HPS3LEN2HPFS3LEN2HP2Hr2Rr2K83Lq03Lq11H2H0FS3LEN2RrS3LEN2Rr3Lq03Lq1S3LEN3Lq03Lq1S3LEN3Lq03Lq1S3LEN2HP2Hr2K83Lq03Lq1S3LEN3Lq0S3LEN2AB3SEP2HP2Hr2K83Lq03Lq1S3LEN2AB3SEP2HP2Hr2K83Lq03Lq1S3LEN3Lq03Lq1S3LEN2HP3Lq03Lq1S3LEN3Lq03Lq1S3LEN2HP2Hr2K8S3LEN2HP2Hr2Rr2K81H2H0S3LEN2HP3Lq0".
if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c25c m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00J0>17614059739.7625467319239.8930413233184.8930629262582.8930652198372.8930654293615.903172197403.79 34542670797.893525611882.89 35854985538.8835856676728.8835986998188.8941160876824.8242332822672.8947055932686.8949618201255.8955913379906.5961589165561.9061591264882.8965299093785.8567728738874.898699810932.79 8699810934.85 8699810935.82 9468518585.90 9470618418.89 00000;00S00n01F01^02602B02]03>03c04H04i05905Z06206P06^07607N07b08:08I08`09309K09cS3LEN2HK2HPS3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq32KlS3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq0S3LEN2HK2HP3Lq03Lq13Lq23Lq3S3LEN2AB2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2AB3SEP2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2AB3SEP2HK2HP2Hr3Lq03Lq13Lq23Lq3S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq32KlS3LEN2HK3Lq03Lq1S3LEN2HK2HP2Hr3Lq03Lq13Lq23Lq32KlS3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK2Hr3Lq03Lq13Lq23Lq32KlS3LEN2HK2HP2HrS3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq2S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK2HP3Lq0S3LEN2HK2HP3Lq03Lq13Lq2S3LEN2HK2HP3Lq03Lq1S3LEN2HK3Lq03Lq13Lq23Lq3S3LEN2HK3Lq03Lq13Lq23Lq3".
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
evt usegs POST (ST 0x1c250 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0050>1952252736.57 23620210391.5733001337551.5746756385821.578528200964.57 00000800=00F00R00]S3LEN2HPS3LENS3LEN3K16S3LEN2HP3K16S3LEN2AB2HP".
if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c1d4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00]0?14939502105.10514939502106.10415532809353.10515532809354.10416246187601.60 17625870649.94 17627852546.94 17799441610.10325465216029.96 28450517914.82 30629262582.95 30652198372.95 30654293615.96 3207237953.95  34540583959.96 34949646288.1033523526320.96  3525611882.95  35986998188.95 37371927852.95 42330731338.96 42332822672.95 42778715608.81 42778738477.95 44141951062.91 45238635437.95 45494427840.95 47055932686.95 47058035412.96 47747482048.81 50707785240.96 51430137632.81 54463712011.95 5668449992.82  5670546306.85  5670546307.88  5670546308.91  59059322704.85 61025648849.88 61589165561.96 61591264882.95 65019182622.96 7503760135.95  9468518585.96  9470618418.95  00000100200300400B00j01R02?02Z02e03@03[04604T05205\06=06a07E07`08E08i09409R09i09j0:H0:c0;>0;F0;G0;O0;j0<80<J0<`0=:0=I0=\0>70>R0>S0>n0?I0?dFFFFS3LEN2HK2HP2HrS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2LwS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K161H2H0S3LEN2HK2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2AB2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K16S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2HPS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq3FS3LEN2HK2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HKFS3LEN2HKS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2LwS3LEN2HK2HP2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq1S3LEN2HK2Lw3Lq13Lq2S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4".
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
evt usegs POST (ST 0x1c1b8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00B0>11445594946.641954168185.64 1954412143.63 23207601716.6424496052053.6432189479286.6335854578228.6435854985538.6437961114563.6447747482048.6347747893974.6455913381321.5857481181359.6457716083907.6458422563556.6558424662383.6664329521941.648712226349.64 00000;00F00N00V00^00c01801M01[01`01h02302;02F02N02V02W02_S3LEN2HP2LwS3LEN2HP2LwS3LEN2HPS3LEN2LwS3LEN2LwS3LENS3LEN2AB3SEP2HP2Hr2LwS3LEN2AB3SEP2HP2Hr2LwS3LEN2HP2Hr2LwS3LENS3LEN2LwS3LEN2HP2HrS3LEN2LwS3LEN2Hr2LwS3LEN2LwS3LEN2LwFS3LEN2Lw".
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
evt usegs POST (ST 0x1c2dc m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00]0?14939502105.10514939502106.10416246187601.60 17799441610.10325465216029.96 27869909680.95 28902232586.82 29547073601.88 30629262582.95 30652198372.95 30654293615.96 3130479241.105 3130479242.104 32871115528.81 32871133693.95 34239283936.81 34540583959.96 34949646288.1033523526320.96  3525611882.95  35986998188.95 38442233144.82 38444329074.85 38444329075.88 38444329076.91 41527505799.95 42330731338.96 42332822672.95 45238635437.95 46717093062.91 47055932686.95 47058035412.96 47747482048.81 50707785240.96 54463712011.95 56355875692.95 57286117777.95 61589165561.96 61591264882.95 61736020672.85 63927126121.94 63929341522.94 65019182622.96 9468518585.96  9470618418.95  00000100200@00m01H01f02102D02_03:03U03V03W03b04@04H04f05P06106U07907G07Y07o08I08d09I09m09n0:E0:`0;;0;C0;D0;_0<:0<X0=30=N0=]0>E0>m0>n0?I0?dFFS3LEN2HK2HP2HrS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2LwS3LEN2HK2Lw3Lq13Lq2S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FFS3LEN2HK2HPS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HKS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K161H2H0S3LEN2HK2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2AB2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2HP2LwS3LEN2HK2HP2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K16S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlFS3LEN2HK2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HKFS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq1S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4FS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4".
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
evt usegs POST (ST 0x1c2c8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>1954168185.64 1954412143.63 32189479286.6335854578228.6447575940095.6447747482048.6347747893974.6449684669621.6455495042850.6455913381321.5858422498925.6460842786339.6461231522292.6464329521941.6400000;00C00H00]00e00j01201:01E01P01X01c01k01lS3LEN2HP2LwS3LEN2HPS3LENS3LEN2AB3SEP2HP2Hr2LwS3LEN2LwS3LENS3LEN2LwS3LEN2LwS3LEN2HP2LwS3LEN2HP2HrS3LEN2LwS3LEN2Hr2LwS3LEN2LwF".
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
evt usegs POST (ST 0x1c370 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00]0?13559082540.95 14939502105.10514939502106.10416246187601.60 17799441610.10320461994225.95 25465216029.96 25516933792.85 27324926471.95 29060250920.81 29060294621.95 30629262582.95 30652198372.95 30654293615.96 34540583959.96 34949646288.1033523526320.96  3525611882.95  35986998188.95 36029045281.88 39837713106.85 39837713107.88 39837713108.91 39839811480.82 42330731338.96 42332822672.95 43927186569.10543927186570.10445238635437.95 45838477930.82 47055932686.95 47058035412.96 47747482048.81 48411116489.94 48412876274.94 49862951696.95 50707785240.96 51556470438.91 54463712011.95 61589165561.96 61591264882.95 65019182622.96 7338841760.81  9468518585.96  9470618418.95  00000K00L00M00[01H01f02A02P02k03603T03o04J04e05C06006Q07507Y07l08>08T08n09<09a0:E0:F0:G0:H0:S0:n0;I0;Q0<90<a0=?0=@0=W0>20>M0>h0>i0?10?L0?gS3LEN2HK2Lw3Lq13Lq23Lq33Lq4FFS3LEN2HK2HP2HrS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq1S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HPS3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42Kl3K161H2H0S3LEN2HK2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2AB2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlS3LEN2HK2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq1S3LEN2HK2HP2Lw3Lq13Lq2S3LEN2HK2HP2Lw3Lq13Lq23Lq3S3LEN2HK2HP2LwS3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq43K16S3LEN2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq42KlFFFS3LEN2HK2LwS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HKS3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2AB3SEP2HK2HP2Hr2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq42KlFS3LEN2HK2Lw3Lq13Lq23Lq3S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4FS3LEN2HKS3LEN2HK2Lw3Lq13Lq23Lq33Lq4S3LEN2HK2Lw3Lq13Lq23Lq33Lq4".
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
evt usegs POST (ST 0x1c34c m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>12904082803.6419265887139.641954168185.64 1954412143.63 22593628578.6430723275572.6432189479286.6335854578228.6435854985538.6443772821919.6447747482048.6347747893974.6451735867829.6452099707821.6455913381321.5858422563556.6558424662383.6664329521941.6467361222914.6567363322505.6600000>00I00T00\00g00o01401I01^01f01k02302;02C02N02V02^02_02g02oS3LEN2HP2Hr2LwS3LEN2Hr2LwS3LEN2HP2LwS3LEN2HPS3LEN2HP2LwS3LEN2LwS3LENS3LEN2AB3SEP2HP2Hr2LwS3LEN2AB3SEP2HP2Hr2LwS3LEN2LwS3LENS3LEN2LwS3LEN2LwS3LEN2LwS3LEN2HP2HrS3LEN2LwS3LEN2LwFS3LEN2LwS3LEN2Lw".
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
evt usegs POST (ST 0x1c1a4 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>17614059739.621954349123.66 1954350020.67 32189484253.6732189484890.6646067125452.6646067126091.6747747445867.6747747446764.6655913379906.5759836705152.6659836705287.6700000800D00P00Y00b00n01:01C01D01O01P01QS3LEN2HPS3LEN2HP3Lq0S3LEN2HP3Lq0S3LEN3Lq0S3LEN3Lq0S3LEN2Hr3Lq0S3LEN2Hr3Lq0S3LEN3Lq0SS3LEN2HP2HrFF".
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
evt usegs POST (ST 0x1c180 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>1952251972.57 1952252736.58 34949646288.6541711908335.5846069222603.5750707785240.5858165550833.658528200964.58 8528201216.57 00000800@00U00V00_00`01101=01HS3LEN2HPS3LEN2HPS3LEN2HP3K323K161H2H0FS3LEN3K32FS3LEN2HP3K161H2H0S3LEN2HP3K32S3LEN2AB2HP".
if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt usegs POST (ST 0x1c178 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>14527800125.5755713077998.578539203201.59 00000800=00>S3LEN2HPS3LENF".
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evt usegs POST (ST 0x1c148 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>15007267655.5717614059739.5919620497067.6835854508628.5935987008627.6139332109038.6043984391875.6144096333846.6144098420809.6049682117334.6049684208265.6158422962257.6158425049102.608530298113.61 9535722215.60 9537829560.61 00000;00F00G00Y00d00l01401B01M01U01]01e01m02;02C02KS3LEN2HK2HPS3LEN2HK2HPFS3LEN2AB3SEP2HK2HPS3LEN2HK2HPS3LEN2HKS3LEN2HKS3LEN2HK2HP2K1S3LEN2HK2HPS3LEN2HKS3LEN2HKS3LEN2HKS3LEN2HKS3LEN2AB2HK2HPS3LEN2HKS3LEN2HK".
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma memcpy_body : forall junk,
rw_cells usegs m D [CB (Z.to_nat n) junk] -> bytes_at usegs m S src -> mem_inv usegs m ->
evt usegs POST (ST 0x1c130 m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using AB LEN SEP.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>21981031364.4525708206614.6125708207259.5425708256798.4725712457666.4735283523713.4735296064472.5435296064853.6135296112989.4739334206190.4639334206190.4743545014749.4743549202433.4755163157952.475960583647.61 5960585042.54 5960601047.47 5964801035.47 8385880958.47 00000500600700800900:00;00<00=00B00G00O00Z00_00`00a00b00c00hS3LENFFFFFFFFS3LENS3LENS3LEN2ABS3LEN2AB2K0S3LENFFFFS3LEN".
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
Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at usegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells usegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv usegs m ->
evt usegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c130) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32139438783.4400000<S3LEN1B2B21R".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
