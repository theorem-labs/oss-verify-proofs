(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells I_memset I_memcpy Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
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

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D C N : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(q - 2240, q); (D, D + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo q
/\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
#[using="Type"] Lemma memset_callZ : forall RNG (SLO SHI RLO RHI : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte) (lo : Z),
rw_cells asegs m D [CB (Z.to_nat N) junk] ->
mem_inv asegs m ->
(0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
ashenv m -> shclean m SLO SHI RLO RHI -> (SLO <= D)%Z -> (D + N <= SHI)%Z ->
(D + N <= lo \/ q <= D)%Z -> (N <= 2^40)%Z ->
rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG D N -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
evtF asegs RNG (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N lo m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f78) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros DST MI Hq HD HC HN ST LO KH ENV SH S1 S2 SEP N40 RIMG RSTK RD RSH.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>2426920135.77 28006836306.6329765907847.6439351988809.7356777638822.6157622410744.988549037137.62 00000400800<00@00D00G00KS2LOS2HCS2HNS2HNS2HqS1HS2HD".
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(q - 2240, q); (D, D + N)]%Z m) as MU.
destruct (ashenv_core _ ENV) as (E1 & E2 & E3 & E4 & E5 & E6).
pose proof (shclean_sub _ _ _ _ _ D (D + N) SH S1 ltac:(lia) S2) as SH'.
destruct SH' as (U & HU & WR & AB).
step.
eapply evtF_mono.
{ eapply (memset_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N)) with (RLO2 := RLO) (RHI2 := RHI);
rewrite ?Eq, ?Ed, ?En; unfold ICPT_DEPTH in *; try eassumption; try lia. }
intros ms' P. unfold memset_i_post in P. rewrite !Eq, !Ed, !Ec, !En in P. unfold memset_postZ, ICPT_DEPTH.
destruct_exs P. destruct P as (E & MU' & REST). repeat (lazymatch goal with |- ex _ => eexists end).
split; [exact E|]. split; [| exact REST].
eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition memcpy_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D : Z) (a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(q - 2240, q); (D, D + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo q
/\ rw_cells asegs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.
#[using="Type"] Lemma memcpy_callZ : forall RNG (SLO1 SHI1 RLO1 RHI1 SLO2 SHI2 RLO2 RHI2 : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q D : Z) (src junk : list byte) (lo : Z),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z ->
(bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
ashenv m ->
shclean m SLO1 SHI1 RLO1 RHI1 -> (SLO1 <= bv_unsigned a1)%Z -> (bv_unsigned a1 + bv_unsigned a2 <= SHI1)%Z ->
shclean m SLO2 SHI2 RLO2 RHI2 -> (SLO2 <= D)%Z -> (D + bv_unsigned a2 <= SHI2)%Z ->
(bv_unsigned a1 + bv_unsigned a2 <= q - 2240 \/ q <= bv_unsigned a1)%Z ->
(D + bv_unsigned a2 <= lo \/ q <= D)%Z ->
(bv_unsigned a2 <= 2^40)%Z ->
rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG D (bv_unsigned a2) ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF asegs RNG (memcpy_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D a1 a2 src lo m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f7c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros SRC LEN DST Hq HD SEP MI ST LO KH ENV SH1 S11 S12 SH2 S21 S22 SEPS SEPD N40 RIMG RSTK RS RD RSH1 RSH2.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>23323716516.8527505236020.8956788127004.738549037137.74 00000800@00H00PS3LEN2R2S3LEN2R2S3LEN2HqS3LEN2HD".
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (E : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
pose proof (bv_unsigned_in_range 64 a1) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R1, R2. cbn in R1, R2.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(q - 2240, q); (D, D + bv_unsigned a2)]%Z m) as MU.
destruct (ashenv_core _ ENV) as (E1 & E2 & E3 & E4 & E5 & E6).
pose proof (shclean_sub _ _ _ _ _ (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) SH1 S11 ltac:(lia) S12) as (U1 & HU1 & WR1 & AB1).
pose proof (shclean_sub _ _ _ _ _ D (D + bv_unsigned a2) SH2 S21 ltac:(lia) S22) as (U2 & HU2 & WR2 & AB2).
step.
eapply evtF_mono.
{ eapply (memcpy_i_spec RNG ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D)) with (src := src) (junk := junk)
(RLO1 := RLO1) (RHI1 := RHI1) (RLO2 := RLO2) (RHI2 := RHI2);
rewrite ?E, ?Eq; try eassumption; try lia. }
intros ms' P. unfold memcpy_i_post in P. rewrite !E, !Eq in P. unfold memcpy_postZ. exact P.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition memcpy_postv (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(q - 2240, q); (Dst, Dst + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo q
/\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at asegs m' Src src.
#[using="Type"] Lemma memcpy_callw : forall RNG (SLO1 SHI1 RLO1 RHI1 SLO2 SHI2 RLO2 RHI2 : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q Dst Src N : Z) (src junk : list byte) (lo : Z),
bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv asegs m ->
(0 <= q < 2^64)%Z ->
stk asegs m lo q -> (lo <= q - 2240)%Z -> (KHIGH <= lo)%Z ->
ashenv m ->
shclean m SLO1 SHI1 RLO1 RHI1 -> (SLO1 <= Src)%Z -> (Src + N <= SHI1)%Z ->
shclean m SLO2 SHI2 RLO2 RHI2 -> (SLO2 <= Dst)%Z -> (Dst + N <= SHI2)%Z ->
(Src + N <= q - 2240 \/ q <= Src)%Z ->
(Dst + N <= lo \/ q <= Dst)%Z ->
(N <= 2^40)%Z ->
rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG Src N -> rng RNG Dst N ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF asegs RNG (memcpy_postv ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f7c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros BA LEN DC SEP HN HS HD MI Hq ST LO KH ENV SH1 S11 S12 SH2 S21 S22 SEPS SEPD N40 RIMG RSTK RS RD RSH1 RSH2.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>29765905911.7731113014002.7658034908368.7500000800@00HS3LEN2HNS3LEN2HSS3LEN2HD".
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evtF_mono.
{ eapply (memcpy_callZ RNG SLO1 SHI1 RLO1 RHI1 SLO2 SHI2 RLO2 RHI2 ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Src) (Z_to_bv 64 N)) with (src := src) (junk := junk) (q := q);
rewrite ?ED, ?ES, ?EN; try eassumption; try lia. }
intros ms' P. unfold memcpy_postZ in P. rewrite ES, EN in P. exact P.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
