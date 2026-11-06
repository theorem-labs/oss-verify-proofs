(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply Lib.SepCache Q9A7 Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Q9A7.
Import Q7UD. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Notation rsegs := asegs.
Import ListNotations.
Open Scope bv_scope.

Definition memcpy_entry := 0xdb34c%Z.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.

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
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at rsegs m1 S src /\ u8arr rsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1.

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
evt rsegs POST (ST 0xdb70c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_2 by lia.
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
Qed.

Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb6e0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb6d8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed.

Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb68c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed.

Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb3b4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed.

Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb684 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed.

Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb3ac m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed.

Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb5f8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
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
Qed.

Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb4c8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb4a8 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed.

Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb478 m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed.

Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb46c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed.

Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb3f0 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
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
Qed.

Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb3d4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb4f8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
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
Qed.

Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb4e4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb58c m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
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
Qed.

Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb568 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb3c0 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed.

Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb39c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed.

Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdb394 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed.

Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evt rsegs POST (ST 0xdb364 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed.

Lemma memcpy_body : forall junk,
rw_cells rsegs m D [CB (Z.to_nat n) junk] -> bytes_at rsegs m S src -> mem_inv rsegs m ->
evt rsegs POST (ST 0xdb34c m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using AB LEN SEP.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
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
Qed.
End Proofs.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at rsegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv rsegs m ->
evt rsegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Q9ox QRjH Qnhz QSpR QZDE QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import QsRG.Mq0 Q9ox.Mq0 QRjH.

Import QZsi.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module LMg := QZDE.

Section Getrandom.
Context {fF : FPF} {fC : FPC}.
Variable segs : list Segment.
Variable J : aj_base segs.

Definition aj_getrandom_stmt : Prop :=
forall regs (pc : word) mem rom c buf len T,
CK J c -> getr regs 17 = Z_to_bv 64 278 -> getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 len ->
(getr regs 12 = Z_to_bv 64 0 \/ getr regs 12 = Z_to_bv 64 GRND_NONBLOCK) ->
1 <= len <= 256 -> buf + len <= TASK_SIZE -> LMg.wr_at segs mem buf len ->
(forall bs c', Z.of_nat (length bs) = len -> CNEXT J c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J T c' (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
(mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] [])))) ->
AJ J T c (epend regs pc mem rom (getr regs 17)).

End Getrandom.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Q9A7.
Import QbFI. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Notation rsegs := asegs.
Import ListNotations.
Open Scope bv_scope.

Definition memcpy_entry := 0xdda10%Z.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.

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
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at rsegs m1 S src /\ u8arr rsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1.

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
evt rsegs POST (ST 0xdddd0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_2 by lia.
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
Qed.

Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddda4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddd9c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed.

Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddd50 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed.

Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdda78 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed.

Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddd48 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed.

Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdda70 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed.

Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddcbc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
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
Qed.

Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddb8c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddb6c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed.

Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddb3c m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed.

Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddb30 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed.

Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddab4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
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
Qed.

Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdda98 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddbbc m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
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
Qed.

Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddba8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddc50 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
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
Qed.

Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xddc2c m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdda84 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed.

Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdda60 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed.

Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt rsegs POST (ST 0xdda58 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed.

Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evt rsegs POST (ST 0xdda28 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed.

Lemma memcpy_body : forall junk,
rw_cells rsegs m D [CB (Z.to_nat n) junk] -> bytes_at rsegs m S src -> mem_inv rsegs m ->
evt rsegs POST (ST 0xdda10 m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using AB LEN SEP.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
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
Qed.
End Proofs.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at rsegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv rsegs m ->
evt rsegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QZsi.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Lemma acost_le5 : forall n, 0 <= n -> acostA n <= 16 * n + 512.
Proof. intros n H. unfold acostA. destruct (Z.leb_spec n 64512); lia. Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ms_gp (ms : machine_state) : word := Sem.reg_get (ms_regs ms) (Z_to_bv 5 3).
Definition gp_ok5 (L : heap_layout_A) (g : word) : Prop := g = Z_to_bv 64 (hl_gp L).

Definition AJ5of (L : heap_layout_A) (J : aj_base (hl_segs L)) {X : Type} (A : X) (T : TSet) (c : config) (ms : machine_state) : Prop :=
gp_ok5 L (ms_gp ms) -> AJ J T c ms.

Definition AJe (L : heap_layout_A) (J : aj_base (hl_segs L)) {X : Type} (A : X) (T : TSet) (c : config) (ms : machine_state) : Prop :=
AJ J T c ms.

Record bud := Bud { bB : Z; bD : Z; bM : Z }.
Definition charge (x : bud) (cm cd : Z) : bud := Bud (bB x - cm) (bD x - cd) (bM x).
Definition chargeM (x : bud) (k : Z) : bud := Bud (bB x) (bD x) (bM x - k).

Definition M2D : Z := 134217728.
Lemma uw_cost_nonneg5 : forall u : QZsi.uwd, 0 <= QZsi.uw_cost u. Proof. intros []; cbn; lia. Qed.

Definition blink (B : bud) (B6 : QZsi.bud) : Prop :=
0 <= bB B /\ bB B <= QZsi.bB B6 /\ bB B <= 512 * QZsi.bN B6 /\ bB B <= 2^30 /\ 0 <= bD B /\ bD B <= QZsi.bD B6 /\ 0 <= bM B /\ 16 * bB B <= QZsi.bQ B6 /\ bD B <= 134217728 * QZsi.bM B6.

Section IfaceA5.
Variable L : heap_layout_A.
Let segs : list Segment := hl_segs L.
Notation errno_a := (hl_tp L - 164).
Notation shad := (QZsi.shad L).
Notation fr_ivs := (QZsi.fr_ivs L).
Notation uw_pre := (QZsi.uw_pre L).
Notation uw_ok := (QZsi.uw_ok L).

Record heap_iface_A := HIA {
hiA_J : aj_base (hl_segs L);
ASA : Type;
HEAPA : ASA -> list blk  -> list blk  -> list frame  -> bud  ->
(word -> option byte) -> config -> Prop;
hiA_top : Z;
hiA_top_hi : alloc_ceiling < hiA_top;
hiA_top_le : hiA_top <= 2^47;
hiA_bot : Z;
hiA_bot_top : hiA_bot mod 8 = 0 /\ hiA_bot <= hiA_top;
heapA_cok : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> CK hiA_J c;
heapA_mem_inv : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> mem_inv segs m;
heapA_budget : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> 0 <= bB B /\ 0 <= bD B;
heapA_budgetM : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> 0 <= bM B;
heapA_bB_bound : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> bB B + 2^23 <= 2^39;
heapA_cfg_next : forall A LB LM FR B m c c', HEAPA A LB LM FR B m c -> CNEXT hiA_J c c' -> HEAPA A LB LM FR B m c';
heapA_blk_lt40 : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) -> n < 2^40;
heapA_blk_le26 : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) LB -> n <= 2^26;
heapA_blk : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= alloc_ceiling /\ wr_at segs m a n;
heapA_blk_img : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n <= hl_img_lo L \/ hl_img_hi L <= a;
heapA_blk_disjoint : forall A LB LM FR B m c a n a' n', HEAPA A LB LM FR B m c ->
In (a, n) (LB ++ LM) -> In (a', n') (LB ++ LM) -> a <> a' -> (a + n <= a' \/ a' + n' <= a);
heapA_blk_nodup : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> List.NoDup (map blk_addr (LB ++ LM));
heapA_blk_not_static : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= i < n -> ~ hl_client_static L (a + i);
heapA_perm : forall A LB LB' LM LM' FR FR' B m c, HEAPA A LB LM FR B m c ->
Permutation LB LB' -> Permutation LM LM' -> Permutation FR FR' -> HEAPA A LB' LM' FR' B m c;
heapA_blk_slack : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16;
heapA_shadow_blk : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) LB ->
bytes_at segs m (shad a) (shadow_bytes n);
heapA_shadow_glob : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
Forall (fun g => bytes_at segs m (shad (fst g)) (repeat (Z_to_bv 8 0) (Z.to_nat (snd g / 8)))) (hl_globals L);
heapA_shadow_sep : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad a + i)
/\ (shad a + i < hl_img_lo L \/ hl_img_hi L <= shad a + i);
heapA_sb_cells : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
bytes_at segs m (hl_got_sb L) (le8 (Z_to_bv 64 (hl_sb_cell L))) /\
bytes_at segs m (hl_sb_cell L) (le8 (Z_to_bv 64 (hl_sb L))) /\
bytes_at segs m (hl_got_uar L) (le8 (Z_to_bv 64 (hl_uar_cell L))) /\
bytes_at segs m (hl_uar_cell L) (le4 (Z_to_bv 64 1));
heapA_frame : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR ->
0 <= k <= 3 /\ F mod fr_size k = 0 /\ 0 < F /\ F + fr_size k <= alloc_ceiling /\
(F + fr_size k <= hl_img_lo L \/ hl_img_hi L <= F) /\
wr_at segs m F (fr_size k - 8) /\
wr_at segs m (shad F) (fr_shadow_len k) /\

(exists fp, bytes_at segs m (F + fr_size k - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling fp /\ (fp < hl_img_lo L \/ hl_img_hi L <= fp) /\
~ hl_scratch L fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad F' <= fp < shad F' + fr_shadow_len k')));
heapA_frame_disjoint : forall A LB LM FR B m c F k a n, HEAPA A LB LM FR B m c -> In (F, k) FR -> In (a, n) (LB ++ LM) ->
F + fr_size k <= a \/ a + n <= F;
heapA_frame_apart : forall A LB LM FR B m c F k F' k', HEAPA A LB LM FR B m c ->
In (F, k) FR -> In (F', k') FR -> F <> F' ->
F + fr_size k <= F' \/ F' + fr_size k' <= F;
heapA_frame_nodup : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> NoDup (map fr_base FR);
heapA_frame_appmem : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR ->
F + fr_size k + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= F;
heapA_frame_shadow_sep : forall A LB LM FR B m c F k i, HEAPA A LB LM FR B m c -> In (F, k) FR ->
0 <= i < fr_shadow_len k ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad F + i)
/\ (shad F + i < hl_img_lo L \/ hl_img_hi L <= shad F + i);
heapA_client_frame : forall A LB LM FR B m m' c, HEAPA A LB LM FR B m c ->
(forall a, 0 <= a < 2^64 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling a ->
~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad F <= a < shad F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
mem_inv segs m' ->
HEAPA A LB LM FR B m' c;
heapA_canary : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
exists g : word,
bytes_at segs m (hl_got_guard L) (le8 (Z_to_bv 64 (hl_guard L))) /\
bytes_at segs m (hl_guard L) (le8 g) /\ bytes_at segs m (hl_tp L - 16) (le8 g);
heapA_need_locks : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> bytes_at segs m (hl_libc L + 3) [Z_to_bv 8 0];
heapA_consts : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_consts L);
heapA_rtc : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_rt_consts L);
heapA_errno : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> exists errv : word, rw_cells segs m errno_a [C4 errv];
heapA_frame_above : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR -> hl_img_hi L <= F;
heapA_shadow_words : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
exists w : list byte, length w = 8%nat /\ bytes_at segs m ((shad a + i) / 8 * 8) w;
heapA_shadow_stack : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c ->
hiA_bot <= a -> a + n <= hiA_top + 2^22 -> a + n <= 2^47 -> 0 < n ->
bytes_at segs m (shad a) (repeat (Z_to_bv 8 0) (Z.to_nat ((a + n - 1) / 8 - a / 8 + 1)));
heapA_shadow_img : forall A LB LM FR B m c g, HEAPA A LB LM FR B m c ->
hl_img_lo L <= 8 * g -> 8 * g + 8 <= hl_img_hi L ->
bytes_at segs m (g + hl_sb L) [Z_to_bv 8 (img_shadow_val (hl_reg_globals L) g)];
heapA_blk_appmem : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= a;
hiA_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_malloc L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA A' LB LM FR (charge B (16 * n + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAPA A' ((r, n) :: LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ) ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs));
hiA_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok (hl_free L) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' c' ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs));
hiA_calloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (cnt sz lo : Z) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 1 <= cnt * sz < 2^40 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_calloc L) ra u ->
16 * (cnt * sz) + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA A' LB LM FR (charge B (16 * (cnt * sz) + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ rw_cells segs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ HEAPA A' ((r, cnt * sz) :: LB) LM FR (charge B (16 * (cnt * sz) + 512) (uw_cost u)) m' c') ) ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs));
hiA_realloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA A LB LM FR B m c -> In (p, n0) LB ->
rw_cells segs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_realloc L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m'
/\ HEAPA A' LB LM FR (charge B (16 * n + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells segs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAPA A' ((r, n) :: lb_remove p LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ) ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc L)) fc None m (seg_rom segs));
hiA_strdup : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (src ab nb lo : Z) (str : list byte) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^32 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 src ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_strdup L) ra u ->
16 * (Z.of_nat (length str) + 1) + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv
/\ HEAPA A' LB LM FR (charge B (16 * (Z.of_nat (length str) + 1) + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ bytes_at segs m' r (str ++ [Z_to_bv 8 0])
/\ HEAPA A' ((r, Z.of_nat (length str) + 1) :: LB) LM FR
(charge B (16 * (Z.of_nat (length str) + 1) + 512) (uw_cost u)) m' c') ) ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_strdup L)) fc None m (seg_rom segs));
hiA_malloc2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word),
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 4096 -> Z.of_nat (length LM) < 8 -> M2D <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA A' LB LM FR (charge B 0 M2D) m' c')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAPA A' LB ((r, n) :: LM) FR (charge B 0 M2D) m' c') ) ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc2 L)) fc None m (seg_rom segs));
hiA_free2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word),
HEAPA A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LM) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ lb_remove p LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA A' LB (lb_remove p LM) FR B m' c' ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free2 L)) fc None m (seg_rom segs));
hiA_stack_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' c' A' (Fr : Z),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells segs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at segs m' (shad Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA A' LB LM ((Fr, k) :: FR) B m' c' ->
AJ5of L hiA_J A' T c' ms') ->
AJ5of L hiA_J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc L k)) fc None m (seg_rom segs));
hiA_frame_release : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : TSet) (A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (Fr k fp pc : Z) (rX : bv 5),
HEAPA A LB LM FR B m c -> In (Fr, k) FR ->
bytes_at segs m (Fr + fr_size k - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
Sem.reg_get R rX = Z_to_bv 64 fp ->
bv_unsigned rX <> 0 ->
code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' c' A',
model_vm_only (cfg_model c) (cfg_model c') ->
HEAPA A' LB LM (fr_remove Fr FR) B m' c' ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
AJ5of L hiA_J A' T c' (MS R F (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
AJ5of L hiA_J A T c (MS R F (Z_to_bv 64 pc) fc None m (seg_rom segs))
}.

Section Inst.
Variable H6 : QZsi.heap_iface_A L.
Notation J6 := (QZsi.hiA_J L H6).
Definition HEAPA5 (A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud)
(m : word -> option byte) (c : config) : Prop :=
exists B6, QZsi.HEAPA L H6 A LB LM FR B6 m c /\ blink B B6.

Ltac open5 := repeat match goal with H : HEAPA5 _ _ _ _ _ _ _ |- _ => destruct H as (?B6 & ?HP6 & ?LK) end.

Lemma s5_heapA_cok : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> CK J6 c.
Proof. intros. open5. eapply (QZsi.heapA_cok L H6); eauto. Qed.
Lemma s5_heapA_mem_inv : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> mem_inv segs m.
Proof. intros. open5. eapply (QZsi.heapA_mem_inv L H6); eauto. Qed.
Lemma s5_heapA_budget : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> 0 <= bB B /\ 0 <= bD B.
Proof. intros. open5. unfold blink in *. lia. Qed.
Lemma s5_heapA_budgetM : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> 0 <= bM B.
Proof. intros. open5. unfold blink in *. lia. Qed.
Lemma s5_heapA_bB_bound : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> bB B + 2^23 <= 2^39.
Proof. intros. open5. unfold blink in *. lia. Qed.
Lemma s5_heapA_cfg_next : forall A LB LM FR B m c c', HEAPA5 A LB LM FR B m c -> CNEXT J6 c c' -> HEAPA5 A LB LM FR B m c'.
Proof. intros. open5. eexists; split; [eapply (QZsi.heapA_cfg_next L H6); eauto | eassumption]. Qed.
Lemma s5_heapA_blk_lt40 : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) (LB ++ LM) -> n < 2^40.
Proof. intros. open5. eapply (QZsi.heapA_blk_lt40 L H6); eauto. Qed.
Lemma s5_heapA_blk_le26 : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) LB -> n <= 2^26.
Proof. intros. open5. eapply (QZsi.heapA_blk_le26 L H6); eauto. Qed.
Lemma s5_heapA_blk : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= alloc_ceiling /\ wr_at segs m a n.
Proof. intros. open5. eapply (QZsi.heapA_blk L H6); eauto. Qed.
Lemma s5_heapA_blk_img : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n <= hl_img_lo L \/ hl_img_hi L <= a.
Proof. intros. open5. eapply (QZsi.heapA_blk_img L H6); eauto. Qed.
Lemma s5_heapA_blk_disjoint : forall A LB LM FR B m c a n a' n', HEAPA5 A LB LM FR B m c ->
In (a, n) (LB ++ LM) -> In (a', n') (LB ++ LM) -> a <> a' -> (a + n <= a' \/ a' + n' <= a).
Proof. intros. open5. eapply (QZsi.heapA_blk_disjoint L H6); eauto. Qed.
Lemma s5_heapA_blk_nodup : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> List.NoDup (map blk_addr (LB ++ LM)).
Proof. intros. open5. eapply (QZsi.heapA_blk_nodup L H6); eauto. Qed.
Lemma s5_heapA_blk_not_static : forall A LB LM FR B m c a n i, HEAPA5 A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= i < n -> ~ hl_client_static L (a + i).
Proof. intros. open5. eapply (QZsi.heapA_blk_not_static L H6); eauto. Qed.
Lemma s5_heapA_perm : forall A LB LB' LM LM' FR FR' B m c, HEAPA5 A LB LM FR B m c ->
Permutation LB LB' -> Permutation LM LM' -> Permutation FR FR' -> HEAPA5 A LB' LM' FR' B m c.
Proof. intros. open5. eexists; split; [eapply (QZsi.heapA_perm L H6); eauto | eassumption]. Qed.
Lemma s5_heapA_blk_slack : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16.
Proof. intros. open5. eapply (QZsi.heapA_blk_slack L H6); eauto. Qed.
Lemma s5_heapA_shadow_blk : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) LB ->
bytes_at segs m (shad a) (shadow_bytes n).
Proof. intros. open5. eapply (QZsi.heapA_shadow_blk L H6); eauto. Qed.
Lemma s5_heapA_shadow_glob : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c ->
Forall (fun g => bytes_at segs m (shad (fst g)) (repeat (Z_to_bv 8 0) (Z.to_nat (snd g / 8)))) (hl_globals L).
Proof. intros. open5. eapply (QZsi.heapA_shadow_glob L H6); eauto. Qed.
Lemma s5_heapA_shadow_sep : forall A LB LM FR B m c a n i, HEAPA5 A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad a + i)
/\ (shad a + i < hl_img_lo L \/ hl_img_hi L <= shad a + i).
Proof. intros. open5. eapply (QZsi.heapA_shadow_sep L H6); eauto. Qed.
Lemma s5_heapA_sb_cells : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c ->
bytes_at segs m (hl_got_sb L) (le8 (Z_to_bv 64 (hl_sb_cell L))) /\
bytes_at segs m (hl_sb_cell L) (le8 (Z_to_bv 64 (hl_sb L))) /\
bytes_at segs m (hl_got_uar L) (le8 (Z_to_bv 64 (hl_uar_cell L))) /\
bytes_at segs m (hl_uar_cell L) (le4 (Z_to_bv 64 1)).
Proof. intros. open5. eapply (QZsi.heapA_sb_cells L H6); eauto. Qed.
Lemma s5_heapA_frame : forall A LB LM FR B m c F k, HEAPA5 A LB LM FR B m c -> In (F, k) FR ->
0 <= k <= 3 /\ F mod fr_size k = 0 /\ 0 < F /\ F + fr_size k <= alloc_ceiling /\
(F + fr_size k <= hl_img_lo L \/ hl_img_hi L <= F) /\
wr_at segs m F (fr_size k - 8) /\
wr_at segs m (shad F) (fr_shadow_len k) /\

(exists fp, bytes_at segs m (F + fr_size k - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling fp /\ (fp < hl_img_lo L \/ hl_img_hi L <= fp) /\
~ hl_scratch L fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad F' <= fp < shad F' + fr_shadow_len k'))).
Proof. intros. open5. eapply (QZsi.heapA_frame L H6); eauto. Qed.
Lemma s5_heapA_frame_disjoint : forall A LB LM FR B m c F k a n, HEAPA5 A LB LM FR B m c -> In (F, k) FR -> In (a, n) (LB ++ LM) ->
F + fr_size k <= a \/ a + n <= F.
Proof. intros. open5. eapply (QZsi.heapA_frame_disjoint L H6); eauto. Qed.
Lemma s5_heapA_frame_apart : forall A LB LM FR B m c F k F' k', HEAPA5 A LB LM FR B m c ->
In (F, k) FR -> In (F', k') FR -> F <> F' ->
F + fr_size k <= F' \/ F' + fr_size k' <= F.
Proof. intros. open5. eapply (QZsi.heapA_frame_apart L H6); eauto. Qed.
Lemma s5_heapA_frame_nodup : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> NoDup (map fr_base FR).
Proof. intros. open5. eapply (QZsi.heapA_frame_nodup L H6); eauto. Qed.
Lemma s5_heapA_frame_appmem : forall A LB LM FR B m c F k, HEAPA5 A LB LM FR B m c -> In (F, k) FR ->
F + fr_size k + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= F.
Proof. intros. open5. eapply (QZsi.heapA_frame_appmem L H6); eauto. Qed.
Lemma s5_heapA_frame_shadow_sep : forall A LB LM FR B m c F k i, HEAPA5 A LB LM FR B m c -> In (F, k) FR ->
0 <= i < fr_shadow_len k ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad F + i)
/\ (shad F + i < hl_img_lo L \/ hl_img_hi L <= shad F + i).
Proof. intros. open5. eapply (QZsi.heapA_frame_shadow_sep L H6); eauto. Qed.
Lemma s5_heapA_client_frame : forall A LB LM FR B m m' c, HEAPA5 A LB LM FR B m c ->
(forall a, 0 <= a < 2^64 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling a ->
~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad F <= a < shad F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
mem_inv segs m' ->
HEAPA5 A LB LM FR B m' c.
Proof. intros. open5. eexists; split; [eapply (QZsi.heapA_client_frame L H6); eauto | eassumption]. Qed.
Lemma s5_heapA_canary : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c ->
exists g : word,
bytes_at segs m (hl_got_guard L) (le8 (Z_to_bv 64 (hl_guard L))) /\
bytes_at segs m (hl_guard L) (le8 g) /\ bytes_at segs m (hl_tp L - 16) (le8 g).
Proof. intros. open5. eapply (QZsi.heapA_canary L H6); eauto. Qed.
Lemma s5_heapA_need_locks : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> bytes_at segs m (hl_libc L + 3) [Z_to_bv 8 0].
Proof. intros. open5. eapply (QZsi.heapA_need_locks L H6); eauto. Qed.
Lemma s5_heapA_consts : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_consts L).
Proof. intros. open5. eapply (QZsi.heapA_consts L H6); eauto. Qed.
Lemma s5_heapA_rtc : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_rt_consts L).
Proof. intros. open5. eapply (QZsi.heapA_rtc L H6); eauto. Qed.
Lemma s5_heapA_errno : forall A LB LM FR B m c, HEAPA5 A LB LM FR B m c -> exists errv : word, rw_cells segs m errno_a [C4 errv].
Proof. intros. open5. eapply (QZsi.heapA_errno L H6); eauto. Qed.
Lemma s5_heapA_frame_above : forall A LB LM FR B m c F k, HEAPA5 A LB LM FR B m c -> In (F, k) FR -> hl_img_hi L <= F.
Proof. intros. open5. eapply (QZsi.heapA_frame_above L H6); eauto. Qed.
Lemma s5_heapA_shadow_words : forall A LB LM FR B m c a n i, HEAPA5 A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
exists w : list byte, length w = 8%nat /\ bytes_at segs m ((shad a + i) / 8 * 8) w.
Proof. intros. open5. eapply (QZsi.heapA_shadow_words L H6); eauto. Qed.
Lemma s5_heapA_shadow_stack : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c ->
(QZsi.hiA_bot L H6) <= a -> a + n <= (QZsi.hiA_top L H6) + 2^22 -> a + n <= 2^47 -> 0 < n ->
bytes_at segs m (shad a) (repeat (Z_to_bv 8 0) (Z.to_nat ((a + n - 1) / 8 - a / 8 + 1))).
Proof. intros. open5. eapply (QZsi.heapA_shadow_stack L H6); eauto. Qed.
Lemma s5_heapA_shadow_img : forall A LB LM FR B m c g, HEAPA5 A LB LM FR B m c ->
hl_img_lo L <= 8 * g -> 8 * g + 8 <= hl_img_hi L ->
bytes_at segs m (g + hl_sb L) [Z_to_bv 8 (img_shadow_val (hl_reg_globals L) g)].
Proof. intros. open5. eapply (QZsi.heapA_shadow_img L H6); eauto. Qed.
Lemma s5_heapA_blk_appmem : forall A LB LM FR B m c a n, HEAPA5 A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= a.
Proof. intros. open5. eapply (QZsi.heapA_blk_appmem L H6); eauto. Qed.
Lemma s5_hiA_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word) (u : uwd),
HEAPA5 A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre (QZsi.hiA_top L H6) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_malloc L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA5 A' LB LM FR (charge B (16 * n + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAPA5 A' ((r, n) :: LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ) ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs)).
Proof.
intros until u. intros HP ST LO LOS SPA HT ERR TP A0 N UW UWK BB BD K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 n ltac:(lia)) as AC.
eapply (QZsi.hiA_malloc L H6) with (B := B6) (n := n) (u := u) (errv := errv) (lo := lo);
[ exact HP6 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0
| lia | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' HPR ERR').
- right. split; [exact Hr|]. split; [exact BLK|]. eexists; split; [exact HP'|]; unfold blink, charge, QZsi.charge, QZsi.chargeQ; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ]; try (pose proof (uw_cost_nonneg5 u)); lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPA5 A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p ->
uw_pre (QZsi.hiA_top L H6) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok (hl_free L) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA5 A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' c' ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs)).
Proof.
intros until u. intros HP HIN ST LO LOS SPA HT ERR TP A0 UWP BB BD K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
eapply (QZsi.hiA_free L H6) with (B := B6) (p := p) (u := u) (errv := errv) (lo := lo);
[ exact HP6 | exact HIN | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0
| exact UWP | destruct (Z.eqb p 0); lia | ].
intros ms' m' c' A' r RS VM ST' HPR ERR' HP'.
eapply (K ms' m' c' A' r RS VM ST' HPR ERR').
- eexists; split; [exact HP'|]; unfold blink, charge, QZsi.charge, QZsi.chargeQ; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ]; try (pose proof (uw_cost_nonneg5 u)); destruct (Z.eqb p 0); lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_calloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (cnt sz lo : Z) (errv : word) (u : uwd),
HEAPA5 A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 1 <= cnt * sz < 2^40 ->
uw_pre (QZsi.hiA_top L H6) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_calloc L) ra u ->
16 * (cnt * sz) + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA5 A' LB LM FR (charge B (16 * (cnt * sz) + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ rw_cells segs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ HEAPA5 A' ((r, cnt * sz) :: LB) LM FR (charge B (16 * (cnt * sz) + 512) (uw_cost u)) m' c') ) ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs)).
Proof.
intros until u. intros HP ST LO LOS SPA HT ERR TP A0 A1 CNT SZ PROD UW UWK BB BD K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 (cnt * sz) ltac:(lia)) as AC.
eapply (QZsi.hiA_calloc L H6) with (B := B6) (cnt := cnt) (sz := sz) (u := u) (errv := errv) (lo := lo);
[ exact HP6 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | exact A1
| nia | nia | lia | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' HPR ERR').
- right. split; [exact Hr|]. split; [exact BLK|]. eexists; split; [exact HP'|]; unfold blink, charge, QZsi.charge, QZsi.chargeQ; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ]; try (pose proof (uw_cost_nonneg5 u)); lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_realloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA5 A LB LM FR B m c -> In (p, n0) LB ->
rw_cells segs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre (QZsi.hiA_top L H6) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_realloc L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m'
/\ HEAPA5 A' LB LM FR (charge B (16 * n + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells segs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAPA5 A' ((r, n) :: lb_remove p LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ) ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc L)) fc None m (seg_rom segs)).
Proof.
intros until u. intros HP HIN BLK0 ST LO LOS SPA HT ERR TP A0 A1 N UW UWK BB BD K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 n ltac:(lia)) as AC.
eapply (QZsi.hiA_realloc L H6) with (B := B6) (p := p) (n0 := n0) (n := n) (u := u) (errv := errv) (lo := lo) (old := old) (junk0 := junk0);
[ exact HP6 | exact HIN | exact BLK0 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | exact A1
| lia | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' ERR' Hr HPR BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' ERR').
- right. split; [exact Hr|]. split; [exact HPR|]. split; [exact BLK|]. eexists; split; [exact HP'|]; unfold blink, charge, QZsi.charge, QZsi.chargeQ; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ]; try (pose proof (uw_cost_nonneg5 u)); lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_strdup : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (src ab nb lo : Z) (str : list byte) (errv : word) (u : uwd),
HEAPA5 A LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^32 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 src ->
uw_pre (QZsi.hiA_top L H6) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_strdup L) ra u ->
16 * (Z.of_nat (length str) + 1) + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv
/\ HEAPA5 A' LB LM FR (charge B (16 * (Z.of_nat (length str) + 1) + 512) (uw_cost u)) m' c')
\/ (r <> 0 /\ bytes_at segs m' r (str ++ [Z_to_bv 8 0])
/\ HEAPA5 A' ((r, Z.of_nat (length str) + 1) :: LB) LM FR
(charge B (16 * (Z.of_nat (length str) + 1) + 512) (uw_cost u)) m' c') ) ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_strdup L)) fc None m (seg_rom segs)).
Proof.
intros until u. intros HP HIN LE1 LE2 BYTES NOZ LEN ST LO LOS SPA HT ERR TP A0 UW UWK BB BD K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 (Z.of_nat (length str) + 1) ltac:(lia)) as AC.
eapply (QZsi.hiA_strdup L H6) with (B := B6) (src := src) (ab := ab) (nb := nb) (str := str) (u := u) (errv := errv) (lo := lo);
[ exact HP6 | exact HIN | exact LE1 | exact LE2 | exact BYTES | exact NOZ | lia | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR
| exact TP | exact GP | exact A0 | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BYTES' HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' HPR ERR').
- right. split; [exact Hr|]. split; [exact BYTES'|]. eexists; split; [exact HP'|]; unfold blink, charge, QZsi.charge, QZsi.chargeQ; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ]; try (pose proof (uw_cost_nonneg5 u)); lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_malloc2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word),
HEAPA5 A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 4096 -> Z.of_nat (length LM) < 8 -> M2D <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA5 A' LB LM FR (charge B 0 M2D) m' c')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAPA5 A' LB ((r, n) :: LM) FR (charge B 0 M2D) m' c') ) ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc2 L)) fc None m (seg_rom segs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP A0 N LML BM K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
eapply (QZsi.hiA_malloc2 L H6) with (B := B6) (n := n) (errv := errv) (lo := lo);
[ exact HP6 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | exact N | exact LML | unfold M2D in BM; lia | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' OUT.
eapply (K ms' m' c' A' r errv' RS VM ST' HPR ERR').
- destruct OUT as [(Hr & He & HP') | (Hr & BLK & HP')]; [left | right]; (split; [exact Hr|]); (split; [eassumption|]);
(eexists; split; [exact HP' | unfold blink, charge, M2D, QZsi.chargeM in *; cbn [bB bD bM QZsi.bB QZsi.bD QZsi.bN QZsi.bM QZsi.bQ] in *; lia]).
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_free2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word),
HEAPA5 A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LM) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ lb_remove p LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA5 A' LB (lb_remove p LM) FR B m' c' ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free2 L)) fc None m (seg_rom segs)).
Proof.
intros until errv. intros HP HIN ST LO LOS SPA HT ERR TP A0 K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
eapply (QZsi.hiA_free2 L H6) with (B := B6) (p := p) (errv := errv) (lo := lo);
[ exact HP6 | exact HIN | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | ].
intros ms' m' c' A' r RS VM ST' HPR ERR' HP'.
eapply (K ms' m' c' A' r RS VM ST' HPR ERR').
- eexists; split; [exact HP' | exact LK].
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_stack_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA5 A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' c' A' (Fr : Z),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells segs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at segs m' (shad Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA5 A' LB LM ((Fr, k) :: FR) B m' c' ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc L k)) fc None m (seg_rom segs)).
Proof.
intros until lo. intros HP K02 BYTES MOD8 FRL ST LO LOS SPA HT TP A0 K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
eapply (QZsi.hiA_stack_malloc L H6) with (B := B6) (k := k) (bytes := bytes) (lo := lo);
[ exact HP6 | exact K02 | exact BYTES | exact MOD8 | exact FRL | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact TP | exact GP | exact A0 | ].
intros ms' m' A' Fr RS ST' HPR FRNZ BLK SHB HP'.
eapply (K ms' m' c A' Fr RS (model_vm_only_refl _) ST' HPR FRNZ BLK SHB).
- eexists; split; [exact HP' | exact LK].
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
Lemma s5_hiA_frame_release : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : TSet) (A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (Fr k fp pc : Z) (rX : bv 5),
HEAPA5 A LB LM FR B m c -> In (Fr, k) FR ->
bytes_at segs m (Fr + fr_size k - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
Sem.reg_get R rX = Z_to_bv 64 fp ->
bv_unsigned rX <> 0 ->
code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' c' A',
model_vm_only (cfg_model c) (cfg_model c') ->
HEAPA5 A' LB LM (fr_remove Fr FR) B m' c' ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
AJ5of L J6 A' T c' (MS R F (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
AJ5of L J6 A T c (MS R F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
intros until rX. intros HP HIN BYTES FPR REG RXNZ CODE K HGP.
destruct HP as (B6 & HP6 & LK).
eapply (QZsi.hiA_frame_release L H6) with (B := B6) (Fr := Fr) (k := k) (fp := fp) (rX := rX);
[ exact HP6 | exact HIN | exact BYTES | exact FPR | exact REG | exact RXNZ | exact CODE | ].
intros m' A' HP' AGR WV.
eapply (K m' c A'); [ apply model_vm_only_refl | eexists; split; [exact HP' | exact LK] | exact AGR | exact WV | exact HGP ].
Qed.
Lemma s5_hiA_realloc_nf : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : QZsi.ASA L H6) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA5 A LB LM FR B m c -> In (p, n0) LB ->
rw_cells segs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < (QZsi.hiA_top L H6) + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre (QZsi.hiA_top L H6) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_realloc L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' errno_a [C4 errv'] ->
(r <> 0 /\ heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells segs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAPA5 A' ((r, n) :: lb_remove p LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ->
AJ5of L J6 A' T c' ms') ->
AJ5of L J6 A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc L)) fc None m (seg_rom segs)).
Proof.
intros until u. intros HP HIN BLK0 ST LO LOS SPA HT ERR TP A0 A1 N UW UWK BB BD K HGP.
destruct HP as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 n ltac:(lia)) as AC.
eapply (QZsi.hiA_realloc L H6) with (B := B6) (p := p) (n0 := n0) (n := n) (u := u) (errv := errv) (lo := lo) (old := old) (junk0 := junk0);
[ exact HP6 | exact HIN | exact BLK0 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | exact A1
| lia | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' ERR' Hr HPR BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' ERR').
- split; [exact Hr|]. split; [exact HPR|]. split; [exact BLK|]. eexists; split; [exact HP'|]; unfold blink, charge, QZsi.charge, QZsi.chargeQ; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ]; try (pose proof (uw_cost_nonneg5 u)); lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.

Definition hi5_of_v6 : heap_iface_A :=
HIA J6
(QZsi.ASA L H6)
HEAPA5
(QZsi.hiA_top L H6)
(QZsi.hiA_top_hi L H6)
(QZsi.hiA_top_le L H6)
(QZsi.hiA_bot L H6)
(QZsi.hiA_bot_top L H6)
s5_heapA_cok
s5_heapA_mem_inv
s5_heapA_budget
s5_heapA_budgetM
s5_heapA_bB_bound
s5_heapA_cfg_next
s5_heapA_blk_lt40
s5_heapA_blk_le26
s5_heapA_blk
s5_heapA_blk_img
s5_heapA_blk_disjoint
s5_heapA_blk_nodup
s5_heapA_blk_not_static
s5_heapA_perm
s5_heapA_blk_slack
s5_heapA_shadow_blk
s5_heapA_shadow_glob
s5_heapA_shadow_sep
s5_heapA_sb_cells
s5_heapA_frame
s5_heapA_frame_disjoint
s5_heapA_frame_apart
s5_heapA_frame_nodup
s5_heapA_frame_appmem
s5_heapA_frame_shadow_sep
s5_heapA_client_frame
s5_heapA_canary
s5_heapA_need_locks
s5_heapA_consts
s5_heapA_rtc
s5_heapA_errno
s5_heapA_frame_above
s5_heapA_shadow_words
s5_heapA_shadow_stack
s5_heapA_shadow_img
s5_heapA_blk_appmem
s5_hiA_malloc
s5_hiA_free
s5_hiA_calloc
s5_hiA_realloc
s5_hiA_strdup
s5_hiA_malloc2
s5_hiA_free2
s5_hiA_stack_malloc
s5_hiA_frame_release.

Lemma heapa5_enter : forall A LB LM FR B B6 m c,
QZsi.HEAPA L H6 A LB LM FR B6 m c -> blink B B6 -> HEAPA hi5_of_v6 A LB LM FR B m c.
Proof. intros A LB LM FR B B6 m c HP LK. exists B6. split; [exact HP | exact LK]. Qed.
Lemma heapa5_exit : forall A LB LM FR B m c,
HEAPA hi5_of_v6 A LB LM FR B m c -> exists B6, QZsi.HEAPA L H6 A LB LM FR B6 m c /\ blink B B6.
Proof. intros A LB LM FR B m c HP. exact HP. Qed.
End Inst.
End IfaceA5.

Lemma aj5_back : forall (L : heap_layout_A) (J : aj_base (hl_segs L)) (X : Type) (A : X) T c ms,
gp_ok5 L (ms_gp ms) -> AJ5of L J A T c ms -> AJe L J A T c ms.
Proof. intros L J X A T c ms H K. exact (K H). Qed.
Lemma aj5_enter_l : forall (L : heap_layout_A) (J : aj_base (hl_segs L)) (X : Type) (A : X) T c ms,
(gp_ok5 L (ms_gp ms) -> evt (hl_segs L) (AJe L J A T c) ms) -> AJ5of L J A T c ms.
Proof. intros L J X A T c ms H HGP. apply (aj_evt J). exact (H HGP). Qed.
End RC__1.
Arguments gp_ok5 : simpl never.

Notation AJ5 L HIx := (AJ5of L (hiA_J L HIx)).
Notation AJ5e L HIx := (AJe L (hiA_J L HIx)).

Ltac gp5_norm H :=
lazymatch type of H with
| gp_ok5 ?L (ms_gp (MS (mkR _ _ ?g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _)) => change (gp_ok5 L g) in H
| _ => idtac
end.
Ltac gp5_solve :=
first [ assumption
| lazymatch goal with |- gp_ok5 ?L (ms_gp (MS (mkR _ _ ?g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _)) => change (gp_ok5 L g); assumption end
| match goal with H : gp_ok5 _ _ |- _ => exact H end
| reflexivity ].
Ltac evt_done5 :=
apply evt_done;
lazymatch goal with
| |- AJe ?L ?J ?A ?T ?c ?ms => refine (aj5_back L J _ A T c ms _ _); [ gp5_solve | ]
end.
Ltac aj5_enter :=
lazymatch goal with
| |- AJ5of ?L ?J ?A ?T ?c ?ms => refine (aj5_enter_l L J _ A T c ms _); let H := fresh "HGP" in intro H; gp5_norm H
end.
