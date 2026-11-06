(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq6.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac litn := fold_closed_in_goal.

Ltac wrange := match goal with |- bv_unsigned ?w <= _ => pose proof (bv_unsigned_in_range 64 w) as WR; unfold bv_modulus in WR; change (2 ^ Z.of_N 64)%Z with (2^64)%Z in WR; lia end.

Ltac u8range := match goal with |- bv_unsigned (Z_to_bv 64 (Z.land ?x 255)) <= _ =>
change (Z.land x 255) with (Z.land x (2^8 - 1)); rewrite (zb_land_mask x 8) by lia;
pose proof (Z.mod_pos_bound x (2^8) ltac:(lia)); rewrite unsigned_lit by lia; lia end.

Lemma neq_wz : forall x y, 0 <= x < 2^64 -> -2^64 <= y < 2^64 -> x <> y -> x <> y + 2^64 ->
bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y Hx Hy N1 N2. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small x) by lia.
destruct (Z.lt_ge_cases y 0).
- replace y with ((y + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition cii_WSA (sp P : Z) : list (Z * Z) := [(sp - 16, sp); (P + 8, P + 16)].

Definition cii_postA (vmax kmax : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (cii_WSA (bv_unsigned sp) P) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ bv_unsigned a0 <= vmax
/\ rw_cells asegs m' P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (Z.max (rem - kmax) 0))]
/\ bytes_at asegs m' ptr data
/\ stk asegs m' lo (bv_unsigned sp).

Definition cii_A_stmt (entry kmax A1 A2 vmax : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
a0 = Z_to_bv 64 P -> bv_unsigned a1 = A1 -> bv_unsigned a2 = A2 ->
asan_rt_ok m ->
rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 ->
0x647000 <= P -> P + 16 <= alloc_ceiling -> (P + 24 <= A_SB \/ A_HMB <= P) -> ptr + rem <= alloc_ceiling -> (rem = 0 \/ P + 16 <= ptr \/ ptr + rem <= P) ->
mem_inv asegs m ->
evt asegs (cii_postA vmax kmax ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition CII_U8_B  : Z := 0x92d5c.
Definition CII_I32_B : Z := 0x92e40.
Definition CII_I64_B : Z := 0x92f5c.
Definition CII_U64_B : Z := 0x93080.

Section Cii.

Lemma cii_EV : forall sp P ptr rem m mc,
unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
alloc_ceiling <= sp - 16 -> 0 <= P -> P + 16 <= alloc_ceiling -> (P + 24 <= A_SB \/ A_HMB <= P) -> ptr + rem <= alloc_ceiling -> 0 < ptr ->
munch [(sp - 16, sp); (P + 8, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
(0 < rem -> unpoisoned asegs mc A_SB ptr rem).
Proof.
intros sp P ptr rem m mc UNP PAL UND LO P0 PAC PAPP DLO PTR0 MUc. pose proof alloc_ceiling_range as ACR.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(sp - 16, sp); (P + 8, P + 16)]).
{ unfold A_SB, A_HMB in *. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
assert (UP : unpoisoned asegs mc A_SB P 16) by (eapply unpoisoned_keep; [exact UNP | exact MUc | lia | lia | exact WAPP]).
split; [apply (unpoisoned_al8_ro mc P 16 P UP); lia|]. split; [apply (unpoisoned_al8_ro mc P 16 (P + 8) UP); [lia | lia | clear - PAL; Z.div_mod_to_equations; lia]|].
intros Hr. pose proof (UND Hr) as U. pose proof U as (_ & _). eapply unpoisoned_keep; [exact U | exact MUc | lia | | exact WAPP].
unfold unpoisoned, shadow_span_hi, A_SB in U. lia.
Qed.
End Cii.
Section U8.
Lemma cii_u8_B : cii_A_stmt CII_U8_B 1 0 255 255.
Proof.
unfold cii_A_stmt, CII_U8_B. intros until data. intros A0 A1 A2 RT FDP UNP PAL SRC LEN PTR0 UND ST LO LOS PIM PAC PAPP DLO PDS MI. subst a0. unfold A_SB, A_HMB in PAPP.
replace a1 with (Z_to_bv 64 0) by (rewrite <- A1; symmetry; apply eq_sym, Z_to_bv_lit_self).
replace a2 with (Z_to_bv 64 255) by (rewrite <- A2; symmetry; apply eq_sym, Z_to_bv_lit_self).
clear A1 A2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (cii_WSA (bv_unsigned sp) P) m) as MU. unfold cii_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells in RTC. apply Forall_app in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply QsKa.Mqa.ro_C8_of_bytes_at in GOT. apply QsKa.Mqa.ro_C8_of_bytes_at in CELL.
assert (EV : forall mc, munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
(0 < rem -> unpoisoned asegs mc A_SB ptr rem))
by (intros mc MUc; eapply (cii_EV (bv_unsigned sp) P ptr rem m mc); try eassumption; lia).
carve_frame 16%nat ST.
step. step.
step. if_lit. step. if_lit.
step. step. step.
destruct (EV _ MU) as (SHP & SHP8 & UNDc).
step. step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step.
step.
destruct (Z.eq_dec rem 0) as [R0 | N0].
- rewrite R0 in *. if_true.
step. step. step. step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
finish.
all: try (change (Z.max (0 - 1) 0) with 0; assumption).
all: try u8range.
- if_falsex.
step. rewrite ?zxb_zero. step. if_false.
step.
step. step.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPj & _ & UNDj) end.
step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step. step.
step. if_falsex.
step. rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 ptr)) by (rewrite (unsigned_lit 0), (unsigned_lit ptr) by lia; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (ptr + (rem + -1))) 1) by (rewrite ?(unsigned_lit (ptr + (rem + -1))) by lia; lia).
step. litn. step. if_false. step. if_falsex.
destruct (unpoisoned_byte_ro _ ptr rem (ptr + (rem + -1)) (UNDj ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1).
step. step. sh_norm. step.
step.
lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc _ ?mm _) =>
assert (B_LD : forall (za3 za4 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (ptr + (rem + -1))) (Z_to_bv 64 0) (Z_to_bv 64 255) za3 za4 (Z_to_bv 64 1) (Z_to_bv 64 0) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FF (Z_to_bv 64 0x92de4) fcc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B_LD.
- rewrite (QsKa.Mqa.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem + -1))) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply B_LD. }
intros za3 za4. clear SHK v1 Hv1.
destruct (nth_error data (Z.to_nat (rem - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
lazymatch goal with H : bytes_at asegs ?mx ptr data |- _ => pose proof (u8ro_read asegs mx ptr data (rem - 1) b1 _ H Hb1 ltac:(lia) eq_refl) as RD1 end.
replace (ptr + (rem - 1)) with (ptr + (rem + -1)) in RD1 by lia.
step. clear RD1.
step.
step. step. step. step. step. step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
finish.
all: try (replace (Z.max (rem - 1) 0) with (rem + -1) by lia; assumption).
all: try u8range.
Qed.
End U8.

Section S_cii_i32_B.
Lemma cii_i32_B : cii_A_stmt CII_I32_B 4 (2^64 - 2^31) (2^31 - 1) (2^64 - 1).
Proof.
unfold cii_A_stmt, CII_I32_B. intros until data. intros A0 A1 A2 RT FDP UNP PAL SRC LEN PTR0 UND ST LO LOS PIM PAC PAPP DLO PDS MI. subst a0. unfold A_SB, A_HMB in PAPP.
replace a1 with (Z_to_bv 64 18446744071562067968) by (change 18446744071562067968 with (2^64 - 2^31); rewrite <- A1; symmetry; apply eq_sym, Z_to_bv_lit_self).
replace a2 with (Z_to_bv 64 2147483647) by (change 2147483647 with (2^31 - 1); rewrite <- A2; symmetry; apply eq_sym, Z_to_bv_lit_self).
clear A1 A2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (cii_WSA (bv_unsigned sp) P) m) as MU. unfold cii_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells in RTC. apply Forall_app in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply QsKa.Mqa.ro_C8_of_bytes_at in GOT. apply QsKa.Mqa.ro_C8_of_bytes_at in CELL.
assert (EV : forall mc, munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
(0 < rem -> unpoisoned asegs mc A_SB ptr rem))
by (intros mc MUc; eapply (cii_EV (bv_unsigned sp) P ptr rem m mc); try eassumption; lia).
carve_frame 16%nat ST.
step. step. step.
step. if_lit.
step. litn. try replace (Z_to_bv 64 (-18446744069414584321)) with (Z_to_bv 64 4294967295) by (apply bv_eq; vm_compute; reflexivity).
step. if_lit.
step. step. step.
destruct (EV _ MU) as (SHP & SHP8 & UNDc).
step. step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. step. step. sh_norm. step. step.

assert (EXITF : forall (mc : word -> option byte) (acc xa3 xt0 xt3 xt5 xt6 xs0 : word) (c : Z),
rw_cells asegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] ->
bytes_at asegs mc ptr data -> c = Z.max (rem - 4) 0 ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (cii_postA (2 ^ 64 - 1) 4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp xt0 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) xs0 s1
(Z_to_bv 64 P) (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 (P + 8)) xa3 (Z_to_bv 64 4294967295) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 (Z_to_bv 64 23) xt5 xt6)
F (Z_to_bv 64 0x92e5c) fc None mc (seg_rom asegs))).
{ intros mc acc xa3 xt0 xt3 xt5 xt6 xs0 c FRc STc FDPc SRCc Hc MUc WMc MIc.
clear FR ST FDP SRC MU WM MI SHP SHP8 UNDc.
step. litn. step. if_lit.
step. step.
step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame H STc (bv_unsigned sp) end.
finish.
all: try (rewrite <- Hc; exact FDPc).
all: try wrange. }

assert (LOOPI : forall (fuel : nat) (i : Z) (mc : word -> option byte) (acc xa3 xt5 xt6 xs0 : word),
4 - i <= Z.of_nat fuel -> 0 <= i <= 3 -> i <= rem ->
rw_cells asegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem - i))] ->
bytes_at asegs mc ptr data ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (cii_postA (2 ^ 64 - 1) 4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (8 * i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) xs0 s1
(Z_to_bv 64 P) (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 (P + 8)) xa3 (Z_to_bv 64 4294967295) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 23) xt5 xt6)
F (Z_to_bv 64 0x92ebc) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc acc xa3 xt5 xt6 xs0 Hfuel Hi Hir FR2 ST2 FDP2 SRC2 MU2 WM2 MI2; [exfalso; lia|].
clear FR ST FDP SRC MU WM MI SHP SHP8 UNDc.
step.
destruct (Z.eq_dec (rem - i) 0) as [E0 | N0].
{ replace (rem - i + -1) with (-1) by lia. if_true.
eapply EXITF with (c := rem - i); [exact FR2 | exact ST2 | exact FDP2 | exact SRC2 | lia | exact MU2 | exact WM2 | exact MI2]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wz x y) by lia end. cbv beta iota.
destruct (EV _ MU2) as (SHPi & SHP8i & UNDi).
step. rewrite ?zxb_zero. step. if_false.
step.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPj & _ & UNDj) end.
step. rewrite ?zxb_zero. step. if_false.
step. step.
step. if_falsex.
step. rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 ptr)) by (rewrite (unsigned_lit 0), (unsigned_lit ptr) by lia; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (ptr + (rem - i + -1))) 1) by (rewrite ?(unsigned_lit (ptr + (rem - i + -1))) by lia; lia).
step. litn. step. if_false. step. if_falsex.
destruct (unpoisoned_byte_ro _ ptr rem (ptr + (rem - i + -1)) (UNDj ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1).
step. step. sh_norm. step.
step.
lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc _ ?mm _) =>
assert (B_LD : forall (zt5 zt6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (8 * i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 0) s1
(Z_to_bv 64 P) (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (ptr + (rem - i + -1))) (Z_to_bv 64 4294967295) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 23) zt5 zt6)
FF (Z_to_bv 64 0x92f04) fcc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B_LD.
- rewrite (QsKa.Mqa.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem - i + -1))) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply B_LD. }
intros zt5 zt6. clear SHK v1 Hv1.
destruct (nth_error data (Z.to_nat (rem - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
lazymatch goal with H : bytes_at asegs ?mx ptr data |- _ => pose proof (u8ro_read asegs mx ptr data (rem - i - 1) b1 _ H Hb1 ltac:(lia) eq_refl) as RD1 end.
replace (ptr + (rem - i - 1)) with (ptr + (rem - i + -1)) in RD1 by lia.
step. clear RD1.
step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx P _ |- _ => rename H into FDP3 end.
destruct (Z.eq_dec i 3) as [IL | INL].
- subst i. if_lit. fold_mkR.
eapply EXITF with (c := rem - 3 + -1); [exact FR2 | exact ST2 | exact FDP3 | eassumption | lia | eassumption | eassumption | eassumption].
- assert (Hic : i = 0 \/ i = 1 \/ i = 2) by lia. clear INL.
destruct Hic as [-> | [-> | ->]]; if_lit.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end. }
fold_mkR.
replace (Z_to_bv 64 (rem + -1)) with (Z_to_bv 64 (rem - 0 + -1)) by (f_equal; lia).
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FDP by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 4%nat 0); [lia | lia | lia | exact FR | exact ST | exact FDP | exact SRC | exact MU | exact WM | exact MI].
Qed.
End S_cii_i32_B.

Section S_cii_i64_B.
Lemma cii_i64_B : cii_A_stmt CII_I64_B 8 (2^63) (2^63 - 1) (2^64 - 1).
Proof.
unfold cii_A_stmt, CII_I64_B. intros until data. intros A0 A1 A2 RT FDP UNP PAL SRC LEN PTR0 UND ST LO LOS PIM PAC PAPP DLO PDS MI. subst a0. unfold A_SB, A_HMB in PAPP.
replace a1 with (Z_to_bv 64 9223372036854775808) by (change 9223372036854775808 with (2^63); rewrite <- A1; symmetry; apply eq_sym, Z_to_bv_lit_self).
replace a2 with (Z_to_bv 64 9223372036854775807) by (change 9223372036854775807 with (2^63 - 1); rewrite <- A2; symmetry; apply eq_sym, Z_to_bv_lit_self).
clear A1 A2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (cii_WSA (bv_unsigned sp) P) m) as MU. unfold cii_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells in RTC. apply Forall_app in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply QsKa.Mqa.ro_C8_of_bytes_at in GOT. apply QsKa.Mqa.ro_C8_of_bytes_at in CELL.
assert (EV : forall mc, munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
(0 < rem -> unpoisoned asegs mc A_SB ptr rem))
by (intros mc MUc; eapply (cii_EV (bv_unsigned sp) P ptr rem m mc); try eassumption; lia).
carve_frame 16%nat ST.
step. step. step.
step. if_lit.
step. litn. try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
step. if_lit.
step. step. step.
destruct (EV _ MU) as (SHP & SHP8 & UNDc).
step. step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. step. step. sh_norm. step. step.

assert (EXITF : forall (mc : word -> option byte) (acc xa3 xt0 xt3 xt5 xt6 xs0 : word) (c : Z),
rw_cells asegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] ->
bytes_at asegs mc ptr data -> c = Z.max (rem - 8) 0 ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (cii_postA (2 ^ 64 - 1) 8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp xt0 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) xs0 s1
(Z_to_bv 64 P) (Z_to_bv 64 9223372036854775808) (Z_to_bv 64 (P + 8)) xa3 (Z_to_bv 64 18446744073709551615) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 (Z_to_bv 64 55) xt5 xt6)
F (Z_to_bv 64 0x93038) fc None mc (seg_rom asegs))).
{ intros mc acc xa3 xt0 xt3 xt5 xt6 xs0 c FRc STc FDPc SRCc Hc MUc WMc MIc.
clear FR ST FDP SRC MU WM MI SHP SHP8 UNDc.
step. step. if_lit.
step.
step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame H STc (bv_unsigned sp) end.
finish.
all: try (rewrite <- Hc; exact FDPc).
all: try wrange. }

assert (LOOPI : forall (fuel : nat) (i : Z) (mc : word -> option byte) (acc xa3 xt5 xt6 xs0 : word),
8 - i <= Z.of_nat fuel -> 0 <= i <= 7 -> i <= rem ->
rw_cells asegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem - i))] ->
bytes_at asegs mc ptr data ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (cii_postA (2 ^ 64 - 1) 8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (8 * i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) xs0 s1
(Z_to_bv 64 P) (Z_to_bv 64 9223372036854775808) (Z_to_bv 64 (P + 8)) xa3 (Z_to_bv 64 18446744073709551615) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 55) xt5 xt6)
F (Z_to_bv 64 0x92fbc) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc acc xa3 xt5 xt6 xs0 Hfuel Hi Hir FR2 ST2 FDP2 SRC2 MU2 WM2 MI2; [exfalso; lia|].
clear FR ST FDP SRC MU WM MI SHP SHP8 UNDc.
step.
destruct (Z.eq_dec (rem - i) 0) as [E0 | N0].
{ replace (rem - i + -1) with (-1) by lia. if_true.
eapply EXITF with (c := rem - i); [exact FR2 | exact ST2 | exact FDP2 | exact SRC2 | lia | exact MU2 | exact WM2 | exact MI2]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wz x y) by lia end. cbv beta iota.
destruct (EV _ MU2) as (SHPi & SHP8i & UNDi).
step. rewrite ?zxb_zero. step. if_false.
step.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPj & _ & UNDj) end.
step. rewrite ?zxb_zero. step. if_false.
step. step.
step. if_falsex.
step. rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 ptr)) by (rewrite (unsigned_lit 0), (unsigned_lit ptr) by lia; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (ptr + (rem - i + -1))) 1) by (rewrite ?(unsigned_lit (ptr + (rem - i + -1))) by lia; lia).
step. litn. step. if_false. step. if_falsex.
destruct (unpoisoned_byte_ro _ ptr rem (ptr + (rem - i + -1)) (UNDj ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1).
step. step. sh_norm. step.
step.
lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc _ ?mm _) =>
assert (B_LD : forall (zt5 zt6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (8 * i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 0) s1
(Z_to_bv 64 P) (Z_to_bv 64 9223372036854775808) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (ptr + (rem - i + -1))) (Z_to_bv 64 18446744073709551615) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 55) zt5 zt6)
FF (Z_to_bv 64 0x93004) fcc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B_LD.
- rewrite (QsKa.Mqa.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem - i + -1))) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply B_LD. }
intros zt5 zt6. clear SHK v1 Hv1.
destruct (nth_error data (Z.to_nat (rem - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
lazymatch goal with H : bytes_at asegs ?mx ptr data |- _ => pose proof (u8ro_read asegs mx ptr data (rem - i - 1) b1 _ H Hb1 ltac:(lia) eq_refl) as RD1 end.
replace (ptr + (rem - i - 1)) with (ptr + (rem - i + -1)) in RD1 by lia.
step. clear RD1.
step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx P _ |- _ => rename H into FDP3 end.
destruct (Z.eq_dec i 7) as [IL | INL].
- subst i. if_lit. fold_mkR.
eapply EXITF with (c := rem - 7 + -1); [exact FR2 | exact ST2 | exact FDP3 | eassumption | lia | eassumption | eassumption | eassumption].
- assert (Hic : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia. clear INL.
destruct Hic as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; if_lit.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end. }
fold_mkR.
replace (Z_to_bv 64 (rem + -1)) with (Z_to_bv 64 (rem - 0 + -1)) by (f_equal; lia).
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FDP by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 8%nat 0); [lia | lia | lia | exact FR | exact ST | exact FDP | exact SRC | exact MU | exact WM | exact MI].
Qed.
End S_cii_i64_B.

Section S_cii_u64_B.
Lemma cii_u64_B : cii_A_stmt CII_U64_B 8 0 (2^64 - 1) (2^64 - 1).
Proof.
unfold cii_A_stmt, CII_U64_B. intros until data. intros A0 A1 A2 RT FDP UNP PAL SRC LEN PTR0 UND ST LO LOS PIM PAC PAPP DLO PDS MI. subst a0. unfold A_SB, A_HMB in PAPP.
replace a1 with (Z_to_bv 64 0) by (rewrite <- A1; symmetry; apply eq_sym, Z_to_bv_lit_self).
replace a2 with (Z_to_bv 64 18446744073709551615) by (change 18446744073709551615 with (2^64 - 1); rewrite <- A2; symmetry; apply eq_sym, Z_to_bv_lit_self).
clear A1 A2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (cii_WSA (bv_unsigned sp) P) m) as MU. unfold cii_WSA in MU.
pose proof (wmono_refl asegs m) as WM.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells in RTC. apply Forall_app in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply QsKa.Mqa.ro_C8_of_bytes_at in GOT. apply QsKa.Mqa.ro_C8_of_bytes_at in CELL.
assert (EV : forall mc, munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc ->
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
(0 < rem -> unpoisoned asegs mc A_SB ptr rem))
by (intros mc MUc; eapply (cii_EV (bv_unsigned sp) P ptr rem m mc); try eassumption; lia).
carve_frame 16%nat ST.
step. step. step.
step. if_lit.
step. litn. try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
step. if_lit.
step. step. step.
destruct (EV _ MU) as (SHP & SHP8 & UNDc).
step. step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. step. step. sh_norm. step. step.

assert (EXITF : forall (mc : word -> option byte) (acc xa3 xt0 xt3 xt5 xt6 xs0 : word) (c : Z),
rw_cells asegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] ->
bytes_at asegs mc ptr data -> c = Z.max (rem - 8) 0 ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (cii_postA (2 ^ 64 - 1) 8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp xt0 (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) xs0 s1
(Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 (P + 8)) xa3 (Z_to_bv 64 18446744073709551615) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 (Z_to_bv 64 55) xt5 xt6)
F (Z_to_bv 64 0x9315c) fc None mc (seg_rom asegs))).
{ intros mc acc xa3 xt0 xt3 xt5 xt6 xs0 c FRc STc FDPc SRCc Hc MUc WMc MIc.
clear FR ST FDP SRC MU WM MI SHP SHP8 UNDc.
step. step. if_lit.
step.
step. step. step. step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame H STc (bv_unsigned sp) end.
finish.
all: try (rewrite <- Hc; exact FDPc).
all: try wrange. }

assert (LOOPI : forall (fuel : nat) (i : Z) (mc : word -> option byte) (acc xa3 xt5 xt6 xs0 : word),
8 - i <= Z.of_nat fuel -> 0 <= i <= 7 -> i <= rem ->
rw_cells asegs mc (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -16) ->
rw_cells asegs mc P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem - i))] ->
bytes_at asegs mc ptr data ->
munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 8, P + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (cii_postA (2 ^ 64 - 1) 8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (8 * i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) xs0 s1
(Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 (P + 8)) xa3 (Z_to_bv 64 18446744073709551615) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 55) xt5 xt6)
F (Z_to_bv 64 0x930e0) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc acc xa3 xt5 xt6 xs0 Hfuel Hi Hir FR2 ST2 FDP2 SRC2 MU2 WM2 MI2; [exfalso; lia|].
clear FR ST FDP SRC MU WM MI SHP SHP8 UNDc.
step.
destruct (Z.eq_dec (rem - i) 0) as [E0 | N0].
{ replace (rem - i + -1) with (-1) by lia. if_true.
eapply EXITF with (c := rem - i); [exact FR2 | exact ST2 | exact FDP2 | exact SRC2 | lia | exact MU2 | exact WM2 | exact MI2]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wz x y) by lia end. cbv beta iota.
destruct (EV _ MU2) as (SHPi & SHP8i & UNDi).
step. rewrite ?zxb_zero. step. if_false.
step.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (EV _ MUc) as (SHPj & _ & UNDj) end.
step. rewrite ?zxb_zero. step. if_false.
step. step.
step. if_falsex.
step. rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 ptr)) by (rewrite (unsigned_lit 0), (unsigned_lit ptr) by lia; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (ptr + (rem - i + -1))) 1) by (rewrite ?(unsigned_lit (ptr + (rem - i + -1))) by lia; lia).
step. litn. step. if_false. step. if_falsex.
destruct (unpoisoned_byte_ro _ ptr rem (ptr + (rem - i + -1)) (UNDj ltac:(lia)) ltac:(lia)) as (v1 & SHK & Hv1).
step. step. sh_norm. step.
step.
lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc _ ?mm _) =>
assert (B_LD : forall (zt5 zt6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (8 * i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 0) s1
(Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (ptr + (rem - i + -1))) (Z_to_bv 64 18446744073709551615) acc (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 55) zt5 zt6)
FF (Z_to_bv 64 0x93128) fcc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B_LD.
- rewrite (QsKa.Mqa.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem - i + -1))) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply B_LD. }
intros zt5 zt6. clear SHK v1 Hv1.
destruct (nth_error data (Z.to_nat (rem - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
lazymatch goal with H : bytes_at asegs ?mx ptr data |- _ => pose proof (u8ro_read asegs mx ptr data (rem - i - 1) b1 _ H Hb1 ltac:(lia) eq_refl) as RD1 end.
replace (ptr + (rem - i - 1)) with (ptr + (rem - i + -1)) in RD1 by lia.
step. clear RD1.
step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx P _ |- _ => rename H into FDP3 end.
destruct (Z.eq_dec i 7) as [IL | INL].
- subst i. if_lit. fold_mkR.
eapply EXITF with (c := rem - 7 + -1); [exact FR2 | exact ST2 | exact FDP3 | eassumption | lia | eassumption | eassumption | eassumption].
- assert (Hic : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia. clear INL.
destruct Hic as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; if_lit.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end.
+ step. step. step. step. if_lit. fold_mkR.
lazymatch goal with |- context [Z_to_bv 64 (rem - ?i0 + -2)] =>
replace (rem - i0 + -2) with (rem - (i0 + 1) + -1) by lia;
replace (rem - i0 + -1) with (rem - (i0 + 1)) in FDP3 by lia;
eapply (IH (i0 + 1)); [lia | lia | lia | exact FR2 | exact ST2 | exact FDP3 | eassumption | eassumption | eassumption | eassumption] end. }
fold_mkR.
replace (Z_to_bv 64 (rem + -1)) with (Z_to_bv 64 (rem - 0 + -1)) by (f_equal; lia).
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FDP by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 8%nat 0); [lia | lia | lia | exact FR | exact ST | exact FDP | exact SRC | exact MU | exact WM | exact MI].
Qed.
End S_cii_u64_B.

End RC__1.
