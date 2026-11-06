(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg X1dj X1cr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.MallocA Require Import X1dn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X0hr
X0j1 X0hh X046 X0j6 X0j8 X0gp X0gd X0g8 X0hs X0hf X0gf X0go X0ge X02a X0gg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X18c X182 X0v4 X19p X19r X17a X16y X16t X18d X180 X170 X179 X16z X0t9 X171.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X170 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X179 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X171.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
| H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition realloc_B_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(M UB n' B : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0x46800) sp gp tp t0' t1' t2' (Z_to_bv 64 B) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16))
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 B) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 n') (Z_to_bv 64 UB)
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 deallocate_entry) fc None m' (seg_rom bsegs)
/\ munch [(UB, UB + n')]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' UB [CB (Z.to_nat n') src]
/\ bytes_at bsegs m' (M + 16) src.

Lemma realloc_B_spec : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (M UB n nold b1 B : Z) (ctx : word) (src uj : list byte),
(1 <= n <= 2^31)%Z -> (1 <= nold < 2^32)%Z -> (0 < UB)%Z -> (UB + Z.min n nold < 2^63)%Z -> (0 < M)%Z -> (M + 16 + nold < 2^63)%Z ->
(0 <= b1 < 256)%Z ->
rw_cells bsegs m M [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 nold); C8 ctx] ->
bytes_at bsegs m (M + 16) src -> length src = Z.to_nat (Z.min n nold) ->
rw_cells bsegs m UB [CB (Z.to_nat (Z.min n nold)) uj] ->
(M + 16 + Z.min n nold <= UB \/ UB + Z.min n nold <= M)%Z ->
ro_cells bsegs m 0xfc140 [C8 (Z_to_bv 64 0xfe038)] -> ro_cells bsegs m 0xfe038 [C8 (Z_to_bv 64 0xf16f4)] ->
mem_inv bsegs m ->
evt bsegs (realloc_B_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc M UB (Z.min n nold) B src m)
(MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 B) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INST) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4676c) fc None m (seg_rom bsegs)).
Proof.
intros until uj. intros Hn Hno HUB HUBh HM HMh Hb1 HD SRC LEN DST SEP G1 G2 MI.
pose proof (munch_refl [(UB, UB + Z.min n nold)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold INST, g_instance, deallocate_entry in *.
zstep. zstep. ifF.
do 3 zstep. zstep. ifT.
do 3 zstep. zstep. ifF.
do 4 zstep.
change (Z.land (Z.shiftl (bv_unsigned (zx16 (Z_to_bv 64 0))) 32) 18446744073709551615) with 0%Z.
rewrite Z.lor_0_l, zx32_small, unsigned_lit by lia.
zstep.
assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (EUo : bv_unsigned (Z_to_bv 64 nold) = nold) by (apply unsigned_lit; lia).
destruct (Z.ltb_spec n nold) as [LT|GE].
-
ifT.
replace (Z.min n nold) with n in * by lia.
do 3 zstep. zstep.
assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply unsigned_lit; lia).
assert (EUM : bv_unsigned (Z_to_bv 64 (M + 16)) = (M + 16)%Z) by (apply unsigned_lit; lia).
call (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ src uj).
all: rewrite ?EUB, ?EUM, ?EUn, ?EUo; try eassumption; try lia.
rewrite ?EUB, ?EUM, ?EUn, ?EUo in *.
do 6 zstep. zstep.
apply evt_done. unfold realloc_B_post, deallocate_entry, INST, g_instance.
do 10 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
-
ifF.
replace (Z.min n nold) with nold in * by lia.
zstep.
do 3 zstep. zstep.
assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply unsigned_lit; lia).
assert (EUM : bv_unsigned (Z_to_bv 64 (M + 16)) = (M + 16)%Z) by (apply unsigned_lit; lia).
call (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ src uj).
all: rewrite ?EUB, ?EUM, ?EUn, ?EUo; try eassumption; try lia.
rewrite ?EUB, ?EUM, ?EUn, ?EUo in *.
do 6 zstep. zstep.
apply evt_done. unfold realloc_B_post, deallocate_entry, INST, g_instance.
do 10 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Definition realloc_C_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(UB lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2208, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp).

Lemma realloc_C_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
ra0 s0 s1 s2 s3 s4 s5 s6 s0r s1r s2r s3r s4r (F : bvmap 5 word) fc (m : mem) (UB lo : Z) (ws : list word) (w : word)
(jp jq jr : list byte),
(0 < UB < 2^63)%Z ->
stk bsegs m lo (bv_unsigned sp + -2208) -> (lo <= bv_unsigned sp + -2208)%Z -> (0x65b000 <= lo)%Z ->
rw_cells bsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells bsegs m (bv_unsigned sp + -72) [CB 8 jp] ->
rw_cells bsegs m (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
u64arr bsegs m (bv_unsigned sp + -2120) ws -> length ws = 255%nat ->
rw_cells bsegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w] ->
rw_cells bsegs m (bv_unsigned sp + -2144) [CB 8 jq] ->
rw_cells bsegs m (bv_unsigned sp + -2160) [CB 8 jr; C8 (Z_to_bv 64 0x68770)] ->
rw_cells bsegs m (bv_unsigned sp + -2208) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x466f0)] ->
mem_inv bsegs m ->
evt bsegs (realloc_C_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc UB lo m)
(MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
s2' s3' (Z_to_bv 64 UB) s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x46800) fc None m (seg_rom bsegs)).
Proof.
intros until jr. intros HUB ST HLO HIMG FRs FRp FRt TB HTB FRb FRq FRa FRr MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
pose proof (munch_refl [(SP - 2208, SP)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
apply u64arr_rw_ma in TB. rewrite HTB in TB.
zhide.

zstep. do 6 zstep. zstep.
release_frame FRr ST (SP + -2160)%Z.
zstep.

zstep. ifF.
do 2 zstep.
release_frame FRa ST (SP + -2144)%Z.
zstep.

do 10 zstep.
release_frame FRq ST (SP + -2136)%Z.
release_frame FRb ST (SP + -2120)%Z. release_frame TB ST (SP + -80)%Z. release_frame FRt ST (SP + -72)%Z.
release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
zstep.
finish.
all: rewrite ?(unsigned_lit SP) by lia; try assumption.
Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
| H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition realloc_B_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(M UB n' B : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0x46714) sp gp tp t0' t1' t2' (Z_to_bv 64 B) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16))
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 B) (Z_to_bv 64 1) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 n') (Z_to_bv 64 UB)
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 deallocate_entry) fc None m' (seg_rom asegs)
/\ munch [(UB, UB + n')]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' UB [CB (Z.to_nat n') src]
/\ bytes_at asegs m' (M + 16) src.

Lemma realloc_B_spec : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (M UB n nold b1 B : Z) (ctx : word) (src uj : list byte),
(1 <= n <= 2^31)%Z -> (1 <= nold < 2^32)%Z -> (0 < UB)%Z -> (UB + Z.min n nold < 2^63)%Z -> (0 < M)%Z -> (M + 16 + nold < 2^63)%Z ->
(0 <= b1 < 256)%Z ->
rw_cells asegs m M [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 nold); C8 ctx] ->
bytes_at asegs m (M + 16) src -> length src = Z.to_nat (Z.min n nold) ->
rw_cells asegs m UB [CB (Z.to_nat (Z.min n nold)) uj] ->
(M + 16 + Z.min n nold <= UB \/ UB + Z.min n nold <= M)%Z ->
ro_cells asegs m 0xf38c0 [C8 (Z_to_bv 64 0xf57b8)] -> ro_cells asegs m 0xf57b8 [C8 (Z_to_bv 64 0xe8e80)] ->
mem_inv asegs m ->
evt asegs (realloc_B_post sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc M UB (Z.min n nold) B src m)
(MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 B) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 INST) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x46680) fc None m (seg_rom asegs)).
Proof.
intros until uj. intros Hn Hno HUB HUBh HM HMh Hb1 HD SRC LEN DST SEP G1 G2 MI.
pose proof (munch_refl [(UB, UB + Z.min n nold)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold INST, g_instance, deallocate_entry in *.
zstep. zstep. ifF.
do 3 zstep. zstep. ifT.
do 3 zstep. zstep. ifF.
do 4 zstep.
change (Z.land (Z.shiftl (bv_unsigned (zx16 (Z_to_bv 64 0))) 32) 18446744073709551615) with 0%Z.
rewrite Z.lor_0_l, zx32_small, unsigned_lit by lia.
zstep.
assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (EUo : bv_unsigned (Z_to_bv 64 nold) = nold) by (apply unsigned_lit; lia).
destruct (Z.ltb_spec n nold) as [LT|GE].
-
ifT.
replace (Z.min n nold) with n in * by lia.
do 3 zstep. zstep.
assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply unsigned_lit; lia).
assert (EUM : bv_unsigned (Z_to_bv 64 (M + 16)) = (M + 16)%Z) by (apply unsigned_lit; lia).
call (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ src uj).
all: rewrite ?EUB, ?EUM, ?EUn, ?EUo; try eassumption; try lia.
rewrite ?EUB, ?EUM, ?EUn, ?EUo in *.
do 6 zstep. zstep.
apply evt_done. unfold realloc_B_post, deallocate_entry, INST, g_instance.
do 10 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
-
ifF.
replace (Z.min n nold) with nold in * by lia.
zstep.
do 3 zstep. zstep.
assert (EUB : bv_unsigned (Z_to_bv 64 UB) = UB) by (apply unsigned_lit; lia).
assert (EUM : bv_unsigned (Z_to_bv 64 (M + 16)) = (M + 16)%Z) by (apply unsigned_lit; lia).
call (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ src uj).
all: rewrite ?EUB, ?EUM, ?EUn, ?EUo; try eassumption; try lia.
rewrite ?EUB, ?EUM, ?EUn, ?EUo in *.
do 6 zstep. zstep.
apply evt_done. unfold realloc_B_post, deallocate_entry, INST, g_instance.
do 10 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Definition realloc_C_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(UB lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2208, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).

Lemma realloc_C_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
ra0 s0 s1 s2 s3 s4 s5 s6 s0r s1r s2r s3r s4r (F : bvmap 5 word) fc (m : mem) (UB lo : Z) (ws : list word) (w : word)
(jp jq jr : list byte),
(0 < UB < 2^63)%Z ->
stk asegs m lo (bv_unsigned sp + -2208) -> (lo <= bv_unsigned sp + -2208)%Z -> (0x652000 <= lo)%Z ->
rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jp] ->
rw_cells asegs m (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
u64arr asegs m (bv_unsigned sp + -2120) ws -> length ws = 255%nat ->
rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w] ->
rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jq] ->
rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 jr; C8 (Z_to_bv 64 0x68684)] ->
rw_cells asegs m (bv_unsigned sp + -2208) [C8 s4r; C8 s3r; C8 s2r; C8 s1r; C8 s0r; C8 (Z_to_bv 64 0x46604)] ->
mem_inv asegs m ->
evt asegs (realloc_C_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc UB lo m)
(MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7
s2' s3' (Z_to_bv 64 UB) s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x46714) fc None m (seg_rom asegs)).
Proof.
intros until jr. intros HUB ST HLO HIMG FRs FRp FRt TB HTB FRb FRq FRa FRr MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
pose proof (munch_refl [(SP - 2208, SP)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
apply u64arr_rw_ma in TB. rewrite HTB in TB.
zhide.

zstep. do 6 zstep. zstep.
release_frame FRr ST (SP + -2160)%Z.
zstep.

zstep. ifF.
do 2 zstep.
release_frame FRa ST (SP + -2144)%Z.
zstep.

do 10 zstep.
release_frame FRq ST (SP + -2136)%Z.
release_frame FRb ST (SP + -2120)%Z. release_frame TB ST (SP + -80)%Z. release_frame FRt ST (SP + -72)%Z.
release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
zstep.
finish.
all: rewrite ?(unsigned_lit SP) by lia; try assumption.
Qed.
