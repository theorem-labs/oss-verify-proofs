(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1sa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X03z X04v X0jg X00b.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X04r X04t X04l X04u X04q X04m.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X0ux X0vt X19x X0ra.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0vp X0vr X0vj X0vs X0vo X0vk.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vk.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

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
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma pcom_dstr_spec : forall (q p ap nx S : Z) (str : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s4 = Z_to_bv 64 90148 ->
s5 = Z_to_bv 64 ap -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) -> s10 = Z_to_bv 64 (-1) -> s11 = Z_to_bv 64 37 ->
0 < nx < 256 ->
bytes_at bsegs m p (zb8 [37; 115; nx]) -> rw_cells bsegs m (q + -2216) DIR0 ->
ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> q <= ap -> ap + 8 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ q <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) -> pctx m ->
stk bsegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> p + 3 <= lo -> q <= 2^47 ->
mem_inv bsegs m ->
evt bsegs (pcd_post q (p + 2) (ap + 8) gp tp s0 s2 s4 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59798) fc None m (seg_rom bsegs)).
Proof using RIP.
intros until m. intros -> -> -> -> -> -> -> -> -> -> NX BY DIR SLOT QAP APH CS S0 SSEP SH CHK PCX ST LO LOLO PLO QH MI.
unfold kHighShadowEnd in LOLO.
apply dir0_split in DIR. unfold DIRS in DIR. cbn [repeat] in DIR.
pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map] in PB.
unfold zb8 in BY. cbn [map] in BY.
pose proof (bytes_at_nth1 bsegs m p _ 0 _ BY eq_refl) as B0. pose proof (bytes_at_nth1 bsegs m p _ 1 _ BY eq_refl) as B1.
pose proof (bytes_at_nth1 bsegs m p _ 2 _ BY eq_refl) as B2. clear BY.
change (Z.of_nat 0) with 0 in B0. change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2. rewrite Z.add_0_r in B0.
apply ro_C1_of_bytes in B0. apply ro_C1_of_bytes in B1. apply ro_C1_of_bytes in B2.
pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
assert (EUn : bv_unsigned (Z_to_bv 8 nx) = nx) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
zhide.
xsteps_to 0x79ce0%Z. strchr_call.
xsteps_to 0x79ce0%Z. strchr_call.
xsteps_to 0x79ce0%Z. strchr_call.
xsteps_to 0x79ce0%Z. strchr_call.
xsteps_to 0x79ce0%Z. strchr_call.
xsteps_to 0x79ce0%Z. strchr_call.
xsteps_to 0x79d80%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CS1 : cstr_at mm S str) by
(apply (cstr_agree m mm S str CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia) end.
call internal_strlen_spec; [reflexivity| exact CS1| assumption|].
xsteps_to 0x59b88%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CHK1 : chk_ok mm S (Z.of_nat (length str) + 1)) by
(eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]);
destruct PCX1 as (M2S1 & PC1) end.
call (pcs_check RIP (q + -2240) S (Z.of_nat (length str) + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
all: first [ exact ST | exact CHK1 | exact M2S1 | exact PC1 | assumption | (unfold kHighShadowEnd; lia) | lia | idtac ].
xsteps_to 0x5976c%Z.
brF K.
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 (q + -2240))) |- _ => rewrite EUs in H; rename H into ST2 end.
apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
apply evt_done; unfold pcd_post; do 19 eexists; split; [reflexivity|].
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST2| eexists; exact DIR].
Qed.
End WithRIP.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

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
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call asegs m mm MU WM end end.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma pcom_dstr_spec : forall (q p ap nx S : Z) (str : list byte) (lo : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s4 = Z_to_bv 64 89908 ->
s5 = Z_to_bv 64 ap -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) -> s10 = Z_to_bv 64 (-1) -> s11 = Z_to_bv 64 37 ->
0 < nx < 256 ->
bytes_at asegs m p (zb8 [37; 115; nx]) -> rw_cells asegs m (q + -2216) DIR0 ->
ro_cells asegs m ap [C8 (Z_to_bv 64 S)] -> q <= ap -> ap + 8 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ q <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) -> pctx m ->
stk asegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> p + 3 <= lo -> q <= 2^47 ->
mem_inv asegs m ->
evt asegs (pcd_post q (p + 2) (ap + 8) gp tp s0 s2 s4 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x596ac) fc None m (seg_rom asegs)).
Proof using RIP.
intros until m. intros -> -> -> -> -> -> -> -> -> -> NX BY DIR SLOT QAP APH CS S0 SSEP SH CHK PCX ST LO LOLO PLO QH MI.
unfold kHighShadowEnd in LOLO.
apply dir0_split in DIR. unfold DIRS in DIR. cbn [repeat] in DIR.
pose proof (bytes_at_bound _ _ _ _ BY) as PB. cbn [length zb8 map] in PB.
unfold zb8 in BY. cbn [map] in BY.
pose proof (bytes_at_nth1 asegs m p _ 0 _ BY eq_refl) as B0. pose proof (bytes_at_nth1 asegs m p _ 1 _ BY eq_refl) as B1.
pose proof (bytes_at_nth1 asegs m p _ 2 _ BY eq_refl) as B2. clear BY.
change (Z.of_nat 0) with 0 in B0. change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2. rewrite Z.add_0_r in B0.
apply ro_C1_of_bytes in B0. apply ro_C1_of_bytes in B1. apply ro_C1_of_bytes in B2.
pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
assert (EUap : bv_unsigned (Z_to_bv 64 ap) = ap) by (apply unsigned_lit; lia).
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
assert (EUn : bv_unsigned (Z_to_bv 8 nx) = nx) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
zhide.
xsteps_to 0x79bf4%Z. strchr_call.
xsteps_to 0x79bf4%Z. strchr_call.
xsteps_to 0x79bf4%Z. strchr_call.
xsteps_to 0x79bf4%Z. strchr_call.
xsteps_to 0x79bf4%Z. strchr_call.
xsteps_to 0x79bf4%Z. strchr_call.
xsteps_to 0x79c94%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CS1 : cstr_at mm S str) by
(apply (cstr_agree m mm S str CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; lia) end.
call internal_strlen_spec; [reflexivity| exact CS1| assumption|].
xsteps_to 0x59a9c%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CHK1 : chk_ok mm S (Z.of_nat (length str) + 1)) by
(eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]);
destruct PCX1 as (M2S1 & PC1) end.
call (pcs_check RIP (q + -2240) S (Z.of_nat (length str) + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
all: first [ exact ST | exact CHK1 | exact M2S1 | exact PC1 | assumption | (unfold kHighShadowEnd; lia) | lia | idtac ].
xsteps_to 0x59680%Z.
brF K.
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (q + -2240))) |- _ => rewrite EUs in H; rename H into ST2 end.
apply rw_forget in DIR; cbn [cells_size csize Nat.add] in DIR.
apply evt_done; unfold pcd_post; do 19 eexists; split; [reflexivity|].
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST2| eexists; exact DIR].
Qed.
End WithRIP.
