(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X07r.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yj X0yq X0yl X0ym X0yo X0yp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma corr_rows : forall m cq cb, rw_cells bsegs m cq [CB 112 cb] ->
exists r0 r1 r2 r3 : list word, length r0 = 7%nat /\ length r1 = 7%nat /\ length r2 = 7%nat /\ length r3 = 7%nat
/\ rw_cells bsegs m cq (f32 r0) /\ rw_cells bsegs m (cq + 28) (f32 r1) /\ rw_cells bsegs m (cq + 56) (f32 r2) /\ rw_cells bsegs m (cq + 84) (f32 r3).
Proof.
intros m cq cb CQ.
destruct (rw_cells_CB_f32 bsegs _ _ 28%nat _ CQ) as (c & Lc & CQ').
destruct (f32_split bsegs m cq c 7%nat ltac:(lia) CQ') as [Q0 QR]. change (4 * Z.of_nat 7) with 28 in QR.
assert (L1 : length (skipn 7 c) = 21%nat) by (rewrite skipn_length; lia).
destruct (f32_split bsegs m (cq + 28) (skipn 7 c) 7%nat ltac:(lia) QR) as [Q1 QR2]. change (4 * Z.of_nat 7) with 28 in QR2.
assert (L2 : length (skipn 7 (skipn 7 c)) = 14%nat) by (rewrite skipn_length; lia).
destruct (f32_split bsegs m (cq + 28 + 28) (skipn 7 (skipn 7 c)) 7%nat ltac:(lia) QR2) as [Q2 Q3]. change (4 * Z.of_nat 7) with 28 in Q3.
replace (cq + 28 + 28) with (cq + 56) in * by lia. replace (cq + 56 + 28) with (cq + 84) in * by lia.
exists (firstn 7 c), (firstn 7 (skipn 7 c)), (firstn 7 (skipn 7 (skipn 7 c))), (skipn 7 (skipn 7 (skipn 7 c))).
split; [rewrite firstn_length_le; lia|]. split; [rewrite firstn_length_le; lia|]. split; [rewrite firstn_length_le; lia|].
split; [rewrite skipn_length; lia|].
exact (conj Q0 (conj Q1 (conj Q2 Q3))).
Qed.

Lemma fchain_15_front : forall (a b c z : word) (G : bvmap 5 word),
bvmap_set 12 a (bvmap_set 13 b (bvmap_set 14 c (bvmap_set 15 z G))) = bvmap_set 15 z (bvmap_set 12 a (bvmap_set 13 b (bvmap_set 14 c G))).
Proof. intros. norm_fchain. reflexivity. Qed.

Definition ip_body_stmt : Prop :=
forall (q lo EB eoff p IP f cq : Z) (eb ip : list word) (cb j48 : list byte)
(ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
length eb = 500%nat -> 0 <= eoff - p - 6 -> eoff - p <= 414 -> eoff + 80 <= 500 -> 0 <= eoff -> length ip = 80%nat ->
rw_cells bsegs m EB (f32 eb) -> rw_cells bsegs m IP (f32 ip) -> rw_cells bsegs m cq [CB 112 cb] ->
rw_cells bsegs m (q + 32) [C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 p); CB 8 j48; C8 (Z_to_bv 64 IP)] ->
aobj bsegs m EB 2000 -> aobj bsegs m IP 320 -> aobj bsegs m cq 112 -> aobj bsegs m SHIFT_FILT 84 ->
EB mod 4 = 0 -> IP mod 4 = 0 -> cq = f + 32 -> f mod 64 = 0 -> 0 < EB ->
stk bsegs m lo q -> lo <= q - 48 -> SH_HI <= lo -> q + 192 < 2^63 ->
EB + 2000 <= lo -> q + 192 <= IP -> IP + 320 <= APP_TOP ->
IMG_TOP_B <= cq -> cq + 112 <= lo -> (cq + 112 <= SH_LO \/ SH_HI <= cq) -> (cq + 112 <= EB \/ EB + 2000 <= cq) ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
(F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ip' : list word) (cb' : list byte),
ms = MS (mkR ra' (Z_to_bv 64 q) gp tp t0' t1' t2' s0 (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 A_ip_epi) fc' None m' (seg_rom bsegs)
/\ munch [(q + -48, q); (q + 48, q + 56); (cq, cq + 112); (IP, IP + 320)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ stk bsegs m' lo q
/\ rw_cells bsegs m' IP (f32 ip') /\ length ip' = 80%nat /\ rw_cells bsegs m' cq [CB 112 cb']
/\ rw_cells bsegs m' (q + 32) [C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 SHIFT_FILT); C8 (Z_to_bv 64 IP)])
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (EB + 4 * eoff - 4 * p - 12)) s3 (Z_to_bv 64 (EB + 4 * eoff)) s5 s6 s7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_body) fc None m (seg_rom bsegs)).
Lemma ip_body : ip_body_stmt.
Proof.
intros q lo EB eoff p IP f cq eb ip cb j48 ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
LEB R1 R2 R3 R4 LIP XEB XIP CQ FRS OBE OBI OBC OBT E4 IP4 Hcq F64 EB0 ST QLO LOS Q63 EBLO QIP IPT CQ0 CQLO CQSH CQEB CC MI FRM.
unfold A_ip_body, A_ip_epi.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof CQ0 as CQ0'. unfold IMG_TOP_B in CQ0'. pose proof CQSH as CQSH'. unfold SH_LO, SH_HI in CQSH'.
unfold APP_TOP in *.
pose proof (munch_refl [(q + -48, q); (q + 48, q + 56); (cq, cq + 112); (IP, IP + 320)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(q + -48, q); (q + 48, q + 56); (cq, cq + 112); (IP, IP + 320)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (CQ8 : cq mod 8 = 0) by (clear - Hcq F64; Z.div_mod_to_equations; lia).

chunk_uncons FRS as F32. chunk_uncons FRS as F40. chunk_uncons FRS as F48. rename FRS into F56.
replace (q + 32 + 8) with (q + 40) in F40 by lia. replace (q + 32 + 8 + 8) with (q + 48) in F48 by lia. replace (q + 32 + 8 + 8 + 8) with (q + 56) in F56 by lia.

destruct (corr_rows m cq cb CQ) as (r0 & r1 & r2 & r3 & L0 & L1 & L2 & L3 & Q0 & Q1 & Q2 & Q3); clear CQ.
destruct r0 as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|? ?]]]]]]]]; cbn in L0; try lia. clear L0.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XIP) as BIP; rewrite cells_size_f32, LIP in BIP.

ato 0xa96f0.
rewrite zb_lxor_ones by lia. replace (f + 32) with cq by lia.
change (Z_to_bv 64 0) with (Z_to_bv 64 (4 * Z.of_nat (@length word []))).
pose proof (aobj_munch bsegs _ m _ EB 2000 OBE MU (shfree_of_aobj bsegs _ m EB 2000 OF OBE)) as OBEc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(q + -48, q); (cq, cq + 28)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc cq (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
call (corr0_loop EB eoff p q lo cq eb mc gp tp s0 s10 s11 LEB R1 R2 R3 R4 OBEc E4 EB0 QLO LOS ltac:(lia) EBLO CQ0 CQLO CQSH CQEB
6%nat [] [y1; y2; y3; y4; y5; y6] cq y0);
[ reflexivity | reflexivity | cbn [length]; lia | exact FRM | eassumption | exact MU0 | exact WM0 | exact CC | exact ST | exact XEB | exact XD0 | exact Q0 | ] end.
clear MU0 WM0 XD0 OBEc FRM. rename MI0 into MI.
match goal with H : frm0 _, H2 : rw_cells _ _ cq (f32 ?c), H3 : length ?c = 7%nat |- _ =>
rename H into FRM; rename H2 into C0; rename H3 into Lc;
destruct c as [|c00 [|c01 [|c02 [|c03 [|c04 [|c05 [|c06 [|? ?]]]]]]]]; cbn in Lc; try lia; clear Lc end.

bato 0xa9740.
rewrite zb_lxor_ones by lia.
Ltac row MU OF OBT OBC CQ8 CQ0 CQSH i fb cq rq q RQ LQ SL :=
lazymatch type of MU with munch _ ?m0 ?mc =>
lazymatch goal with FRM : frm0 _, MI : mem_inv _ mc, C0 : rw_cells _ mc cq (f32 [?x0; ?x1; ?x2; ?x3; ?x4; ?x5; ?x6]) |- _ =>
let RO := fresh "RO" in
destruct (shift_filt_row mc i MI ltac:(lia)) as (?f0 & ?f1 & ?f2 & ?f3 & ?f4 & ?f5 & ?f6 & RO);
replace (SHIFT_FILT + 28 * i) with fb in RO by reflexivity;
let OBTc := fresh "OBTc" in let OBCc := fresh "OBCc" in
pose proof (aobj_munch bsegs _ m0 mc SHIFT_FILT 84 OBT MU (shfree_of_aobj bsegs _ m0 SHIFT_FILT 84 OF OBT)) as OBTc;
pose proof (aobj_munch bsegs _ m0 mc cq 112 OBC MU (shfree_of_aobj bsegs _ m0 cq 112 OF OBC)) as OBCc;
lazymatch type of RO with ro_cells _ _ _ (f32 [?g0; ?g1; ?g2; ?g3; ?g4; ?g5; ?g6]) =>
call (filt_row i fb cq rq q _ _ _ _ _ _ g0 g1 g2 g3 g4 g5 g6 x0 x1 x2 x3 x4 x5 x6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc);
[ lia | lia | exact LQ | reflexivity | exact FRM | exact MI | exact OBTc | exact OBCc | exact CQ8 | exact CQ0 | exact CQSH | exact C0 | exact RQ | exact RO
| exact SL | lia | lia | ] end;
clear OBTc OBCc FRM; try clear RO; try clear RQ
end end.
Ltac row_names RQ LQ :=
rename MI0 into MI;
match goal with H : frm0 _, H2 : rw_cells _ _ _ (f32 ?c), H3 : length ?c = 7%nat |- _ => rename H into FRM; rename H2 into RQ; rename H3 into LQ end.
row MU OF OBT OBC CQ8 CQ0 CQSH 0 149472 cq (cq + 28) q Q1 L1 F48. row_names RQ1 LQ1.
ato 0xa9740. rewrite fchain_15_front.
row MU OF OBT OBC CQ8 CQ0 CQSH 1 149500 cq (cq + 56) q Q2 L2 F48. row_names RQ2 LQ2.
ato 0xa9740. rewrite fchain_15_front.
row MU OF OBT OBC CQ8 CQ0 CQSH 2 149528 cq (cq + 84) q Q3 L3 F48. row_names RQ3 LQ3.
ato 0xa9878.

chunk_cat C0 RQ1. chunk_cat C0 RQ2. chunk_cat C0 RQ3. rewrite <- !f32_app in C0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (amax cq mc); [ clear - CQ0' Q63 CQLO QLO; lia | | exact FRM | exact MI | exact C0] | ] end.
{ rewrite !length_app. cbn [length]. lia. }
clear FRM. intros ms' (mi & mj & t0' & t1' & t4' & a3' & a6' & a7' & G2 & fc2 & -> & FRM & Hmi & Hmj).

ato 0xa996c.
set (e30 := Z.shiftr (Z.shiftl ((mi + -1) mod 18446744073709551616) 32 mod 18446744073709551616) 30) in *.
set (e27 := Z.shiftr (Z.shiftl ((mi + -1) mod 18446744073709551616) 32 mod 18446744073709551616) 27) in *.
set (fb := 149472 + (e27 - e30)) in *.
set (t5w := Z_to_bv 64 (Z.lxor (fb mod 18446744073709551616) 18446744073709551615)) in *.
set (t4w := Z_to_bv 64 fb) in *.
set (t3w := Z_to_bv 64 (e27 - e30)) in *.
assert (HFB : 1 <= mi -> fb = SHIFT_FILT + 28 * (mi - 1) /\ t3w = Z_to_bv 64 (28 * (mi - 1)) /\ t4w = Z_to_bv 64 fb /\ t5w = Z_to_bv 64 (18446744073709551615 - fb)).
{ intros M1. assert (E : e27 - e30 = 28 * (mi - 1)) by (subst e27 e30; assert (mi = 1 \/ mi = 2 \/ mi = 3) as [-> | [-> | ->]] by lia; reflexivity).
assert (Efb : fb = SHIFT_FILT + 28 * (mi - 1)) by (subst fb; rewrite E; unfold SHIFT_FILT; lia).
split; [exact Efb|]. split; [subst t3w; rewrite E; reflexivity|]. split; [reflexivity|].
subst t5w. rewrite (Z.mod_small fb) by (rewrite Efb; unfold SHIFT_FILT; lia). rewrite zb_lxor_ones by (rewrite Efb; unfold SHIFT_FILT; lia). reflexivity. }
clearbody t3w t4w t5w fb e27 e30.
rewrite !Zminus_mod_idemp_l.
rewrite (swrap32_mod64_add (p - mj) 3) by lia.
replace (p mod 18446744073709551616 - mj) with (p mod 18446744073709551616 + - mj) by lia.
rewrite (swrap32_mod64_add p (- mj)) by lia.
replace (p + - mj) with (p - mj) by lia.
rewrite Z.lxor_nilpotent. replace (0 <? 0) with false by reflexivity.
rewrite (lxor_sign_mod (p - mj + 3)), (lxor_sign_mod (p - mj)) by lia.
replace (p - mj + 3 + 9223372036854775808 <? p - mj + 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite zb_lxor_ones by lia. rewrite swrap32_small by lia. rewrite Z.add_0_r. cbn [Z.b2z].
change (Z_to_bv 64 149472) with (Z_to_bv 64 SHIFT_FILT).
assert (SEP : IP + 320 <= EB \/ EB + 2000 <= IP) by lia.
assert (IPI : IMG_TOP_B <= IP) by (unfold IMG_TOP_B; lia).
assert (OFc : offsh [(IP, IP + 320)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct ip as [|i0 iprest]; [cbn in LIP; lia|]. cbn [length] in LIP.
pose proof (aobj_munch bsegs _ m _ EB 2000 OBE MU (shfree_of_aobj bsegs _ m EB 2000 OF OBE)) as OBEc.
pose proof (aobj_munch bsegs _ m _ IP 320 OBI MU (shfree_of_aobj bsegs _ m IP 320 OF OBI)) as OBIc.
pose proof (aobj_munch bsegs _ m _ SHIFT_FILT 84 OBT MU (shfree_of_aobj bsegs _ m SHIFT_FILT 84 OF OBT)) as OBTc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(IP, IP + 320)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc IP (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XIP as XC0; replace IP with (IP + 4 * 0) in XC0 at 1 by lia;
call (floop EB eoff p IP mi mj (p - mj + 3) fb q eb _ _ _ _ _ _ _ _ t3w t4w t5w LEB R1 R2 R3 R4 E4 EB0 IP4 Hmi Hmj eq_refl HFB SEP IPI ltac:(lia) Q63 QIP
mc iprest [] i0 0 _ _ _ _ _ _ _ _ mc);
[ reflexivity | lia | exact OBEc | exact OBIc | exact OBTc | exact OFc | exact FRM | exact MI | exact MU0 | exact WM0 | exact XEB | exact XD0 | exact XC0 | exact F56 | ] end.
clear MU0 WM0 XD0 OBEc OBIc OBTc FRM.
apply rw_cells_f32_CB in C0. rewrite !length_app, LQ1, LQ2, LQ3 in C0. cbn [length Nat.add] in C0. change (4 * 28)%nat with 112%nat in C0.
change (Z_to_bv 64 149472) with (Z_to_bv 64 SHIFT_FILT) in F48.
chunk_cat F32 F40. chunk_cat F32 F48. chunk_cat F32 F56. cbn [app] in F32.
apply evt_done. do 31 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. split; [exact C0| exact F32].
Qed.
