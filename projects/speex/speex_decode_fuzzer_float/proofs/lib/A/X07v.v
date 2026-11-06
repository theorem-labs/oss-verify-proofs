(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X07r
X07y X07t X07u X07w X07x.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition ip_body_stmt : Prop :=
forall (q lo EB eoff p IP f cq : Z) (eb ip : list word) (cb : list byte)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
length eb = 500%nat -> 0 <= eoff - p - 6 -> eoff - p <= 414 -> eoff + 80 <= 500 -> 0 <= eoff -> length ip = 80%nat ->
rw_cells asegs m EB (f32 eb) -> rw_cells asegs m IP (f32 ip) -> rw_cells asegs m cq [CB 112 cb] ->
aobj asegs m EB 2000 -> aobj asegs m IP 320 -> aobj asegs m cq 112 -> aobj asegs m SHIFT_FILT 84 ->
EB mod 4 = 0 -> IP mod 4 = 0 -> cq = f + 32 -> f mod 64 = 0 ->
stk asegs m lo q -> lo <= q - 16 -> SH_HI <= lo -> q + 160 < 2^63 ->
EB + 2000 <= lo -> q + 160 <= IP -> IP + 320 <= APP_TOP ->
IMG_TOP <= cq -> cq + 112 <= lo -> (cq + 112 <= SH_LO \/ SH_HI <= cq) -> (cq + 112 <= EB \/ EB + 2000 <= cq) ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s9' s10' s11' t3' t4' t5' t6' : word)
(F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ip' : list word) (cb' : list byte),
ms = MS (mkR ra' (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' s4' s5' s6' s7 (Z_to_bv 64 f) s9' s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 A_ip_epi) fc' None m' (seg_rom asegs)
/\ munch [(q + -16, q); (cq, cq + 112); (IP, IP + 320)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc' /\ stk asegs m' lo q
/\ rw_cells asegs m' IP (f32 ip') /\ length ip' = 80%nat /\ rw_cells asegs m' cq [CB 112 cb'])
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 p) (Z_to_bv 64 IP) (Z_to_bv 64 (EB + 4 * eoff)) (Z_to_bv 64 cq) (Z_to_bv 64 (EB + 4 * eoff - 4 * p)) s7 (Z_to_bv 64 f)
(Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_body) fc None m (seg_rom asegs)).

Lemma corr_rows : forall m cq cb, rw_cells asegs m cq [CB 112 cb] ->
exists r0 r1 r2 r3 : list word, length r0 = 7%nat /\ length r1 = 7%nat /\ length r2 = 7%nat /\ length r3 = 7%nat
/\ rw_cells asegs m cq (f32 r0) /\ rw_cells asegs m (cq + 28) (f32 r1) /\ rw_cells asegs m (cq + 56) (f32 r2) /\ rw_cells asegs m (cq + 84) (f32 r3).
Proof.
intros m cq cb CQ.
destruct (rw_cells_CB_f32 asegs _ _ 28%nat _ CQ) as (c & Lc & CQ').
destruct (f32_split asegs m cq c 7%nat ltac:(lia) CQ') as [Q0 QR]. change (4 * Z.of_nat 7) with 28 in QR.
assert (L1 : length (skipn 7 c) = 21%nat) by (rewrite skipn_length; lia).
destruct (f32_split asegs m (cq + 28) (skipn 7 c) 7%nat ltac:(lia) QR) as [Q1 QR2]. change (4 * Z.of_nat 7) with 28 in QR2.
assert (L2 : length (skipn 7 (skipn 7 c)) = 14%nat) by (rewrite skipn_length; lia).
destruct (f32_split asegs m (cq + 28 + 28) (skipn 7 (skipn 7 c)) 7%nat ltac:(lia) QR2) as [Q2 Q3]. change (4 * Z.of_nat 7) with 28 in Q3.
replace (cq + 28 + 28) with (cq + 56) in * by lia. replace (cq + 56 + 28) with (cq + 84) in * by lia.
exists (firstn 7 c), (firstn 7 (skipn 7 c)), (firstn 7 (skipn 7 (skipn 7 c))), (skipn 7 (skipn 7 (skipn 7 c))).
split; [rewrite firstn_length_le; lia|]. split; [rewrite firstn_length_le; lia|]. split; [rewrite firstn_length_le; lia|].
split; [rewrite skipn_length; lia|].
exact (conj Q0 (conj Q1 (conj Q2 Q3))).
Qed.

Lemma fchain_15_front : forall (a b c z : word) (G : bvmap 5 word),
bvmap_set 12 a (bvmap_set 13 b (bvmap_set 14 c (bvmap_set 15 z G))) = bvmap_set 15 z (bvmap_set 12 a (bvmap_set 13 b (bvmap_set 14 c G))).
Proof. intros. norm_fchain. reflexivity. Qed.

Lemma swrap32_sub_mod64 : forall a x, bv_swrap 32 (a - x mod 18446744073709551616) = bv_swrap 32 (a - x).
Proof.
intros a x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (a - (x - 18446744073709551616 * (x / 18446744073709551616)) + 2147483648)
with ((a - x + 2147483648) + (4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma row_off : forall x, 0 <= x <= 2 ->
Z.shiftr (Z.shiftl (x mod 18446744073709551616) 32 mod 18446744073709551616) 27
- Z.shiftr (Z.shiftl (x mod 18446744073709551616) 32 mod 18446744073709551616) 30 = 28 * x.
Proof. intros x Hx. assert (x = 0 \/ x = 1 \/ x = 2) as [->|[->| ->]] by lia; reflexivity. Qed.

Lemma ip_body : ip_body_stmt.
Proof.
intros q lo EB eoff p IP f cq eb ip cb ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 s11 t3 t4 t5 t6 F fc m
LEB R1 R2 R3 R4 LIP XEB XIP CQ OBE OBI OBC OBT E4 IP4 Hcq F64 ST QLO LOS Q63 EBLO QIP IPT CQ0 CQLO CQSH CQEB CC MI FRM.
unfold A_ip_body, A_ip_epi.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof CQ0 as CQ0'. unfold IMG_TOP in CQ0'. pose proof CQSH as CQSH'. unfold SH_LO, SH_HI in CQSH'.
unfold APP_TOP in *.
pose proof (munch_refl [(q + -16, q); (cq, cq + 112); (IP, IP + 320)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(q + -16, q); (cq, cq + 112); (IP, IP + 320)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (CQ8 : cq mod 8 = 0) by (clear - Hcq F64; Z.div_mod_to_equations; lia).

destruct (corr_rows m cq cb CQ) as (r0 & r1 & r2 & r3 & L0 & L1 & L2 & L3 & Q0 & Q1 & Q2 & Q3); clear CQ.
destruct r0 as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|? ?]]]]]]]]; cbn in L0; try lia. clear L0.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XIP) as BIP; rewrite cells_size_f32, LIP in BIP.

do 3 astep. replace (f + 60) with (cq + 28) by lia.
replace (EB + 4 * eoff - 4 * p + -12) with (EB + 4 * eoff - 4 * p - 12 + 4 * Z.of_nat (@length word [])) by (cbn [length]; lia).
pose proof (aobj_munch asegs _ m _ EB 2000 OBE MU (shfree_of_aobj asegs _ m EB 2000 OF OBE)) as OBEc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(q + -16, q); (cq, cq + 28)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc cq (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
call (corr0_loop EB eoff p IP q lo cq eb mc gp tp s0 s1 s7 (Z_to_bv 64 f) LEB R1 R2 R3 R4 OBEc E4 QLO LOS ltac:(lia) EBLO CQ0 CQLO CQSH CQEB
6%nat [] [y1; y2; y3; y4; y5; y6] cq _ y0);
[ reflexivity | reflexivity | cbn [length]; lia | reflexivity | exact FRM | eassumption | exact MU0 | exact WM0 | exact CC | exact ST | exact XEB | exact XD0 | exact Q0 | ] end.
clear MU0 WM0 XD0 OBEc FRM. rename MI0 into MI.
match goal with H : frm0 _, H2 : rw_cells _ _ cq (f32 ?c), H3 : length ?c = 7%nat |- _ =>
rename H into FRM; rename H2 into C0; rename H3 into Lc;
destruct c as [|c00 [|c01 [|c02 [|c03 [|c04 [|c05 [|c06 [|? ?]]]]]]]]; cbn in Lc; try lia; clear Lc end.

ato 0xa5ad0.
Ltac row MU OF OBT OBC CQ8 CQ0 CQSH i fb cq rq RQ LQ :=
lazymatch type of MU with munch _ ?m0 ?mc =>
lazymatch goal with FRM : frm0 _, MI : mem_inv _ mc, C0 : rw_cells _ mc cq (f32 [?x0; ?x1; ?x2; ?x3; ?x4; ?x5; ?x6]) |- _ =>
let RO := fresh "RO" in
destruct (shift_filt_row mc i MI ltac:(lia)) as (?f0 & ?f1 & ?f2 & ?f3 & ?f4 & ?f5 & ?f6 & RO);
replace (SHIFT_FILT + 28 * i) with fb in RO by reflexivity;
let OBTc := fresh "OBTc" in let OBCc := fresh "OBCc" in
pose proof (aobj_munch asegs _ m0 mc SHIFT_FILT 84 OBT MU (shfree_of_aobj asegs _ m0 SHIFT_FILT 84 OF OBT)) as OBTc;
pose proof (aobj_munch asegs _ m0 mc cq 112 OBC MU (shfree_of_aobj asegs _ m0 cq 112 OF OBC)) as OBCc;
lazymatch type of RO with ro_cells _ _ _ (f32 [?g0; ?g1; ?g2; ?g3; ?g4; ?g5; ?g6]) =>
call (filt_row i fb cq rq _ _ _ _ _ _ _ _ _ _ _ _ g0 g1 g2 g3 g4 g5 g6 x0 x1 x2 x3 x4 x5 x6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc);
[ lia | lia | exact LQ | reflexivity | exact FRM | exact MI | exact OBTc | exact OBCc | exact CQ8 | exact CQ0 | exact CQSH | exact C0 | exact RQ | exact RO | ] end;
clear OBTc OBCc FRM; try clear RO; try clear RQ
end end.
Ltac row_names RQ LQ :=
rename MI0 into MI;
match goal with H : frm0 _, H2 : rw_cells _ _ _ (f32 ?c), H3 : length ?c = 7%nat |- _ => rename H into FRM; rename H2 into RQ; rename H3 into LQ end.
row MU OF OBT OBC CQ8 CQ0 CQSH 0 149472 cq (cq + 28) Q1 L1. row_names RQ1 LQ1.
ato 0xa5ad0. rewrite fchain_15_front.
row MU OF OBT OBC CQ8 CQ0 CQSH 1 149500 cq (cq + 56) Q2 L2. row_names RQ2 LQ2.
ato 0xa5ad0. rewrite fchain_15_front.
row MU OF OBT OBC CQ8 CQ0 CQSH 2 149528 cq (cq + 84) Q3 L3. row_names RQ3 LQ3.
ato 0xa5bd4.

chunk_cat C0 RQ1. chunk_cat C0 RQ2. chunk_cat C0 RQ3. rewrite <- !f32_app in C0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (amax cq mc); [ clear - CQ0' Q63 CQLO QLO; lia | | exact FRM | exact MI | exact C0] | ] end.
{ rewrite !length_app. cbn [length]. lia. }
clear FRM. intros ms' (mi & mj & t0' & t1' & t2' & a3' & a5' & a6' & a7' & G2 & fc2 & -> & FRM & Hmi & Hmj).

ato 0xa5c94.
rewrite swrap32_sub_mod64, (swrap32_small (mj - p)), swrap32_mod64_add by lia.
lazymatch goal with |- context [Z_to_bv 64 (?e + 149472)] => set (a6z := e + 149472) end.
assert (HA6 : 1 <= mi -> a6z = SHIFT_FILT + 28 * (mi - 1)) by (intros; subst a6z; rewrite (row_off (mi + -1)) by lia; unfold SHIFT_FILT; lia).
clearbody a6z.
assert (Hd : mj - p + -3 = mj - p - 3) by lia.
assert (SEP : IP + 320 <= EB \/ EB + 2000 <= IP) by lia.
assert (IPI : IMG_TOP <= IP) by (unfold IMG_TOP; lia).
assert (OFc : offsh [(IP, IP + 320)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct ip as [|i0 iprest]; [cbn in LIP; lia|]. cbn [length] in LIP.
pose proof (aobj_munch asegs _ m _ EB 2000 OBE MU (shfree_of_aobj asegs _ m EB 2000 OF OBE)) as OBEc.
pose proof (aobj_munch asegs _ m _ IP 320 OBI MU (shfree_of_aobj asegs _ m IP 320 OF OBI)) as OBIc.
pose proof (aobj_munch asegs _ m _ SHIFT_FILT 84 OBT MU (shfree_of_aobj asegs _ m SHIFT_FILT 84 OF OBT)) as OBTc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(IP, IP + 320)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc IP (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XIP as XC0; replace IP with (IP + 4 * 0) in XC0 at 1 by lia;
call (floop EB eoff p IP mi mj (mj - p + -3) a6z eb _ _ _ _ _ _ _ _ _ _ _ _ _ _ LEB R1 R2 R3 R4 E4 IP4 Hmi Hmj Hd HA6 SEP IPI mc iprest [] i0 0 (mj - p + -3) _ _ _ _ _ _ _ _ _ mc);
[ reflexivity | lia | lia | exact OBEc | exact OBIc | exact OBTc | exact OFc | exact FRM | exact MI | exact MU0 | exact WM0 | exact XEB | exact XD0 | exact XC0 | ] end.
clear MU0 WM0 XD0 OBEc OBIc OBTc FRM.
apply rw_cells_f32_CB in C0. rewrite !length_app, LQ1, LQ2, LQ3 in C0. cbn [length Nat.add] in C0. change (4 * 28)%nat with 112%nat in C0.
apply evt_done. do 29 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. exact C0.
Qed.
