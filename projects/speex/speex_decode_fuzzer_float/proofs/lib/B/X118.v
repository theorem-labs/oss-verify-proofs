(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1cg X1dk X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X09e.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yq X0yp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma zbv_mod_add : forall x k, Z_to_bv 64 (x mod 18446744073709551616 + k) = Z_to_bv 64 (x + k).
Proof. intros. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma lxor_sign_nn : forall j, 0 <= j < 2^63 -> Z.lxor j 9223372036854775808 = j + 9223372036854775808.
Proof. intros j Hj. rewrite <- (lxor_sign_mod j) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section L1B.
Variables (EB e32 exc pp GA : Z) (neb : nat).
Variables ra sp gp tp t1 t2 s0 a2 a3 a5 a6 s9 t3 t4 t6 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Hypothesis OBE : aobj bsegs m EB NE.
Hypothesis OB32 : aobj bsegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : EB + NE <= e32 \/ e32 + 160 <= EB.
Hypothesis XE4 : (exc - EB) mod 4 = 0.
Hypothesis EPOS : 0 < EB.
Hypothesis XPOS : 0 < e32.
Hypothesis EXR : exc < 2^62.
Hypothesis PPR : 1 <= pp <= 272.
Hypothesis GAS : e32 + 160 <= GA.
Local Notation W := [(e32, e32 + 160)].

Definition p3B_l1_post (qe jt : Z) (nd : nat) (tl : list word) (m0 : mem) : machine_state -> Prop :=
fun ms' => exists a1' s7' s10' s11' F' fc' m' (dn' : list word),
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 s0 (Z_to_bv 64 e32) (Z_to_bv 64 qe) a1' a2 a3 (Z_to_bv 64 1) a5 a6 (Z_to_bv 64 1)
(Z_to_bv 64 exc) (Z_to_bv 64 jt) (Z_to_bv 64 GA) (Z_to_bv 64 0) (Z_to_bv 64 qe) s7' (Z_to_bv 64 SHB) s9 s10' s11' t3 t4 (Z_to_bv 64 pp) t6)
F' (Z_to_bv 64 0xacec0) fc' None m' (seg_rom bsegs)
/\ munch W m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m' /\ frm0 fc'
/\ rw_cells bsegs m' e32 (f32 dn') /\ length dn' = nd /\ rw_cells bsegs m' qe (f32 tl).

Ltac l1_iter j pr :=
let HINT := fresh "HINT" in
pose proof (OB32 : sh_cur _) as HINT;
bato 0xace08; astep; chk_merge OB32 4; clear HINT;
bato 0xace1c; rewrite !swrap32_mod64_add by lia; rewrite !Z.add_0_r;
bato 0xace24; rewrite (addr_shift2 exc (j - pp) pr) by lia;
bato 0xace3c; rewrite (lxor_sign_mod (j - pp)) by lia; rewrite (ptr_sgn_guard exc (j - pp) pr) by lia;
pose proof (OBE : sh_cur _) as HINT;
bato 0xace60; astep; chk_merge OBE 4; clear HINT;
pose proof (OB32 : sh_cur _) as HINT;
bato 0xace6c; astep; chk_merge OB32 4; clear HINT;
bato 0xace88; bnorm; astep.

Lemma p3B_l1 : forall (proc dn tl wrest : list word) (y x g : word) (j cnt pr q qe jt : Z) (nd : nat) (a1v s7v s10v s11v : word) F0 fc m1,
q = e32 + 4 * j -> j = Z.of_nat (length dn) -> cnt = Z.of_nat (S (length proc)) -> jt = j + cnt -> qe = e32 + 4 * jt -> nd = (length dn + S (length proc))%nat ->
pr = exc + 4 * (j - pp) -> Z.of_nat (length dn) + Z.of_nat (S (length proc)) + Z.of_nat (length tl) = 40 -> (length proc <= length wrest)%nat ->
EB <= pr -> pr + 4 * Z.of_nat (S (length wrest)) <= EB + NE -> jt <= pp ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 pr (f32 (x :: wrest)) -> rw_cells bsegs m1 e32 (f32 dn) -> rw_cells bsegs m1 q (f32 (y :: proc ++ tl)) -> rw_cells bsegs m1 GA [C4 g] ->
evt bsegs (p3B_l1_post qe jt nd tl m)
(MS (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 s0 (Z_to_bv 64 e32) (Z_to_bv 64 q) a1v a2 a3 (Z_to_bv 64 1) a5 a6 (Z_to_bv 64 1)
(Z_to_bv 64 exc) (Z_to_bv 64 j) (Z_to_bv 64 GA) (Z_to_bv 64 cnt) (Z_to_bv 64 q) s7v (Z_to_bv 64 SHB) s9 s10v s11v t3 t4 (Z_to_bv 64 pp) t6)
F0 (Z_to_bv 64 0xacde8) fc None m1 (seg_rom bsegs)).
Proof using OBE OB32 E4 X4 EX XE4 EPOS XPOS EXR PPR GAS.
induction proc as [|y' proc IH]; intros dn tl wrest y x g j cnt pr q qe jt nd a1v s7v s10v s11v F0 fc m1 Eq Ej Ec Ejt Eqe End Epr HL HW P1 P2 HJT FRM MU OF WM MI WIN D32 R32 GC;
pose proof OBE as (OE0 & OE1 & _); pose proof OB32 as (O320 & O321 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ R32) as B32; rewrite cells_size_f32 in B32; cbn [length] in *;
rewrite f32_cons in WIN; rewrite f32_cons in R32;
assert (PR4 : pr mod 4 = 0) by (clear - Epr XE4 E4; subst pr; Z.div_mod_to_equations; lia);
assert (Q4 : q mod 4 = 0) by (clear - Eq X4; subst q; Z.div_mod_to_equations; lia).
- chunk_uncons WIN as X1. chunk_uncons R32 as Y1.
l1_iter j pr. sh_if. bato 0xacec0.
chunk_snoc D32 Y1. f32_norm D32.
replace (q + 4) with qe in * by lia. replace (j + 1) with jt by lia. replace (cnt + -1) with 0 by lia.
unfold p3B_l1_post. finish.
+ exact D32.
+ rewrite length_app. cbn [length]. lia.
- destruct wrest as [|x' wrest']; [cbn [length] in HW; lia|]. cbn [length] in *.
chunk_uncons WIN as X1. chunk_uncons R32 as Y1. cbn [app] in R32.
l1_iter j pr. cbn [length]. sh_if.
chunk_snoc D32 Y1. f32_norm D32.
lazymatch type of D32 with rw_cells _ _ _ (f32 (dn ++ [?v])) =>
eapply (IH (dn ++ [v]) tl wrest' y' x' g (j + 1) (cnt + -1) (pr + 4) (q + 4) qe jt nd); try eassumption end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End L1B.

Section L2B.
Variables (EB e32 exc pp pitch GA : Z) (neb : nat).
Variables ra sp gp tp t1 t2 s0 a2 a3 a5 a6 s10 s11 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Hypothesis OBE : aobj bsegs m EB NE.
Hypothesis OB32 : aobj bsegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : EB + NE <= e32 \/ e32 + 160 <= EB.
Hypothesis XE4 : (exc - EB) mod 4 = 0.
Hypothesis EPOS : 0 < EB.
Hypothesis XPOS : 0 < e32.
Hypothesis EXR : exc < 2^62.
Hypothesis PPR : 1 <= pp <= 272.
Hypothesis PITR : 17 <= pitch <= 271.
Hypothesis GAS : e32 + 160 <= GA.
Local Notation W := [(e32, e32 + 160)].

Definition p3B_l2_post (qe jt : Z) (nd : nat) (tl : list word) (m0 : mem) : machine_state -> Prop :=
fun ms' => exists a1' s5' s6' s7' F' fc' m' (dn' : list word),
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 s0 (Z_to_bv 64 e32) (Z_to_bv 64 qe) a1' a2 a3 (Z_to_bv 64 1) a5 a6 (Z_to_bv 64 1)
(Z_to_bv 64 exc) (Z_to_bv 64 jt) (Z_to_bv 64 qe) s5' s6' s7' (Z_to_bv 64 SHB) (Z_to_bv 64 pitch) s10 s11
(Z_to_bv 64 jt) (Z_to_bv 64 jt) (Z_to_bv 64 pp) (Z_to_bv 64 GA))
F' (Z_to_bv 64 0xacfe8) fc' None m' (seg_rom bsegs)
/\ munch W m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m' /\ frm0 fc'
/\ rw_cells bsegs m' e32 (f32 dn') /\ length dn' = nd /\ rw_cells bsegs m' qe (f32 tl).

Ltac l2_iter j pr :=
let HINT := fresh "HINT" in
bato 0xacf0c; rewrite (lxor_sign_nn j) by lia; rewrite (ptr_sgn_guard e32 j (e32 + 4 * j)) by lia;
pose proof (OB32 : sh_cur _) as HINT;
bato 0xacf20; astep; chk_merge OB32 4; clear HINT;
bato 0xacf3c; rewrite !swrap32_mod64_add by lia; rewrite !Z.add_0_r;
replace ((j - pp) mod 18446744073709551616 - pitch) with ((j - pp) mod 18446744073709551616 + - pitch) by lia;
rewrite !swrap32_mod64_add by lia; rewrite !zbv_mod_add;
bato 0xacf48; rewrite !swrap32_mod64_add by lia; rewrite !Z.add_0_r;
bato 0xacf4c; rewrite (addr_shift2 exc (j - pp + - pitch) pr) by lia;
bato 0xacf64; rewrite (lxor_sign_mod (j - pp + - pitch)) by lia; rewrite (ptr_sgn_guard exc (j - pp + - pitch) pr) by lia;
pose proof (OBE : sh_cur _) as HINT;
bato 0xacf88; astep; chk_merge OBE 4; clear HINT;
pose proof (OB32 : sh_cur _) as HINT;
bato 0xacf94; astep; chk_merge OB32 4; clear HINT;
bato 0xacfb0; bnorm; astep.

Lemma p3B_l2 : forall (proc dn tl wrest : list word) (y x g : word) (j pr q qe jt : Z) (nd : nat) (a1v s5v s6v s7v : word) F0 fc m1,
q = e32 + 4 * j -> j = Z.of_nat (length dn) -> jt = j + Z.of_nat (S (length proc)) -> qe = e32 + 4 * jt -> nd = (length dn + S (length proc))%nat ->
pr = exc + 4 * (j - pp - pitch) -> Z.of_nat (length dn) + Z.of_nat (S (length proc)) + Z.of_nat (length tl) = 40 -> (length proc <= length wrest)%nat ->
EB <= pr -> pr + 4 * Z.of_nat (S (length wrest)) <= EB + NE -> jt <= pp + pitch ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 pr (f32 (x :: wrest)) -> rw_cells bsegs m1 e32 (f32 dn) -> rw_cells bsegs m1 q (f32 (y :: proc ++ tl)) -> rw_cells bsegs m1 GA [C4 g] ->
evt bsegs (p3B_l2_post qe jt nd tl m)
(MS (mkR ra sp gp tp (Z_to_bv 64 1) t1 t2 s0 (Z_to_bv 64 e32) (Z_to_bv 64 q) a1v a2 a3 (Z_to_bv 64 1) a5 a6 (Z_to_bv 64 1)
(Z_to_bv 64 exc) (Z_to_bv 64 jt) (Z_to_bv 64 q) s5v s6v s7v (Z_to_bv 64 SHB) (Z_to_bv 64 pitch) s10 s11
(Z_to_bv 64 j) (Z_to_bv 64 j) (Z_to_bv 64 pp) (Z_to_bv 64 GA))
F0 (Z_to_bv 64 0xacef4) fc None m1 (seg_rom bsegs)).
Proof using OBE OB32 E4 X4 EX XE4 EPOS XPOS EXR PPR PITR GAS.
induction proc as [|y' proc IH]; intros dn tl wrest y x g j pr q qe jt nd a1v s5v s6v s7v F0 fc m1 Eq Ej Ejt Eqe End Epr HL HW P1 P2 HJT FRM MU OF WM MI WIN D32 R32 GC;
pose proof OBE as (OE0 & OE1 & _); pose proof OB32 as (O320 & O321 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ R32) as B32; rewrite cells_size_f32 in B32; cbn [length] in *;
rewrite f32_cons in WIN; rewrite f32_cons in R32;
assert (PR4 : pr mod 4 = 0) by (clear - Epr XE4 E4; subst pr; Z.div_mod_to_equations; lia);
assert (Q4 : q mod 4 = 0) by (clear - Eq X4; subst q; Z.div_mod_to_equations; lia).
- chunk_uncons WIN as X1. chunk_uncons R32 as Y1. subst q.
l2_iter j pr. sh_if. bato 0xacfe8.
chunk_snoc D32 Y1. f32_norm D32.
replace (e32 + 4 * j + 4) with qe in * by lia. replace (j + 1) with jt by lia.
unfold p3B_l2_post. finish.
+ exact D32.
+ rewrite length_app. cbn [length]. lia.
- destruct wrest as [|x' wrest']; [cbn [length] in HW; lia|]. cbn [length] in *.
chunk_uncons WIN as X1. chunk_uncons R32 as Y1. cbn [app] in R32. subst q.
l2_iter j pr. cbn [length]. sh_if.
chunk_snoc D32 Y1. f32_norm D32.
replace (e32 + 4 * j + 4) with (e32 + 4 * (j + 1)) in * by lia.
lazymatch type of D32 with rw_cells _ _ _ (f32 (dn ++ [?v])) =>
eapply (IH (dn ++ [v]) tl wrest' y' x' g (j + 1) (pr + 4) (e32 + 4 * (j + 1)) qe jt nd); try eassumption end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End L2B.

Lemma f32_winP : forall m B (l : list word) (n : Z) (cnt : nat), rw_cells bsegs m B (f32 l) ->
0 <= n -> n + Z.of_nat cnt <= Z.of_nat (length l) ->
exists w, length w = cnt /\ rw_cells bsegs m (B + 4 * n) (f32 w).
Proof.
intros m B l n cnt X Hn Hn2.
pose proof (rw_cells_f32_mid bsegs m B l (Z.to_nat n) cnt X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
exists (firstn cnt (skipn (Z.to_nat n) l)). split; [| exact W].
rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia.
Qed.

Section ITERB.
Variables (EB e0 e32 usp lo pitch : Z) (neb : nat).
Variables ra gp tp : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Local Notation exc := (EB + 4 * e0).
Hypothesis OBE : aobj bsegs m EB NE.
Hypothesis OB32 : aobj bsegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : hidp (EB + NE <= e32 \/ e32 + 160 <= EB).
Hypothesis XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32).
Hypothesis XAP : e32 + 160 <= lo.
Hypothesis LO : lo <= usp - 144.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^62.
Hypothesis E0a : 290 <= e0.
Hypothesis E0b : e0 + 40 <= Z.of_nat neb.
Hypothesis PIT : 17 <= pitch <= 271.
Hypothesis EPOS : 0 < EB.
Hypothesis XPOS : 0 < e32.
Local Notation W := [(e32, e32 + 160)].

Definition p3B_iter_R (i : Z) (a0 a1 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (usp + -144)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 (pitch + 1 - i)) (Z_to_bv 64 40) (Z_to_bv 64 e32) a0 a1
(Z_to_bv 64 (pitch + 1)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (usp + -124)) (Z_to_bv 64 1)
(Z_to_bv 64 exc) s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) (Z_to_bv 64 pitch) s10 s11 t3 t4 t5 t6.

Local Ltac p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s PPV TMP1 GAv g GCx :=
bato 0xacde8;
let w := fresh "w" in let Lw := fresh "Lw" in let WIN := fresh "WIN" in let x := fresh "x" in let wrest := fresh "wrest" in
let y := fresh "y" in let rest32 := fresh "rest32" in let LP := fresh "LP" in let LT := fresh "LT" in
let proc := fresh "proc" in let tl := fresh "tl" in let EX' := fresh "EX'" in let OBE1 := fresh "OBE1" in let OB321 := fresh "OB321" in
destruct (f32_winP m1 EB eb (e0 - PPV) (Z.to_nat TMP1) XE ltac:(lia) ltac:(lia)) as (w & Lw & WIN);
destruct w as [|x wrest]; [cbn [length] in Lw; lia|]; cbn [length] in Lw;
replace (EB + 4 * (e0 - PPV)) with (exc + 4 * (0 - PPV)) in WIN by lia;
destruct e32s as [|y rest32]; [cbn [length] in L32; lia|]; cbn [length] in L32;
rewrite <- (firstn_skipn (Z.to_nat (TMP1 - 1)) rest32) in X32;
assert (LP : Z.of_nat (length (firstn (Z.to_nat (TMP1 - 1)) rest32)) = TMP1 - 1) by (rewrite firstn_length_le; lia);
assert (LT : Z.of_nat (length (skipn (Z.to_nat (TMP1 - 1)) rest32)) = 40 - TMP1) by (rewrite length_skipn; lia);
set (proc := firstn (Z.to_nat (TMP1 - 1)) rest32) in *; set (tl := skipn (Z.to_nat (TMP1 - 1)) rest32) in *; clearbody proc tl;
pose proof (aobj_munch bsegs W m m1 EB NE OBE MU (shfree_of_aobj bsegs W m EB NE OF OBE)) as OBE1;
pose proof (aobj_munch bsegs W m m1 e32 160 OB32 MU (shfree_of_aobj bsegs W m e32 160 OF OB32)) as OB321;
rewrite f32_cons in X32;
pose proof (EX : _ \/ _) as EX';
eapply evt_cut; [ eapply (p3B_l1 EB e32 exc PPV GAv neb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 OBE1 OB321 E4 X4 EX' XE4 EPOS XPOS ltac:(lia) ltac:(lia) ltac:(lia)
proc [] tl wrest y x g 0 TMP1 (exc + 4 * (0 - PPV)) e32 (e32 + 4 * TMP1) TMP1 (Z.to_nat TMP1))
| clear WIN X32 GCx; post_call bsegs m1; clear EX' ];
try (cbn [length] in *; lia); try eassumption;
try (rewrite f32_nil; apply rw_cells_nil; lia);
try (apply munch_refl); try (apply wmono_refl); try reflexivity.

Local Ltac p3B_skip2 :=
bato 0xacfe8;
cbn [length Nat.add] in *;
match goal with D : rw_cells bsegs ?mm e32 (f32 ?dn'), T : rw_cells bsegs ?mm _ (f32 ?tl), LD : length ?dn' = _ |- _ =>
chunk_cat D T; rewrite <- f32_app in D; finish; [ exact D | rewrite length_app; lia ] end.

Local Ltac p3B_l2cut MU OF XE XE4 eb PPV TMP3 GAv g GCx :=
bato 0xacef4;
replace (e32 + Z.shiftl PPV 2) with (e32 + 4 * PPV) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with D : rw_cells bsegs mc e32 (f32 ?dn), T : rw_cells bsegs mc (e32 + 4 * PPV) (f32 ?tl), LD : length ?dn = _ |- _ =>
let w2 := fresh "w" in let Lw2 := fresh "Lw" in let WIN2 := fresh "WIN" in let xq := fresh "x" in let wrest2 := fresh "wrest" in
let yq := fresh "y" in let rest2 := fresh "rest" in let LP2 := fresh "LP" in let LT2 := fresh "LT" in
let proc2 := fresh "proc" in let tl2 := fresh "tl" in let EX2 := fresh "EX'" in let OBE2 := fresh "OBE2" in let OB322 := fresh "OB322" in
destruct (f32_winP mc EB eb (e0 - pitch) (Z.to_nat (TMP3 - PPV)) XE ltac:(lia) ltac:(lia)) as (w2 & Lw2 & WIN2);
destruct w2 as [|xq wrest2]; [cbn [length] in Lw2; lia|]; cbn [length] in Lw2;
replace (EB + 4 * (e0 - pitch)) with (exc + 4 * (PPV - PPV - pitch)) in WIN2 by lia;
destruct tl as [|yq rest2]; [cbn [length] in *; lia|];
rewrite <- (firstn_skipn (Z.to_nat (TMP3 - PPV - 1)) rest2) in T;
assert (LP2 : Z.of_nat (length (firstn (Z.to_nat (TMP3 - PPV - 1)) rest2)) = TMP3 - PPV - 1) by (rewrite firstn_length_le; cbn [length] in *; lia);
assert (LT2 : Z.of_nat (length (skipn (Z.to_nat (TMP3 - PPV - 1)) rest2)) = 40 - TMP3) by (rewrite length_skipn; cbn [length] in *; lia);
set (proc2 := firstn (Z.to_nat (TMP3 - PPV - 1)) rest2) in *; set (tl2 := skipn (Z.to_nat (TMP3 - PPV - 1)) rest2) in *; clearbody proc2 tl2;
rewrite f32_cons in T;
pose proof (aobj_munch bsegs W m mc EB NE OBE MU (shfree_of_aobj bsegs W m EB NE OF OBE)) as OBE2;
pose proof (aobj_munch bsegs W m mc e32 160 OB32 MU (shfree_of_aobj bsegs W m e32 160 OF OB32)) as OB322;
pose proof (EX : _ \/ _) as EX2;
eapply evt_cut; [ eapply (p3B_l2 EB e32 exc PPV pitch GAv neb _ _ _ _ _ _ _ _ _ _ _ _ _ mc OBE2 OB322 E4 X4 EX2 XE4 EPOS XPOS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
proc2 dn tl2 wrest2 yq xq g PPV (exc + 4 * (PPV - PPV - pitch)) (e32 + 4 * PPV) (e32 + 4 * TMP3) TMP3 (Z.to_nat TMP3))
| clear WIN2 T D GCx; post_call bsegs mc; clear EX2 ]
end end;
try reflexivity; try (cbn [length] in *; lia); try eassumption;
try (apply munch_refl); try (apply wmono_refl).
Local Ltac p3B_fin :=
cbn [length Nat.add] in *;
match goal with D : rw_cells bsegs ?mm e32 (f32 ?dn'), T : rw_cells bsegs ?mm _ (f32 ?tl), LD : length ?dn' = _ |- _ =>
chunk_cat D T; rewrite <- f32_app in D; finish; [ exact D | rewrite length_app; lia ] end.

Lemma p3B_iter : forall (i : Z) (eb e32s : list word) (j0 j16 : list byte) (cpv g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(a0 a1 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F0 fc m1,
0 <= i <= 2 -> length eb = neb -> length e32s = 40%nat ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 (usp + -144) [CB 8 j0; C8 cpv; CB 4 j16; C4 g0; C4 g1; C4 g2; C8 cfs0; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3;
C8 c2; C8 c1; C8 c0; C8 cra] ->
rw_cells bsegs m1 EB (f32 eb) -> rw_cells bsegs m1 e32 (f32 e32s) ->
evt bsegs (fun ms' => exists a0' a1' s3' s4' s5' s6' s7' s10' s11' t3' t4' t5' t6' F' fc' m' (e32' : list word),
ms' = MS (p3B_iter_R i a0' a1' s3' s4' s5' s6' s7' s10' s11' t3' t4' t5' t6') F' (Z_to_bv 64 0xacfe8) fc' None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ frm0 fc'
/\ rw_cells bsegs m' e32 (f32 e32') /\ length e32' = 40%nat)
(MS (p3B_iter_R i a0 a1 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6) F0 (Z_to_bv 64 0xacd94) fc None m1 (seg_rom bsegs)).
Proof using OBE OB32 E4 X4 EX XSH XAP LO LOS SPH E0a E0b PIT EPOS XPOS.
intros i eb e32s j0 j16 cpv g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra a0 a1 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F0 fc m1 Hi LE L32 FRM MU OF WM MI FR XE X32.
pose proof OBE as (OE0 & OE1 & _). pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
unfold p3B_iter_R in *.
assert (XE4 : (exc - EB) mod 4 = 0) by (replace (exc - EB) with (e0 * 4) by lia; apply Z_mod_mult).
assert (GAS0 : e32 + 160 <= usp + -124) by lia.
assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia. clear Hi.
destruct (Z_lt_dec 40 (pitch + 1 - i)) as [PP|PP]; [| destruct (Z.eq_dec (pitch + 1 - i) 40) as [PQ|PQ]; [| destruct (Z_lt_dec 40 (pitch + 1 - i + pitch)) as [PR|PR] ] ].
- pose proof FR as GC. chunk_uncons GC as K0. chunk_uncons GC as K1. chunk_uncons GC as K2. chunk_uncons GC as G0c. chunk_uncons GC as G1c. chunk_uncons GC as G2c.
clear GC K0 K1 K2. replace (usp + -144 + 8 + 8 + 4 + 4 + 4) with (usp + -116) in G2c by lia.
replace (usp + -144 + 8 + 8 + 4 + 4) with (usp + -120) in G1c by lia. replace (usp + -144 + 8 + 8 + 4) with (usp + -124) in G0c by lia.
destruct Hi3 as [ -> | [ -> | -> ] ].
+ clear G0c G1c. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 0) 40 (usp + -116) g2 G2c. p3B_skip2.
+ clear G0c G2c. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 1) 40 (usp + -120) g1 G1c. p3B_skip2.
+ clear G1c G2c. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 2) 40 (usp + -124) g0 G0c. p3B_skip2.
- pose proof FR as GC. chunk_uncons GC as K0. chunk_uncons GC as K1. chunk_uncons GC as K2. chunk_uncons GC as G0c. chunk_uncons GC as G1c. chunk_uncons GC as G2c.
clear GC K0 K1 K2. replace (usp + -144 + 8 + 8 + 4 + 4 + 4) with (usp + -116) in G2c by lia.
replace (usp + -144 + 8 + 8 + 4 + 4) with (usp + -120) in G1c by lia. replace (usp + -144 + 8 + 8 + 4) with (usp + -124) in G0c by lia.
destruct Hi3 as [ -> | [ -> | -> ] ].
+ clear G0c G1c. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 0) (pitch + 1 - 0) (usp + -116) g2 G2c. p3B_skip2.
+ clear G0c G2c. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 1) (pitch + 1 - 1) (usp + -120) g1 G1c. p3B_skip2.
+ clear G1c G2c. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 2) (pitch + 1 - 2) (usp + -124) g0 G0c. p3B_skip2.
- pose proof FR as GC. chunk_uncons GC as K0. chunk_uncons GC as K1. chunk_uncons GC as K2. chunk_uncons GC as G0c. chunk_uncons GC as G1c. chunk_uncons GC as G2c.
clear GC K0 K1 K2. replace (usp + -144 + 8 + 8 + 4 + 4 + 4) with (usp + -116) in G2c by lia.
replace (usp + -144 + 8 + 8 + 4 + 4) with (usp + -120) in G1c by lia. replace (usp + -144 + 8 + 8 + 4) with (usp + -124) in G0c by lia.
destruct Hi3 as [ -> | [ -> | -> ] ].
+ clear G0c G1c. pose proof G2c as G2d. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 0) (pitch + 1 - 0) (usp + -116) g2 G2c. p3B_l2cut MU OF XE XE4 eb (pitch + 1 - 0) 40 (usp + -116) g2 G2d. p3B_fin.
+ clear G0c G2c. pose proof G1c as G1d. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 1) (pitch + 1 - 1) (usp + -120) g1 G1c. p3B_l2cut MU OF XE XE4 eb (pitch + 1 - 1) 40 (usp + -120) g1 G1d. p3B_fin.
+ clear G1c G2c. pose proof G0c as G0d. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 2) (pitch + 1 - 2) (usp + -124) g0 G0c. p3B_l2cut MU OF XE XE4 eb (pitch + 1 - 2) 40 (usp + -124) g0 G0d. p3B_fin.
- pose proof FR as GC. chunk_uncons GC as K0. chunk_uncons GC as K1. chunk_uncons GC as K2. chunk_uncons GC as G0c. chunk_uncons GC as G1c. chunk_uncons GC as G2c.
clear GC K0 K1 K2. replace (usp + -144 + 8 + 8 + 4 + 4 + 4) with (usp + -116) in G2c by lia.
replace (usp + -144 + 8 + 8 + 4 + 4) with (usp + -120) in G1c by lia. replace (usp + -144 + 8 + 8 + 4) with (usp + -124) in G0c by lia.
destruct Hi3 as [ -> | [ -> | -> ] ].
+ clear G0c G1c. pose proof G2c as G2d. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 0) (pitch + 1 - 0) (usp + -116) g2 G2c. p3B_l2cut MU OF XE XE4 eb (pitch + 1 - 0) (pitch + 1 - 0 + pitch) (usp + -116) g2 G2d. p3B_fin.
+ clear G0c G2c. pose proof G1c as G1d. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 1) (pitch + 1 - 1) (usp + -120) g1 G1c. p3B_l2cut MU OF XE XE4 eb (pitch + 1 - 1) (pitch + 1 - 1 + pitch) (usp + -120) g1 G1d. p3B_fin.
+ clear G1c G2c. pose proof G0c as G0d. p3B_l1cut m1 MU OF XE X32 L32 XE4 eb e32s (pitch + 1 - 2) (pitch + 1 - 2) (usp + -124) g0 G0c. p3B_l2cut MU OF XE XE4 eb (pitch + 1 - 2) (pitch + 1 - 2 + pitch) (usp + -124) g0 G0d. p3B_fin.
Qed.
End ITERB.

Tactic Notation "rshapeW" uconstr(T) :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let H := fresh "RS" in
eassert (H : R = T) by (cbv [mkR p3B_iter_R]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ]);
rewrite H; clear H
end.

Section W2B.
Variables (EB e0 e32 usp lo pitch : Z) (neb : nat).
Variables gp tp : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Local Notation exc := (EB + 4 * e0).
Hypothesis OBE : aobj bsegs m EB NE.
Hypothesis OB32 : aobj bsegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : hidp (EB + NE <= e32 \/ e32 + 160 <= EB).
Hypothesis XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32).
Hypothesis XAP : e32 + 160 <= lo.
Hypothesis LO : lo <= usp - 144.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^62.
Hypothesis E0a : 290 <= e0.
Hypothesis E0b : e0 + 40 <= Z.of_nat neb.
Hypothesis PIT : 17 <= pitch <= 271.
Hypothesis EPOS : 0 < EB.
Hypothesis XPOS : 0 < e32.
Local Notation W := [(e32, e32 + 160)].

Local Ltac p3B_it MU OF i :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with XE : rw_cells bsegs mc EB (f32 ?eb), X32 : rw_cells bsegs mc e32 (f32 ?e32s), FR : rw_cells bsegs mc (usp + -144) _ |- _ =>
let EX' := fresh "EX'" in let OBE1 := fresh "OBE1" in let OB321 := fresh "OB321" in
pose proof (aobj_munch bsegs W m mc EB NE OBE MU (shfree_of_aobj bsegs W m EB NE OF OBE)) as OBE1;
pose proof (aobj_munch bsegs W m mc e32 160 OB32 MU (shfree_of_aobj bsegs W m e32 160 OF OB32)) as OB321;
eapply evt_cut; [ eapply (p3B_iter EB e0 e32 usp lo pitch neb _ gp tp mc OBE1 OB321 E4 X4 EX XSH XAP LO LOS SPH E0a E0b PIT EPOS XPOS i eb e32s)
| clear X32; pose proof (EX : _ \/ _) as EX'; post_call bsegs mc; clear EX' ];
clear OBE1 OB321 end end;
try eassumption; try lia; try (apply munch_refl); try (apply wmono_refl); unfold p3B_iter_R.

Lemma p3B_w2 : forall (eb e32s : list word) (j0 j16 : list byte) (cpv g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc,
length eb = neb -> length e32s = 40%nat ->
frm0 fc -> mem_inv bsegs m -> stk bsegs m lo (usp + -144) ->
rw_cells bsegs m (usp + -144) [CB 8 j0; C8 cpv; CB 4 j16; C4 g0; C4 g1; C4 g2; C8 cfs0; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3;
C8 c2; C8 c1; C8 c0; C8 cra] ->
rw_cells bsegs m EB (f32 eb) -> rw_cells bsegs m e32 (f32 e32s) ->
evt bsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' m' (e32' : list word),
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3' t4' t5' t6')
F' (ret_pc cra) fc' None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ frm0 fc'
/\ rw_cells bsegs m' e32 (f32 e32') /\ length e32' = 40%nat)
(MS (mkR ra (Z_to_bv 64 (usp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 exc) s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) (Z_to_bv 64 pitch) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xacd64)) fc None m (seg_rom bsegs)).
Proof using OBE OB32 E4 X4 EX XSH XAP LO LOS SPH E0a E0b PIT EPOS XPOS.
intros eb e32s j0 j16 cpv g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc
LE L32 FRM MI ST FR XE X32.
replace (ret_pc (Z_to_bv 64 0xacd64)) with (Z_to_bv 64 0xacd64) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof OBE as (OE0 & OE1 & _). pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (pose proof (XSH : _ \/ _) as Y1; cbn; unfold SH_LO, SH_HI in *; lia).
bato 0xacd94.
rewrite (land3_al e32 X4). replace (0 <? e32) with true by (symmetry; apply Z.ltb_lt; lia). replace (0 <? exc) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [Z.b2z]. alits.
rshapeW (p3B_iter_R EB e0 e32 usp pitch ra gp tp 0 _ _ _ _ _ _ _ _ _ _ _ _ _). p3B_it MU OF 0.
bato 0xacd94.
bnorm. rshapeW (p3B_iter_R EB e0 e32 usp pitch ra gp tp 1 _ _ _ _ _ _ _ _ _ _ _ _ _). p3B_it MU OF 1.
bato 0xacd94. bnorm. rshapeW (p3B_iter_R EB e0 e32 usp pitch ra gp tp 2 _ _ _ _ _ _ _ _ _ _ _ _ _). p3B_it MU OF 2.
bato 0xad02c.
match goal with FRx : rw_cells bsegs _ (usp + -144) _, STx : stk bsegs _ lo (usp + -144) |- _ =>
release_frame FRx STx usp end.
astep. astep.
finish.
all: eassumption.
Qed.
End W2B.

