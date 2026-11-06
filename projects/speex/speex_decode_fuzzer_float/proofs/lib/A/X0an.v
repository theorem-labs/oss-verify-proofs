(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1cg X1dk X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X09e X0am.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma zbv_neg_idx : forall exc idx, Z_to_bv 64 (exc + Z.shiftl (idx mod 18446744073709551616) 2) = Z_to_bv 64 (exc + 4 * idx).
Proof.
intros exc idx. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. change (2^64) with 18446744073709551616.
rewrite Z.add_mod by lia. rewrite (Z.mul_mod (idx mod 18446744073709551616) 4) by lia. rewrite Z.mod_mod by lia.
rewrite <- (Z.mul_mod idx 4) by lia. rewrite <- Z.add_mod by lia. f_equal. lia.
Qed.

Section L1.
Variables (EB e32 : Z) (neb : nat).
Variables ra sp gp tp t0 t1 t2 t3 t4 s0 s1 s2 s7 s8 s10 s11 a2 a3 a4 a5 a6 a7 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Hypothesis OBE : aobj asegs m EB NE.
Hypothesis OB32 : aobj asegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : EB + NE <= e32 \/ e32 + 160 <= EB.
Local Notation W := [(e32, e32 + 160)].

Definition p3_l1_post (qe pe : Z) (nd : nat) (tl : list word) (m0 : mem) : machine_state -> Prop :=
fun ms' => exists s4' s5' s6' F' fc' m' (dn' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 qe) (Z_to_bv 64 pe) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 qe) s4' s5' s6' s7 s8 (Z_to_bv 64 SHB) s10 s11
t3 t4 (Z_to_bv 64 pe) (Z_to_bv 64 0))
F' (Z_to_bv 64 0xa838c) fc' None m' (seg_rom asegs)
/\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ frm0 fc'
/\ rw_cells asegs m' e32 (f32 dn') /\ length dn' = nd /\ rw_cells asegs m' qe (f32 tl).

Lemma p3_l1_ind : forall (proc dn tl wrest : list word) (y x : word) (kz pr q qe pe : Z) (nd : nat) (s4 s5 s6 : word) F0 fc m1,
qe = q + 4 * Z.of_nat (S (length proc)) -> pe = pr + 4 * Z.of_nat (S (length proc)) -> nd = (length dn + S (length proc))%nat ->
kz = Z.of_nat (S (length proc)) -> q = e32 + 4 * Z.of_nat (length dn) ->
Z.of_nat (length dn) + Z.of_nat (S (length proc)) + Z.of_nat (length tl) = 40 -> (length proc <= length wrest)%nat ->
EB <= pr -> pr + 4 * Z.of_nat (S (length wrest)) <= EB + NE -> (pr - EB) mod 4 = 0 ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 pr (f32 (x :: wrest)) -> rw_cells asegs m1 e32 (f32 dn) -> rw_cells asegs m1 q (f32 (y :: proc ++ tl)) ->
evt asegs (p3_l1_post qe pe nd tl m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 pr) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 q) s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11
t3 t4 (Z_to_bv 64 pr) (Z_to_bv 64 kz))
F0 (Z_to_bv 64 0xa8308) fc None m1 (seg_rom asegs)).
Proof.
induction proc as [|y' proc IH]; intros dn tl wrest y x kz pr q qe pe nd s4 s5 s6 F0 fc m1 Eqe Epe End Hkz Eq HL HW P1 P2 P4 FRM MU OF WM MI WIN D32 R32;
pose proof OBE as (OE0 & OE1 & _); pose proof OB32 as (O320 & O321 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ R32) as B32; rewrite cells_size_f32 in B32; cbn [length] in *;
subst kz qe pe nd; rewrite f32_cons in WIN; rewrite f32_cons in R32.
- chunk_uncons WIN as X1. chunk_uncons R32 as Y1.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa8314. astep. chk_merge OB32 4. clear HINT.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa8328. astep. chk_merge OBE 4. clear HINT.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa8334. astep. chk_merge OB32 4. clear HINT.
ato 0xa8354. astep. try sh_if.
ato 0xa838c.
chunk_snoc D32 Y1. f32_norm D32.
unfold p3_l1_post. finish.
+ exact D32.
+ rewrite length_app. cbn [length]. lia.
- destruct wrest as [|x' wrest']; [cbn [length] in HW; lia|]. cbn [length] in *.
chunk_uncons WIN as X1. chunk_uncons R32 as Y1. cbn [app] in R32.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa8314. astep. chk_merge OB32 4. clear HINT.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa8328. astep. chk_merge OBE 4. clear HINT.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa8334. astep. chk_merge OB32 4. clear HINT.
ato 0xa8354. astep. cbn [length]. sh_if.
chunk_snoc D32 Y1. f32_norm D32.
lazymatch type of D32 with rw_cells _ _ _ (f32 (dn ++ [?v])) =>
eapply (IH (dn ++ [v]) tl wrest' y' x' _ (pr + 4) (q + 4)); try eassumption end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
all: try (clear - P4; Z.div_mod_to_equations; lia).
Qed.
End L1.

Lemma swrap32_mod64_small : forall x c, -2^31 <= x + c < 2^31 ->
bv_swrap 32 (x mod 18446744073709551616 + c) = x + c.
Proof.
intros x c H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
replace (x mod 18446744073709551616) with (x - 18446744073709551616 * (x / 18446744073709551616))
by (pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)); lia).
replace (x - 18446744073709551616 * (x / 18446744073709551616) + c + 2147483648)
with ((x + c + 2147483648) + (- 4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Section L2.
Variables (EB e32 exc : Z) (neb : nat).
Variables ra sp gp tp t0 s0 s1 s4 s5 s6 s7 s8 s10 s11 a2 a3 a4 a5 a6 a7 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Hypothesis OBE : aobj asegs m EB NE.
Hypothesis OB32 : aobj asegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis XE4 : (exc - EB) mod 4 = 0.
Hypothesis EX : EB + NE <= e32 \/ e32 + 160 <= EB.
Local Notation W := [(e32, e32 + 160)].

Definition p3_l2_post (qe je idxe jt : Z) (nd : nat) (tl : list word) (m0 : mem) : machine_state -> Prop :=
fun ms' => exists a1' s3' t4' t6' F' fc' m' (dn' : list word),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 je) (Z_to_bv 64 idxe) s0 s1 (Z_to_bv 64 qe) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 exc) s3' s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11
(Z_to_bv 64 qe) t4' (Z_to_bv 64 jt) t6')
F' (Z_to_bv 64 0xa8444) fc' None m' (seg_rom asegs)
/\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ frm0 fc'
/\ rw_cells asegs m' e32 (f32 dn') /\ length dn' = nd /\ rw_cells asegs m' qe (f32 tl).

Lemma p3_l2_ind : forall (proc dn tl wrest : list word) (y x : word) (j jt idx q qe idxe : Z) (nd : nat) (a1 s3 t4 t6 : word) F0 fc m1,
qe = q + 4 * Z.of_nat (S (length proc)) -> idxe = idx + Z.of_nat (S (length proc)) -> nd = (length dn + S (length proc))%nat ->
jt - j = Z.of_nat (S (length proc)) -> 0 <= j -> jt <= 40 -> q = e32 + 4 * Z.of_nat (length dn) ->
Z.of_nat (length dn) + Z.of_nat (S (length proc)) + Z.of_nat (length tl) = 40 -> (length proc <= length wrest)%nat ->
-400 <= idx -> idxe <= 0 ->
EB <= exc + 4 * idx -> exc + 4 * idx + 4 * Z.of_nat (S (length wrest)) <= EB + NE ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 (exc + 4 * idx) (f32 (x :: wrest)) -> rw_cells asegs m1 e32 (f32 dn) -> rw_cells asegs m1 q (f32 (y :: proc ++ tl)) ->
evt asegs (p3_l2_post qe jt idxe jt nd tl m)
(MS (mkR ra sp gp tp t0 (Z_to_bv 64 j) (Z_to_bv 64 idx) s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 exc) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11
(Z_to_bv 64 q) t4 (Z_to_bv 64 jt) t6)
F0 (Z_to_bv 64 0xa83bc) fc None m1 (seg_rom asegs)).
Proof.
induction proc as [|y' proc IH]; intros dn tl wrest y x j jt idx q qe idxe nd a1 s3 t4 t6 F0 fc m1 Eqe Eie End Hj J0 JT Eq HL HW I0 I1 P1 P2 FRM MU OF WM MI WIN D32 R32;
pose proof OBE as (OE0 & OE1 & _); pose proof OB32 as (O320 & O321 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ R32) as B32; rewrite cells_size_f32 in B32; cbn [length] in *;
subst qe idxe nd; rewrite f32_cons in WIN; rewrite f32_cons in R32.
- chunk_uncons WIN as X1. chunk_uncons R32 as Y1.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa83c8. astep. chk_merge OB32 4. clear HINT.
ato 0xa83d4. rewrite zbv_neg_idx.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa83e4. astep. chk_merge OBE 4. clear HINT.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa83f0. astep. chk_merge OB32 4. clear HINT.
ato 0xa840c. astep. try sh_if.
ato 0xa8444. rewrite swrap32_mod64_small by lia.
chunk_snoc D32 Y1. f32_norm D32.
unfold p3_l2_post.
replace (j + 1) with jt by lia.
finish.
+ exact D32.
+ rewrite length_app. cbn [length]. lia.
- destruct wrest as [|x' wrest']; [cbn [length] in HW; lia|]. cbn [length] in *.
chunk_uncons WIN as X1. chunk_uncons R32 as Y1. cbn [app] in R32.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa83c8. astep. chk_merge OB32 4. clear HINT.
ato 0xa83d4. rewrite zbv_neg_idx.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa83e4. astep. chk_merge OBE 4. clear HINT.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa83f0. astep. chk_merge OB32 4. clear HINT.
ato 0xa840c. astep. cbn [length]. sh_if.
rewrite swrap32_mod64_small by lia.
chunk_snoc D32 Y1. f32_norm D32.
replace (exc + 4 * idx + 4) with (exc + 4 * (idx + 1)) in WIN by lia.
lazymatch type of D32 with rw_cells _ _ _ (f32 (dn ++ [?v])) =>
eapply (IH (dn ++ [v]) tl wrest' y' x' (j + 1) jt (idx + 1) (q + 4)); try eassumption end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End L2.

Section ITER.
Variables (EB e0 e32 usp lo pitch : Z) (neb : nat).
Variables ra gp tp s8 s10 s11 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Local Notation exc := (EB + 4 * e0).
Hypothesis OBE : aobj asegs m EB NE.
Hypothesis OB32 : aobj asegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : hidp (EB + NE <= e32 \/ e32 + 160 <= EB).
Hypothesis XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32).
Hypothesis XAP : e32 + 160 <= lo.
Hypothesis LO : lo <= usp - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis E0a : 290 <= e0.
Hypothesis E0b : e0 + 40 <= Z.of_nat neb.
Hypothesis PIT : 17 <= pitch <= 271.
Local Notation W := [(e32, e32 + 160)].

Definition p3_iter_R (i : Z) (t1 t2 a0 a1 s3 s4 s5 s6 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (usp + -128)) gp tp (Z_to_bv 64 (pitch + 1 - i)) t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 (pitch + 1)) (Z_to_bv 64 2)
(Z_to_bv 64 (usp + -124)) (Z_to_bv 64 (i - (2 * pitch + 1))) (Z_to_bv 64 3) (Z_to_bv 64 exc) s3 s4 s5 s6 (Z_to_bv 64 pitch) s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6.

Local Ltac p3_l1cut m1 MU OF XE X32 L32 eb e32s PPV TMP1 :=
ato 0xa82b4; astep; sh_if; ato 0xa82c0; astep; sh_if; ato 0xa82d0; rewrite ?swrap32_small by lia; astep; sh_if; ato 0xa82dc; astep; try sh_if;
ato 0xa8308;
pose proof (aobj_munch asegs W m m1 EB NE OBE MU (shfree_of_aobj asegs W m EB NE OF OBE)) as OBE1;
pose proof (aobj_munch asegs W m m1 e32 160 OB32 MU (shfree_of_aobj asegs W m e32 160 OF OB32)) as OB321;
let XMR := fresh "XMR" in let MR := fresh "MR" in let LMR := fresh "LMR" in let x := fresh "x" in let wrest := fresh "wrest" in
let y := fresh "y" in let rest32 := fresh "rest32" in let n1 := fresh "n1" in let LP := fresh "LP" in let LT := fresh "LT" in
let proc := fresh "proc" in let tl := fresh "tl" in let EX' := fresh "EX'" in
destruct (f32_split asegs m1 EB eb (Z.to_nat (e0 - PPV)) ltac:(lia) XE) as [_ XMR];
rewrite Z2Nat.id in XMR by lia;
set (MR := skipn (Z.to_nat (e0 - PPV)) eb) in *;
assert (LMR : Z.of_nat (length MR) = Z.of_nat neb - (e0 - PPV)) by (unfold MR; rewrite length_skipn; lia);
clearbody MR; destruct MR as [|x wrest]; [cbn [length] in LMR; lia|];
destruct e32s as [|y rest32]; [cbn [length] in L32; lia|]; cbn [length] in L32;
set (n1 := Z.to_nat (TMP1 - 1));
rewrite <- (firstn_skipn n1 rest32) in X32;
assert (LP : Z.of_nat (length (firstn n1 rest32)) = TMP1 - 1) by (rewrite firstn_length_le; lia);
assert (LT : Z.of_nat (length (skipn n1 rest32)) = 40 - TMP1) by (rewrite length_skipn; lia);
set (proc := firstn n1 rest32) in *; set (tl := skipn n1 rest32) in *; clearbody proc tl; clear n1;
lazymatch goal with |- context [Z_to_bv 64 (exc - ?sh mod 18446744073709551616)] =>
replace (Z_to_bv 64 (exc - sh mod 18446744073709551616)) with (Z_to_bv 64 (EB + 4 * (e0 - PPV)))
by (f_equal; rewrite Z.shiftl_mul_pow2, Z.mod_small by lia; lia) end;
(eapply evt_cut; [ eapply (p3_l1_ind EB e32 neb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 OBE1 OB321 E4 X4 EX proc [] tl wrest y x _ _ _ _ _ _)
| clear XMR X32; pose proof (EX : _ \/ _) as EX'; post_call asegs m1; clear EX' ]);
try (cbn [length] in *; lia); try eassumption;
try (rewrite f32_nil; apply rw_cells_nil; lia);
try (apply munch_refl); try (apply wmono_refl); try reflexivity.

Local Ltac p3_skip2 :=
ato 0xa8394; rewrite ?swrap32_small by lia; astep; sh_if; ato 0xa839c; astep; sh_if;
cbn [length Nat.add] in *;
match goal with D : rw_cells asegs ?mm e32 (f32 ?dn'), T : rw_cells asegs ?mm _ (f32 ?tl), LD : length ?dn' = _ |- _ =>
chunk_cat D T; rewrite <- f32_app in D; finish; [ exact D | rewrite length_app; lia ] end.

Local Ltac p3_l2cut MU OF XE XE4 eb PPV TMP3 :=
ato 0xa8394; rewrite ?swrap32_small by lia; astep; sh_if; ato 0xa839c; astep; sh_if; ato 0xa83bc;
cbn [length Nat.add] in *;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with D : rw_cells asegs mc e32 (f32 ?dn), T : rw_cells asegs mc (e32 + ?qo) (f32 ?tl), LD : length ?dn = _ |- _ =>
let qa := constr:(e32 + qo) in let OBE2 := fresh "OBE2" in let OB322 := fresh "OB322" in
let XMR := fresh "XMR" in let MR := fresh "MR" in let LMR := fresh "LMR" in let x := fresh "x" in let wrest := fresh "wrest" in
let y := fresh "y" in let rest := fresh "rest" in let n2 := fresh "n2" in let LP := fresh "LP" in let LT2 := fresh "LT" in
let proc := fresh "proc" in let tl2 := fresh "tl" in let EX' := fresh "EX'" in
pose proof (aobj_munch asegs W m mc EB NE OBE MU (shfree_of_aobj asegs W m EB NE OF OBE)) as OBE2;
pose proof (aobj_munch asegs W m mc e32 160 OB32 MU (shfree_of_aobj asegs W m e32 160 OF OB32)) as OB322;
destruct (f32_split asegs mc EB eb (Z.to_nat (e0 - pitch)) ltac:(lia) XE) as [_ XMR];
set (MR := skipn (Z.to_nat (e0 - pitch)) eb) in *;
assert (LMR : Z.of_nat (length MR) = Z.of_nat neb - (e0 - pitch)) by (unfold MR; rewrite length_skipn; lia);
clearbody MR; destruct MR as [|x wrest]; [cbn [length] in LMR; lia|];
replace (EB + 4 * Z.of_nat (Z.to_nat (e0 - pitch))) with (exc + 4 * (- pitch)) in XMR by lia;
destruct tl as [|y rest]; [cbn [length] in *; lia|];
set (n2 := Z.to_nat (TMP3 - PPV - 1));
rewrite <- (firstn_skipn n2 rest) in T;
assert (LP : Z.of_nat (length (firstn n2 rest)) = TMP3 - PPV - 1) by (rewrite firstn_length_le; cbn [length] in *; lia);
assert (LT2 : Z.of_nat (length (skipn n2 rest)) = 40 - TMP3) by (rewrite length_skipn; cbn [length] in *; lia);
set (proc := firstn n2 rest) in *; set (tl2 := skipn n2 rest) in *; clearbody proc tl2; clear n2;
lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?z)] => replace (bv_swrap 32 z) with (- pitch) by (rewrite swrap32_mod64_small by lia; lia) end;
lazymatch goal with |- context [Z_to_bv 64 (e32 + ?sh ≪ 2)] => replace (e32 + sh ≪ 2) with qa by (rewrite Z.shiftl_mul_pow2 by lia; lia) end;
(eapply evt_cut; [ eapply (p3_l2_ind EB e32 exc neb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc OBE2 OB322 E4 X4 XE4 EX proc dn tl2 wrest y x _ _ _ _ _ _ _ _ _ _ _)
| clear XMR T D; pose proof (EX : _ \/ _) as EX'; post_call asegs mc; clear EX' ])
end end;
try reflexivity; try (cbn [length] in *; lia); try eassumption;
try (apply munch_refl); try (apply wmono_refl).
Local Ltac p3_fin :=
cbn [length Nat.add] in *;
match goal with D : rw_cells asegs ?mm e32 (f32 ?dn'), T : rw_cells asegs ?mm _ (f32 ?tl), LD : length ?dn' = _ |- _ =>
chunk_cat D T; rewrite <- f32_app in D; finish; [ exact D | rewrite length_app; lia ] end.

Lemma p3_iter : forall (i : Z) (eb e32s : list word) (j0 : list byte) (g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(t1 t2 a0 a1 s3 s4 s5 s6 t3 t4 t5 t6 : word) F0 fc m1,
0 <= i <= 2 -> length eb = neb -> length e32s = 40%nat ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 (usp + -128) (p3_frame j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m1 EB (f32 eb) -> rw_cells asegs m1 e32 (f32 e32s) ->
evt asegs (fun ms' => exists t1' t2' a0' a1' s3' s4' s5' s6' t3' t4' t5' t6' F' fc' m' (e32' : list word),
ms' = MS (p3_iter_R i t1' t2' a0' a1' s3' s4' s5' s6' t3' t4' t5' t6') F' (Z_to_bv 64 0xa8444) fc' None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ frm0 fc'
/\ rw_cells asegs m' e32 (f32 e32') /\ length e32' = 40%nat)
(MS (p3_iter_R i t1 t2 a0 a1 s3 s4 s5 s6 t3 t4 t5 t6) F0 (Z_to_bv 64 0xa82b0) fc None m1 (seg_rom asegs)).
Proof.
intros i eb e32s j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra t1 t2 a0 a1 s3 s4 s5 s6 t3 t4 t5 t6 F0 fc m1 Hi LE L32 FRM MU OF WM MI FR XE X32.
pose proof OBE as (OE0 & OE1 & _). pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
unfold p3_iter_R, p3_frame in *.
assert (XE4 : (exc - EB) mod 4 = 0) by (replace (exc - EB) with (e0 * 4) by lia; apply Z_mod_mult).
assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia. clear Hi.
destruct (Z_lt_dec 40 (pitch + 1 - i)) as [PP|PP]; [| destruct (Z.eq_dec (pitch + 1 - i) 40) as [PQ|PQ]; [| destruct (Z_lt_dec 40 (pitch + 1 - i + pitch)) as [PR|PR] ] ].
- destruct Hi3 as [ -> | [ -> | -> ] ].
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 0) 40. p3_skip2.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 1) 40. p3_skip2.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 2) 40. p3_skip2.
- destruct Hi3 as [ -> | [ -> | -> ] ].
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 0) (pitch + 1 - 0). p3_skip2.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 1) (pitch + 1 - 1). p3_skip2.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 2) (pitch + 1 - 2). p3_skip2.
- destruct Hi3 as [ -> | [ -> | -> ] ].
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 0) (pitch + 1 - 0). p3_l2cut MU OF XE XE4 eb (pitch + 1 - 0) 40. p3_fin.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 1) (pitch + 1 - 1). p3_l2cut MU OF XE XE4 eb (pitch + 1 - 1) 40. p3_fin.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 2) (pitch + 1 - 2). p3_l2cut MU OF XE XE4 eb (pitch + 1 - 2) 40. p3_fin.
- destruct Hi3 as [ -> | [ -> | -> ] ].
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 0) (pitch + 1 - 0). p3_l2cut MU OF XE XE4 eb (pitch + 1 - 0) (pitch + 1 - 0 + pitch). p3_fin.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 1) (pitch + 1 - 1). p3_l2cut MU OF XE XE4 eb (pitch + 1 - 1) (pitch + 1 - 1 + pitch). p3_fin.
+ p3_l1cut m1 MU OF XE X32 L32 eb e32s (pitch + 1 - 2) (pitch + 1 - 2). p3_l2cut MU OF XE XE4 eb (pitch + 1 - 2) (pitch + 1 - 2 + pitch). p3_fin.
Qed.
End ITER.

Lemma zbv_m64 : forall x, Z_to_bv 64 (18446744073709551615 - x) = Z_to_bv 64 (- x - 1).
Proof.
intros x. apply Z_to_bv_eqm. replace (18446744073709551615 - x) with ((- x - 1) + 1 * 18446744073709551616) by lia.
change (2^64) with 18446744073709551616. rewrite Z_mod_plus_full. reflexivity.
Qed.

Section W2.
Variables (EB e0 e32 usp lo start v1 : Z) (neb : nat).
Variables gp tp : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Local Notation exc := (EB + 4 * e0).
Hypothesis OBE : aobj asegs m EB NE.
Hypothesis OB32 : aobj asegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis EX : hidp (EB + NE <= e32 \/ e32 + 160 <= EB).
Hypothesis XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32).
Hypothesis XAP : e32 + 160 <= lo.
Hypothesis LO : lo <= usp - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis E0a : 290 <= e0.
Hypothesis E0b : e0 + 40 <= Z.of_nat neb.
Hypothesis ST17 : 17 <= start <= 144.
Hypothesis V1R : 0 <= v1 < 128.
Local Notation W := [(e32, e32 + 160)].

Local Ltac p3_setR i :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with mkR ?ra _ _ _ _ ?t1 ?t2 _ _ ?a0 ?a1 _ _ _ _ _ _ _ ?s3 ?s4 ?s5 ?s6 _ ?s8 _ ?s10 ?s11 ?t3 ?t4 ?t5 ?t6 =>
replace R with (p3_iter_R EB e0 e32 usp (v1 + start) ra gp tp s8 s10 s11 i t1 t2 a0 a1 s3 s4 s5 s6 t3 t4 t5 t6)
by (unfold p3_iter_R; cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ]) end end.

Local Ltac p3_it MU OF i :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with XE : rw_cells asegs mc EB (f32 ?eb), X32 : rw_cells asegs mc e32 (f32 ?e32s) |- _ =>
let EX' := fresh "EX'" in let OBE1 := fresh "OBE1" in let OB321 := fresh "OB321" in
pose proof (aobj_munch asegs W m mc EB NE OBE MU (shfree_of_aobj asegs W m EB NE OF OBE)) as OBE1;
pose proof (aobj_munch asegs W m mc e32 160 OB32 MU (shfree_of_aobj asegs W m e32 160 OF OB32)) as OB321;
eapply evt_cut; [ eapply (p3_iter EB e0 e32 usp lo (v1 + start) neb _ gp tp _ _ _ mc OBE1 OB321 E4 X4 EX XAP LO LOS E0a E0b ltac:(lia) i eb e32s)
| clear X32; pose proof (EX : _ \/ _) as EX'; post_call asegs mc; clear EX' ];
clear OBE1 OB321 end end;
try eassumption; try lia; try (apply munch_refl); try (apply wmono_refl); unfold p3_iter_R.

Lemma p3_w2 : forall (eb e32s : list word) (j0 : list byte) (g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
length eb = neb -> length e32s = 40%nat ->
frm0 fc -> mem_inv asegs m -> stk asegs m lo (usp + -128) ->
rw_cells asegs m (usp + -128) (p3_frame j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m EB (f32 eb) -> rw_cells asegs m e32 (f32 e32s) ->
evt asegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' m' (e32' : list word),
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3' t4' t5' t6')
F' (ret_pc cra) fc' None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ frm0 fc'
/\ rw_cells asegs m' e32 (f32 e32') /\ length e32' = 40%nat)
(MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 exc) (Z_to_bv 64 start) s4 (Z_to_bv 64 v1) s6 (Z_to_bv 64 (v1 + start)) s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xa8288)) fc None m (seg_rom asegs)).
Proof.
intros eb e32s j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 s11 t3 t4 t5 t6 F fc LE L32 FRM MI ST FR XE X32.
replace (ret_pc (Z_to_bv 64 0xa8288)) with (Z_to_bv 64 0xa8288) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof OBE as (OE0 & OE1 & _). pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (pose proof (XSH : _ \/ _) as Y1; cbn; unfold SH_LO, SH_HI in *; lia).
assert (PIT : 17 <= v1 + start <= 271) by lia.
ato 0xa82b0.
rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite (Z.mod_small (v1 * 2 + start * 2)) by lia. rewrite zb_lxor_ones by lia. rewrite zbv_m64.
rewrite ?swrap32_small by lia.
p3_setR 0. p3_it MU OF 0.
ato 0xa82b0. rewrite ?swrap32_small by lia. p3_setR 1. p3_it MU OF 1.
ato 0xa82b0. rewrite ?swrap32_small by lia. p3_setR 2. p3_it MU OF 2.
ato 0xa8454. unfold p3_frame in *. ato 0xa848c.
match goal with FRx : rw_cells asegs _ (usp + -128) _, STx : stk asegs _ lo (usp + -128) |- _ =>
release_frame FRx STx usp end.
astep. astep.
finish.
all: eassumption.
Qed.
End W2.
