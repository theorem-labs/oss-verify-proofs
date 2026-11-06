(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X07r.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yj.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma eb_window : forall m EB (eb : list word) (k : Z), rw_cells bsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= k -> k + 80 <= 500 ->
rw_cells bsegs m (EB + 4 * k) (f32 (firstn 80 (skipn (Z.to_nat k) eb))) /\ Z.of_nat (length (firstn 80 (skipn (Z.to_nat k) eb))) = 4 * 20.
Proof.
intros m EB eb k X L Hk Hk2. split.
- replace (4 * k) with (4 * Z.of_nat (Z.to_nat k)) by lia. apply rw_cells_f32_mid; [exact X| lia].
- rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia.
Qed.

Section A.

Variables (EB eoff p IP q lo cq : Z) (eb : list word) (m0 : mem).
Variables gp tp s0 s10 s11 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis R1 : 0 <= eoff - p - 6.
Hypothesis R2 : eoff - p <= 414.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis OBE : aobj bsegs m0 EB 2000.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis EB0 : 0 < EB.
Hypothesis QLO : lo <= q - 48.
Hypothesis LOS : SH_HI <= lo.
Hypothesis Q63 : q < 2 ^ 63.
Hypothesis EBLO : EB + 2000 <= lo.
Hypothesis CQ0 : IMG_TOP_B <= cq.
Hypothesis CQLO : cq + 112 <= lo.
Hypothesis CQSH : cq + 112 <= SH_LO \/ SH_HI <= cq.
Hypothesis CQEB : cq + 112 <= EB \/ EB + 2000 <= cq.
Local Notation exc := (EB + 4 * eoff).
Local Notation W := [(q + -48, q); (cq, cq + 28)].

Definition corr0_post : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G' : bvmap 5 word) (fc' : bv 32) (m' : mem) (c0 : list word),
ms' = MS (mkR (Z_to_bv 64 0xa9704) (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (exc - 4 * p - 12)) (Z_to_bv 64 28) (Z_to_bv 64 exc) (Z_to_bv 64 (18446744073709551615 - (exc - 4 * p - 12)))
(Z_to_bv 64 28) (Z_to_bv 64 cq) (Z_to_bv 64 SHB) (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xa9714) fc' None m' (seg_rom bsegs)
/\ munch W m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ stk bsegs m' lo q
/\ rw_cells bsegs m' cq (f32 c0) /\ length c0 = 7%nat.

Lemma corr0_loop : forall (k : nat) (done rest : list word) (cs : Z) (cw : word)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 6)%nat ->
cs = cq + 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv bsegs m -> munch W m0 m -> wmono bsegs m0 m -> client_constsB m -> stk bsegs m lo q ->
rw_cells bsegs m EB (f32 eb) ->
rw_cells bsegs m cq (f32 done) -> rw_cells bsegs m cs (f32 (cw :: rest)) ->
evt bsegs corr0_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (exc - 4 * p - 12)) (Z_to_bv 64 (4 * Z.of_nat (length done))) (Z_to_bv 64 exc) (Z_to_bv 64 (18446744073709551615 - (exc - 4 * p - 12)))
(Z_to_bv 64 28) (Z_to_bv 64 cq) (Z_to_bv 64 SHB) (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa96f0) fc None m (seg_rom bsegs)).
Proof.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof CQ0 as CQ0'. unfold IMG_TOP_B in CQ0'. pose proof CQSH as CQSH'. unfold SH_LO, SH_HI in CQSH'.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
induction k as [|k IH]; intros done rest cs cw xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 G fc m
LR LD Hcs FRM MI MU WM CC ST XEB CD CW;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ CW) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (eb_window m EB eb eoff XEB LEB ltac:(lia) ltac:(lia)) as [WX LX];
destruct (eb_window m EB eb (eoff - p - 3 + Z.of_nat (length done)) XEB LEB ltac:(lia) ltac:(lia)) as [WY LY];
pose proof (aobj_munch bsegs W m0 m EB 2000 OBE MU (shfree_of_aobj bsegs W m0 EB 2000 OF OBE)) as OBm;
pose proof CC as (G1 & G2 & G3 & G4);
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in G1, G2, G3, G4.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in CW.
bato 0xa9700.
subst cs. astep.
replace (exc - 4 * p - 12 + 4 * Z.of_nat (length done)) with (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) by lia.
change 80 with (4 * 20).
call (inner_prodB_walk (firstn 80 (skipn (Z.to_nat eoff) eb)) (firstn 80 (skipn (Z.to_nat (eoff - p - 3 + Z.of_nat (length done))) eb)) 20
exc (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) q lo);
[ lia | exact LX | exact LY | apply (aobj_sub bsegs m EB 2000); [exact OBm | lia | lia] | apply (aobj_sub bsegs m EB 2000); [exact OBm | lia | lia]
| clear - E4; Z.div_mod_to_equations; lia | clear - E4; Z.div_mod_to_equations; lia | lia | lia | lia | exact LOS | exact Q63
| exact WX | exact WY | exact FRM | exact ST | lia | lia | exact (conj G1 (conj G2 (conj G3 G4))) | exact MI | ].
rename MI0 into MI || idtac.
astep. astep. astep. astep. sh_if.
chunk_snoc CD CW. rewrite f32_snoc in CD.
replace (4 * Z.of_nat (length done) + 4) with 28 by lia.
apply evt_done; unfold corr0_post.
do 19 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [assumption|].
split; [exact CD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in CW.
subst cs. bato 0xa9700. astep.
replace (exc - 4 * p - 12 + 4 * Z.of_nat (length done)) with (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) by lia.
change 80 with (4 * 20).
call (inner_prodB_walk (firstn 80 (skipn (Z.to_nat eoff) eb)) (firstn 80 (skipn (Z.to_nat (eoff - p - 3 + Z.of_nat (length done))) eb)) 20
exc (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) q lo);
[ lia | exact LX | exact LY | apply (aobj_sub bsegs m EB 2000); [exact OBm | lia | lia] | apply (aobj_sub bsegs m EB 2000); [exact OBm | lia | lia]
| clear - E4; Z.div_mod_to_equations; lia | clear - E4; Z.div_mod_to_equations; lia | lia | lia | lia | exact LOS | exact Q63
| exact WX | exact WY | exact FRM | exact ST | lia | lia | exact (conj G1 (conj G2 (conj G3 G4))) | exact MI | ].
rename MI0 into MI || idtac.
astep. astep. astep. astep. sh_if.
chunk_uncons CW as C1. chunk_snoc CD C1. rewrite f32_snoc in CD.
replace (4 * Z.of_nat (length done) + 4) with (4 * Z.of_nat (length (done ++ [ip_sum fzero_s (firstn 80 (skipn (Z.to_nat eoff) eb))
(firstn 80 (skipn (Z.to_nat (eoff - p - 3 + Z.of_nat (length done))) eb))]))) by (rewrite length_app; cbn [length]; lia).
eapply (IH (done ++ [_]) rest (cq + 4 * Z.of_nat (length done) + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| assumption | exact MI | exact MU | exact WM | exact (conj G1 (conj G2 (conj G3 G4))) | assumption | assumption | exact CD | exact CW ].
Qed.
End A.
