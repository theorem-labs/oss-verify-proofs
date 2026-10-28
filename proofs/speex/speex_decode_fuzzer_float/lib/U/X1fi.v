(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1ev X1ex.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition JX (pc : Z) (m : mem) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (a0 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

Definition JX2 (pc : Z) (m : mem) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

Ltac jx2_done := apply evt_done; sf_eexists 2%nat; split; [reflexivity| assumption].
Ltac jx_intro := try match goal with H : frm0 _ |- _ => clear H end;
let PO := fresh "PO" in let FRM := fresh "FRM" in intros ? PO;
first [ sf_curry 5%nat PO; intros ? ? ? -> FRM; sf_clear PO; sf_fix_order | sf_curry 4%nat PO; intros ? ? -> FRM; sf_clear PO; sf_fix_order ].
Ltac jx_done := apply evt_done; sf_eexists 3%nat; split; [reflexivity| assumption].

Tactic Notation "join" constr(pcJ) integer(n1) integer(n2) :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut rsegs (JX pcJ mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ let B := fresh "B" in if_cases B;
[ do n1 zstep; jx_done | do n2 zstep; jx_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let PO := fresh "PO" in let FRM := fresh "FRM" in intros ? PO; sf_curry 5%nat PO; intros ? ? ? -> FRM; sf_clear PO; sf_fix_order ]
end.

Ltac lit1 :=
match goal with
| |- context [Z.ltb ?a ?b] => is_Z_lit a; is_Z_lit b; let v := eval vm_compute in (Z.ltb a b) in change (Z.ltb a b) with v; cbn [Z.b2z]
| |- context [Z.sub ?a ?b] => is_Z_lit a; is_Z_lit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
| |- context [Z.modulo ?a ?b] => is_Z_lit a; is_Z_lit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
| |- context [Z.land ?a ?b] => is_Z_lit a; is_Z_lit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
| |- context [Z.add ?a ?b] => is_Z_lit a; is_Z_lit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
| |- context [Z.shiftl ?a ?b] => is_Z_lit a; is_Z_lit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
end.
Ltac lits := repeat lit1.

Lemma land_high0 : forall p, 0 <= p < 2^63 -> Z.land p (2^63) = 0.
Proof.
intros p Hp. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n 63) as [->|NE].
- destruct (Z.eq_dec p 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
rewrite (Z.bits_above_log2 p 63) by (try lia; apply Z.log2_lt_pow2; lia). reflexivity.
- rewrite (Z.pow2_bits_false 63 n) by lia. apply andb_false_r.
Qed.

Lemma slt40_norm : forall p, 0 <= p < 2^63 ->
(9223372036854775848 <? Z.lxor p 9223372036854775808) = (40 <? p).
Proof.
intros p Hp. change 9223372036854775808 with (2^63). rewrite <- Z.add_nocarry_lxor by (apply land_high0; lia).
destruct (Z.ltb_spec 40 p); [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Section Mid.
Context {RCEIL : RunCeiling}.
Variables (EB eoff ne I1 I2 pitch lo : Z) (eb i2 : list word).
Variables sp gp tp s0 s8 s9 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis LI2 : length i2 = 80%nat.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis HP : 17 <= pitch <= 144.
Hypothesis HI2 : I2 = I1 + 320.
Local Notation exc := (EB + 4 * eoff).
Hypothesis EX0 : 0 < exc.
Hypothesis EX4 : exc mod 4 = 0.
Hypothesis NE0 : 0 < ne.
Hypothesis NE4 : ne mod 4 = 0.
Hypothesis NEH : ne < 2^64.
Hypothesis I20 : 0 < I2.
Hypothesis I24 : I2 mod 4 = 0.
Hypothesis SLO : lo + 16 <= bv_unsigned sp.
Hypothesis AI2 : apart I2 320 lo (bv_unsigned sp - lo).
Hypothesis AEX : apart exc 320 lo (bv_unsigned sp - lo).

Definition mid_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (ra t0 t1 t2 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 80) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 320) a7
(Z_to_bv 64 ne) (Z_to_bv 64 exc) (Z_to_bv 64 I1) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 0) s8 s9 (Z_to_bv 64 160) (Z_to_bv 64 320)
t3 t4 t5 t6)
F' (Z_to_bv 64 0x249d4) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp).

#[using="LEB LI2 R3 R4 HP EX0 EX4 NE0 NE4 NEH I20 I24 SLO AI2 AEX"] Lemma mc_mid : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
frm0 fc -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m I2 (f32 i2) ->
evt rsegs (mid_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 80) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ne) (Z_to_bv 64 exc) (Z_to_bv 64 I1) (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 I2) s8 s9 (Z_to_bv 64 160) (Z_to_bv 64 320)
t3 t4 t5 t6)
G (Z_to_bv 64 0x24830) fc None m (seg_rom rsegs)).
Proof.
intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 G fc m FRM MI ST XEB XI2.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XI2) as BI2; rewrite cells_size_f32, LI2 in BI2.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct (eb_window m EB eb eoff XEB LEB ltac:(lia) ltac:(lia)) as [WY LY].
pose proof AI2 as AI2'. pose proof AEX as AEX'. unfold apart in AI2', AEX'.

do 4 zstep. join 0x24844 0 1.
do 7 zstep.
call (inner_prod_spec i2 (firstn 80 (skipn (Z.to_nat eoff) eb)) 20 I2 exc lo);
[ exact MI | lia | rewrite LI2; reflexivity | exact LY | exact I20 | exact I24 | exact EX0 | exact EX4
| exact ST | exact SLO | exact AI2 | exact AEX | exact XI2 | exact WY | exact FRM | ].
rename MI0 into MI || idtac. clear WY.

do 2 zstep. join 0x2486c 0 1.

do 4 zstep. join 0x24884 0 2.

do 3 zstep. join 0x248a4 2 3.

do 4 zstep. join 0x248f8 0 17.

do 11 zstep. join 0x24928 0 1.
do 3 zstep. join 0x24938 0 1.

do 2 zstep. if_false_x.
do 5 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut rsegs (JX2 0x24990 mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ rewrite (slt40_norm pitch) by lia; destruct (40 <? pitch) eqn:B40; cbn [Z.b2z]; lits; do 15 zstep; jx2_done
| jx_intro ]
end.
do 17 zstep.
rewrite (land3_al ne NE4), (land3_al exc EX4).
replace (0 <? exc) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <? ne) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [Z.b2z]. alits.
apply evt_done; unfold mid_post.
sf_eexists 12%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. assumption.
Qed.
End Mid.
