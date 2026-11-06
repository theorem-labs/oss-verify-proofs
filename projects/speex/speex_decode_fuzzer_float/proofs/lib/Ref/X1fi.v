(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1hm X1ev X1ex.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Definition JX (pc : Z) (m : mem) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (a0 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

Definition JX2 (pc : Z) (m : mem) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (a0 a1 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

Ltac jx2_done := apply evt_done; sf_eexists 4%nat; split; [reflexivity| assumption].
Ltac jx_intro := try match goal with H : frm0 _ |- _ => clear H end;
let PO := fresh "PO" in let FRM := fresh "FRM" in intros ? PO;
first [ sf_curry 6%nat PO; intros ? ? ? ? -> FRM; sf_clear PO; sf_fix_order | sf_curry 5%nat PO; intros ? ? ? -> FRM; sf_clear PO; sf_fix_order ].
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
Variables (EB eoff ne I1 I2 pitch : Z) (eb i2 : list word).
Variables sp gp tp s0 s8 s9 s10 s11 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis LI2 : length i2 = 80%nat.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis HP : 17 <= pitch <= 144.
Hypothesis HI2 : I2 = I1 + 320.
Local Notation exc := (EB + 4 * eoff).

Definition mid_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ne) (Z_to_bv 64 (I1 + 640)) (Z_to_bv 64 exc) (Z_to_bv 64 ne) a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 exc) (Z_to_bv 64 I1) (Z_to_bv 64 I2) (Z_to_bv 64 40) (Z_to_bv 64 pitch) s8 s9 s10 s11
t3 t4 t5 t6)
F' (Z_to_bv 64 0x2173c) fc' None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'.

#[using="LEB LI2 R3 R4 HP"] Lemma mc_mid : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
frm0 fc -> mem_inv rsegs m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m I2 (f32 i2) ->
evt rsegs (mid_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ne) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 exc) (Z_to_bv 64 I1) (Z_to_bv 64 I2) (Z_to_bv 64 40) (Z_to_bv 64 pitch) s8 s9 s10 s11
t3 t4 t5 t6)
G (Z_to_bv 64 0x215c0) fc None m (seg_rom rsegs)).
Proof.
intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 G fc m FRM MI XEB XI2.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XI2) as BI2; rewrite cells_size_f32, LI2 in BI2.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct (eb_window m EB eb eoff XEB LEB ltac:(lia) ltac:(lia)) as [WY LY].

do 4 zstep. join 0x215d4 0 1.
do 7 zstep.
call (inner_prod_spec i2 (firstn 80 (skipn (Z.to_nat eoff) eb)) 20 I2 exc);
[ exact MI | lia | rewrite LI2; reflexivity | exact LY | exact XI2 | exact WY | exact FRM | ].
rename MI0 into MI || idtac. clear WY.

do 2 zstep. join 0x215fc 0 1.

do 4 zstep. join 0x21614 0 2.

do 3 zstep. join 0x21634 2 3.

do 4 zstep. join 0x21688 0 17.

do 11 zstep. join 0x216b8 0 1.
do 3 zstep. join 0x216c8 0 1.

do 3 zstep. if_false_x.
do 15 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut rsegs (JX2 0x21718 mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ rewrite (slt40_norm pitch) by lia; destruct (40 <? pitch) eqn:B40; cbn [Z.b2z]; lits; do 2 zstep; jx2_done
| jx_intro ]
end.
do 9 zstep.
apply evt_done; unfold mid_post.
sf_eexists 16%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact FRM.
Qed.
End Mid.
