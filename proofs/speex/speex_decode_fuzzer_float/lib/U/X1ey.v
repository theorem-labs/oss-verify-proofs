(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition SHIFT_FILT : Z := 0x11354.

Definition shift_filt_bytes : list byte :=
match image_bytes rsegs SHIFT_FILT 84 with Some bs => bs | None => [] end.
Lemma shift_filt_len : length shift_filt_bytes = 84%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma shift_filt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m SHIFT_FILT [CB 84 shift_filt_bytes].
Proof.
intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold SHIFT_FILT; lia | rewrite shift_filt_len; unfold SHIFT_FILT; lia].
Qed.

Lemma shift_filt_row : forall m r, mem_inv rsegs m -> 0 <= r <= 2 ->
exists f0 f1 f2 f3 f4 f5 f6, ro_cells rsegs m (SHIFT_FILT + 28 * r) (f32 [f0; f1; f2; f3; f4; f5; f6]).
Proof.
intros m r MI Hr. pose proof (shift_filt_ro m MI) as [WF BA]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
pose proof shift_filt_len as L. set (bs := shift_filt_bytes) in *.
rewrite <- (firstn_skipn (Z.to_nat (28 * r)) bs) in BA. apply bytes_at_app in BA as [_ BA].
rewrite firstn_length_le in BA by lia. rewrite Z2Nat.id in BA by lia.
rewrite <- (firstn_skipn 28 (skipn (Z.to_nat (28 * r)) bs)) in BA. apply bytes_at_app in BA as [B1 _].
assert (L28 : length (firstn 28 (skipn (Z.to_nat (28 * r)) bs)) = (4 * 7)%nat) by (rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct (bytes_are_f32 7 _ L28) as (ws & Lws & Ews).
destruct ws as [|f0 [|f1 [|f2 [|f3 [|f4 [|f5 [|f6 [|? ?]]]]]]]]; try (cbn in Lws; lia).
first [ unshelve sf_eexists 7%nat; [ exact (f0) | exact (f1) | exact (f2) | exact (f3) | exact (f4) | exact (f5) | exact (f6) | ] | sf_fb; exists f0, f1, f2, f3, f4, f5, f6 ]. split; [apply cells_wf_f32|]. rewrite Ews. exact B1.
Qed.

Lemma ro_cells_app : forall segs m A cs1 cs2,
ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
split.
- intros [[W1 W2] [B1 B2]]. rewrite (cells_bytes_length cs1 W1) in B2. exact (conj (conj W1 B1) (conj W2 B2)).
- intros [[W1 B1] [W2 B2]]. rewrite (cells_bytes_length cs1 W1). exact (conj (conj W1 W2) (conj B1 B2)).
Qed.
Lemma ro_f32_mid : forall segs m A ws (i k : nat),
ro_cells segs m A (f32 ws) -> (i <= length ws)%nat ->
ro_cells segs m (A + 4 * Z.of_nat i) (f32 (firstn k (skipn i ws))).
Proof.
intros segs m A ws i k H Hi.
rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H. apply ro_cells_app in H. destruct H as [_ H].
rewrite cells_size_f32, firstn_length_le in H by exact Hi.
replace (Z.of_nat (4 * i)) with (4 * Z.of_nat i) in H by lia.
rewrite <- (firstn_skipn k (skipn i ws)) in H. rewrite f32_app in H. apply ro_cells_app in H. destruct H as [H _]. exact H.
Qed.
Lemma ro_f32_uncons : forall segs m A w ws,
ro_cells segs m A (f32 (w :: ws)) -> ro_cells segs m (A + 4) (f32 ws).
Proof.
intros segs m A w ws H. rewrite f32_cons in H. change (C4 w :: f32 ws) with ([C4 w] ++ f32 ws) in H.
apply ro_cells_app in H. destruct H as [_ H]. exact H.
Qed.
Lemma rw_f32_uncons : forall segs m A w ws,
rw_cells segs m A (f32 (w :: ws)) -> rw_cells segs m (A + 4) (f32 ws).
Proof.
intros segs m A w ws H. rewrite f32_cons in H. apply rw_cells_uncons in H. destruct H as [_ H]. exact H.
Qed.

Section K.
Context {RCEIL : RunCeiling}.

Variables (m : mem).
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a7 s2 s3 s9 s10 s11 t4 t5 : word.

Definition k_post (fb cq ke : Z) : machine_state -> Prop :=
fun ms' => exists (s5' s6' s7' s8' t6' : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 cq) a2 a3 (Z_to_bv 64 (18446744073709551615 - cq)) a5 (Z_to_bv 64 6) a7
s2 s3 (Z_to_bv 64 ke) s5' s6' s7' s8' s9 s10 s11 (Z_to_bv 64 (18446744073709551615 - fb)) t4 t5 t6')
G' (Z_to_bv 64 0x24ccc) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

Ltac kbody FB CQ KK KC :=
ub_step; bato 0x24ca8%Z;
let fp := fresh "fp" in set (fp := FB + 4 * KK) in *; ub_step; bato 0x24cb0%Z;
try replace (KC * 4) with (4 * KC) by lia;
let cp := fresh "cp" in set (cp := CQ + 4 * KC) in *; ub_step; subst fp cp.

#[using="Type"] Lemma filt_k : forall (k : nat) (crest frest : list word) (fb cq kk kc ke : Z) (cw fw s8 : word) (G : bvmap 5 word) (fc : bv 32),
length crest = k -> (k <= length frest)%nat -> ke = kk + 1 + Z.of_nat k -> 0 <= kk -> ke <= 7 -> 0 <= kc -> kc + 1 + Z.of_nat k <= 7 ->
0 <= fb -> 0 <= cq ->
frm0 fc -> mem_inv rsegs m ->
rw_cells rsegs m (cq + 4 * kc) (f32 (cw :: crest)) -> ro_cells rsegs m (fb + 4 * kk) (f32 (fw :: frest)) ->
evt rsegs (k_post fb cq ke)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 cq) a2 a3 (Z_to_bv 64 (18446744073709551615 - cq)) a5 (Z_to_bv 64 6) a7
s2 s3 (Z_to_bv 64 ke) (Z_to_bv 64 (4 * kk)) (Z_to_bv 64 (fb + 4 * kk)) (Z_to_bv 64 kc) s8 s9 s10 s11 (Z_to_bv 64 (18446744073709551615 - fb)) t4 t5 (Z_to_bv 64 kk))
G (Z_to_bv 64 0x24c98) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros crest frest fb cq kk kc ke cw fw s8 G fc LC LF Hke Hkk Hke7 Hkc0 Hkc Hfb Hcq FRM MI CW RO;
pose proof (rw_cells_bound _ _ _ _ CW) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (ro_cells_bound _ _ _ _ RO) as BR; rewrite cells_size_f32 in BR; cbn [length] in BR.
- destruct crest; [|cbn in LC; lia]. rewrite f32_cons, f32_nil in CW. rewrite !f32_cons in RO.
kbody fb cq kk kc. bato 0x24ccc%Z.
apply evt_done; unfold k_post. do 7 eexists. split; [reflexivity| assumption].
- destruct crest as [|cw' crest]; [cbn in LC; lia|]. destruct frest as [|fw' frest]; [cbn in LF; lia|].
cbn [length] in LC, LF, BC, BR. rewrite !f32_cons in CW. rewrite !f32_cons in RO.
kbody fb cq kk kc. bato 0x24c98%Z.
rewrite <- !f32_cons in CW. rewrite <- !f32_cons in RO.
apply rw_f32_uncons in CW. apply ro_f32_uncons in RO.
replace (cq + 4 * kc + 4) with (cq + 4 * (kc + 1)) in CW by lia.
replace (fb + 4 * kk + 4) with (fb + 4 * (kk + 1)) in RO by lia.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?S5 ?S6 ?S7 _ _ _ _ _ _ _ ?T6) _ _ _ _ _ _) =>
replace S5 with (Z_to_bv 64 (4 * (kk + 1))) by (f_equal; rewrite ?swrap32_small by lia; lia);
replace S6 with (Z_to_bv 64 (fb + 4 * (kk + 1))) by (f_equal; rewrite ?swrap32_small by lia; lia);
replace S7 with (Z_to_bv 64 (kc + 1)) by (f_equal; rewrite ?swrap32_small by lia; lia);
replace T6 with (Z_to_bv 64 (kk + 1)) by (f_equal; rewrite ?swrap32_small by lia; lia)
end.
eapply (IH crest frest fb cq (kk + 1) (kc + 1) ke cw' fw'); [lia | lia | lia | lia | lia | lia | lia | lia | lia | assumption | exact MI | exact CW | exact RO].
Qed.
End K.

Section R.
Context {RCEIL : RunCeiling}.

Variables (q i fq rq : Z).
Variables xra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 x0 x1 x2 x3 x4 x5 x6 : word.
Hypothesis FQ : fq + 28 <= q.

Definition row_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (t1 t2 t3 t4 t5 t6 s4' s5' s6' s7' s8' : word) (G' : bvmap 5 word) (fc' : bv 32) (m' : mem) (cr' : list word),
ms' = MS (mkR xra (Z_to_bv 64 q) gp tp (Z_to_bv 64 fq) t1 t2 s0 s1 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 q) (Z_to_bv 64 3) (Z_to_bv 64 10)
(Z_to_bv 64 (18446744073709551615 - q)) (Z_to_bv 64 SHIFT_FILT) (Z_to_bv 64 6) (Z_to_bv 64 7) s2 s3 s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0x24d08) fc' None m' (seg_rom rsegs)
/\ munch [(rq, rq + 28)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' rq (f32 cr') /\ length cr' = 7%nat.

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

Ltac mkwin s n i1 W V C0 RO :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (rw_cells_f32_mid rsegs mm q [x0; x1; x2; x3; x4; x5; x6] s n C0 ltac:(cbn; lia)) as W;
cbn [firstn skipn] in W;
pose proof (ro_f32_mid rsegs mm fq [f0; f1; f2; f3; f4; f5; f6] i1 n RO ltac:(cbn; lia)) as V;
cbn [firstn skipn] in V
end.

Ltac fix_row_addr :=
match goal with |- context [Z.sub (Z.modulo (Z.shiftl (i + 1) 5) ?M) (Z.modulo (Z.shiftl (i + 1) 2) ?M')] =>
replace (Z.sub (Z.modulo (Z.shiftl (i + 1) 5) M) (Z.modulo (Z.shiftl (i + 1) 2) M')) with (rq - q)
by (rewrite !Z.shiftl_mul_pow2, !Z.mod_small by lia; lia)
end;
match goal with
| |- context [Z_to_bv 64 (q + (rq - q))] => replace (q + (rq - q)) with rq by lia
| |- context [Z_to_bv 64 (q + 0 + (rq - q))] => replace (q + 0 + (rq - q)) with rq by lia
| |- context [Z_to_bv 64 (q + ?o + (rq - q))] => replace (q + o + (rq - q)) with (rq + o) by lia
end.

Ltac jiter S N I1 KE KN CRE FRE C0 RO :=
ub_step; bato 0x24c98%Z; lits;
let W := fresh "W" in let V := fresh "V" in
mkwin S N I1 W V C0 RO;
lazymatch goal with |- evt _ _ (MS _ _ _ ?fcx _ _ _) =>
lazymatch goal with FRM : frm0 fcx, MI : mem_inv _ _ |- _ =>
eapply evt_cut; [eapply filt_k with (k := KN) (crest := CRE) (frest := FRE) (fb := fq) (cq := q) (kk := Z.of_nat I1) (kc := Z.of_nat S) (ke := KE);
[reflexivity | cbn; lia | cbn; lia | lia | lia | lia | cbn; lia | lia | lia | exact FRM | exact MI | exact W | exact V] | ];
clear W V FRM;
let PO := fresh "PO" in
intros ? PO; destruct PO as (? & ? & ? & ? & ? & ? & ? & -> & FRM)
end
end;
bato 0x24cf8%Z; fix_row_addr; ub_step.

#[using="FQ"] Lemma filt_row : forall (cr : list word) (t1 t2 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
0 <= i <= 2 -> rq = q + 28 + 28 * i -> fq = SHIFT_FILT + 28 * i -> length cr = 7%nat ->
frm0 fc -> mem_inv rsegs m ->
rw_cells rsegs m q (f32 [x0; x1; x2; x3; x4; x5; x6]) -> rw_cells rsegs m rq (f32 cr) ->
ro_cells rsegs m fq (f32 [f0; f1; f2; f3; f4; f5; f6]) ->
evt rsegs (row_post m)
(MS (mkR xra (Z_to_bv 64 q) gp tp (Z_to_bv 64 fq) t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 q) (Z_to_bv 64 3) (Z_to_bv 64 10)
(Z_to_bv 64 (18446744073709551615 - q)) (Z_to_bv 64 SHIFT_FILT) (Z_to_bv 64 6) (Z_to_bv 64 7) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x24c2c) fc None m (seg_rom rsegs)).
Proof.
intros cr t1 t2 t3 t4 t5 t6 G fc m Hi Hrq Hfq LR FRM MI C0 CR RO.
pose proof (rw_cells_bound _ _ _ _ C0) as B0; rewrite cells_size_f32 in B0; cbn [length] in B0.
pose proof (rw_cells_bound _ _ _ _ CR) as BR; rewrite cells_size_f32, LR in BR.
pose proof (ro_cells_bound _ _ _ _ RO) as BF; rewrite cells_size_f32 in BF; cbn [length] in BF.
pose proof (munch_refl [(rq, rq + 28)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct cr as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|? ?]]]]]]]]; try (cbn in LR; lia).
rewrite !f32_cons, f32_nil in CR.
unfold SHIFT_FILT in Hfq |- *.
bato 0x24c60%Z.
assert (R28 : Z.shiftl i 5 mod 18446744073709551616 - Z.shiftl i 2 mod 18446744073709551616 = 28 * i)
by (rewrite !Z.shiftl_mul_pow2, !Z.mod_small by lia; lia).
rewrite R28, <- Hfq. replace (28 * i + q + 28) with rq by lia.
rewrite !(Z.mod_small fq) by lia. rewrite !(Z.mod_small rq) by lia. rewrite !zb_lxor_ones by lia.
jiter 0%nat 4%nat 3%nat 7 3%nat [x1; x2; x3] [f4; f5; f6] C0 RO. bato 0x24c60%Z.
jiter 0%nat 5%nat 2%nat 7 4%nat [x1; x2; x3; x4] [f3; f4; f5; f6] C0 RO. bato 0x24c60%Z.
jiter 0%nat 6%nat 1%nat 7 5%nat [x1; x2; x3; x4; x5] [f2; f3; f4; f5; f6] C0 RO. bato 0x24c60%Z.
jiter 0%nat 7%nat 0%nat 7 6%nat [x1; x2; x3; x4; x5; x6] [f1; f2; f3; f4; f5; f6] C0 RO. bato 0x24c60%Z.
jiter 1%nat 6%nat 0%nat 6 5%nat [x2; x3; x4; x5; x6] [f1; f2; f3; f4; f5] C0 RO. bato 0x24c60%Z.
jiter 2%nat 5%nat 0%nat 5 4%nat [x3; x4; x5; x6] [f1; f2; f3; f4] C0 RO. bato 0x24c60%Z.
jiter 3%nat 4%nat 0%nat 4 3%nat [x4; x5; x6] [f1; f2; f3] C0 RO. bato 0x24d08%Z.
apply evt_done; unfold row_post.
eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, [_; _; _; _; _; _; _]. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact FRM|].
split; [rewrite !f32_cons, f32_nil; exact CR| reflexivity].
Qed.
End R.
