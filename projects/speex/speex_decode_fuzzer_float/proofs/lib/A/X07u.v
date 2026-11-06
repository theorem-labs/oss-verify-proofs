(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition SHIFT_FILT : Z := 0x247e0.

Definition shift_filt_bytes : list byte :=
match image_bytes asegs SHIFT_FILT 84 with Some bs => bs | None => [] end.
Lemma shift_filt_len : length shift_filt_bytes = 84%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma shift_filt_ro : forall m, mem_inv asegs m -> ro_cells asegs m SHIFT_FILT [CB 84 shift_filt_bytes].
Proof.
intros m MI. apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | unfold SHIFT_FILT; lia | rewrite shift_filt_len; unfold SHIFT_FILT; lia].
Qed.

Lemma shift_filt_row : forall m r, mem_inv asegs m -> 0 <= r <= 2 ->
exists f0 f1 f2 f3 f4 f5 f6, ro_cells asegs m (SHIFT_FILT + 28 * r) (f32 [f0; f1; f2; f3; f4; f5; f6]).
Proof.
intros m r MI Hr. pose proof (shift_filt_ro m MI) as [WF BA]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
pose proof shift_filt_len as L. set (bs := shift_filt_bytes) in *.
rewrite <- (firstn_skipn (Z.to_nat (28 * r)) bs) in BA. apply bytes_at_app in BA as [_ BA].
rewrite firstn_length_le in BA by lia. rewrite Z2Nat.id in BA by lia.
rewrite <- (firstn_skipn 28 (skipn (Z.to_nat (28 * r)) bs)) in BA. apply bytes_at_app in BA as [B1 _].
assert (L28 : length (firstn 28 (skipn (Z.to_nat (28 * r)) bs)) = (4 * 7)%nat) by (rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct (bytes_are_f32 7 _ L28) as (ws & Lws & Ews).
destruct ws as [|f0 [|f1 [|f2 [|f3 [|f4 [|f5 [|f6 [|? ?]]]]]]]]; try (cbn in Lws; lia).
exists f0, f1, f2, f3, f4, f5, f6. split; [apply cells_wf_f32|]. rewrite Ews. exact B1.
Qed.

Section K.

Variables (m : mem) (fb cq : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s11 : word.
Hypothesis OBF : aobj asegs m fb 28.
Hypothesis OBC : aobj asegs m cq 28.
Hypothesis FB4 : fb mod 4 = 0.
Hypothesis CQ4 : cq mod 4 = 0.

Definition k_post (G : bvmap 5 word) (ke kf kc : Z) : machine_state -> Prop :=
fun ms' => exists (s6 s10 g12 g13 g14 : word) (fc' : bv 32),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fb + 4 * kf)) (Z_to_bv 64 (cq + 4 * kc)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11
(Z_to_bv 64 ke) (Z_to_bv 64 ke) (Z_to_bv 64 (cq + 4 * kc)) (Z_to_bv 64 (fb + 4 * kf)))
(bvmap_set 12 g12 (bvmap_set 13 g13 (bvmap_set 14 g14 G))) (Z_to_bv 64 0xa5b9c) fc' None m (seg_rom asegs)
/\ frm0 fc'.

Lemma filt_k : forall (k : nat) (crest frest : list word) (kk ke kf kc : Z) (cw fw s6 s10 : word) (G : bvmap 5 word) (fc : bv 32),
length crest = k -> (k <= length frest)%nat -> ke = kk + 1 + Z.of_nat k -> 0 <= kk -> ke <= 7 ->
0 <= kf -> kf + 1 + Z.of_nat k <= 7 -> 0 <= kc -> kc + 1 + Z.of_nat k <= 7 ->
frm0 fc -> mem_inv asegs m ->
rw_cells asegs m (cq + 4 * kc) (f32 (cw :: crest)) -> ro_cells asegs m (fb + 4 * kf) (f32 (fw :: frest)) ->
evt asegs (k_post G ke (kf + 1 + Z.of_nat k) (kc + 1 + Z.of_nat k))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fb + 4 * kf)) (Z_to_bv 64 (cq + 4 * kc)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11
(Z_to_bv 64 ke) (Z_to_bv 64 kk) (Z_to_bv 64 (cq + 4 * kc)) (Z_to_bv 64 (fb + 4 * kf)))
G (Z_to_bv 64 0xa5b34) fc None m (seg_rom asegs)).
Proof using OBF OBC FB4 CQ4.
pose proof OBF as (OF0 & OF1 & _). pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros crest frest kk ke kf kc cw fw s6 s10 G fc LC LF Hke Hkk Hke7 Hkf0 Hkf Hkc0 Hkc FRM MI CW RO;
pose proof (rw_cells_bound _ _ _ _ CW) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (ro_cells_bound _ _ _ _ RO) as BR; rewrite cells_size_f32 in BR; cbn [length] in BR.
- destruct crest; [|cbn in LC; lia]. rewrite f32_cons, f32_nil in CW. rewrite !f32_cons in RO.
do 4 astep. chk_merge OBF 4.
ato 0xa5b54. astep. chk_merge OBC 4.
ato 0xa5b74. astep. sh_if. astep.
replace (kk + 1) with ke by lia.
replace (fb + 4 * kf + 4) with (fb + 4 * (kf + 1 + Z.of_nat 0)) by lia. replace (cq + 4 * kc + 4) with (cq + 4 * (kc + 1 + Z.of_nat 0)) by lia.
apply evt_done; unfold k_post. do 6 eexists. split; [reflexivity| assumption].
- destruct crest as [|cw' crest]; [cbn in LC; lia|]. destruct frest as [|fw' frest]; [cbn in LF; lia|].
cbn [length] in LC, LF, BC, BR. rewrite !f32_cons in CW. rewrite !f32_cons in RO.
do 4 astep. chk_merge OBF 4.
ato 0xa5b54. astep. chk_merge OBC 4.
ato 0xa5b74. astep. sh_if.
rewrite <- !f32_cons in CW. rewrite <- !f32_cons in RO.
apply rw_f32_uncons in CW. apply ro_f32_uncons in RO.
replace (fb + 4 * kf + 4) with (fb + 4 * (kf + 1)) in * by lia. replace (cq + 4 * kc + 4) with (cq + 4 * (kc + 1)) in * by lia.
eapply evt_mono; [eapply (IH crest frest (kk + 1) ke (kf + 1) (kc + 1) cw' fw'); [lia | lia | lia | lia | lia | lia | lia | lia | lia | assumption | exact MI | exact CW | exact RO] |].
intros ms' (s6' & s10' & g12 & g13 & g14 & fc' & -> & FRM'). unfold k_post.
replace (kf + 1 + 1 + Z.of_nat k) with (kf + 1 + Z.of_nat (S k)) by lia. replace (kc + 1 + 1 + Z.of_nat k) with (kc + 1 + Z.of_nat (S k)) by lia.
exists s6', s10', g12, g13, g14, fc'. split; [| exact FRM']. norm_fchain. reflexivity.
Qed.
End K.

Lemma fmv_s_fzero : fmv_s fzero_s = fzero_s.
Proof. reflexivity. Qed.

Section R.

Variables (i fb cq rq : Z).
Variables ra sp gp tp s0 s1 s2 s3 s4 s7 s8 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 x0 x1 x2 x3 x4 x5 x6 : word.
Variables (F : bvmap 5 word).

Local Notation FPF g12 g13 g14 := (bvmap_set 15 fzero_s (bvmap_set 12 g12 (bvmap_set 13 g13 (bvmap_set 14 g14 F)))).

Definition row_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 t3 t4 t5 t6 s6 s10 g12 g13 g14 : word) (fc' : bv 32) (m' : mem) (cr' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 3) (Z_to_bv 64 10) (Z_to_bv 64 (fb + 28)) (Z_to_bv 64 7) (Z_to_bv 64 (fb + 28))
s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
(FPF g12 g13 g14) (Z_to_bv 64 0xa5bd0) fc' None m' (seg_rom asegs)
/\ munch [(rq, rq + 28)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ rw_cells asegs m' rq (f32 cr') /\ length cr' = 7%nat.

Lemma row_addr : forall M, 0 <= i <= 2 -> rq = cq + 28 + 28 * i -> M = 18446744073709551616 ->
Z.shiftl (i + 1) 5 mod M - Z.shiftl (i + 1) 2 mod M = rq - cq.
Proof. intros M Hi Hrq ->. rewrite !Z.shiftl_mul_pow2, !Z.mod_small by lia. lia. Qed.

Ltac jiter W OBT OBC CQSH I1 KC KN cre fre C0 RO :=
ato 0xa5b34; alits; rewrite ?fmv_s_fzero;
(let o := eval vm_compute in (4 * I1) in change (fb + o) with (fb + 4 * I1));
(let o := eval vm_compute in (4 * KC) in change (cq + o) with (cq + 4 * KC));
lazymatch goal with |- evt _ _ (MS _ _ _ ?fcx _ ?mc _) =>
lazymatch goal with FRM : frm0 fcx, MI : mem_inv _ mc, MU : munch W ?m0 mc, OF : offsh W |- _ =>
let OBFm := fresh "OBFm" in let OBCm := fresh "OBCm" in
pose proof (aobj_sub asegs mc SHIFT_FILT 84 fb 28 (aobj_munch asegs W m0 mc SHIFT_FILT 84 OBT MU (shfree_of_aobj asegs W m0 SHIFT_FILT 84 OF OBT)) ltac:(unfold SHIFT_FILT; lia) ltac:(unfold SHIFT_FILT; lia)) as OBFm;
pose proof (aobj_sub asegs mc cq 112 cq 28 (aobj_munch asegs W m0 mc cq 112 OBC MU (shfree_of_aobj asegs W m0 cq 112 OF OBC)) ltac:(lia) ltac:(lia)) as OBCm;
let Wc := fresh "Wc" in let Vf := fresh "Vf" in
pose proof (rw_cells_f32_mid asegs mc cq [x0; x1; x2; x3; x4; x5; x6] (Z.to_nat KC) (S KN) C0 ltac:(cbn; lia)) as Wc; cbn [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in Wc;
pose proof (ro_f32_mid asegs mc fb [f0; f1; f2; f3; f4; f5; f6] (Z.to_nat I1) (S KN) RO ltac:(cbn; lia)) as Vf; cbn [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vf;
eapply evt_cut; [eapply (filt_k mc fb cq) with (k := KN) (crest := cre) (frest := fre) (kk := I1) (kf := I1) (kc := KC);
[exact OBFm | exact OBCm | lia | lia | reflexivity | cbn; lia | reflexivity | lia | lia | lia | cbn; lia | lia | cbn; lia | exact FRM | exact MI | exact Wc | exact Vf] | ];
clear Wc Vf FRM OBFm OBCm;
let ms' := fresh "ms" in intros ms' (?s6 & ?s10 & ?g12 & ?g13 & ?g14 & ?fc & -> & FRM)
end
end;
norm_fchain.

Ltac jtail o :=
ato 0xa5bbc; alits;
lazymatch goal with Hi : 0 <= i <= 2, Hrq : rq = cq + 28 + 28 * i |- _ => rewrite (row_addr _ Hi Hrq eq_refl) end;
lazymatch o with 0 => replace (cq + (rq - cq)) with rq by lia | _ => replace (cq + o + (rq - cq)) with (rq + o) by lia end;
astep.

Lemma filt_row : forall (cr : list word) (t0 t1 t2 a0 a1 t3 t4 t5 t6 s6 s10 : word) (fc : bv 32) (m : mem),
0 <= i <= 2 -> rq = cq + 28 + 28 * i -> length cr = 7%nat -> fb = SHIFT_FILT + 28 * i ->
frm0 fc -> mem_inv asegs m ->
aobj asegs m SHIFT_FILT 84 -> aobj asegs m cq 112 -> cq mod 8 = 0 -> IMG_TOP <= cq -> (cq + 112 <= SH_LO \/ SH_HI <= cq) ->
rw_cells asegs m cq (f32 [x0; x1; x2; x3; x4; x5; x6]) -> rw_cells asegs m rq (f32 cr) ->
ro_cells asegs m fb (f32 [f0; f1; f2; f3; f4; f5; f6]) ->
evt asegs (row_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 3) (Z_to_bv 64 10) (Z_to_bv 64 fb) (Z_to_bv 64 7) (Z_to_bv 64 fb)
s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
(bvmap_set 15 fzero_s F) (Z_to_bv 64 0xa5ad0) fc None m (seg_rom asegs)).
Proof.
intros cr t0 t1 t2 a0 a1 t3 t4 t5 t6 s6 s10 fc m Hi Hrq LR Hfb FRM MI OBT OBC CQ8 CQI CQSH C0 CR RO.
pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP in OC1. pose proof CQI as CQI'. unfold IMG_TOP in CQI'. pose proof CQSH as CQSH'. unfold SH_LO, SH_HI in CQSH'.
pose proof (rw_cells_bound _ _ _ _ C0) as B0; rewrite cells_size_f32 in B0; cbn [length] in B0.
pose proof (rw_cells_bound _ _ _ _ CR) as BR; rewrite cells_size_f32, LR in BR.
pose proof (ro_cells_bound _ _ _ _ RO) as BF; rewrite cells_size_f32 in BF; cbn [length] in BF.
pose proof (munch_refl [(rq, rq + 28)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(rq, rq + 28)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (FB4 : fb mod 4 = 0) by (subst fb; unfold SHIFT_FILT; clear - Hi; Z.div_mod_to_equations; lia).
assert (CQ4 : cq mod 4 = 0) by (clear - CQ8; Z.div_mod_to_equations; lia).
unfold SHIFT_FILT in Hfb.
destruct cr as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|? ?]]]]]]]]; try (cbn in LR; lia).
rewrite !f32_cons, f32_nil in CR.

jiter [(rq, rq + 28)] OBT OBC CQSH 3 0 3%nat [x1; x2; x3] [f4; f5; f6] C0 RO. jtail 0.
jiter [(rq, rq + 28)] OBT OBC CQSH 2 0 4%nat [x1; x2; x3; x4] [f3; f4; f5; f6] C0 RO. jtail 4.
jiter [(rq, rq + 28)] OBT OBC CQSH 1 0 5%nat [x1; x2; x3; x4; x5] [f2; f3; f4; f5; f6] C0 RO. jtail 8.
jiter [(rq, rq + 28)] OBT OBC CQSH 0 0 6%nat [x1; x2; x3; x4; x5; x6] [f1; f2; f3; f4; f5; f6] C0 RO. jtail 12.
jiter [(rq, rq + 28)] OBT OBC CQSH 0 1 5%nat [x2; x3; x4; x5; x6] [f1; f2; f3; f4; f5] C0 RO. jtail 16.
jiter [(rq, rq + 28)] OBT OBC CQSH 0 2 4%nat [x3; x4; x5; x6] [f1; f2; f3; f4] C0 RO. jtail 20.
jiter [(rq, rq + 28)] OBT OBC CQSH 0 3 3%nat [x4; x5; x6] [f1; f2; f3] C0 RO. jtail 24.
ato 0xa5bd0.
apply evt_done; unfold row_post.
eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, [_; _; _; _; _; _; _]. split; [norm_fchain; reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact FRM|].
split; [rewrite !f32_cons, f32_nil; exact CR| reflexivity].
Qed.
End R.
