(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition itv := option (Z * Z).
Definition in_itv (x : Z) (i : itv) : Prop :=
match i with Some (l, h) => l <= x <= h | None => True end.
Lemma in_itv_None : forall x, in_itv x None. Proof. intros; exact I. Qed.
Definition itv_add (a b : itv) : itv :=
match a, b with Some (al, ah), Some (bl, bh) => Some (al + bl, ah + bh) | _, _ => None end.
Definition itv_sub (a b : itv) : itv :=
match a, b with Some (al, ah), Some (bl, bh) => Some (al - bh, ah - bl) | _, _ => None end.
Definition itv_scale (k : Z) (a : itv) : itv :=
match a with Some (l, h) => if 0 <=? k then Some (k * l, k * h) else None | None => None end.
Definition itv_shiftr (a : itv) (k : Z) : itv :=
match a with Some (l, h) => if 0 <=? k then Some (Z.shiftr l k, Z.shiftr h k) else None | None => None end.
Definition itv_div (a : itv) (k : Z) : itv :=
match a with Some (l, h) => if 0 <? k then Some (l / k, h / k) else None | None => None end.
Definition itv_within (lo hi : Z) (a : itv) : itv :=
match a with Some (l, h) => if (lo <=? l) && (h <? hi) then a else None | None => None end.
Definition itv_meet_hi (a : itv) (h' : Z) : itv :=
match a with Some (l, h) => Some (l, Z.min h h') | None => None end.
Lemma itv_add_sound : forall x y a b, in_itv x a -> in_itv y b -> in_itv (x + y) (itv_add a b).
Proof. intros x y [[? ?]|] [[? ?]|]; cbn; intros; try exact I. lia. Qed.
Lemma itv_sub_sound : forall x y a b, in_itv x a -> in_itv y b -> in_itv (x - y) (itv_sub a b).
Proof. intros x y [[? ?]|] [[? ?]|]; cbn; intros; try exact I. lia. Qed.
Lemma itv_scale_sound : forall k x a, in_itv x a -> in_itv (k * x) (itv_scale k a).
Proof.
intros k x [[l h]|]; cbn; intros; [|exact I].
destruct (0 <=? k) eqn:Hk; [|exact I]. apply Z.leb_le in Hk. cbn. nia.
Qed.
Lemma itv_shiftr_sound : forall x a k, in_itv x a -> in_itv (Z.shiftr x k) (itv_shiftr a k).
Proof.
intros x [[l h]|] k; cbn; intros; [|exact I].
destruct (0 <=? k) eqn:Hk; [|exact I]. apply Z.leb_le in Hk. cbn.
rewrite !Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
split; apply Z.div_le_mono; lia.
Qed.
Lemma itv_div_sound : forall x a k, in_itv x a -> in_itv (x / k) (itv_div a k).
Proof.
intros x [[l h]|] k; cbn; intros; [|exact I].
destruct (0 <? k) eqn:Hk; [|exact I]. apply Z.ltb_lt in Hk. cbn.
split; apply Z.div_le_mono; lia.
Qed.
Lemma itv_within_sound : forall lo hi x a, in_itv x a -> in_itv x (itv_within lo hi a).
Proof.
intros lo hi x [[l h]|]; cbn; intros; [|exact I].
destruct ((lo <=? l) && (h <? hi)); cbn; [lia| exact I].
Qed.
Lemma itv_within_bounds : forall lo hi a l h,
itv_within lo hi a = Some (l, h) -> lo <= l /\ h < hi /\ a = Some (l, h).
Proof.
intros lo hi [[l0 h0]|] l h; cbn; [|discriminate].
destruct (lo <=? l0) eqn:H1; destruct (h0 <? hi) eqn:H2; cbn; try discriminate.
intros H. injection H as <- <-. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
Qed.
Lemma itv_meet_hi_sound : forall x a h', in_itv x a -> x <= h' -> in_itv x (itv_meet_hi a h').
Proof. intros x [[l h]|] h'; cbn; intros; [lia| exact I]. Qed.
Definition s_of_u (a : itv) : itv :=
match a with
| Some (l, h) => if h <? half64 then Some (l, h)
else if half64 <=? l then Some (l - M64, h - M64) else None
| None => None
end.
Definition u_of_s (a : itv) : itv :=
match a with
| Some (l, h) => if 0 <=? l then Some (l, h)
else if h <? 0 then Some (l + M64, h + M64) else None
| None => None
end.
Lemma swrap64_of_unsigned : forall u, 0 <= u < M64 ->
bv_swrap 64 u = (if u <? half64 then u else u - M64).
Proof.
intros u Hu. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with half64. change (bv_modulus 64) with M64.
unfold half64, M64 in *.
destruct (u <? 2^63) eqn:H.
- apply Z.ltb_lt in H. rewrite Z.mod_small by lia. lia.
- apply Z.ltb_ge in H. rewrite <- (Z_mod_plus_full _ (-1)) .
rewrite Z.mod_small by lia. lia.
Qed.
Lemma s_of_u_sound : forall u a, 0 <= u < M64 -> in_itv u a -> in_itv (bv_swrap 64 u) (s_of_u a).
Proof.
intros u [[l h]|] Hu; cbn; intros H; [|exact I].
rewrite swrap64_of_unsigned by exact Hu.
destruct (h <? half64) eqn:H1.
- apply Z.ltb_lt in H1. cbn. destruct (u <? half64) eqn:H2; [lia|]. apply Z.ltb_ge in H2. lia.
- destruct (half64 <=? l) eqn:H3; [|exact I]. apply Z.leb_le in H3. cbn.
destruct (u <? half64) eqn:H2; [apply Z.ltb_lt in H2; lia| lia].
Qed.
Lemma wrap64_of_signed : forall s, - half64 <= s < half64 ->
bv_wrap 64 s = (if 0 <=? s then s else s + M64).
Proof.
intros s Hs. unfold bv_wrap. change (bv_modulus 64) with M64. unfold half64, M64 in *.
destruct (0 <=? s) eqn:H.
- apply Z.leb_le in H. apply Z.mod_small. lia.
- apply Z.leb_gt in H. rewrite <- (Z_mod_plus_full _ 1). rewrite Z.mod_small by lia. lia.
Qed.
Lemma u_of_s_sound : forall s a, - half64 <= s < half64 -> in_itv s a -> in_itv (bv_wrap 64 s) (u_of_s a).
Proof.
intros s [[l h]|] Hs; cbn; intros H; [|exact I].
rewrite wrap64_of_signed by exact Hs.
destruct (0 <=? l) eqn:H1.
- apply Z.leb_le in H1. cbn. destruct (0 <=? s) eqn:H2; [lia|]. apply Z.leb_gt in H2. lia.
- destruct (h <? 0) eqn:H3; [|exact I]. apply Z.ltb_lt in H3. cbn.
destruct (0 <=? s) eqn:H2; [apply Z.leb_le in H2; lia| lia].
Qed.
Lemma wrap64_id : forall z, 0 <= z < M64 -> bv_wrap 64 z = z.
Proof. intros. apply bv_wrap_small. change (bv_modulus 64) with M64. lia. Qed.
Lemma swrap64_id : forall z, - half64 <= z < half64 -> bv_swrap 64 z = z.
Proof. intros. apply bv_swrap_small. change (bv_half_modulus 64) with half64. lia. Qed.
Lemma swrap32_id : forall z, - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.
Lemma swrap_add_mod : forall n z k, bv_swrap n (z + k * bv_modulus n) = bv_swrap n z.
Proof.
intros n z k. rewrite <- (bv_swrap_wrap n (z + _)), <- (bv_swrap_wrap n z). f_equal.
unfold bv_wrap. apply Z_mod_plus_full.
Qed.
Lemma swrap_wrap' : forall n z, bv_swrap n (bv_wrap n z) = bv_swrap n z.
Proof. intros. apply bv_swrap_wrap. Qed.
Lemma swrap64_range : forall z, - half64 <= bv_swrap 64 z < half64.
Proof. intros. apply (bv_swrap_in_range 64). discriminate. Qed.
Lemma swrap32_range : forall z, - 2^31 <= bv_swrap 32 z < 2^31.
Proof. intros. apply (bv_swrap_in_range 32). discriminate. Qed.
Lemma signed_is_swrap_unsigned : forall (w : word), bv_signed w = bv_swrap 64 (bv_unsigned w).
Proof. intros w. reflexivity. Qed.
Lemma unsigned_is_wrap_signed : forall (w : word), bv_unsigned w = bv_wrap 64 (bv_signed w).
Proof.
intros w. unfold bv_signed, bv_swrap.
pose proof (u64_range w) as Hw.
change (bv_half_modulus 64) with half64. unfold bv_wrap. change (bv_modulus 64) with M64.
unfold half64, M64 in *.
destruct (Z_lt_le_dec (bv_unsigned w) (2^63)).
- rewrite (Z.mod_small (bv_unsigned w + 2^63)) by lia.
rewrite Z.mod_small by lia. lia.
- rewrite <- (Z_mod_plus_full (bv_unsigned w + 2^63) (-1)).
rewrite (Z.mod_small (bv_unsigned w + 2^63 + -1 * 2^64)) by lia.
rewrite <- (Z_mod_plus_full _ 1). rewrite Z.mod_small by lia. lia.
Qed.
Definition U (E : env) (v : sv) : Z := bv_unsigned (sv_denot E v).
Definition Sg (E : env) (v : sv) : Z := bv_signed (sv_denot E v).
Lemma U_range : forall E v, 0 <= U E v < M64.
Proof. intros. unfold U, M64. apply u64_range. Qed.
Lemma S_range : forall E v, - half64 <= Sg E v < half64.
Proof. intros. unfold Sg. rewrite signed_is_swrap_unsigned. apply swrap64_range. Qed.
Lemma S_of_U : forall E v, Sg E v = bv_swrap 64 (U E v).
Proof. intros. reflexivity. Qed.
Lemma U_of_S : forall E v, U E v = bv_wrap 64 (Sg E v).
Proof. intros. unfold U, Sg. apply unsigned_is_wrap_signed. Qed.
Lemma denot_lit_U : forall E v, sv_denot E v = Z_to_bv 64 (U E v).
Proof. intros. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma zcanon_id : forall z, 0 <= z < M64 -> zcanon z = z.
Proof. intros. unfold zcanon. apply Z.mod_small. lia. Qed.
Lemma zcanon_wrap : forall z, zcanon z = bv_wrap 64 z.
Proof. reflexivity. Qed.
Lemma modM64_wrap : forall z, z mod M64 = bv_wrap 64 z.
Proof. reflexivity. Qed.
Ltac wrap64_solve :=
unfold zcanon; rewrite ?modM64_wrap;
first [ bv_wrap_simplify_solve | apply (f_equal (bv_wrap 64)); lia ].
Lemma U_SLit : forall E z, U E (SLit z) = zcanon z.
Proof. intros. unfold U. cbn [sv_denot]. apply unsigned_lit. Qed.
Lemma S_SLit : forall E z, Sg E (SLit z) = bv_swrap 64 z.
Proof.
intros. rewrite S_of_U, U_SLit, zcanon_wrap. apply bv_swrap_wrap.
Qed.
Lemma U_SOff : forall E n x, U E (SOff n x) = zcanon (bv_unsigned (ew E n) + x).
Proof. intros. unfold U. apply denot_SOff. Qed.
Lemma S_SOff : forall E n x, Sg E (SOff n x) = bv_swrap 64 (bv_unsigned (ew E n) + x).
Proof.
intros. rewrite S_of_U, U_SOff, zcanon_wrap. apply bv_swrap_wrap.
Qed.
Lemma U_SAlu : forall E op a b,
U E (SAlu op a b) = zcanon (zalu_raw 63 64 op (U E a) (U E b)).
Proof.
intros. unfold U at 1. cbn [sv_denot].
rewrite (denot_lit_U E a), (denot_lit_U E b), zalu64_sound, unsigned_lit.
unfold zalu64. pose proof (U_range E a). pose proof (U_range E b).
rewrite !(zcanon_id (U E a)), !(zcanon_id (U E b)) by lia.
unfold zcanon. apply Zmod_mod.
Qed.
Lemma S_SAlu : forall E op a b,
Sg E (SAlu op a b) = bv_swrap 64 (zalu_raw 63 64 op (U E a) (U E b)).
Proof.
intros. rewrite S_of_U, U_SAlu, zcanon_wrap. apply bv_swrap_wrap.
Qed.
Lemma swrap64_zcanon_swrap32 : forall z, bv_swrap 64 (zcanon (bv_swrap 32 z)) = bv_swrap 32 z.
Proof.
intros z. rewrite zcanon_wrap, (bv_swrap_wrap 64).
apply swrap64_id. pose proof (swrap32_range z). unfold half64. lia.
Qed.
Lemma S_SAluw : forall E op a b,
Sg E (SAluw op a b) = bv_swrap 32 (zalu_raw 31 32 op (U E a mod 2^32) (U E b mod 2^32)).
Proof.
intros. unfold Sg. cbn [sv_denot].
rewrite (denot_lit_U E a), (denot_lit_U E b), zalu32_sound, signed_lit.
unfold zalu32. fold (zcanon (bv_swrap 32 (zalu_raw 31 32 op (zu32 (U E a)) (zu32 (U E b))))).
rewrite zcanon_id by apply zcanon_range.
apply swrap64_zcanon_swrap32.
Qed.
Lemma U_SMd : forall E op a b,
U E (SMd op a b) = zcanon (zmd_raw 64 op (U E a) (U E b)).
Proof.
intros. unfold U at 1. cbn [sv_denot].
rewrite (denot_lit_U E a), (denot_lit_U E b), zmd64_sound, unsigned_lit.
unfold zmd64. pose proof (U_range E a). pose proof (U_range E b).
rewrite !(zcanon_id (U E a)), !(zcanon_id (U E b)) by lia.
unfold zcanon. apply Zmod_mod.
Qed.
Lemma S_SMdw : forall E op a b,
Sg E (SMdw op a b) = bv_swrap 32 (zmd_raw 32 op (U E a mod 2^32) (U E b mod 2^32)).
Proof.
intros. unfold Sg. cbn [sv_denot].
rewrite (denot_lit_U E a), (denot_lit_U E b), zmd32_sound, signed_lit.
unfold zmd32. fold (zcanon (bv_swrap 32 (zmd_raw 32 op (zu32 (U E a)) (zu32 (U E b))))).
rewrite zcanon_id by apply zcanon_range.
apply swrap64_zcanon_swrap32.
Qed.
Lemma U_SExt : forall E sg w a,
U E (SExt sg w a) = zcanon (if sg then bv_swrap w (U E a mod 2 ^ Z.of_N w) else U E a mod 2 ^ Z.of_N w).
Proof.
intros. unfold U at 1. cbn [sv_denot]. rewrite (denot_lit_U E a).
rewrite zext_low_sound, unsigned_lit. unfold zext_low.
pose proof (U_range E a). rewrite (zcanon_id (U E a)) by lia.
unfold zcanon at 1. unfold zcanon at 2. apply Zmod_mod.
Qed.
Lemma U_S_mod : forall E v k, 0 <= k <= 64 -> U E v mod 2^k = Sg E v mod 2^k.
Proof.
intros E v k Hk. rewrite U_of_S. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.mod_mod_divide. exists (2^(64-k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Definition rng := (itv * itv)%type.
Definition rng_none : rng := (None, None).
Definition rng_of_u (u : itv) : rng := (u, s_of_u u).
Definition rng_of_s (s : itv) : rng := (u_of_s s, s).
Definition rng_ok (u : Z) (r : rng) : Prop :=
in_itv u (fst r) /\ in_itv (bv_swrap 64 u) (snd r).
Lemma rng_ok_none : forall u, rng_ok u rng_none.
Proof. intros. split; exact I. Qed.
Lemma rng_of_u_ok : forall u i, 0 <= u < M64 -> in_itv u i -> rng_ok u (rng_of_u i).
Proof. intros u i Hu Hi. split; [exact Hi| apply s_of_u_sound; assumption]. Qed.
Lemma wrap64_swrap64 : forall u, 0 <= u < M64 -> bv_wrap 64 (bv_swrap 64 u) = u.
Proof.
intros u Hu. rewrite swrap64_of_unsigned by exact Hu.
unfold bv_wrap. change (bv_modulus 64) with M64. unfold half64, M64 in *.
destruct (u <? 2^63) eqn:H.
- apply Z.mod_small. lia.
- apply Z.ltb_ge in H. rewrite <- (Z_mod_plus_full _ 1). rewrite Z.mod_small; lia.
Qed.
Lemma rng_of_s_ok : forall u i, 0 <= u < M64 -> in_itv (bv_swrap 64 u) i -> rng_ok u (rng_of_s i).
Proof.
intros u i Hu Hi. split; [|exact Hi]. cbn [fst rng_of_s].
rewrite <- (wrap64_swrap64 u Hu) at 1.
apply u_of_s_sound; [apply swrap64_range| exact Hi].
Qed.
Definition two31 : Z := 2 ^ 31.
Definition two32 : Z := 2 ^ 32.
Definition lit_shamt (mask : Z) (b : sv) : option Z :=
match b with SLit s => Some (Z.land (zcanon s) mask) | _ => None end.
Lemma lit_shamt_nonneg : forall mask b k, 0 <= mask -> lit_shamt mask b = Some k -> 0 <= k <= mask.
Proof.
intros mask b k Hm H. destruct b; cbn in H; try discriminate. injection H as <-.
pose proof (Z_land_upper (zcanon z) mask Hm). lia.
Qed.
Definition rng_alu (op : aluop) (b : sv) (ra rb : rng) : rng :=
let '(ua, sa) := ra in let '(ub, sb) := rb in
match op with
| ALU_ADD => (itv_within 0 M64 (itv_add ua ub), itv_within (- half64) half64 (itv_add sa sb))
| ALU_SUB => (itv_within 0 M64 (itv_sub ua ub), itv_within (- half64) half64 (itv_sub sa sb))
| ALU_SLL => match lit_shamt 63 b with
| Some k => rng_of_u (itv_within 0 M64 (itv_scale (2 ^ k) ua))
| None => rng_none end
| ALU_SRL => match lit_shamt 63 b with
| Some k => rng_of_u (itv_shiftr ua k)
| None => rng_none end
| ALU_SRA => match lit_shamt 63 b with
| Some k => rng_of_s (itv_shiftr sa k)
| None => rng_none end
| ALU_AND => match ua, ub with
| Some (_, ah), Some (_, bh) => rng_of_u (Some (0, Z.min ah bh))
| None, Some (_, bh) => rng_of_u (Some (0, bh))
| Some (_, ah), None => rng_of_u (Some (0, ah))
| None, None => rng_none end
| ALU_OR | ALU_XOR => rng_of_u (itv_within 0 M64 (match ua, ub with
| Some (_, ah), Some (_, bh) => Some (0, ah + bh) | _, _ => None end))
| ALU_SLT | ALU_SLTU => rng_of_u (Some (0, 1))
end.
Definition rng_aluw (op : aluop) (b : sv) (ra rb : rng) : rng :=
let '(ua, sa) := ra in let '(ub, sb) := rb in
match op with
| ALU_ADD => rng_of_s (itv_within (- two31) two31
(itv_add (itv_within (- two31) two31 sa) (itv_within (- two31) two31 sb)))
| ALU_SUB => rng_of_s (itv_within (- two31) two31
(itv_sub (itv_within (- two31) two31 sa) (itv_within (- two31) two31 sb)))
| ALU_SLL => match lit_shamt 31 b with
| Some k => rng_of_s (itv_within 0 two31 (itv_scale (2 ^ k) (itv_within 0 two32 ua)))
| None => rng_none end
| ALU_SRL => match lit_shamt 31 b with
| Some k => rng_of_s (itv_within 0 two31 (itv_shiftr (itv_within 0 two32 ua) k))
| None => rng_none end
| ALU_SRA => match lit_shamt 31 b with
| Some k => rng_of_s (itv_shiftr (itv_within (- two31) two31 sa) k)
| None => rng_none end
| ALU_AND => match itv_within 0 two31 ub with
| Some (_, bh) => rng_of_s (Some (0, bh))
| None => rng_none end
| _ => rng_none
end.
Definition lit_val (b : sv) : option Z :=
match b with SLit z => Some (zcanon z) | _ => None end.
Definition rng_md (op : mulop) (a b : sv) (ra rb : rng) : rng :=
let '(ua, sa) := ra in let '(ub, sb) := rb in
match op with
| M_MUL => match lit_val b, lit_val a with
| Some k, _ => rng_of_u (itv_within 0 M64 (itv_scale k ua))
| None, Some k => rng_of_u (itv_within 0 M64 (itv_scale k ub))
| None, None => rng_none end
| M_DIVU => match lit_val b with
| Some k => if 0 <? k then rng_of_u (itv_div ua k) else rng_none
| None => rng_none end
| M_REMU => match lit_val b with
| Some k => if 0 <? k then rng_of_u (itv_meet_hi (Some (0, k - 1))
(match ua with Some (_, ah) => ah | None => k end))
else rng_none
| None => rng_none end
| _ => rng_none
end.
Definition rng_mdw (op : mulop) (a b : sv) (ra rb : rng) : rng :=
let '(ua, sa) := ra in let '(ub, sb) := rb in
match op with
| M_MUL => match lit_val b with
| Some k => if k <? two32 then
rng_of_s (itv_within 0 two31 (itv_scale k (itv_within 0 two32 ua)))
else rng_none
| None => rng_none end
| M_DIVU => match lit_val b with
| Some k => if (0 <? k) && (k <? two32) then
rng_of_s (itv_within 0 two31 (itv_div (itv_within 0 two32 ua) k))
else rng_none
| None => rng_none end
| M_REMU => match lit_val b with
| Some k => if (0 <? k) && (k <=? two31) then
match itv_within 0 two32 ua with
| Some (_, ah) => rng_of_s (Some (0, Z.min ah (k - 1)))
| None => rng_none
end
else rng_none
| None => rng_none end
| _ => rng_none
end.
Definition rng_ext (sg : bool) (w : N) (ra : rng) : rng :=
let '(ua, sa) := ra in
let wz := Z.of_N w in
if sg then
if (0 <? wz) && (wz <=? 64) then
rng_of_s (match itv_within (- 2 ^ (wz - 1)) (2 ^ (wz - 1)) sa with
| Some i => Some i
| None => Some (- 2 ^ (wz - 1), 2 ^ (wz - 1) - 1)
end)
else rng_none
else
if (0 <=? wz) && (wz <=? 64) then
rng_of_u (match itv_within 0 (2 ^ wz) ua with
| Some i => Some i
| None => Some (0, 2 ^ wz - 1)
end)
else rng_none.
Fixpoint sv_ranges (G : facts) (v : sv) : rng :=
match v with
| SLit z => let u := zcanon z in (Some (u, u), Some (bv_swrap 64 u, bv_swrap 64 u))
| SOff n x =>
match atom_lookup (f_atoms G) n with
| Some f => let i := Some (af_lo f + x, af_hi f + x) in
(itv_within 0 M64 i, itv_within (- half64) half64 i)
| None => rng_none
end
| SData d i n => if (Z.of_N n <? 8) then rng_of_u (Some (0, 2 ^ (8 * Z.of_N n) - 1)) else rng_none
| SAlu op a b => rng_alu op b (sv_ranges G a) (sv_ranges G b)
| SAluw op a b => rng_aluw op b (sv_ranges G a) (sv_ranges G b)
| SMd op a b => rng_md op a b (sv_ranges G a) (sv_ranges G b)
| SMdw op a b => rng_mdw op a b (sv_ranges G a) (sv_ranges G b)
| SExt sg w a => rng_ext sg w (sv_ranges G a)
| SF2 (FP2_cmp _ _) _ _ => rng_of_u (Some (0, 1))
| SF1 _ _ | SF2 _ _ _ | SF3 _ _ _ _ => rng_none
end.
Definition sv_urange (G : facts) (v : sv) : itv := fst (sv_ranges G v).
Definition sv_srange (G : facts) (v : sv) : itv := snd (sv_ranges G v).
Lemma swrap64_congr : forall a b, (a - b) mod M64 = 0 -> bv_swrap 64 a = bv_swrap 64 b.
Proof.
intros a b H. rewrite <- (bv_swrap_wrap 64 a), <- (bv_swrap_wrap 64 b). f_equal.
unfold bv_wrap. change (bv_modulus 64) with M64. unfold M64 in *.
apply Z.mod_divide in H; [|lia]. destruct H as [k Hk].
replace a with (b + k * 2^64) by lia. apply Z_mod_plus_full.
Qed.
Lemma swrap64_self_congr : forall u, (u - bv_swrap 64 u) mod M64 = 0.
Proof.
intros u. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with M64.
change (bv_half_modulus 64) with half64. unfold M64, half64.
pose proof (Z.div_mod (u + 2^63) (2^64) ltac:(lia)) as Hd.
set (q := (u + 2^63) / 2^64) in *.
replace (u - ((u + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63)) with (q * 2^64) by lia.
apply Z_mod_mult.
Qed.
Lemma swrap32_congr : forall a b, (a - b) mod two32 = 0 -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
intros a b H. rewrite <- (bv_swrap_wrap 32 a), <- (bv_swrap_wrap 32 b). f_equal.
unfold bv_wrap. change (bv_modulus 32) with two32. unfold two32 in *.
apply Z.mod_divide in H; [|lia]. destruct H as [k Hk].
replace a with (b + k * 2^32) by lia. apply Z_mod_plus_full.
Qed.
Lemma swrap64_self_congr32 : forall u, (u - bv_swrap 64 u) mod two32 = 0.
Proof.
intros u. pose proof (swrap64_self_congr u) as H. unfold M64, two32 in *.
apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. rewrite Hk.
replace (k * 2^64) with ((k * 2^32) * 2^32) by lia. apply Z_mod_mult.
Qed.
Lemma mod32_sub0 : forall a b, a mod two32 = b mod two32 -> (a - b) mod two32 = 0.
Proof.
intros a b H. unfold two32 in *. rewrite Zminus_mod, H, Z.sub_diag. reflexivity.
Qed.
Section g.
Variables (Ua Ub : Z).
Hypothesis HUa : 0 <= Ua < M64.
Hypothesis HUb : 0 <= Ub < M64.
Let Sa := bv_swrap 64 Ua.
Let Sb := bv_swrap 64 Ub.
Lemma Sa_range : - half64 <= Sa < half64. Proof. apply swrap64_range. Qed.
Lemma Sb_range : - half64 <= Sb < half64. Proof. apply swrap64_range. Qed.
Lemma rng_alu_sound : forall op b ra rb,
rng_ok Ua ra -> rng_ok Ub rb ->
(forall s, b = SLit s -> Ub = zcanon s) ->
rng_ok (zcanon (zalu_raw 63 64 op Ua Ub)) (rng_alu op b ra rb).
Proof.
intros op b [ua sa] [ub sb] [Hua Hsa] [Hub Hsb] Hb. cbn [fst snd] in *.
pose proof Sa_range as HSa. pose proof Sb_range as HSb.
assert (Hsw : forall r, bv_swrap 64 (zcanon r) = bv_swrap 64 r).
{ intros r. rewrite zcanon_wrap. apply bv_swrap_wrap. }
destruct op; cbn [rng_alu zalu_raw].
-   split; cbn [fst snd].
+ pose proof (itv_add_sound _ _ _ _ Hua Hub) as H.
destruct (itv_within 0 M64 (itv_add ua ub)) as [[l h]|] eqn:Hw; [|exact I].
apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in H. cbn in H |- *.
rewrite zcanon_id by lia. lia.
+ rewrite Hsw. pose proof (itv_add_sound _ _ _ _ Hsa Hsb) as H.
destruct (itv_within (- half64) half64 (itv_add sa sb)) as [[l h]|] eqn:Hw; [|exact I].
apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in H. cbn in H |- *.
rewrite (swrap64_congr (Ua + Ub) (Sa + Sb)).
* rewrite swrap64_id by lia. lia.
* replace (Ua + Ub - (Sa + Sb)) with ((Ua - Sa) + (Ub - Sb)) by lia.
unfold M64. rewrite Zplus_mod. fold M64. subst Sa Sb. rewrite !swrap64_self_congr. reflexivity.
-   split; cbn [fst snd].
+ pose proof (itv_sub_sound _ _ _ _ Hua Hub) as H.
destruct (itv_within 0 M64 (itv_sub ua ub)) as [[l h]|] eqn:Hw; [|exact I].
apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in H. cbn in H |- *.
rewrite zcanon_id by lia. lia.
+ rewrite Hsw. pose proof (itv_sub_sound _ _ _ _ Hsa Hsb) as H.
destruct (itv_within (- half64) half64 (itv_sub sa sb)) as [[l h]|] eqn:Hw; [|exact I].
apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in H. cbn in H |- *.
rewrite (swrap64_congr (Ua - Ub) (Sa - Sb)).
* rewrite swrap64_id by lia. lia.
* replace (Ua - Ub - (Sa - Sb)) with ((Ua - Sa) - (Ub - Sb)) by lia.
unfold M64. rewrite Zminus_mod. fold M64. subst Sa Sb. rewrite !swrap64_self_congr. reflexivity.
-   destruct (lit_shamt 63 b) as [k|] eqn:Hk; [|apply rng_ok_none].
pose proof (lit_shamt_nonneg 63 b k ltac:(lia) Hk) as Hkr.
assert (Hland : Z.land Ub 63 = k).
{ destruct b; cbn in Hk; try discriminate. injection Hk as <-. rewrite (Hb z eq_refl). reflexivity. }
rewrite Hland. rewrite Z.shiftl_mul_pow2 by lia.
pose proof (itv_scale_sound (2^k) Ua ua Hua) as H. rewrite Z.mul_comm in H.
destruct (itv_within 0 M64 (itv_scale (2 ^ k) ua)) as [[l h]|] eqn:Hw.
+ apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in H. cbn in H.
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| cbn; lia].
+ apply rng_of_u_ok; [apply zcanon_range| exact I].
-   apply rng_of_u_ok; [apply zcanon_range|]. cbn. destruct (_ <? _); rewrite zcanon_id; unfold M64; lia.
-   apply rng_of_u_ok; [apply zcanon_range|]. cbn. destruct (_ <? _); rewrite zcanon_id; unfold M64; lia.
-
assert (Hx : 0 <= Z.lxor Ua Ub) by (apply Z.lxor_nonneg; lia).
assert (Hl : 0 <= Z.land Ua Ub) by (apply Z.land_nonneg; lia).
pose proof (Z.add_lxor_2land Ua Ub) as Hsum.
destruct ua as [[al ah]|]; destruct ub as [[bl bh]|]; cbn [itv_within];
try (apply rng_of_u_ok; [apply zcanon_range| exact I]).
cbn in Hua, Hub.
destruct ((0 <=? 0) && (ah + bh <? M64)) eqn:Hw; [|apply rng_of_u_ok; [apply zcanon_range| exact I]].
apply andb_prop in Hw as [_ Hw]. apply Z.ltb_lt in Hw.
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| cbn; lia].
-   destruct (lit_shamt 63 b) as [k|] eqn:Hk; [|apply rng_ok_none].
pose proof (lit_shamt_nonneg 63 b k ltac:(lia) Hk) as Hkr.
assert (Hland : Z.land Ub 63 = k).
{ destruct b; cbn in Hk; try discriminate. injection Hk as <-. rewrite (Hb z eq_refl). reflexivity. }
rewrite Hland.
pose proof (itv_shiftr_sound Ua ua k Hua) as H.
assert (Hr : 0 <= Z.shiftr Ua k <= Ua).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| exact H].
-   destruct (lit_shamt 63 b) as [k|] eqn:Hk; [|apply rng_ok_none].
pose proof (lit_shamt_nonneg 63 b k ltac:(lia) Hk) as Hkr.
assert (Hland : Z.land Ub 63 = k).
{ destruct b; cbn in Hk; try discriminate. injection Hk as <-. rewrite (Hb z eq_refl). reflexivity. }
rewrite Hland. fold Sa.
pose proof (itv_shiftr_sound Sa sa k Hsa) as H.
assert (Hr : - half64 <= Z.shiftr Sa k < half64).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
unfold half64 in *. split.
- apply Z.div_le_lower_bound; [lia|]. nia.
- apply Z.div_lt_upper_bound; [lia|]. nia. }
apply rng_of_s_ok; [apply zcanon_range|].
rewrite Hsw. rewrite swrap64_id by exact Hr. exact H.
-
assert (Hx : 0 <= Z.lor Ua Ub) by (apply Z.lor_nonneg; lia).
assert (Hl : 0 <= Z.land Ua Ub) by (apply Z.land_nonneg; lia).
pose proof (Z.add_lor_land Ua Ub) as Hsum.
destruct ua as [[al ah]|]; destruct ub as [[bl bh]|]; cbn [itv_within];
try (apply rng_of_u_ok; [apply zcanon_range| exact I]).
cbn in Hua, Hub.
destruct ((0 <=? 0) && (ah + bh <? M64)) eqn:Hw; [|apply rng_of_u_ok; [apply zcanon_range| exact I]].
apply andb_prop in Hw as [_ Hw]. apply Z.ltb_lt in Hw.
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| cbn; lia].
-
assert (Hl : 0 <= Z.land Ua Ub) by (apply Z.land_nonneg; lia).
pose proof (Z_land_upper_l Ua Ub ltac:(lia) ltac:(lia)) as H1.
pose proof (Z_land_upper Ua Ub ltac:(lia)) as H2.
rewrite zcanon_id by lia.
destruct ua as [[al ah]|]; destruct ub as [[bl bh]|]; cbn in Hua, Hub;
try apply rng_ok_none; apply rng_of_u_ok; try lia; cbn; lia.
Qed.
End g.
Section j.
Variables (Ua Ub : Z).
Hypothesis HUa : 0 <= Ua < M64.
Hypothesis HUb : 0 <= Ub < M64.
Let Sa := bv_swrap 64 Ua.
Let Sb := bv_swrap 64 Ub.
Lemma U_mod32_S : forall u, (u mod two32 - bv_swrap 64 u mod two32) mod two32 = 0.
Proof.
intros u. unfold two32. rewrite <- Zminus_mod. apply swrap64_self_congr32.
Qed.
Lemma rng_aluw_sound : forall op b ra rb,
rng_ok Ua ra -> rng_ok Ub rb ->
(forall s, b = SLit s -> Ub = zcanon s) ->
rng_ok (zcanon (bv_swrap 32 (zalu_raw 31 32 op (Ua mod 2^32) (Ub mod 2^32)))) (rng_aluw op b ra rb).
Proof.
intros op b [ua sa] [ub sb] [Hua Hsa] [Hub Hsb] Hb. cbn [fst snd] in *.
pose proof (swrap64_range Ua) as HSa. pose proof (swrap64_range Ub) as HSb. fold Sa in HSa, Hsa. fold Sb in HSb, Hsb.
assert (HS32 : forall r, bv_swrap 64 (zcanon (bv_swrap 32 r)) = bv_swrap 32 r) by apply swrap64_zcanon_swrap32.
assert (Hm32a : 0 <= Ua mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
assert (Hm32b : 0 <= Ub mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
destruct op; cbn [rng_aluw zalu_raw]; try apply rng_ok_none.
-
destruct (itv_within (- two31) two31 sa) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
destruct (itv_within (- two31) two31 sb) as [[bl bh]|] eqn:Hwb;
[apply itv_within_bounds in Hwb as (Hb1 & Hb2 & Hb3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst sa sb. cbn in Hsa, Hsb. cbn [itv_add].
destruct (itv_within (- two31) two31 (Some (al + bl, ah + bh))) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
injection H3 as <- <-.
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32.
rewrite (swrap32_congr _ (Sa + Sb)).
+ unfold two31 in *. rewrite swrap32_id by lia. cbn. lia.
+ replace (Ua mod 2 ^ 32 + Ub mod 2 ^ 32 - (Sa + Sb)) with ((Ua mod two32 - Sa mod two32) + (Ub mod two32 - Sb mod two32) + (Sa mod two32 - Sa) + (Sb mod two32 - Sb)) by (unfold two32; lia).
unfold two32. rewrite Zplus_mod. rewrite (Zplus_mod (_ + _)). rewrite (Zplus_mod (Ua mod _ - _)).
fold two32. subst Sa Sb. rewrite !U_mod32_S.
assert (Hmm : forall z, (z mod two32 - z) mod two32 = 0).
{ intros z. unfold two32. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
rewrite !Hmm. reflexivity.
-
destruct (itv_within (- two31) two31 sa) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
destruct (itv_within (- two31) two31 sb) as [[bl bh]|] eqn:Hwb;
[apply itv_within_bounds in Hwb as (Hb1 & Hb2 & Hb3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst sa sb. cbn in Hsa, Hsb. cbn [itv_sub].
destruct (itv_within (- two31) two31 (Some (al - bh, ah - bl))) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
injection H3 as <- <-.
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32.
rewrite (swrap32_congr _ (Sa - Sb)).
+ unfold two31 in *. rewrite swrap32_id by lia. cbn. lia.
+ replace (Ua mod 2 ^ 32 - Ub mod 2 ^ 32 - (Sa - Sb)) with ((Ua mod two32 - Sa mod two32) - (Ub mod two32 - Sb mod two32) + (Sa mod two32 - Sa) - (Sb mod two32 - Sb)) by (unfold two32; lia).
unfold two32. rewrite Zminus_mod. rewrite (Zplus_mod (_ - _)). rewrite (Zminus_mod (Ua mod _ - _)).
fold two32. subst Sa Sb. rewrite !U_mod32_S.
assert (Hmm : forall z, (z mod two32 - z) mod two32 = 0).
{ intros z. unfold two32. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
rewrite !Hmm. reflexivity.
-   destruct (lit_shamt 31 b) as [k|] eqn:Hk; [|apply rng_ok_none].
pose proof (lit_shamt_nonneg 31 b k ltac:(lia) Hk) as Hkr.
assert (Hland : Z.land (Ub mod 2^32) 31 = k).
{ destruct b; cbn in Hk; try discriminate. injection Hk as <-. rewrite (Hb z eq_refl).
rewrite <- (Z.land_ones (zcanon z) 32) by lia.  rewrite <- Z.land_assoc.
change (Z.land (Z.ones 32) 31) with 31. reflexivity. }
rewrite Hland. rewrite Z.shiftl_mul_pow2 by lia.
destruct (itv_within 0 two32 ua) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | cbn; apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst ua. cbn in Hua.
pose proof (itv_scale_sound (2^k) Ua (Some (al, ah)) Hua) as H.
destruct (itv_within 0 two31 (itv_scale (2 ^ k) (Some (al, ah)))) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
rewrite H3 in H. cbn in H.
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32.
unfold two31, two32 in *. rewrite (Z.mod_small Ua) by lia.
rewrite Z.mul_comm. rewrite swrap32_id by lia. cbn. lia.
-   destruct (lit_shamt 31 b) as [k|] eqn:Hk; [|apply rng_ok_none].
pose proof (lit_shamt_nonneg 31 b k ltac:(lia) Hk) as Hkr.
assert (Hland : Z.land (Ub mod 2^32) 31 = k).
{ destruct b; cbn in Hk; try discriminate. injection Hk as <-. rewrite (Hb z eq_refl).
rewrite <- (Z.land_ones (zcanon z) 32) by lia.  rewrite <- Z.land_assoc.
change (Z.land (Z.ones 32) 31) with 31. reflexivity. }
rewrite Hland.
destruct (itv_within 0 two32 ua) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | cbn; apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst ua. cbn in Hua.
pose proof (itv_shiftr_sound Ua (Some (al, ah)) k Hua) as H.
destruct (itv_within 0 two31 (itv_shiftr (Some (al, ah)) k)) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
rewrite H3 in H. cbn in H.
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32.
unfold two31, two32 in *. rewrite (Z.mod_small Ua) by lia.
rewrite swrap32_id by lia. cbn. lia.
-   destruct (lit_shamt 31 b) as [k|] eqn:Hk; [|apply rng_ok_none].
pose proof (lit_shamt_nonneg 31 b k ltac:(lia) Hk) as Hkr.
assert (Hland : Z.land (Ub mod 2^32) 31 = k).
{ destruct b; cbn in Hk; try discriminate. injection Hk as <-. rewrite (Hb z eq_refl).
rewrite <- (Z.land_ones (zcanon z) 32) by lia.  rewrite <- Z.land_assoc.
change (Z.land (Z.ones 32) 31) with 31. reflexivity. }
rewrite Hland.
destruct (itv_within (- two31) two31 sa) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | cbn; apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst sa. cbn in Hsa.
assert (Hs32 : bv_swrap 32 (Ua mod 2^32) = Sa).
{ rewrite (swrap32_congr _ Sa); [unfold two31 in *; apply swrap32_id; lia|].
replace (Ua mod 2 ^ 32 - Sa) with ((Ua mod two32 - Sa mod two32) + (Sa mod two32 - Sa)) by (unfold two32; lia).
unfold two32. rewrite Zplus_mod. fold two32. subst Sa. rewrite U_mod32_S.
unfold two32. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
rewrite Hs32.
pose proof (itv_shiftr_sound Sa (Some (al, ah)) k Hsa) as H.
assert (Hr : - two31 <= Z.shiftr Sa k < two31).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
unfold two31 in *. split.
- apply Z.div_le_lower_bound; [lia|]. nia.
- apply Z.div_lt_upper_bound; [lia|]. nia. }
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32.
unfold two31 in *. rewrite swrap32_id by lia. exact H.
-
destruct (itv_within 0 two31 ub) as [[bl bh]|] eqn:Hwb;
[apply itv_within_bounds in Hwb as (Hb1 & Hb2 & Hb3) | apply rng_ok_none].
subst ub. cbn in Hub.
assert (Hl : 0 <= Z.land (Ua mod 2^32) (Ub mod 2^32)) by (apply Z.land_nonneg; lia).
pose proof (Z_land_upper (Ua mod 2^32) (Ub mod 2^32) ltac:(lia)) as H2.
unfold two31 in *. rewrite (Z.mod_small Ub) in * by lia.
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32.
rewrite swrap32_id by lia. cbn. lia.
Qed.
End j.
Section o.
Variables (Ua Ub : Z).
Hypothesis HUa : 0 <= Ua < M64.
Hypothesis HUb : 0 <= Ub < M64.
Lemma rng_md_sound : forall op a b ra rb,
rng_ok Ua ra -> rng_ok Ub rb ->
(forall s, a = SLit s -> Ua = zcanon s) ->
(forall s, b = SLit s -> Ub = zcanon s) ->
rng_ok (zcanon (zmd_raw 64 op Ua Ub)) (rng_md op a b ra rb).
Proof.
intros op a b [ua sa] [ub sb] [Hua Hsa] [Hub Hsb] Ha Hb. cbn [fst snd] in *.
destruct op; cbn [rng_md zmd_raw]; try apply rng_ok_none.
-   destruct (lit_val b) as [k|] eqn:Hk.
+ assert (HUbk : Ub = k) by (destruct b; cbn in Hk; try discriminate; injection Hk as <-; apply Hb; reflexivity).
subst Ub. pose proof (itv_scale_sound k Ua ua Hua) as H.
destruct (itv_within 0 M64 (itv_scale k ua)) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_u_ok; [apply zcanon_range| exact I]].
rewrite H3 in H. cbn in H. rewrite Z.mul_comm in H.
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| cbn; lia].
+ destruct (lit_val a) as [k|] eqn:Hka; [|apply rng_ok_none].
assert (HUak : Ua = k) by (destruct a; cbn in Hka; try discriminate; injection Hka as <-; apply Ha; reflexivity).
subst Ua. pose proof (itv_scale_sound k Ub ub Hub) as H.
destruct (itv_within 0 M64 (itv_scale k ub)) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_u_ok; [apply zcanon_range| exact I]].
rewrite H3 in H. cbn in H.
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| cbn; lia].
-   destruct (lit_val b) as [k|] eqn:Hk; [|apply rng_ok_none].
assert (HUbk : Ub = k) by (destruct b; cbn in Hk; try discriminate; injection Hk as <-; apply Hb; reflexivity).
subst Ub. destruct (0 <? k) eqn:Hk0; [|apply rng_ok_none]. apply Z.ltb_lt in Hk0.
replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (itv_div_sound Ua ua k Hua) as H.
assert (0 <= Ua / k <= Ua).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia| exact H].
-   destruct (lit_val b) as [k|] eqn:Hk; [|apply rng_ok_none].
assert (HUbk : Ub = k) by (destruct b; cbn in Hk; try discriminate; injection Hk as <-; apply Hb; reflexivity).
subst Ub. destruct (0 <? k) eqn:Hk0; [|apply rng_ok_none]. apply Z.ltb_lt in Hk0.
replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.mod_pos_bound Ua k Hk0) as Hm.
assert (Ua mod k <= Ua) by (apply Z.mod_le; lia).
rewrite zcanon_id by lia. apply rng_of_u_ok; [lia|].
destruct ua as [[al ah]|]; cbn in Hua |- *; lia.
Qed.
Lemma rng_mdw_sound : forall op a b ra rb,
rng_ok Ua ra -> rng_ok Ub rb ->
(forall s, b = SLit s -> Ub = zcanon s) ->
rng_ok (zcanon (bv_swrap 32 (zmd_raw 32 op (Ua mod 2^32) (Ub mod 2^32)))) (rng_mdw op a b ra rb).
Proof.
intros op a b [ua sa] [ub sb] [Hua Hsa] [Hub Hsb] Hb. cbn [fst snd] in *.
assert (HS32 : forall r, bv_swrap 64 (zcanon (bv_swrap 32 r)) = bv_swrap 32 r) by apply swrap64_zcanon_swrap32.
assert (Hm32a : 0 <= Ua mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
destruct op; cbn [rng_mdw zmd_raw]; try apply rng_ok_none.
-   destruct (lit_val b) as [k|] eqn:Hk; [|apply rng_ok_none].
assert (HUbk : Ub = k) by (destruct b; cbn in Hk; try discriminate; injection Hk as <-; apply Hb; reflexivity).
subst Ub. destruct (k <? two32) eqn:Hk2; [|apply rng_ok_none]. apply Z.ltb_lt in Hk2. unfold two32 in Hk2.
destruct (itv_within 0 two32 ua) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | cbn; apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst ua. cbn in Hua. unfold two32 in *.
pose proof (itv_scale_sound k Ua (Some (al, ah)) Hua) as H.
destruct (itv_within 0 two31 (itv_scale k (Some (al, ah)))) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
rewrite H3 in H. cbn in H. unfold two31 in *.
rewrite (Z.mod_small Ua), (Z.mod_small k) by lia.
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32. rewrite Z.mul_comm, swrap32_id by lia. cbn. lia.
-   destruct (lit_val b) as [k|] eqn:Hk; [|apply rng_ok_none].
assert (HUbk : Ub = k) by (destruct b; cbn in Hk; try discriminate; injection Hk as <-; apply Hb; reflexivity).
subst Ub. destruct ((0 <? k) && (k <? two32)) eqn:Hk2; [|apply rng_ok_none].
apply andb_prop in Hk2 as [Hk0 Hk2]. apply Z.ltb_lt in Hk0. apply Z.ltb_lt in Hk2. unfold two32 in Hk2.
destruct (itv_within 0 two32 ua) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | cbn; apply rng_of_s_ok; [apply zcanon_range| exact I]].
subst ua. cbn in Hua. unfold two32 in *.
pose proof (itv_div_sound Ua (Some (al, ah)) k Hua) as H.
destruct (itv_within 0 two31 (itv_div (Some (al, ah)) k)) as [[l h]|] eqn:Hw;
[apply itv_within_bounds in Hw as (H1 & H2 & H3) | apply rng_of_s_ok; [apply zcanon_range| exact I]].
rewrite H3 in H. cbn in H. unfold two31 in *.
rewrite (Z.mod_small Ua), (Z.mod_small k) by lia.
replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32. rewrite swrap32_id by lia. cbn. lia.
-   destruct (lit_val b) as [k|] eqn:Hk; [|apply rng_ok_none].
assert (HUbk : Ub = k) by (destruct b; cbn in Hk; try discriminate; injection Hk as <-; apply Hb; reflexivity).
subst Ub. destruct ((0 <? k) && (k <=? two31)) eqn:Hk2; [|apply rng_ok_none].
apply andb_prop in Hk2 as [Hk0 Hk2]. apply Z.ltb_lt in Hk0. apply Z.leb_le in Hk2. unfold two31 in Hk2.
destruct (itv_within 0 two32 ua) as [[al ah]|] eqn:Hwa;
[apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3) | apply rng_ok_none].
subst ua. cbn in Hua. unfold two32 in *.
rewrite (Z.mod_small Ua), (Z.mod_small k) by lia.
replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.mod_pos_bound Ua k Hk0) as Hm.
assert (Ua mod k <= Ua) by (apply Z.mod_le; lia).
apply rng_of_s_ok; [apply zcanon_range|]. rewrite HS32. rewrite swrap32_id by lia. cbn. lia.
Qed.
End o.
Lemma swrapN_congr : forall (w : N) a b, (a - b) mod 2 ^ Z.of_N w = 0 -> bv_swrap w a = bv_swrap w b.
Proof.
intros w a b H. rewrite <- (bv_swrap_wrap w a), <- (bv_swrap_wrap w b). f_equal.
unfold bv_wrap, bv_modulus.
pose proof (Z.pow_pos_nonneg 2 (Z.of_N w) ltac:(lia) ltac:(lia)).
apply Z.mod_divide in H; [|lia]. destruct H as [k Hk].
replace a with (b + k * 2^Z.of_N w) by lia. apply Z_mod_plus_full.
Qed.
Lemma swrapN_range : forall (w : N) z, 0 < Z.of_N w ->
- 2 ^ (Z.of_N w - 1) <= bv_swrap w z < 2 ^ (Z.of_N w - 1).
Proof.
intros w z Hw. pose proof (bv_swrap_in_range w z ltac:(lia)) as H.
unfold bv_half_modulus, bv_modulus in H.
replace (2 ^ Z.of_N w `div` 2) with (2 ^ (Z.of_N w - 1)) in H; [exact H|].
replace (Z.of_N w) with (Z.of_N w - 1 + 1) at 2 by lia. rewrite Z.pow_add_r by lia.
rewrite Z.pow_1_r. rewrite Z.div_mul; lia.
Qed.
Lemma swrapN_id : forall (w : N) z, 0 < Z.of_N w ->
- 2 ^ (Z.of_N w - 1) <= z < 2 ^ (Z.of_N w - 1) -> bv_swrap w z = z.
Proof.
intros w z Hw Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N w `div` 2) with (2 ^ (Z.of_N w - 1)); [exact Hz|].
replace (Z.of_N w) with (Z.of_N w - 1 + 1) at 2 by lia. rewrite Z.pow_add_r by lia.
rewrite Z.pow_1_r. rewrite Z.div_mul; lia.
Qed.
Section t.
Variables (Ua : Z).
Hypothesis HUa : 0 <= Ua < M64.
Let Sa := bv_swrap 64 Ua.
Lemma rng_ext_sound : forall (sg : bool) w ra,
rng_ok Ua ra ->
rng_ok (zcanon (if sg then bv_swrap w (Ua mod 2 ^ Z.of_N w) else Ua mod 2 ^ Z.of_N w)) (rng_ext sg w ra).
Proof.
intros sg w [ua sa] [Hua Hsa]. cbn [fst snd] in *. fold Sa in Hsa.
unfold rng_ext. set (wz := Z.of_N w).
destruct sg.
- destruct ((0 <? wz) && (wz <=? 64)) eqn:Hw; [|apply rng_ok_none].
apply andb_prop in Hw as [Hw0 Hw64]. apply Z.ltb_lt in Hw0. apply Z.leb_le in Hw64.
pose proof (Z.pow_pos_nonneg 2 wz ltac:(lia) ltac:(lia)) as Hp.
pose proof (Z.pow_pos_nonneg 2 (wz - 1) ltac:(lia) ltac:(lia)) as Hp1.
assert (Hpw : 2 ^ wz = 2 * 2 ^ (wz - 1)).
{ replace wz with (wz - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
assert (Hle : 2 ^ (wz - 1) <= half64).
{ unfold half64. apply Z.pow_le_mono_r; lia. }
assert (HcS : (Ua - Sa) mod 2 ^ wz = 0).
{ pose proof (swrap64_self_congr Ua) as Hc. fold Sa in Hc. unfold M64 in Hc.
apply Z.mod_divide in Hc; [|lia]. destruct Hc as [k Hk]. rewrite Hk.
replace (2^64) with (2^(64 - wz) * 2^wz) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z_mod_mult. }
assert (Hval : bv_swrap w (Ua mod 2 ^ wz) = bv_swrap w Sa).
{ apply swrapN_congr. fold wz.
replace (Ua mod 2 ^ wz - Sa) with ((Ua mod 2^wz - Ua) + (Ua - Sa)) by lia.
rewrite Zplus_mod, HcS, Z.add_0_r, Zmod_mod. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
rewrite Hval.
pose proof (swrapN_range w Sa Hw0) as Hr. fold wz in Hr.
apply rng_of_s_ok; [apply zcanon_range|].
rewrite zcanon_wrap, (bv_swrap_wrap 64). rewrite swrap64_id by lia.
destruct (itv_within (- 2 ^ (wz - 1)) (2 ^ (wz - 1)) sa) as [[l h]|] eqn:Hwi.
+ apply itv_within_bounds in Hwi as (H1 & H2 & H3). subst sa. cbn in Hsa.
rewrite swrapN_id by (subst wz; lia). cbn. lia.
+ cbn. subst wz. lia.
- destruct ((0 <=? wz) && (wz <=? 64)) eqn:Hw; [|apply rng_ok_none].
apply andb_prop in Hw as [Hw0 Hw64]. apply Z.leb_le in Hw0. apply Z.leb_le in Hw64.
pose proof (Z.pow_pos_nonneg 2 wz ltac:(lia) ltac:(lia)) as Hp.
assert (Hle : 2 ^ wz <= M64) by (unfold M64; apply Z.pow_le_mono_r; lia).
pose proof (Z.mod_pos_bound Ua (2^wz) Hp) as Hm.
rewrite zcanon_id by lia.
apply rng_of_u_ok; [lia|].
destruct (itv_within 0 (2 ^ wz) ua) as [[l h]|] eqn:Hwi.
+ apply itv_within_bounds in Hwi as (H1 & H2 & H3). subst ua. cbn in Hua.
rewrite Z.mod_small by lia. cbn. lia.
+ cbn. lia.
Qed.
End t.
Lemma data_word_range : forall E d i n, (Z.of_N n < 8) -> 0 <= data_word E d i n <= 2 ^ (8 * Z.of_N n) - 1.
Proof.
intros E d i n Hn. unfold data_word.
set (bs := firstn (N.to_nat n) (skipn (Z.to_nat i) (ed E d))).
pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as Hb.
assert (Hlen : (length bs <= N.to_nat n)%nat) by (subst bs; apply firstn_le_length).
assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ (8 * Z.of_N n)) by (apply Z.pow_le_mono_r; lia).
lia.
Qed.
Theorem sv_ranges_sound : forall E G v, facts_ok E G -> rng_ok (U E v) (sv_ranges G v).
Proof.
intros E G v HG. induction v; cbn [sv_ranges].
-   split; cbn [fst snd]; rewrite U_SLit; cbn; lia.
-   destruct (atom_lookup (f_atoms G) n) as [f|] eqn:Hl; [|apply rng_ok_none].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hb & Hal & Hk).
rewrite U_SOff. split; cbn [fst snd].
+ destruct (itv_within 0 M64 (Some (af_lo f + z, af_hi f + z))) as [[l h]|] eqn:Hw; [|exact I].
apply itv_within_bounds in Hw as (H1 & H2 & H3). injection H3 as <- <-.
rewrite zcanon_id by lia. cbn. lia.
+ destruct (itv_within (- half64) half64 (Some (af_lo f + z, af_hi f + z))) as [[l h]|] eqn:Hw; [|exact I].
apply itv_within_bounds in Hw as (H1 & H2 & H3). injection H3 as <- <-.
rewrite zcanon_wrap, (bv_swrap_wrap 64), swrap64_id by lia. cbn. lia.
-   rewrite U_SAlu. apply rng_alu_sound; try apply U_range; try assumption.
intros s ->. apply U_SLit.
-   rewrite U_of_S, S_SAluw, <- zcanon_wrap. apply rng_aluw_sound; try apply U_range; try assumption.
intros s ->. apply U_SLit.
-   rewrite U_SMd. apply rng_md_sound; try apply U_range; try assumption.
+ intros s ->. apply U_SLit.
+ intros s ->. apply U_SLit.
-   rewrite U_of_S, S_SMdw, <- zcanon_wrap. apply rng_mdw_sound; try apply U_range; try assumption.
intros s ->. apply U_SLit.
-   rewrite U_SExt. apply rng_ext_sound; [apply U_range| assumption].
-   destruct (Z.of_N n <? 8) eqn:Hn; [|apply rng_ok_none]. apply Z.ltb_lt in Hn.
pose proof (data_word_range E d i n Hn) as Hr.
assert (Hp : 2 ^ (8 * Z.of_N n) <= 2^56) by (apply Z.pow_le_mono_r; lia).
unfold U. cbn [sv_denot]. rewrite unsigned_lit, zcanon_id by (unfold M64; lia).
apply rng_of_u_ok; [unfold M64; lia| cbn; lia].
-   apply rng_ok_none.
-   destruct op; try apply rng_ok_none.
unfold U. cbn [sv_denot fpop2_denot].
destruct (fst (fcmp_sem op (fp_format fmt) (fp_arg fmt (sv_denot E v1)) (fp_arg fmt (sv_denot E v2))));
change w1 with (Z_to_bv 64 1); change w0 with (Z_to_bv 64 0); rewrite unsigned_lit;
rewrite zcanon_small by lia;
(apply rng_of_u_ok; [unfold M64; lia | cbn; lia]).
-   apply rng_ok_none.
Qed.
Corollary sv_urange_sound : forall E G v l h,
facts_ok E G -> sv_urange G v = Some (l, h) -> l <= bv_unsigned (sv_denot E v) <= h.
Proof.
intros E G v l h HG H. pose proof (proj1 (sv_ranges_sound E G v HG)) as Hu.
unfold sv_urange in H. rewrite H in Hu. exact Hu.
Qed.
Corollary sv_srange_sound : forall E G v l h,
facts_ok E G -> sv_srange G v = Some (l, h) -> l <= bv_signed (sv_denot E v) <= h.
Proof.
intros E G v l h HG H. pose proof (proj2 (sv_ranges_sound E G v HG)) as Hs.
unfold sv_srange in H. rewrite H in Hs. exact Hs.
Qed.
Definition itv_disjoint (a b : itv) : bool :=
match a, b with
| Some (al, ah), Some (bl, bh) => (ah <? bl) || (bh <? al)
| _, _ => false
end.
Definition itv_lt (a b : itv) : option bool :=
match a, b with
| Some (al, ah), Some (bl, bh) =>
if ah <? bl then Some true else if bh <=? al then Some false else None
| _, _ => None
end.
Lemma itv_disjoint_sound : forall x y a b,
in_itv x a -> in_itv y b -> itv_disjoint a b = true -> x <> y.
Proof.
intros x y [[al ah]|] [[bl bh]|]; cbn; intros Hx Hy H; try discriminate.
apply orb_prop in H as [H|H]; apply Z.ltb_lt in H; lia.
Qed.
Lemma itv_lt_sound : forall x y a b r,
in_itv x a -> in_itv y b -> itv_lt a b = Some r -> (x <? y) = r.
Proof.
intros x y [[al ah]|] [[bl bh]|] r; cbn; intros Hx Hy H; try discriminate.
destruct (ah <? bl) eqn:H1.
- injection H as <-. apply Z.ltb_lt in H1. apply Z.ltb_lt. lia.
- destruct (bh <=? al) eqn:H2; [|discriminate]. injection H as <-.
apply Z.leb_le in H2. apply Z.ltb_ge. lia.
Qed.
Definition decide_eq2 (G : facts) (a b : sv) : option bool :=
match decide_eq G a b with
| Some r => Some r
| None =>
let '(ua, sa) := sv_ranges G a in
let '(ub, sb) := sv_ranges G b in
if itv_disjoint ua ub || itv_disjoint sa sb then Some false else None
end.
Definition decide_ltu2 (G : facts) (a b : sv) : option bool :=
match decide_ltu G a b with
| Some r => Some r
| None => itv_lt (sv_urange G a) (sv_urange G b)
end.
Definition decide_lts2 (G : facts) (a b : sv) : option bool :=
match decide_lts G a b with
| Some r => Some r
| None => itv_lt (sv_srange G a) (sv_srange G b)
end.
Definition decide_cond2 (G : facts) (c : branch_cond) (a b : sv) : option bool :=
if cond_assumed (f_conds G) c a b then Some true
else if cond_assumed (f_conds G) (neg_bc c) a b then Some false
else match c with
| BC_EQ => decide_eq2 G a b
| BC_NE => option_map negb (decide_eq2 G a b)
| BC_LTU => decide_ltu2 G a b
| BC_GEU => option_map negb (decide_ltu2 G a b)
| BC_LT => decide_lts2 G a b
| BC_GE => option_map negb (decide_lts2 G a b)
end.
Lemma decide_eq2_sound : forall E G a b r,
facts_ok E G -> decide_eq2 G a b = Some r ->
bv_eqb (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold decide_eq2 in H.
destruct (decide_eq G a b) as [r'|] eqn:Hd.
{ injection H as <-. eapply decide_eq_sound; eauto. }
pose proof (sv_ranges_sound E G a HG) as [Hua Hsa].
pose proof (sv_ranges_sound E G b HG) as [Hub Hsb].
destruct (sv_ranges G a) as [ua sa]. destruct (sv_ranges G b) as [ub sb]. cbn [fst snd] in *.
destruct (itv_disjoint ua ub || itv_disjoint sa sb) eqn:Hdis; [|discriminate].
injection H as <-. apply bv_eqb_false_iff. intros Heq.
apply orb_prop in Hdis as [Hdis|Hdis].
- apply (itv_disjoint_sound _ _ _ _ Hua Hub Hdis). unfold U. rewrite Heq. reflexivity.
- apply (itv_disjoint_sound _ _ _ _ Hsa Hsb Hdis). unfold U. rewrite Heq. reflexivity.
Qed.
Lemma decide_ltu2_sound : forall E G a b r,
facts_ok E G -> decide_ltu2 G a b = Some r ->
bv_ltu (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold decide_ltu2 in H.
destruct (decide_ltu G a b) as [r'|] eqn:Hd.
{ injection H as <-. eapply decide_ltu_sound; eauto. }
pose proof (proj1 (sv_ranges_sound E G a HG)) as Hua.
pose proof (proj1 (sv_ranges_sound E G b HG)) as Hub.
unfold bv_ltu. eapply itv_lt_sound; [exact Hua | exact Hub | exact H].
Qed.
Lemma decide_lts2_sound : forall E G a b r,
facts_ok E G -> decide_lts2 G a b = Some r ->
bv_lts (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold decide_lts2 in H.
destruct (decide_lts G a b) as [r'|] eqn:Hd.
{ injection H as <-. eapply decide_lts_sound; eauto. }
pose proof (proj2 (sv_ranges_sound E G a HG)) as Hsa.
pose proof (proj2 (sv_ranges_sound E G b HG)) as Hsb.
rewrite bv_lts_signed. eapply itv_lt_sound; [exact Hsa | exact Hsb | exact H].
Qed.
Lemma decide_cond2_sound : forall E G c a b r,
facts_ok E G -> decide_cond2 G c a b = Some r ->
branch_taken c (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G c a b r HG H. unfold decide_cond2 in H.
destruct (cond_assumed (f_conds G) c a b) eqn:Hc1.
{ injection H as <-. eapply cond_assumed_sound; [apply (proj1 (proj2 HG)) | exact Hc1]. }
destruct (cond_assumed (f_conds G) (neg_bc c) a b) eqn:Hc2.
{ injection H as <-.
pose proof (cond_assumed_sound E _ _ _ _ (proj1 (proj2 HG)) Hc2) as Hn.
rewrite branch_taken_neg in Hn. destruct (branch_taken c _ _); [discriminate|reflexivity]. }
destruct c; cbn [branch_taken].
- eapply decide_eq2_sound; eauto.
- destruct (decide_eq2 G a b) as [r'|] eqn:Hd; [|discriminate]. cbn in H. injection H as <-.
f_equal. eapply decide_eq2_sound; eauto.
- eapply decide_lts2_sound; eauto.
- destruct (decide_lts2 G a b) as [r'|] eqn:Hd; [|discriminate]. cbn in H. injection H as <-.
f_equal. eapply decide_lts2_sound; eauto.
- eapply decide_ltu2_sound; eauto.
- destruct (decide_ltu2 G a b) as [r'|] eqn:Hd; [|discriminate]. cbn in H. injection H as <-.
f_equal. eapply decide_ltu2_sound; eauto.
Qed.
Lemma U_inj : forall E a b, U E a = U E b -> sv_denot E a = sv_denot E b.
Proof. intros E a b H. apply bv_eq. exact H. Qed.
Lemma S_inj : forall E a b, Sg E a = Sg E b -> sv_denot E a = sv_denot E b.
Proof. intros E a b H. apply bv_eq_signed. exact H. Qed.
Definition ext_is_id (G : facts) (sg : bool) (w : N) (a : sv) : bool :=
let wz := Z.of_N w in
if sg then (0 <? wz) && (wz <=? 64) &&
match itv_within (- 2 ^ (wz - 1)) (2 ^ (wz - 1)) (sv_srange G a) with Some _ => true | None => false end
else (0 <=? wz) && (wz <=? 64) &&
match itv_within 0 (2 ^ wz) (sv_urange G a) with Some _ => true | None => false end.
Definition s_ext2 (G : facts) (sg : bool) (w : N) (a : sv) : sv :=
match a with
| SLit x => SLit (zext_low sg w x)
| _ => if ext_is_id G sg w a then a else SExt sg w a
end.
Lemma ext_signed_val : forall (w : N) Ua, 0 <= Ua < M64 -> 0 < Z.of_N w <= 64 ->
bv_swrap w (Ua mod 2 ^ Z.of_N w) = bv_swrap w (bv_swrap 64 Ua).
Proof.
intros w Ua HUa Hw. set (wz := Z.of_N w) in *. set (Sa := bv_swrap 64 Ua).
pose proof (Z.pow_pos_nonneg 2 wz ltac:(lia) ltac:(lia)) as Hp.
assert (HcS : (Ua - Sa) mod 2 ^ wz = 0).
{ pose proof (swrap64_self_congr Ua) as Hc. fold Sa in Hc. unfold M64 in Hc.
apply Z.mod_divide in Hc; [|lia]. destruct Hc as [k Hk]. rewrite Hk.
replace (2^64) with (2^(64 - wz) * 2^wz) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z_mod_mult. }
apply swrapN_congr. fold wz.
replace (Ua mod 2 ^ wz - Sa) with ((Ua mod 2^wz - Ua) + (Ua - Sa)) by lia.
rewrite Zplus_mod, HcS, Z.add_0_r, Zmod_mod. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity.
Qed.
Lemma ext_is_id_sound : forall E G sg w a,
facts_ok E G -> ext_is_id G sg w a = true -> U E (SExt sg w a) = U E a.
Proof.
intros E G sg w a HG H. unfold ext_is_id in H.
pose proof (sv_ranges_sound E G a HG) as [Hua Hsa].
pose proof (U_range E a) as HU.
rewrite U_SExt. set (wz := Z.of_N w) in *.
destruct sg.
- apply andb_prop in H as [H Hi]. apply andb_prop in H as [H0 H64].
apply Z.ltb_lt in H0. apply Z.leb_le in H64.
unfold sv_srange in Hi.
destruct (itv_within (- 2 ^ (wz - 1)) (2 ^ (wz - 1)) (snd (sv_ranges G a))) as [[l h]|] eqn:Hw; [|discriminate].
apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in Hsa. cbn in Hsa.
subst wz. rewrite (ext_signed_val w (U E a)) by lia.
rewrite swrapN_id by lia.
rewrite zcanon_wrap. apply wrap64_swrap64. exact HU.
- apply andb_prop in H as [H Hi]. apply andb_prop in H as [H0 H64].
apply Z.leb_le in H0. apply Z.leb_le in H64.
unfold sv_urange in Hi.
destruct (itv_within 0 (2 ^ wz) (fst (sv_ranges G a))) as [[l h]|] eqn:Hw; [|discriminate].
apply itv_within_bounds in Hw as (H1 & H2 & H3). rewrite H3 in Hua. cbn in Hua.
rewrite Z.mod_small by lia. apply zcanon_id. exact HU.
Qed.
Lemma s_ext2_sound : forall E G (sg : bool) (w : N) a,
facts_ok E G ->
sv_denot E (s_ext2 G sg w a) =
(if sg then sext 64 (bv_extract 0 w (sv_denot E a)) else zext 64 (bv_extract 0 w (sv_denot E a))).
Proof.
intros E G sg w a HG.
transitivity (sv_denot E (SExt sg w a)); [| cbn [sv_denot]; destruct sg; reflexivity].
assert (Hgen : sv_denot E (if ext_is_id G sg w a then a else SExt sg w a) = sv_denot E (SExt sg w a)).
{ destruct (ext_is_id G sg w a) eqn:Hid; [|reflexivity].
apply U_inj. symmetry. apply (ext_is_id_sound E G); assumption. }
unfold s_ext2. destruct a; try exact Hgen.
cbn [sv_denot]. symmetry. exact (zext_low_sound sg w z).
Qed.
Definition aluw_is_alu (G : facts) (op : aluop) (a b : sv) : bool :=
match op with
| ALU_ADD | ALU_SUB =>
match snd (rng_aluw op b (sv_ranges G a) (sv_ranges G b)) with Some _ => true | None => false end
| ALU_SLL =>
match b with
| SLit s => (zcanon s <? 32) &&
match snd (rng_aluw op b (sv_ranges G a) (sv_ranges G b)) with Some _ => true | None => false end
| _ => false
end
| _ => false
end.
Definition s_aluw2 (G : facts) (op : aluop) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (zalu32 op x y)
| _, _ => if aluw_is_alu G op a b then s_alu G op a b else SAluw op a b
end.
Lemma aluw_is_alu_sound : forall E G op a b,
facts_ok E G -> aluw_is_alu G op a b = true -> Sg E (SAluw op a b) = Sg E (SAlu op a b).
Proof.
intros E G op a b HG H. unfold aluw_is_alu in H.
pose proof (sv_ranges_sound E G a HG) as [Hua Hsa].
pose proof (sv_ranges_sound E G b HG) as [Hub Hsb].
pose proof (U_range E a) as HUa. pose proof (U_range E b) as HUb.
rewrite S_SAluw, S_SAlu.
pose proof (swrap64_range (U E a)) as HSa. pose proof (swrap64_range (U E b)) as HSb.
remember (bv_swrap 64 (U E a)) as Sa eqn:HeqSa. remember (bv_swrap 64 (U E b)) as Sb eqn:HeqSb.
destruct (sv_ranges G a) as [ua sa]. destruct (sv_ranges G b) as [ub sb]. cbn [fst snd] in *.
assert (Hm32a : 0 <= U E a mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
assert (Hmm : forall z, (z mod two32 - z) mod two32 = 0).
{ intros z. unfold two32. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
destruct op; try discriminate; cbn [rng_aluw zalu_raw snd] in H; cbn [zalu_raw].
-
destruct (itv_within (- two31) two31 sa) as [[al ah]|] eqn:Hwa; [apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3)| cbn in H; discriminate].
destruct (itv_within (- two31) two31 sb) as [[bl bh]|] eqn:Hwb; [apply itv_within_bounds in Hwb as (Hb1 & Hb2 & Hb3)| cbn in H; discriminate].
subst sa sb. cbn [in_itv fst snd] in Hsa, Hsb. cbn [itv_add] in H.
destruct (itv_within (- two31) two31 (Some (al + bl, ah + bh))) as [[l h]|] eqn:Hw; [apply itv_within_bounds in Hw as (H1 & H2 & H3)| cbn in H; discriminate].
injection H3 as <- <-. unfold two31, half64 in *.
rewrite (swrap32_congr _ (Sa + Sb)).
+ rewrite swrap32_id by lia. rewrite (swrap64_congr _ (Sa + Sb)); [rewrite swrap64_id by (unfold half64; lia); reflexivity|].
replace (U E a + U E b - (Sa + Sb)) with ((U E a - Sa) + (U E b - Sb)) by lia.
unfold M64. rewrite Zplus_mod. subst Sa Sb. rewrite !swrap64_self_congr. reflexivity.
+ replace (U E a mod 2 ^ 32 + U E b mod 2 ^ 32 - (Sa + Sb)) with ((U E a mod two32 - Sa mod two32) + (U E b mod two32 - Sb mod two32) + (Sa mod two32 - Sa) + (Sb mod two32 - Sb)) by (unfold two32; lia).
unfold two32. rewrite Zplus_mod. rewrite (Zplus_mod (_ + _)). rewrite (Zplus_mod (U E a mod _ - _)).
fold two32. subst Sa Sb. rewrite !U_mod32_S. rewrite !Hmm. reflexivity.
-
destruct (itv_within (- two31) two31 sa) as [[al ah]|] eqn:Hwa; [apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3)| cbn in H; discriminate].
destruct (itv_within (- two31) two31 sb) as [[bl bh]|] eqn:Hwb; [apply itv_within_bounds in Hwb as (Hb1 & Hb2 & Hb3)| cbn in H; discriminate].
subst sa sb. cbn [in_itv fst snd] in Hsa, Hsb. cbn [itv_sub] in H.
destruct (itv_within (- two31) two31 (Some (al - bh, ah - bl))) as [[l h]|] eqn:Hw; [apply itv_within_bounds in Hw as (H1 & H2 & H3)| cbn in H; discriminate].
injection H3 as <- <-. unfold two31, half64 in *.
rewrite (swrap32_congr _ (Sa - Sb)).
+ rewrite swrap32_id by lia. rewrite (swrap64_congr _ (Sa - Sb)); [rewrite swrap64_id by (unfold half64; lia); reflexivity|].
replace (U E a - U E b - (Sa - Sb)) with ((U E a - Sa) - (U E b - Sb)) by lia.
unfold M64. rewrite Zminus_mod. subst Sa Sb. rewrite !swrap64_self_congr. reflexivity.
+ replace (U E a mod 2 ^ 32 - U E b mod 2 ^ 32 - (Sa - Sb)) with ((U E a mod two32 - Sa mod two32) - (U E b mod two32 - Sb mod two32) + (Sa mod two32 - Sa) - (Sb mod two32 - Sb)) by (unfold two32; lia).
unfold two32. rewrite Zminus_mod. rewrite (Zplus_mod (_ - _)). rewrite (Zminus_mod (U E a mod _ - _)).
fold two32. subst Sa Sb. rewrite !U_mod32_S. rewrite !Hmm. reflexivity.
-
destruct b as [sft| | | | | | | | | |]; try discriminate.
apply andb_prop in H as [Hs32 H]. apply Z.ltb_lt in Hs32.
cbn [lit_shamt] in H.
pose proof (zcanon_range sft) as Hzr.
assert (Hk : 0 <= Z.land (zcanon sft) 31 <= 31) by (pose proof (Z_land_upper (zcanon sft) 31 ltac:(lia)); lia).
set (k := Z.land (zcanon sft) 31) in *.
assert (Hland32 : Z.land (U E (SLit sft) mod 2^32) 31 = k /\ Z.land (U E (SLit sft)) 63 = k).
{ rewrite U_SLit. split.
- rewrite <- (Z.land_ones (zcanon sft) 32) by lia. rewrite <- Z.land_assoc.
change (Z.land (Z.ones 32) 31) with 31. reflexivity.
- subst k. change 31 with (Z.ones 5). change 63 with (Z.ones 6).
rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
destruct Hland32 as [Hl32 Hl64]. rewrite Hl32, Hl64.
destruct (itv_within 0 two32 ua) as [[al ah]|] eqn:Hwa; [apply itv_within_bounds in Hwa as (Ha1 & Ha2 & Ha3)| cbn in H; discriminate].
subst ua. cbn [in_itv fst snd] in Hua.
pose proof (itv_scale_sound (2^k) (U E a) (Some (al, ah)) Hua) as Hs.
destruct (itv_within 0 two31 (itv_scale (2 ^ k) (Some (al, ah)))) as [[l h]|] eqn:Hw; [apply itv_within_bounds in Hw as (H1 & H2 & H3)| cbn in H; discriminate].
rewrite H3 in Hs. cbn [in_itv itv_scale fst snd] in Hs. unfold two31, two32 in *.
rewrite (Z.mod_small (U E a)) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
rewrite swrap32_id by lia. rewrite swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma s_aluw2_sound : forall E G op a b,
facts_ok E G ->
sv_denot E (s_aluw2 G op a b) = sext 64 (alu32 op (low32 (sv_denot E a)) (low32 (sv_denot E b))).
Proof.
intros E G op a b HG.
transitivity (sv_denot E (SAluw op a b)); [| reflexivity].
unfold s_aluw2.
assert (Hgen : sv_denot E (if aluw_is_alu G op a b then s_alu G op a b else SAluw op a b) = sv_denot E (SAluw op a b)).
{ destruct (aluw_is_alu G op a b) eqn:Hid; [|reflexivity].
rewrite s_alu_sound by exact HG. transitivity (sv_denot E (SAlu op a b)); [reflexivity|].
apply S_inj. symmetry. apply (aluw_is_alu_sound E G); assumption. }
destruct a; try exact Hgen. destruct b; try exact Hgen.
cbn [sv_denot]. symmetry. apply zalu32_sound.
Qed.
Definition lin := list (nat * Z).
Fixpoint lin_denot (E : env) (l : lin) : Z :=
match l with [] => 0 | (n, c) :: r => c * bv_unsigned (ew E n) + lin_denot E r end.
Fixpoint lin_ins (n : nat) (c : Z) (l : lin) : lin :=
match l with
| [] => [(n, c)]
| (m, d) :: r =>
if Nat.ltb n m then (n, c) :: l
else if Nat.eqb n m then (m, c + d) :: r
else (m, d) :: lin_ins n c r
end.
Fixpoint lin_merge (a b : lin) : lin :=
match a with [] => b | (n, c) :: r => lin_ins n c (lin_merge r b) end.
Definition lin_scale (k : Z) (l : lin) : lin := map (fun p => (fst p, k * snd p)) l.
Fixpoint lin_clean (l : lin) : lin :=
match l with [] => [] | (n, c) :: r => if c =? 0 then lin_clean r else (n, c) :: lin_clean r end.
Lemma lin_ins_denot : forall E n c l, lin_denot E (lin_ins n c l) = c * bv_unsigned (ew E n) + lin_denot E l.
Proof.
intros E n c l. induction l as [|[m d] r IH]; [reflexivity|].
cbn -[Nat.ltb Nat.eqb Z.mul Z.add].
destruct (Nat.ltb n m); [reflexivity|].
destruct (Nat.eqb n m) eqn:Hnm; cbn -[Z.mul Z.add].
- apply Nat.eqb_eq in Hnm. subst. lia.
- rewrite IH. lia.
Qed.
Lemma lin_merge_denot : forall E a b, lin_denot E (lin_merge a b) = lin_denot E a + lin_denot E b.
Proof.
intros E a b. induction a as [|[n c] r IH]; cbn; [reflexivity|].
rewrite lin_ins_denot, IH. lia.
Qed.
Lemma lin_scale_denot : forall E k l, lin_denot E (lin_scale k l) = k * lin_denot E l.
Proof.
intros E k l. induction l as [|[n c] r IH]; [cbn; lia|].
unfold lin_scale. cbn [map fst snd lin_denot]. fold (lin_scale k r). rewrite IH. lia.
Qed.
Lemma lin_clean_denot : forall E l, lin_denot E (lin_clean l) = lin_denot E l.
Proof.
intros E l. induction l as [|[n c] r IH]; cbn; [reflexivity|].
destruct (c =? 0) eqn:Hc; cbn; rewrite IH; [apply Z.eqb_eq in Hc; subst; lia| reflexivity].
Qed.
Fixpoint lin_of (v : sv) : option (lin * Z) :=
match v with
| SLit z => Some ([], z)
| SOff n x => Some ([(n, 1)], x)
| SAlu ALU_ADD a b =>
match lin_of a, lin_of b with
| Some (la, ca), Some (lb, cb) => Some (lin_merge la lb, ca + cb)
| _, _ => None
end
| SAlu ALU_SUB a b =>
match lin_of a, lin_of b with
| Some (la, ca), Some (lb, cb) => Some (lin_merge la (lin_scale (-1) lb), ca - cb)
| _, _ => None
end
| SAlu ALU_SLL a (SLit s) =>
match lin_of a with
| Some (la, ca) => Some (lin_scale (2 ^ Z.land (zcanon s) 63) la, 2 ^ Z.land (zcanon s) 63 * ca)
| None => None
end
| SMd M_MUL a (SLit s) =>
match lin_of a with
| Some (la, ca) => Some (lin_scale (zcanon s) la, zcanon s * ca)
| None => None
end
| SMd M_MUL (SLit s) b =>
match lin_of b with
| Some (lb, cb) => Some (lin_scale (zcanon s) lb, zcanon s * cb)
| None => None
end
| _ => None
end.
Lemma lin_of_sound : forall E v l c,
lin_of v = Some (l, c) -> U E v = (lin_denot E l + c) mod M64.
Proof.
intros E v. induction v; intros l c H; cbn [lin_of] in H; try discriminate.
- injection H as <- <-. rewrite U_SLit. cbn. reflexivity.
- injection H as <- <-. rewrite U_SOff. cbn. unfold zcanon. f_equal. lia.
-   destruct op; try discriminate.
+ destruct (lin_of v1) as [[la ca]|] eqn:Ha; [|discriminate].
destruct (lin_of v2) as [[lb cb]|] eqn:Hb; [|discriminate].
injection H as <- <-. rewrite U_SAlu. cbn [zalu_raw].
rewrite (IHv1 la ca eq_refl), (IHv2 lb cb eq_refl).
rewrite lin_merge_denot. unfold zcanon, M64. rewrite <- Zplus_mod. f_equal. lia.
+ destruct (lin_of v1) as [[la ca]|] eqn:Ha; [|discriminate].
destruct (lin_of v2) as [[lb cb]|] eqn:Hb; [|discriminate].
injection H as <- <-. rewrite U_SAlu. cbn [zalu_raw].
rewrite (IHv1 la ca eq_refl), (IHv2 lb cb eq_refl).
rewrite lin_merge_denot, lin_scale_denot. unfold zcanon, M64. rewrite <- Zminus_mod. f_equal. lia.
+ destruct v2 as [s| | | | | | | | | |]; try discriminate.
destruct (lin_of v1) as [[la ca]|] eqn:Ha; [|discriminate].
injection H as <- <-. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (IHv1 la ca eq_refl).
pose proof (zcanon_range s). pose proof (Z_land_upper (zcanon s) 63 ltac:(lia)).
assert (Hk : 0 <= Z.land (zcanon s) 63) by (apply Z.land_nonneg; lia).
rewrite Z.shiftl_mul_pow2 by exact Hk.
rewrite lin_scale_denot. unfold zcanon, M64. rewrite Zmult_mod_idemp_l. f_equal. lia.
-   destruct op; try discriminate.
destruct v2 as [s|n2 x2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|g2 w2 a2|d2 i2 m2|f2 a2|f2 a2 b2|f2 a2 b2 c2].
1:{ assert (H' : match lin_of v1 with
| Some (la, ca) => Some (lin_scale (zcanon s) la, zcanon s * ca)
| None => None end = Some (l, c)) by (destruct v1; exact H).
clear H. destruct (lin_of v1) as [[la ca]|] eqn:Ha; [|discriminate]. injection H' as <- <-.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (IHv1 la ca eq_refl), lin_scale_denot.
unfold zcanon, M64. rewrite Zmult_mod_idemp_l. f_equal. lia. }
all: destruct v1 as [s1| | | | | | | | | |]; try discriminate;
match type of H with context [match lin_of ?x with _ => _ end] =>
destruct (lin_of x) as [[lb cb]|] eqn:Hb; try discriminate end;
injection H as <- <-; rewrite U_SMd; cbn [zmd_raw]; rewrite U_SLit;
rewrite (IHv2 lb cb eq_refl), lin_scale_denot;
unfold zcanon, M64; rewrite Zmult_mod_idemp_r; f_equal; lia.
Qed.
Fixpoint lin_eqb (a b : lin) : bool :=
match a, b with
| [], [] => true
| (n, c) :: r, (m, d) :: q => Nat.eqb n m && (c =? d) && lin_eqb r q
| _, _ => false
end.
Lemma lin_eqb_eq : forall a b, lin_eqb a b = true -> a = b.
Proof.
induction a as [|[n c] r IH]; intros [|[m d] q] H; cbn in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. apply IH. exact H3.
Qed.
Definition lin_nf (v : sv) : option (lin * Z) :=
match lin_of v with Some (l, c) => Some (lin_clean l, c) | None => None end.
Lemma lin_nf_sound : forall E v l c,
lin_nf v = Some (l, c) -> U E v = (lin_denot E l + c) mod M64.
Proof.
intros E v l c H. unfold lin_nf in H. destruct (lin_of v) as [[l0 c0]|] eqn:Hl; [|discriminate].
injection H as <- <-. rewrite lin_clean_denot. eapply lin_of_sound. exact Hl.
Qed.
Fixpoint alias_lin_lookup (al : list (sv * sv)) (l : lin) (c : Z) : option sv :=
match al with
| [] => None
| (a, SOff k d) :: r =>
match lin_nf a with
| Some (la, ca) => if lin_eqb la l then Some (SOff k (d + (c - ca))) else alias_lin_lookup r l c
| None => alias_lin_lookup r l c
end
| _ :: r => alias_lin_lookup r l c
end.
Lemma alias_lin_lookup_sound : forall E al l c v w,
alias_ok E al ->
U E v = (lin_denot E l + c) mod M64 ->
alias_lin_lookup al l c = Some w -> sv_denot E w = sv_denot E v.
Proof.
intros E al l c v w Hal Hv. induction al as [|[a b] r IH]; cbn; intros H; [discriminate|].
destruct Hal as [Hab Hr].
destruct b as [|k d| | | | | | | | |]; try (apply IH; assumption).
destruct (lin_nf a) as [[la ca]|] eqn:Hnf; [|apply IH; assumption].
destruct (lin_eqb la l) eqn:Heq; [|apply IH; assumption].
injection H as <-. apply lin_eqb_eq in Heq. subst la.
apply U_inj. rewrite Hv, U_SOff.
pose proof (lin_nf_sound E a _ _ Hnf) as Ha.
apply (f_equal (fun w => bv_unsigned w)) in Hab. change (U E a = U E (SOff k d)) in Hab.
rewrite U_SOff in Hab. rewrite Ha in Hab. unfold zcanon, M64 in *.
replace (bv_unsigned (ew E k) + (d + (c - ca))) with ((bv_unsigned (ew E k) + d) + (c - ca)) by lia.
rewrite <- Zplus_mod_idemp_l, <- Hab, Zplus_mod_idemp_l. f_equal. lia.
Qed.
Definition mono (n : nat) (k : Z) : sv :=
if k =? 1 then SOff n 0
else match is_pow2 k with
| Some e => if e <=? 63 then SAlu ALU_SLL (SOff n 0) (SLit e) else SMd M_MUL (SOff n 0) (SLit k)
| None => SMd M_MUL (SOff n 0) (SLit k)
end.
Fixpoint add_monos (acc : sv) (l : lin) : sv :=
match l with [] => acc | (n, k) :: r => add_monos (SAlu ALU_ADD acc (mono n k)) r end.
Definition sv_of_lin (l : lin) (c : Z) : sv :=
match l with
| [] => SLit (zcanon c)
| [(n, k)] =>
if k =? 1 then SOff n (owrap c)
else if k =? -1 then SAlu ALU_SUB (SLit 0) (SOff n (owrap (- c)))
else if zcanon c =? 0 then mono n k
else SAlu ALU_ADD (mono n k) (SLit c)
| (n, k) :: r =>
if k =? 1 then add_monos (SOff n (owrap c)) r
else if zcanon c =? 0 then add_monos (mono n k) r
else add_monos (SAlu ALU_ADD (mono n k) (SLit c)) r
end.
Lemma U_SOff_owrap : forall E n x, U E (SOff n (owrap x)) = U E (SOff n x).
Proof. intros. unfold U. rewrite SOff_owrap. reflexivity. Qed.
Lemma mono_sound : forall E n k, U E (mono n k) = (k * bv_unsigned (ew E n)) mod M64.
Proof.
intros E n k. unfold mono. pose proof (u64_range (ew E n)) as Hr.
assert (Hmul : U E (SMd M_MUL (SOff n 0) (SLit k)) = (k * bv_unsigned (ew E n)) mod M64).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff, U_SLit.
unfold zcanon, M64. rewrite Z.add_0_r, Zmult_mod_idemp_r, Zmult_mod_idemp_l. f_equal. lia. }
destruct (k =? 1) eqn:Hk.
- apply Z.eqb_eq in Hk. subst. rewrite U_SOff. unfold zcanon. f_equal. lia.
- destruct (is_pow2 k) as [e|] eqn:Hp; [|exact Hmul].
apply is_pow2_sound in Hp as [He Hke].
destruct (e <=? 63) eqn:He63; [|exact Hmul]. apply Z.leb_le in He63.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit.
rewrite (zcanon_id e) by (unfold M64; lia).
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small e) by lia.
rewrite Z.shiftl_mul_pow2 by lia. subst k.
unfold zcanon, M64. rewrite Z.add_0_r, Zmult_mod_idemp_l. f_equal. lia.
Qed.
Lemma add_monos_sound : forall E l acc,
U E (add_monos acc l) = (U E acc + lin_denot E l) mod M64.
Proof.
intros E l. induction l as [|[n k] r IH]; intros acc; cbn [add_monos lin_denot].
- pose proof (U_range E acc). rewrite Z.add_0_r. symmetry. apply Z.mod_small. lia.
- rewrite IH. rewrite U_SAlu. cbn [zalu_raw]. rewrite mono_sound.
unfold zcanon, M64. rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma sv_of_lin_sound : forall E l c, U E (sv_of_lin l c) = (lin_denot E l + c) mod M64.
Proof.
intros E l c. unfold sv_of_lin. destruct l as [|[n k] r].
- rewrite U_SLit. cbn. unfold zcanon. apply Zmod_mod.
- destruct r as [|p r'].
{ cbn [lin_denot]. destruct (k =? 1) eqn:Hk.
- apply Z.eqb_eq in Hk. subst. rewrite U_SOff_owrap, U_SOff. wrap64_solve.
- destruct (k =? -1) eqn:Hk1.
+ apply Z.eqb_eq in Hk1. subst. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff_owrap, U_SOff. wrap64_solve.
+ destruct (zcanon c =? 0) eqn:Hc.
* apply Z.eqb_eq in Hc. rewrite mono_sound.
rewrite zcanon_wrap in Hc. rewrite !modM64_wrap.
rewrite <- (bv_wrap_add_idemp_r 64 _ c). rewrite Hc, Z.add_0_r. bv_wrap_simplify_solve.
* rewrite U_SAlu. cbn [zalu_raw]. rewrite mono_sound, U_SLit. wrap64_solve. }
set (r := p :: r') in *.
cbn [lin_denot]. fold (lin_denot E r). destruct (k =? 1) eqn:Hk.
+ apply Z.eqb_eq in Hk. subst. rewrite add_monos_sound, U_SOff_owrap, U_SOff.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l. f_equal. lia.
+ destruct (zcanon c =? 0) eqn:Hc.
* apply Z.eqb_eq in Hc. rewrite add_monos_sound, mono_sound.
rewrite zcanon_wrap in Hc. rewrite !modM64_wrap.
rewrite <- (bv_wrap_add_idemp_r 64 _ c) . rewrite Hc, Z.add_0_r. bv_wrap_simplify_solve.
* rewrite add_monos_sound, U_SAlu. cbn [zalu_raw]. rewrite mono_sound, U_SLit.
unfold zcanon. rewrite !modM64_wrap. bv_wrap_simplify_solve.
Qed.
Definition aliased2 (G : facts) (v : sv) : sv :=
let v1 := alias_lookup (f_alias G) v in
if negb (sv_eqb v1 v) then v1 else
match v with
| SLit _ | SOff _ _ => v
| _ =>
match lin_nf v with
| None => v
| Some (l, c) =>
match l with
| [] => SLit (zcanon c)
| [(n, k)] => if k =? 1 then SOff n c else
match alias_lin_lookup (f_alias G) l c with Some w => w | None => sv_of_lin l c end
| _ => match alias_lin_lookup (f_alias G) l c with Some w => w | None => sv_of_lin l c end
end
end
end.
Lemma aliased2_sound : forall E G v, facts_ok E G -> sv_denot E (aliased2 G v) = sv_denot E v.
Proof.
intros E G v HG. pose proof HG as (_ & _ & Hal). unfold aliased2.
destruct (negb (sv_eqb (alias_lookup (f_alias G) v) v)).
{ apply alias_lookup_sound. exact Hal. }
assert (Hgen : sv_denot E
match lin_nf v with
| None => v
| Some (l, c) =>
match l with
| [] => SLit (zcanon c)
| [(n, k)] => if k =? 1 then SOff n c else
match alias_lin_lookup (f_alias G) l c with Some w => w | None => sv_of_lin l c end
| _ => match alias_lin_lookup (f_alias G) l c with Some w => w | None => sv_of_lin l c end
end
end = sv_denot E v).
{ destruct (lin_nf v) as [[l c]|] eqn:Hnf; [|reflexivity].
pose proof (lin_nf_sound E v l c Hnf) as Hv.
assert (Hlk : sv_denot E match alias_lin_lookup (f_alias G) l c with Some w => w | None => sv_of_lin l c end = sv_denot E v).
{ destruct (alias_lin_lookup (f_alias G) l c) eqn:Hl.
- eapply alias_lin_lookup_sound; eauto.
- apply U_inj. rewrite sv_of_lin_sound, Hv. reflexivity. }
destruct l as [|[n k] [|p r]].
- apply U_inj. rewrite U_SLit, Hv. cbn. unfold zcanon. apply Zmod_mod.
- destruct (k =? 1) eqn:Hk; [|exact Hlk].
apply Z.eqb_eq in Hk. subst k. apply U_inj. rewrite U_SOff, Hv. cbn -[Z.add Z.mul]. unfold zcanon. f_equal. lia.
- exact Hlk. }
destruct v; try exact Hgen; reflexivity.
Qed.
Definition lin_divisible (m : Z) (l : lin) : bool := forallb (fun p => snd p mod m =? 0) l.
Definition lin_div (m : Z) (l : lin) : lin := map (fun p => (fst p, snd p / m)) l.
Lemma lin_div_denot : forall E m l, m <> 0 -> lin_divisible m l = true ->
lin_denot E l = m * lin_denot E (lin_div m l).
Proof.
intros E m l Hm. induction l as [|[n c] r IH]; cbn [lin_denot lin_div lin_divisible map forallb fst snd]; intros H.
- lia.
- apply andb_prop in H as [Hc Hr]. fold (lin_div m r). fold (lin_divisible m r) in Hr.
rewrite (IH Hr). apply Z.eqb_eq in Hc.
rewrite (Z.div_mod c m Hm) at 1. rewrite Hc. lia.
Qed.
Definition srl_lin (G : facts) (a : sv) (k : Z) : option sv :=
let k' := Z.land (zcanon k) 63 in
if k' =? 0 then None else
match lin_of a with
| Some (l, c) =>
let m := 2 ^ k' in
if lin_divisible m l && (zcanon c mod m =? 0) then
let w := sv_of_lin (lin_div m l) (zcanon c / m) in
match fst (sv_ranges G w) with
| Some (_, hi) => if hi <? 2 ^ (64 - k') then Some w else None
| None => None
end
else None
| None => None
end.
Lemma srl_lin_sound : forall E G a k w, facts_ok E G -> srl_lin G a k = Some w ->
U E w = zcanon (zalu_raw 63 64 ALU_SRL (U E a) (U E (SLit k))).
Proof.
intros E G a k w HG H. unfold srl_lin in H.
set (k' := Z.land (zcanon k) 63) in H.
destruct (k' =? 0) eqn:Hk0; [discriminate|].
destruct (lin_of a) as [[l c]|] eqn:Hlin; [|discriminate].
destruct (lin_divisible (2 ^ k') l && (zcanon c mod 2 ^ k' =? 0)) eqn:Hdiv; [|discriminate].
apply andb_prop in Hdiv as [Hdl Hdc]. apply Z.eqb_eq in Hdc.
destruct (fst (sv_ranges G (sv_of_lin (lin_div (2 ^ k') l) (zcanon c / 2 ^ k')))) as [[lo hi]|] eqn:Hr; [|discriminate].
destruct (hi <? 2 ^ (64 - k')) eqn:Hhi; [|discriminate]. injection H as <-.
apply Z.ltb_lt in Hhi.
assert (Hk' : 0 < k' <= 63).
{ subst k'. pose proof (Z_land_upper (zcanon k) 63 ltac:(lia)). apply Z.eqb_neq in Hk0. lia. }
set (w := sv_of_lin (lin_div (2 ^ k') l) (zcanon c / 2 ^ k')) in *.
pose proof (sv_ranges_sound E G w HG) as [Hu _]. rewrite Hr in Hu. cbn [fst in_itv] in Hu.
pose proof (U_range E w) as Hwr.
assert (Hw : U E w = (lin_denot E (lin_div (2 ^ k') l) + zcanon c / 2 ^ k') mod M64) by (subst w; apply sv_of_lin_sound).
pose proof (lin_of_sound E a l c Hlin) as Ha.
assert (Hm : 0 < 2 ^ k') by (apply Z.pow_pos_nonneg; lia).
rewrite (lin_div_denot E (2 ^ k') l ltac:(lia) Hdl) in Ha.
cbn [zalu_raw]. rewrite U_SLit. fold k'.
rewrite Z.shiftr_div_pow2 by lia.
assert (Hpow : 2 ^ k' * 2 ^ (64 - k') = M64).
{ unfold M64. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Ha' : U E a = 2 ^ k' * U E w).
{ rewrite Ha, Hw. unfold M64.
set (L := lin_denot E (lin_div (2 ^ k') l)) in *.
assert (Hc : c mod 2^64 = 2 ^ k' * (zcanon c / 2 ^ k')).
{ unfold zcanon, M64 in Hdc |- *. rewrite (Z.div_mod (c mod 2^64) (2^k')) at 1 by lia. lia. }
rewrite <- Zplus_mod_idemp_r. rewrite Hc.
replace (2 ^ k' * L + 2 ^ k' * (zcanon c / 2 ^ k')) with (2 ^ k' * (L + zcanon c / 2 ^ k')) by lia.
set (q := L + zcanon c / 2 ^ k') in *.
rewrite <- Zmult_mod_idemp_r.
apply Z.mod_small. change (2 ^ 64) with M64. rewrite <- Hw. unfold M64 in *.
assert (2 ^ k' * U E w <= 2 ^ k' * (2 ^ (64 - k') - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
rewrite Ha'. rewrite Z.mul_comm, Z.div_mul by lia. symmetry. apply zcanon_id. exact Hwr.
Qed.
Definition and_comm_args (op : aluop) (a b : sv) : sv * sv :=
match op, a, b with
| ALU_AND, SLit _, SLit _ => (a, b)
| ALU_AND, SLit _, _ => (b, a)
| _, _, _ => (a, b)
end.
Lemma alu64_and_comm : forall x y : word, alu64 ALU_AND x y = alu64 ALU_AND y x.
Proof.
intros x y. rewrite <- (Z_to_bv_bv_unsigned 64 x), <- (Z_to_bv_bv_unsigned 64 y).
rewrite !zalu64_sound. f_equal. unfold zalu64. cbn [zalu_raw]. rewrite Z.land_comm. reflexivity.
Qed.
Lemma and_comm_args_sound : forall E op a b,
alu64 op (sv_denot E (fst (and_comm_args op a b))) (sv_denot E (snd (and_comm_args op a b)))
= alu64 op (sv_denot E a) (sv_denot E b).
Proof.
intros E op a b. unfold and_comm_args.
destruct op; try reflexivity. destruct a; try reflexivity. destruct b; try reflexivity;
cbn [fst snd]; apply alu64_and_comm.
Qed.
Definition s_alu2 (G : facts) (op : aluop) (a b : sv) : sv :=
match a, b with
| SLit _, SLit _ => s_alu G op a b
| _, _ =>
match op with
| ALU_SLTU => match decide_ltu2 G a b with Some r => s_lit01 r | None => SAlu op a b end
| ALU_SLT => match decide_lts2 G a b with Some r => s_lit01 r | None => SAlu op a b end
| ALU_SRL =>
match (match b with SLit k => srl_lin G a k | _ => None end) with
| Some w => w
| None => let (a', b') := and_comm_args op a b in aliased2 G (s_alu G op a' b')
end
| _ => let (a', b') := and_comm_args op a b in aliased2 G (s_alu G op a' b')
end
end.
Lemma s_alu2_sound : forall E G op a b,
facts_ok E G ->
sv_denot E (s_alu2 G op a b) = alu64 op (sv_denot E a) (sv_denot E b).
Proof.
intros E G op a b HG. unfold s_alu2.
assert (Hgen : sv_denot E
match op with
| ALU_SLTU => match decide_ltu2 G a b with Some r => s_lit01 r | None => SAlu op a b end
| ALU_SLT => match decide_lts2 G a b with Some r => s_lit01 r | None => SAlu op a b end
| ALU_SRL =>
match (match b with SLit k => srl_lin G a k | _ => None end) with
| Some w => w
| None => let (a', b') := and_comm_args op a b in aliased2 G (s_alu G op a' b')
end
| _ => let (a', b') := and_comm_args op a b in aliased2 G (s_alu G op a' b')
end = alu64 op (sv_denot E a) (sv_denot E b)).
{ assert (Hdef : forall op', sv_denot E (let (a', b') := and_comm_args op' a b in aliased2 G (s_alu G op' a' b'))
= alu64 op' (sv_denot E a) (sv_denot E b)).
{ intros op'. rewrite <- (and_comm_args_sound E _ a b).
destruct (and_comm_args _ a b) as [a' b']; cbn [fst snd].
rewrite aliased2_sound by exact HG. apply s_alu_sound. exact HG. }
destruct op; try apply Hdef.
3:{ destruct b as [kk| | | | | | | | | | ]; try apply Hdef.
destruct (srl_lin G a kk) as [w|] eqn:Hs; [|apply Hdef].
transitivity (sv_denot E (SAlu ALU_SRL a (SLit kk))); [|reflexivity].
apply U_inj. rewrite (srl_lin_sound E G a kk w HG Hs). rewrite <- U_SAlu. reflexivity. }
- destruct (decide_lts2 G a b) as [r|] eqn:Hd; [|reflexivity].
rewrite <- (decide_lts2_sound E G a b r HG Hd). apply s_lit01_lts.
- destruct (decide_ltu2 G a b) as [r|] eqn:Hd; [|reflexivity].
rewrite <- (decide_ltu2_sound E G a b r HG Hd). apply s_lit01_ltu. }
destruct a; try exact Hgen. destruct b; try exact Hgen. apply s_alu_sound. exact HG.
Qed.
Lemma low32_unsigned_mod : forall w : word, bv_unsigned (low32 w) = bv_unsigned w mod M32.
Proof.
intros w. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. rewrite low32_lit_unsigned. reflexivity.
Qed.
Lemma aluw_addsub_of_lit : forall op (a b : word) z,
(op = ALU_ADD \/ op = ALU_SUB) ->
alu64 op a b = Z_to_bv 64 z ->
sext 64 (alu32 op (low32 a) (low32 b)) = Z_to_bv 64 (zalu32 op z 0).
Proof.
intros op a b z Hop Heq.
rewrite <- zalu32_sound. f_equal. apply bv_eq. rewrite !alu32_unsigned.
rewrite !low32_unsigned_mod. rewrite !Z_to_bv_unsigned.
apply (f_equal bv_unsigned) in Heq. rewrite Z_to_bv_unsigned in Heq.
rewrite <- (Z_to_bv_bv_unsigned 64 a) in Heq. rewrite <- (Z_to_bv_bv_unsigned 64 b) in Heq.
rewrite zalu64_sound, Z_to_bv_unsigned in Heq.
unfold bv_wrap in *. unfold M32. change (bv_modulus 32) with (2^32). change (bv_modulus 64) with (2^64) in *.
unfold zalu64, zcanon, M64 in Heq. rewrite Z.mod_mod in Heq by lia.
pose proof (u64_range a). pose proof (u64_range b).
rewrite !(Z.mod_small (bv_unsigned _) (2^64)) in Heq by lia.
destruct Hop as [-> | ->]; cbn [zalu_raw] in *.
- rewrite <- Zplus_mod. rewrite !Zmod_0_l, Z.add_0_r, Z.mod_mod by lia.
rewrite <- Heq. symmetry. apply Z.mod_mod_divide. exists (2^32); reflexivity.
- rewrite <- Zminus_mod. rewrite !Zmod_0_l, Z.sub_0_r, Z.mod_mod by lia.
rewrite <- Heq. symmetry. apply Z.mod_mod_divide. exists (2^32); reflexivity.
Qed.
Definition s_aluw3_gen (G : facts) (op : aluop) (a b : sv) : sv :=
if aluw_is_alu G op a b then s_alu2 G op a b else SAluw op a b.
Definition s_aluw3 (G : facts) (op : aluop) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (zalu32 op x y)
| _, _ =>
match op with
| ALU_ADD | ALU_SUB =>
match s_alu2 G op a b with
| SLit z => SLit (zalu32 op z 0)
| _ => s_aluw3_gen G op a b
end
| _ => s_aluw3_gen G op a b
end
end.
Lemma s_aluw3_sound : forall E G op a b,
facts_ok E G ->
sv_denot E (s_aluw3 G op a b) = sext 64 (alu32 op (low32 (sv_denot E a)) (low32 (sv_denot E b))).
Proof.
intros E G op a b HG.
transitivity (sv_denot E (SAluw op a b)); [| reflexivity].
unfold s_aluw3.
assert (Hgen : sv_denot E (s_aluw3_gen G op a b) = sv_denot E (SAluw op a b)).
{ unfold s_aluw3_gen. destruct (aluw_is_alu G op a b) eqn:Hid; [|reflexivity].
rewrite s_alu2_sound by exact HG. transitivity (sv_denot E (SAlu op a b)); [reflexivity|].
apply S_inj. symmetry. apply (aluw_is_alu_sound E G); assumption. }
assert (Hlit : forall z, (op = ALU_ADD \/ op = ALU_SUB) -> s_alu2 G op a b = SLit z ->
sv_denot E (SLit (zalu32 op z 0)) = sv_denot E (SAluw op a b)).
{ intros z Hop Hz. cbn [sv_denot]. symmetry. apply aluw_addsub_of_lit; [exact Hop|].
rewrite <- (s_alu2_sound E G op a b HG). rewrite Hz. reflexivity. }
assert (Hgen2 : sv_denot E
match op with
| ALU_ADD | ALU_SUB =>
match s_alu2 G op a b with
| SLit z => SLit (zalu32 op z 0)
| _ => s_aluw3_gen G op a b
end
| _ => s_aluw3_gen G op a b
end = sv_denot E (SAluw op a b)).
{ destruct op; try exact Hgen;
(destruct (s_alu2 G _ a b) eqn:Hz; try exact Hgen; eapply Hlit; [auto | reflexivity]). }
destruct a; try exact Hgen2. destruct b; try exact Hgen2.
cbn [sv_denot]. symmetry. apply zalu32_sound.
Qed.
Lemma sext32_small : forall z, -2^31 <= z < 2^31 -> sext 64 (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 z.
Proof.
intros z Hz. rewrite (zext_low_sound true 32 z). unfold zext_low.
apply Z_to_bv64_eq_mod. unfold zcanon, M64. rewrite Zmod_mod.
change (2 ^ Z.of_N 32) with (2^32).
rewrite (Z.mod_mod_divide z (2^64) (2^32)) by (exists (2^32); reflexivity).
f_equal. change (z mod 2 ^ 32) with (bv_wrap 32 z). rewrite (bv_swrap_wrap 32). apply swrap32_id. lia.
Qed.
Lemma bv_eqb_small : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne]; [apply bv_eqb_refl|].
apply bv_eqb_neq. intros Heq. apply (f_equal bv_signed) in Heq.
rewrite !Z_to_bv_signed in Heq. rewrite !swrap64_id in Heq by (unfold half64; lia). lia.
Qed.
