(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QVsB QwAs QKyU QCiC QKJh Q6sh QZzg Qbkb QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig QVsB.Mq1 QwAs.Mq2.
Import QKyU QCiC.Mq0 QKJh Q6sh.Mq1.
Import QZzg Qbkb.Mq0.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma zlength_zupd {A} (l : list A) i v : zlength (zupd l i v) = zlength l.
Proof.
unfold zlength, zupd. destruct (i <? 0); [reflexivity|]. f_equal.
revert l. generalize (Z.to_nat i) as n. induction n as [|n IH]; intros [|x l]; cbn; auto.
Qed.
Lemma nth_error_znth {A} (d : A) l i : 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth d l i).
Proof.
intros Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|]. unfold zlength in Hi.
apply nth_error_nth'. lia.
Qed.
Lemma nth_error_map_znth {A B} (f : A -> B) (d : A) l i :
0 <= i < zlength l -> nth_error (map f l) (Z.to_nat i) = Some (f (znth d l i)).
Proof. intros Hi. rewrite nth_error_map, (nth_error_znth d) by exact Hi. reflexivity. Qed.
Lemma upd_nat_upd {A} (l : list A) n v : upd_nat l n v = upd l n v.
Proof. revert n. induction l as [|x l IH]; intros [|n]; cbn; auto; f_equal; apply IH. Qed.
Lemma zupd_upd {A} (l : list A) i v : 0 <= i -> zupd l i v = upd l (Z.to_nat i) v.
Proof. intros Hi. unfold zupd. destruct (Z.ltb_spec0 i 0); [lia|]. apply upd_nat_upd. Qed.
Lemma map_upd {A B} (f : A -> B) l n v : map f (upd l n v) = upd (map f l) n (f v).
Proof. revert n. induction l as [|x l IH]; intros [|n]; cbn; auto; f_equal; apply IH. Qed.
Lemma map_zupd {A B} (f : A -> B) l i v : map f (zupd l i v) = zupd (map f l) i (f v).
Proof. unfold zupd. destruct (i <? 0); [reflexivity|]. rewrite !upd_nat_upd. apply map_upd. Qed.
Lemma Forall_upd {A} (P : A -> Prop) l n v : Forall P l -> P v -> Forall P (upd l n v).
Proof. revert n. induction l as [|x l IH]; intros [|n] HL Hv; cbn; auto; inversion HL; subst; constructor; auto. Qed.
Lemma Forall_zupd {A} (P : A -> Prop) l i v : Forall P l -> P v -> Forall P (zupd l i v).
Proof. intros HL Hv. unfold zupd. destruct (i <? 0); [exact HL|]. rewrite upd_nat_upd. apply Forall_upd; assumption. Qed.
Lemma Forall_znth {A} (P : A -> Prop) (d : A) l i : Forall P l -> 0 <= i < zlength l -> P (znth d l i).
Proof.
intros HL Hi. pose proof (nth_error_znth d l i Hi) as Hn. apply nth_error_In in Hn.
revert Hn. apply Forall_forall. exact HL.
Qed.

Lemma swrap32_of_lit x d : bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d) = bv_swrap 32 (x + d).
Proof.
rewrite !bv_swrap32_eq, unsigned_lit_wrap. f_equal.
pose proof (Z.div_mod x (2^64) ltac:(lia)) as E.
replace (x mod 2^64 + d + 2^31) with ((x + d + 2^31) + (- (x / 2^64) * 2^32) * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma swrap32_small x : -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros H. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma addiw_small x d : -2^31 <= x + d < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d)) = Z_to_bv 64 (x + d).
Proof. intros H. rewrite swrap32_of_lit, swrap32_small by lia. reflexivity. Qed.

Section Eqs.
Context {ptr : Type}.
Local Notation FS := (FSt ptr).
Implicit Types (σ : FS).

Lemma types_at_eq σ i : in_range i (zlength (f_types σ)) = true -> types_at i σ = ARet (znth 0 (f_types σ) i, σ).
Proof. unfold types_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma btypes_at_eq σ i : in_range i (zlength (f_btypes σ)) = true -> btypes_at i σ = ARet (znth 0 (f_btypes σ) i, σ).
Proof. unfold btypes_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma types_at_unr σ i : in_range i (zlength (f_types σ)) = false -> types_at i σ = AUnr.
Proof. unfold types_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma btypes_at_unr σ i : in_range i (zlength (f_btypes σ)) = false -> btypes_at i σ = AUnr.
Proof. unfold btypes_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma types_set_eq σ i v : in_range i (zlength (f_types σ)) = true -> in_u32 v = true ->
types_set i v σ = ARet (tt, set_types (zupd (f_types σ) i v) σ).
Proof. unfold types_set, abind, aget, aput, aunr. cbn. intros -> ->. reflexivity. Qed.
Lemma btypes_set_eq σ i v : in_range i (zlength (f_btypes σ)) = true -> in_u32 v = true ->
btypes_set i v σ = ARet (tt, set_btypes (zupd (f_btypes σ) i v) σ).
Proof. unfold btypes_set, abind, aget, aput, aunr. cbn. intros -> ->. reflexivity. Qed.
Lemma types_set_unr σ i v : in_range i (zlength (f_types σ)) && in_u32 v = false -> types_set i v σ = AUnr.
Proof. unfold types_set, abind, aget, aput, aunr. cbn. intros ->. reflexivity. Qed.
Lemma btypes_set_unr σ i v : in_range i (zlength (f_btypes σ)) && in_u32 v = false -> btypes_set i v σ = AUnr.
Proof. unfold btypes_set, abind, aget, aput, aunr. cbn. intros ->. reflexivity. Qed.

End Eqs.

#[export] Hint Resolve types_at_eq btypes_at_eq types_set_eq btypes_set_eq
types_at_unr btypes_at_unr types_set_unr btypes_set_unr : mstep_eqs.

Record faddrs : Type := mkFAd {
fa_str : Z;
fa_types : Z;
fa_btypes : Z;
fa_levels : Z
}.

Definition u32ok (v : Z) : Prop := 0 <= v < 2^32.
Definition s8ok (v : Z) : Prop := -128 <= v < 128.

Definition ageom {BAND : Band} (FA : faddrs) (len Astr nstr : Z) : Prop :=
0 < len ->
let S := fa_str FA in let T := fa_types FA in let BT := fa_btypes FA in let LV := fa_levels FA in
(Astr <= S /\ S + 4 * len <= Astr + nstr /\ S mod 4 = 0)
/\ (appr Astr (nstr) /\ Astr + nstr <= band_lo)
/\ (appr T (4 * len) /\ T + 4 * len <= band_lo)
/\ (appr BT (4 * len) /\ BT + 4 * len <= band_lo)
/\ (appr LV (len) /\ LV + len <= band_lo)
/\ (T + 4 * len <= BT \/ BT + 4 * len <= T)
/\ (T + 4 * len <= LV \/ LV + len <= T)
/\ (BT + 4 * len <= LV \/ LV + len <= BT)
/\ (T + 4 * len <= Astr \/ Astr + nstr <= T)
/\ (BT + 4 * len <= Astr \/ Astr + nstr <= BT)
/\ (LV + len <= Astr \/ Astr + nstr <= LV).

Lemma ageom_nums {BAND : Band} FA len Astr nstr : ageom FA len Astr nstr -> 0 < len ->
let S := fa_str FA in let T := fa_types FA in let BT := fa_btypes FA in let LV := fa_levels FA in
Astr <= S /\ S + 4 * len <= Astr + nstr /\ S mod 4 = 0
/\ appr_lia Astr nstr /\ Astr + nstr <= band_lo
/\ appr_lia T (4 * len) /\ T + 4 * len <= band_lo
/\ appr_lia BT (4 * len) /\ BT + 4 * len <= band_lo
/\ appr_lia LV len /\ LV + len <= band_lo
/\ (T + 4 * len <= BT \/ BT + 4 * len <= T)
/\ (T + 4 * len <= LV \/ LV + len <= T)
/\ (BT + 4 * len <= LV \/ LV + len <= BT)
/\ (T + 4 * len <= Astr \/ Astr + nstr <= T)
/\ (BT + 4 * len <= Astr \/ Astr + nstr <= BT)
/\ (LV + len <= Astr \/ Astr + nstr <= LV).
Proof.
intros G L. specialize (G L). cbv zeta in *. pose proof (@band_lo_range BAND) as BR.
destruct G as ((S1 & S2 & S3) & (A1 & B1) & (A2 & B2) & (A3 & B3) & (A4 & B4) & D).
assert (N : 0 <= nstr) by (clear - S1 S2 L; lia).
split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
split; [apply appr_to_lia; [exact N| clear - B1 BR; lia| exact A1]|]. split; [exact B1|].
split; [apply appr_to_lia; [clear - L; lia| clear - B2 BR; lia| exact A2]|]. split; [exact B2|].
split; [apply appr_to_lia; [clear - L; lia| clear - B3 BR; lia| exact A3]|]. split; [exact B3|].
split; [apply appr_to_lia; [clear - L; lia| clear - B4 BR; lia| exact A4]|]. split; [exact B4|].
exact D.
Qed.

Section AArr.
Context {BAND : Band}.
Variable segs : list Segment.
Context {ptr : Type}.
Implicit Types (σ : FSt ptr) (m : word -> option byte) (FA : faddrs).

Definition arepA FA (len : Z) (cps : list Z) σ m : Prop :=
(zlength cps = len /\ Forall u32ok cps /\ bytes_at segs m (fa_str FA) (u32s (map (Z_to_bv 64) cps)))
/\ (zlength (f_types σ) = len /\ Forall u32ok (f_types σ) /\ u32arr segs m (fa_types FA) (map (Z_to_bv 64) (f_types σ)))
/\ (zlength (f_btypes σ) = len /\ Forall u32ok (f_btypes σ) /\ u32arr segs m (fa_btypes FA) (map (Z_to_bv 64) (f_btypes σ)))
/\ (zlength (f_levels σ) = len /\ Forall s8ok (f_levels σ) /\ u8arr segs m (fa_levels FA) (map (Z_to_bv 8) (f_levels σ))).

Lemma arepA_lens FA len cps σ m : arepA FA len cps σ m ->
zlength cps = len /\ zlength (f_types σ) = len /\ zlength (f_btypes σ) = len /\ zlength (f_levels σ) = len.
Proof. intros ((? & _) & (? & _) & (? & _) & (? & _)). auto. Qed.
Lemma arepA_len_nonneg FA len cps σ m : arepA FA len cps σ m -> 0 <= len.
Proof. intros ((H & _) & _). unfold zlength in H. lia. Qed.
Lemma arepA_cps_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> 0 <= znth 0 cps i < 2^32.
Proof. intros ((HL & HF & _) & _) Hi. apply (Forall_znth u32ok 0); [exact HF| lia]. Qed.
Lemma arepA_types_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> 0 <= znth 0 (f_types σ) i < 2^32.
Proof. intros (_ & (HL & HF & _) & _) Hi. apply (Forall_znth u32ok 0); [exact HF| lia]. Qed.
Lemma arepA_btypes_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> 0 <= znth 0 (f_btypes σ) i < 2^32.
Proof. intros (_ & _ & (HL & HF & _) & _) Hi. apply (Forall_znth u32ok 0); [exact HF| lia]. Qed.
Lemma arepA_levels_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> -128 <= znth 0 (f_levels σ) i < 128.
Proof. intros (_ & _ & _ & (HL & HF & _)) Hi. apply (Forall_znth s8ok 0); [exact HF| lia]. Qed.

Lemma arepA_ext FA len cps σ σ' m : arepA FA len cps σ m ->
f_types σ' = f_types σ -> f_btypes σ' = f_btypes σ -> f_levels σ' = f_levels σ -> arepA FA len cps σ' m.
Proof. intros AR E1 E2 E3. unfold arepA. rewrite E1, E2, E3. exact AR. Qed.

Lemma arepA_read_str FA len cps σ m i a :
arepA FA len cps σ m -> 0 <= i < len -> a = wa (fa_str FA + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (znth 0 cps i))).
Proof.
intros ((HL & HF & HB) & _) Hi ->.
pose proof (nth_error_map_znth (Z_to_bv 64) 0 cps i ltac:(lia)) as Hn.
destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m (fa_str FA) (u32s (map (Z_to_bv 64) cps)) (4 * Z.to_nat i) 4 HB).
2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma arepA_read_types FA len cps σ m i a :
arepA FA len cps σ m -> 0 <= i < len -> a = wa (fa_types FA + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (znth 0 (f_types σ) i))).
Proof.
intros (_ & (HL & HF & HA) & _) Hi Ha. eapply u32arr_read; [exact HA| apply (nth_error_map_znth _ 0); lia| lia| exact Ha].
Qed.
Lemma arepA_read_btypes FA len cps σ m i a :
arepA FA len cps σ m -> 0 <= i < len -> a = wa (fa_btypes FA + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (znth 0 (f_btypes σ) i))).
Proof.
intros (_ & _ & (HL & HF & HA) & _) Hi Ha. eapply u32arr_read; [exact HA| apply (nth_error_map_znth _ 0); lia| lia| exact Ha].
Qed.

Lemma arepA_store_types FA len Astr nstr cps σ m i v (w : word) :
ageom FA len Astr nstr -> arepA FA len cps σ m ->
0 <= i < len -> bv_unsigned w mod 2^32 = v mod 2^32 -> 0 <= v < 2^32 ->
store_ok segs m (wa (fa_types FA + 4 * i)) 4 = true
/\ arepA FA len cps (set_types (zupd (f_types σ) i v) σ) (write_to_mem m (wa (fa_types FA + 4 * i)) (le4 w)).
Proof.
intros GE AR Hi Hw Hv. pose proof AR as ((CL & CF & CB) & (TL & TF & TA) & (BL & BF & BA) & (LL & LF & LA)).
pose proof (ageom_nums _ _ _ _ GE ltac:(lia)) as NU. cbv zeta in NU.
destruct NU as (S1 & S2 & _ & A1 & A2 & T1 & T2 & B1 & B2 & L1 & L2 & D1 & D2 & D3 & D4 & D5 & D6).
assert (SOK : store_ok segs m (wa (fa_types FA + 4 * i)) 4 = true).
{ eapply u32arr_store_ok; [exact TA| | reflexivity]. rewrite length_map. unfold zlength in TL. lia. }
split; [exact SOK|].
assert (EW : le4 w = le4 (Z_to_bv 64 v)).
{ rewrite <- (Z_to_bv_lit_self w). apply le4_eqm. exact Hw. }
unfold arepA. destruct σ as [rr pp ww nn tt bb ll]; cbn [f_types f_btypes f_levels set_types] in *.
split; [|split; [|split]].
- split; [exact CL|]. split; [exact CF|].
apply bytes_at_write_other; [exact CB| lia| rewrite length_le4; lia|].
rewrite length_le4, u32s_length, length_map. unfold zlength in CL. lia.
- split; [rewrite zlength_zupd; exact TL|]. split; [apply Forall_zupd; [exact TF| exact Hv]|].
rewrite map_zupd, zupd_upd, EW by lia. eapply u32arr_write; [exact TA| rewrite length_map; unfold zlength in TL; lia].
- split; [exact BL|]. split; [exact BF|].
apply u32arr_frame; [exact BA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in BL. lia.
- split; [exact LL|]. split; [exact LF|].
apply u8arr_frame; [exact LA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in LL. lia.
Qed.

Lemma arepA_store_btypes FA len Astr nstr cps σ m i v (w : word) :
ageom FA len Astr nstr -> arepA FA len cps σ m ->
0 <= i < len -> bv_unsigned w mod 2^32 = v mod 2^32 -> 0 <= v < 2^32 ->
store_ok segs m (wa (fa_btypes FA + 4 * i)) 4 = true
/\ arepA FA len cps (set_btypes (zupd (f_btypes σ) i v) σ) (write_to_mem m (wa (fa_btypes FA + 4 * i)) (le4 w)).
Proof.
intros GE AR Hi Hw Hv. pose proof AR as ((CL & CF & CB) & (TL & TF & TA) & (BL & BF & BA) & (LL & LF & LA)).
pose proof (ageom_nums _ _ _ _ GE ltac:(lia)) as NU. cbv zeta in NU.
destruct NU as (S1 & S2 & _ & A1 & A2 & T1 & T2 & B1 & B2 & L1 & L2 & D1 & D2 & D3 & D4 & D5 & D6).
assert (SOK : store_ok segs m (wa (fa_btypes FA + 4 * i)) 4 = true).
{ eapply u32arr_store_ok; [exact BA| | reflexivity]. rewrite length_map. unfold zlength in BL. lia. }
split; [exact SOK|].
assert (EW : le4 w = le4 (Z_to_bv 64 v)).
{ rewrite <- (Z_to_bv_lit_self w). apply le4_eqm. exact Hw. }
unfold arepA. destruct σ as [rr pp ww nn tt bb ll]; cbn [f_types f_btypes f_levels set_btypes] in *.
split; [|split; [|split]].
- split; [exact CL|]. split; [exact CF|].
apply bytes_at_write_other; [exact CB| lia| rewrite length_le4; lia|].
rewrite length_le4, u32s_length, length_map. unfold zlength in CL. lia.
- split; [exact TL|]. split; [exact TF|].
apply u32arr_frame; [exact TA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in TL. lia.
- split; [rewrite zlength_zupd; exact BL|]. split; [apply Forall_zupd; [exact BF| exact Hv]|].
rewrite map_zupd, zupd_upd, EW by lia. eapply u32arr_write; [exact BA| rewrite length_map; unfold zlength in BL; lia].
- split; [exact LL|]. split; [exact LF|].
apply u8arr_frame; [exact LA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in LL. lia.
Qed.

Lemma arepA_munch_hi FA len Astr nstr cps σ m m' W :
ageom FA len Astr nstr -> 0 < len -> arepA FA len cps σ m ->
munch W m m' -> wmono segs m m' -> Forall (fun iv => band_lo <= fst iv) W ->
arepA FA len cps σ m'.
Proof.
intros GE L AR MU WM HW.
pose proof (ageom_nums _ _ _ _ GE L) as NU. cbv zeta in NU.
destruct NU as (S1 & S2 & _ & A1 & A2 & T1 & T2 & B1 & B2 & L1 & L2 & _).
pose proof AR as ((CL & CF & CB) & (TL & TF & TA) & (BL & BF & BA) & (LL & LF & LA)).
assert (DJ : forall A n, A + n <= band_lo -> disjoint_from W A n).
{ intros A n HA. clear -HW HA. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
inversion HW as [|x l H1 H2]; subst. cbn in H1. split; [lia| apply IH; exact H2]. }
unfold arepA. split; [|split; [|split]].
- split; [exact CL|]. split; [exact CF|].
eapply bytes_at_transport; [exact CB| exact MU|]. rewrite u32s_length, length_map. unfold zlength in CL. apply DJ. lia.
- split; [exact TL|]. split; [exact TF|]. eapply u32arr_transport; [exact TA| exact MU| exact WM|]. rewrite length_map. unfold zlength in TL. apply DJ. lia.
- split; [exact BL|]. split; [exact BF|]. eapply u32arr_transport; [exact BA| exact MU| exact WM|]. rewrite length_map. unfold zlength in BL. apply DJ. lia.
- split; [exact LL|]. split; [exact LF|]. eapply u8arr_transport; [exact LA| exact MU| exact WM|]. rewrite length_map. unfold zlength in LL. apply DJ. lia.
Qed.

Lemma arepA_munch_nil FA cps σ m m' :
arepA FA 0 cps σ m -> wmono segs m m' -> arepA FA 0 cps σ m'.
Proof.
intros ((CL & CF & CB) & (TL & TF & [TB TW]) & (BL & BF & [BB BW]) & (LL & LF & [LB1 LW])) WM.
assert (E : forall (l : list Z), zlength l = 0 -> l = []) by (intros [|x l] H; [reflexivity| unfold zlength in H; cbn in H; lia]).
pose proof (E _ CL) as E1. pose proof (E _ TL) as E2. pose proof (E _ BL) as E3. pose proof (E _ LL) as E4.
assert (B0 : forall A m1 m2, bytes_at segs m1 A [] -> bytes_at segs m2 A []).
{ intros A m1 m2 (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros i Hi. cbn in Hi. lia. }
unfold arepA, u32arr, u8arr. rewrite E1, E2, E3, E4 in *. cbn [map u32s length Z.of_nat Z.mul] in *.
split; [| split; [| split]]; (split; [assumption|]); (split; [assumption|]).
- eapply B0; eassumption.
- split; [eapply B0; eassumption| eapply wr_at_transport; eauto].
- split; [eapply B0; eassumption| eapply wr_at_transport; eauto].
- split; [eapply B0; eassumption| eapply wr_at_transport; eauto].
Qed.

End AArr.

Arguments arepA segs {ptr} FA len cps σ m : simpl never.
Arguments arepA_lens {segs ptr FA len cps σ m} _.
Arguments arepA_len_nonneg {segs ptr FA len cps σ m} _.
Arguments arepA_cps_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_types_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_btypes_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_levels_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_ext {segs ptr FA len cps σ σ' m} _ _ _ _.
Arguments arepA_read_str {segs ptr FA len cps σ m} i a _ _ _.
Arguments arepA_read_types {segs ptr FA len cps σ m} i a _ _ _.
Arguments arepA_read_btypes {segs ptr FA len cps σ m} i a _ _ _.
Arguments arepA_store_types {BAND} {segs ptr FA len Astr nstr cps σ m} i v w _ _ _ _ _.
Arguments arepA_store_btypes {BAND} {segs ptr FA len Astr nstr cps σ m} i v w _ _ _ _ _.
Arguments arepA_munch_hi {BAND} {segs ptr FA len Astr nstr cps σ m m' W} _ _ _ _ _ _.
Arguments arepA_munch_nil {segs ptr FA cps σ m m'} _ _.

Ltac arr_getreg n :=
lazymatch goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
lazymatch v with
| Some ?w => w
| _ => fail "arr_getreg: register" n "not concrete"
end
end.
Ltac arr_lia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac arr_addr := unfold wa; f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; arr_lia.

Ltac areadA_fin H :=
let H2 := fresh "RD" in
lazymatch type of H with
| ?P1 -> ?P2 -> ?T => assert (H2 : T) by (apply H; [arr_lia | arr_addr]); clear H
end.
Tactic Notation "areadA_str" constr(AR) constr(rs) constr(k) :=
let a := arr_getreg rs in let H := fresh in pose proof (arepA_read_str k a AR) as H; areadA_fin H.
Tactic Notation "areadA_types" constr(AR) constr(rs) constr(k) :=
let a := arr_getreg rs in let H := fresh in pose proof (arepA_read_types k a AR) as H; areadA_fin H.
Tactic Notation "areadA_btypes" constr(AR) constr(rs) constr(k) :=
let a := arr_getreg rs in let H := fresh in pose proof (arepA_read_btypes k a AR) as H; areadA_fin H.
Ltac arr_clear := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.
Ltac anormA :=
repeat match goal with
| |- context [zx32 (Z_to_bv 64 ?v)] => rewrite (zx32_small v) by lia
| |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_small v) by lia
| |- context [zxb (Z_to_bv 8 ?v)] => rewrite (zxb_b8 v); rewrite (Z.mod_small v 256) by lia
| |- context [sxb (Z_to_bv 8 ?v)] => rewrite (sxb_b8 v) by lia
end.

Ltac astoreA H AR :=
let HS := fresh "HS" in let ARn := fresh "ARn" in
destruct H as [HS ARn];
step;
lazymatch type of ARn with
| arepA ?segs _ _ _ _ (write_to_mem ?m (wa ?a) ?bs) =>
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ ?mg _) => replace mg with (write_to_mem m (wa a) bs) by (first [reflexivity | f_equal; unfold wa; f_equal; lia])
end;
try (lazymatch goal with
| HI : mem_inv segs m |- _ => apply (mem_inv_store segs m (wa a) bs) in HI; [| simpl_sizes; exact HS]
end);
transport_chunks segs m a bs;
repeat match goal with
| ST : stk segs m ?lo ?hi |- _ => apply (stk_write segs m lo hi a bs) in ST; [| lia | simpl_sizes; slia]
| WM : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WM
| MU : munch ?Wq ?mq m |- _ =>
first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
| fail 100 "astoreA: store outside the declared footprint:" a ]
end;
clear HS; clear AR; rename ARn into AR;
let m' := fresh "m" in let E := fresh in
remember (write_to_mem m (wa a) bs) as m' eqn:E; clear E;
repeat match goal with
| Hx : ov_read_bytes _ m _ _ = Some _ |- _ => clear Hx
| Hx : store_ok _ m _ _ = true |- _ => clear Hx
end;
try clear m
end.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKJh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qbkb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbkb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma zlength_zupd {A} (l : list A) i v : zlength (zupd l i v) = zlength l.
Proof.
unfold zlength, zupd. destruct (i <? 0); [reflexivity|]. f_equal.
revert l. generalize (Z.to_nat i) as n. induction n as [|n IH]; intros [|x l]; cbn; auto.
Qed.
Lemma nth_error_znth {A} (d : A) l i : 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth d l i).
Proof.
intros Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|]. unfold zlength in Hi.
apply nth_error_nth'. lia.
Qed.
Lemma nth_error_map_znth {A B} (f : A -> B) (d : A) l i :
0 <= i < zlength l -> nth_error (map f l) (Z.to_nat i) = Some (f (znth d l i)).
Proof. intros Hi. rewrite nth_error_map, (nth_error_znth d) by exact Hi. reflexivity. Qed.
Lemma upd_nat_upd {A} (l : list A) n v : upd_nat l n v = upd l n v.
Proof. revert n. induction l as [|x l IH]; intros [|n]; cbn; auto; f_equal; apply IH. Qed.
Lemma zupd_upd {A} (l : list A) i v : 0 <= i -> zupd l i v = upd l (Z.to_nat i) v.
Proof. intros Hi. unfold zupd. destruct (Z.ltb_spec0 i 0); [lia|]. apply upd_nat_upd. Qed.
Lemma map_upd {A B} (f : A -> B) l n v : map f (upd l n v) = upd (map f l) n (f v).
Proof. revert n. induction l as [|x l IH]; intros [|n]; cbn; auto; f_equal; apply IH. Qed.
Lemma map_zupd {A B} (f : A -> B) l i v : map f (zupd l i v) = zupd (map f l) i (f v).
Proof. unfold zupd. destruct (i <? 0); [reflexivity|]. rewrite !upd_nat_upd. apply map_upd. Qed.
Lemma Forall_upd {A} (P : A -> Prop) l n v : Forall P l -> P v -> Forall P (upd l n v).
Proof. revert n. induction l as [|x l IH]; intros [|n] HL Hv; cbn; auto; inversion HL; subst; constructor; auto. Qed.
Lemma Forall_zupd {A} (P : A -> Prop) l i v : Forall P l -> P v -> Forall P (zupd l i v).
Proof. intros HL Hv. unfold zupd. destruct (i <? 0); [exact HL|]. rewrite upd_nat_upd. apply Forall_upd; assumption. Qed.
Lemma Forall_znth {A} (P : A -> Prop) (d : A) l i : Forall P l -> 0 <= i < zlength l -> P (znth d l i).
Proof.
intros HL Hi. pose proof (nth_error_znth d l i Hi) as Hn. apply nth_error_In in Hn.
revert Hn. apply Forall_forall. exact HL.
Qed.

Lemma swrap32_of_lit x d : bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d) = bv_swrap 32 (x + d).
Proof.
rewrite !bv_swrap32_eq, unsigned_lit_wrap. f_equal.
pose proof (Z.div_mod x (2^64) ltac:(lia)) as E.
replace (x mod 2^64 + d + 2^31) with ((x + d + 2^31) + (- (x / 2^64) * 2^32) * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma swrap32_small x : -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros H. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma addiw_small x d : -2^31 <= x + d < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d)) = Z_to_bv 64 (x + d).
Proof. intros H. rewrite swrap32_of_lit, swrap32_small by lia. reflexivity. Qed.

Section Eqs.
Context {ptr : Type}.
Local Notation FS := (FSt ptr).
Implicit Types (σ : FS).

Lemma types_at_eq σ i : in_range i (zlength (f_types σ)) = true -> types_at i σ = ARet (znth 0 (f_types σ) i, σ).
Proof. unfold types_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma btypes_at_eq σ i : in_range i (zlength (f_btypes σ)) = true -> btypes_at i σ = ARet (znth 0 (f_btypes σ) i, σ).
Proof. unfold btypes_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma types_at_unr σ i : in_range i (zlength (f_types σ)) = false -> types_at i σ = AUnr.
Proof. unfold types_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma btypes_at_unr σ i : in_range i (zlength (f_btypes σ)) = false -> btypes_at i σ = AUnr.
Proof. unfold btypes_at, abind, aget, aret, aunr. cbn. intros ->. reflexivity. Qed.
Lemma types_set_eq σ i v : in_range i (zlength (f_types σ)) = true -> in_u32 v = true ->
types_set i v σ = ARet (tt, set_types (zupd (f_types σ) i v) σ).
Proof. unfold types_set, abind, aget, aput, aunr. cbn. intros -> ->. reflexivity. Qed.
Lemma btypes_set_eq σ i v : in_range i (zlength (f_btypes σ)) = true -> in_u32 v = true ->
btypes_set i v σ = ARet (tt, set_btypes (zupd (f_btypes σ) i v) σ).
Proof. unfold btypes_set, abind, aget, aput, aunr. cbn. intros -> ->. reflexivity. Qed.
Lemma types_set_unr σ i v : in_range i (zlength (f_types σ)) && in_u32 v = false -> types_set i v σ = AUnr.
Proof. unfold types_set, abind, aget, aput, aunr. cbn. intros ->. reflexivity. Qed.
Lemma btypes_set_unr σ i v : in_range i (zlength (f_btypes σ)) && in_u32 v = false -> btypes_set i v σ = AUnr.
Proof. unfold btypes_set, abind, aget, aput, aunr. cbn. intros ->. reflexivity. Qed.

End Eqs.

#[export] Hint Resolve types_at_eq btypes_at_eq types_set_eq btypes_set_eq
types_at_unr btypes_at_unr types_set_unr btypes_set_unr : mstep_eqs.

Record faddrs : Type := mkFAd {
fa_str : Z;
fa_types : Z;
fa_btypes : Z;
fa_levels : Z
}.

Definition u32ok (v : Z) : Prop := 0 <= v < 2^32.
Definition s8ok (v : Z) : Prop := -128 <= v < 128.

Definition ageom {BAND : Band} (FA : faddrs) (len Astr nstr : Z) : Prop :=
0 < len ->
let S := fa_str FA in let T := fa_types FA in let BT := fa_btypes FA in let LV := fa_levels FA in
(Astr <= S /\ S + 4 * len <= Astr + nstr /\ S mod 4 = 0)
/\ (appr Astr (nstr) /\ Astr + nstr <= band_lo)
/\ (appr T (4 * len) /\ T + 4 * len <= band_lo)
/\ (appr BT (4 * len) /\ BT + 4 * len <= band_lo)
/\ (appr LV (len) /\ LV + len <= band_lo)
/\ (T + 4 * len <= BT \/ BT + 4 * len <= T)
/\ (T + 4 * len <= LV \/ LV + len <= T)
/\ (BT + 4 * len <= LV \/ LV + len <= BT)
/\ (T + 4 * len <= Astr \/ Astr + nstr <= T)
/\ (BT + 4 * len <= Astr \/ Astr + nstr <= BT)
/\ (LV + len <= Astr \/ Astr + nstr <= LV).

Lemma ageom_nums {BAND : Band} FA len Astr nstr : ageom FA len Astr nstr -> 0 < len ->
let S := fa_str FA in let T := fa_types FA in let BT := fa_btypes FA in let LV := fa_levels FA in
Astr <= S /\ S + 4 * len <= Astr + nstr /\ S mod 4 = 0
/\ appr_lia Astr nstr /\ Astr + nstr <= band_lo
/\ appr_lia T (4 * len) /\ T + 4 * len <= band_lo
/\ appr_lia BT (4 * len) /\ BT + 4 * len <= band_lo
/\ appr_lia LV len /\ LV + len <= band_lo
/\ (T + 4 * len <= BT \/ BT + 4 * len <= T)
/\ (T + 4 * len <= LV \/ LV + len <= T)
/\ (BT + 4 * len <= LV \/ LV + len <= BT)
/\ (T + 4 * len <= Astr \/ Astr + nstr <= T)
/\ (BT + 4 * len <= Astr \/ Astr + nstr <= BT)
/\ (LV + len <= Astr \/ Astr + nstr <= LV).
Proof.
intros G L. specialize (G L). cbv zeta in *. pose proof (@band_lo_range BAND) as BR.
destruct G as ((S1 & S2 & S3) & (A1 & B1) & (A2 & B2) & (A3 & B3) & (A4 & B4) & D).
assert (N : 0 <= nstr) by (clear - S1 S2 L; lia).
split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
split; [apply appr_to_lia; [exact N| clear - B1 BR; lia| exact A1]|]. split; [exact B1|].
split; [apply appr_to_lia; [clear - L; lia| clear - B2 BR; lia| exact A2]|]. split; [exact B2|].
split; [apply appr_to_lia; [clear - L; lia| clear - B3 BR; lia| exact A3]|]. split; [exact B3|].
split; [apply appr_to_lia; [clear - L; lia| clear - B4 BR; lia| exact A4]|]. split; [exact B4|].
exact D.
Qed.

Section AArr.
Context {BAND : Band}.
Variable segs : list Segment.
Context {ptr : Type}.
Implicit Types (σ : FSt ptr) (m : word -> option byte) (FA : faddrs).

Definition arepA FA (len : Z) (cps : list Z) σ m : Prop :=
(zlength cps = len /\ Forall u32ok cps /\ bytes_at segs m (fa_str FA) (u32s (map (Z_to_bv 64) cps)))
/\ (zlength (f_types σ) = len /\ Forall u32ok (f_types σ) /\ u32arr segs m (fa_types FA) (map (Z_to_bv 64) (f_types σ)))
/\ (zlength (f_btypes σ) = len /\ Forall u32ok (f_btypes σ) /\ u32arr segs m (fa_btypes FA) (map (Z_to_bv 64) (f_btypes σ)))
/\ (zlength (f_levels σ) = len /\ Forall s8ok (f_levels σ) /\ u8arr segs m (fa_levels FA) (map (Z_to_bv 8) (f_levels σ))).

Lemma arepA_lens FA len cps σ m : arepA FA len cps σ m ->
zlength cps = len /\ zlength (f_types σ) = len /\ zlength (f_btypes σ) = len /\ zlength (f_levels σ) = len.
Proof. intros ((? & _) & (? & _) & (? & _) & (? & _)). auto. Qed.
Lemma arepA_len_nonneg FA len cps σ m : arepA FA len cps σ m -> 0 <= len.
Proof. intros ((H & _) & _). unfold zlength in H. lia. Qed.
Lemma arepA_cps_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> 0 <= znth 0 cps i < 2^32.
Proof. intros ((HL & HF & _) & _) Hi. apply (Forall_znth u32ok 0); [exact HF| lia]. Qed.
Lemma arepA_types_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> 0 <= znth 0 (f_types σ) i < 2^32.
Proof. intros (_ & (HL & HF & _) & _) Hi. apply (Forall_znth u32ok 0); [exact HF| lia]. Qed.
Lemma arepA_btypes_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> 0 <= znth 0 (f_btypes σ) i < 2^32.
Proof. intros (_ & _ & (HL & HF & _) & _) Hi. apply (Forall_znth u32ok 0); [exact HF| lia]. Qed.
Lemma arepA_levels_range FA len cps σ m i : arepA FA len cps σ m -> 0 <= i < len -> -128 <= znth 0 (f_levels σ) i < 128.
Proof. intros (_ & _ & _ & (HL & HF & _)) Hi. apply (Forall_znth s8ok 0); [exact HF| lia]. Qed.

Lemma arepA_ext FA len cps σ σ' m : arepA FA len cps σ m ->
f_types σ' = f_types σ -> f_btypes σ' = f_btypes σ -> f_levels σ' = f_levels σ -> arepA FA len cps σ' m.
Proof. intros AR E1 E2 E3. unfold arepA. rewrite E1, E2, E3. exact AR. Qed.

Lemma arepA_read_str FA len cps σ m i a :
arepA FA len cps σ m -> 0 <= i < len -> a = wa (fa_str FA + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (znth 0 cps i))).
Proof.
intros ((HL & HF & HB) & _) Hi ->.
pose proof (nth_error_map_znth (Z_to_bv 64) 0 cps i ltac:(lia)) as Hn.
destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m (fa_str FA) (u32s (map (Z_to_bv 64) cps)) (4 * Z.to_nat i) 4 HB).
2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma arepA_read_types FA len cps σ m i a :
arepA FA len cps σ m -> 0 <= i < len -> a = wa (fa_types FA + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (znth 0 (f_types σ) i))).
Proof.
intros (_ & (HL & HF & HA) & _) Hi Ha. eapply u32arr_read; [exact HA| apply (nth_error_map_znth _ 0); lia| lia| exact Ha].
Qed.
Lemma arepA_read_btypes FA len cps σ m i a :
arepA FA len cps σ m -> 0 <= i < len -> a = wa (fa_btypes FA + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (znth 0 (f_btypes σ) i))).
Proof.
intros (_ & _ & (HL & HF & HA) & _) Hi Ha. eapply u32arr_read; [exact HA| apply (nth_error_map_znth _ 0); lia| lia| exact Ha].
Qed.

Lemma arepA_store_types FA len Astr nstr cps σ m i v (w : word) :
ageom FA len Astr nstr -> arepA FA len cps σ m ->
0 <= i < len -> bv_unsigned w mod 2^32 = v mod 2^32 -> 0 <= v < 2^32 ->
store_ok segs m (wa (fa_types FA + 4 * i)) 4 = true
/\ arepA FA len cps (set_types (zupd (f_types σ) i v) σ) (write_to_mem m (wa (fa_types FA + 4 * i)) (le4 w)).
Proof.
intros GE AR Hi Hw Hv. pose proof AR as ((CL & CF & CB) & (TL & TF & TA) & (BL & BF & BA) & (LL & LF & LA)).
pose proof (ageom_nums _ _ _ _ GE ltac:(lia)) as NU. cbv zeta in NU.
destruct NU as (S1 & S2 & _ & A1 & A2 & T1 & T2 & B1 & B2 & L1 & L2 & D1 & D2 & D3 & D4 & D5 & D6).
assert (SOK : store_ok segs m (wa (fa_types FA + 4 * i)) 4 = true).
{ eapply u32arr_store_ok; [exact TA| | reflexivity]. rewrite length_map. unfold zlength in TL. lia. }
split; [exact SOK|].
assert (EW : le4 w = le4 (Z_to_bv 64 v)).
{ rewrite <- (Z_to_bv_lit_self w). apply le4_eqm. exact Hw. }
unfold arepA. destruct σ as [rr pp ww nn tt bb ll]; cbn [f_types f_btypes f_levels set_types] in *.
split; [|split; [|split]].
- split; [exact CL|]. split; [exact CF|].
apply bytes_at_write_other; [exact CB| lia| rewrite length_le4; lia|].
rewrite length_le4, u32s_length, length_map. unfold zlength in CL. lia.
- split; [rewrite zlength_zupd; exact TL|]. split; [apply Forall_zupd; [exact TF| exact Hv]|].
rewrite map_zupd, zupd_upd, EW by lia. eapply u32arr_write; [exact TA| rewrite length_map; unfold zlength in TL; lia].
- split; [exact BL|]. split; [exact BF|].
apply u32arr_frame; [exact BA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in BL. lia.
- split; [exact LL|]. split; [exact LF|].
apply u8arr_frame; [exact LA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in LL. lia.
Qed.

Lemma arepA_store_btypes FA len Astr nstr cps σ m i v (w : word) :
ageom FA len Astr nstr -> arepA FA len cps σ m ->
0 <= i < len -> bv_unsigned w mod 2^32 = v mod 2^32 -> 0 <= v < 2^32 ->
store_ok segs m (wa (fa_btypes FA + 4 * i)) 4 = true
/\ arepA FA len cps (set_btypes (zupd (f_btypes σ) i v) σ) (write_to_mem m (wa (fa_btypes FA + 4 * i)) (le4 w)).
Proof.
intros GE AR Hi Hw Hv. pose proof AR as ((CL & CF & CB) & (TL & TF & TA) & (BL & BF & BA) & (LL & LF & LA)).
pose proof (ageom_nums _ _ _ _ GE ltac:(lia)) as NU. cbv zeta in NU.
destruct NU as (S1 & S2 & _ & A1 & A2 & T1 & T2 & B1 & B2 & L1 & L2 & D1 & D2 & D3 & D4 & D5 & D6).
assert (SOK : store_ok segs m (wa (fa_btypes FA + 4 * i)) 4 = true).
{ eapply u32arr_store_ok; [exact BA| | reflexivity]. rewrite length_map. unfold zlength in BL. lia. }
split; [exact SOK|].
assert (EW : le4 w = le4 (Z_to_bv 64 v)).
{ rewrite <- (Z_to_bv_lit_self w). apply le4_eqm. exact Hw. }
unfold arepA. destruct σ as [rr pp ww nn tt bb ll]; cbn [f_types f_btypes f_levels set_btypes] in *.
split; [|split; [|split]].
- split; [exact CL|]. split; [exact CF|].
apply bytes_at_write_other; [exact CB| lia| rewrite length_le4; lia|].
rewrite length_le4, u32s_length, length_map. unfold zlength in CL. lia.
- split; [exact TL|]. split; [exact TF|].
apply u32arr_frame; [exact TA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in TL. lia.
- split; [rewrite zlength_zupd; exact BL|]. split; [apply Forall_zupd; [exact BF| exact Hv]|].
rewrite map_zupd, zupd_upd, EW by lia. eapply u32arr_write; [exact BA| rewrite length_map; unfold zlength in BL; lia].
- split; [exact LL|]. split; [exact LF|].
apply u8arr_frame; [exact LA| lia| rewrite length_le4; lia|].
rewrite length_le4, length_map. unfold zlength in LL. lia.
Qed.

Lemma arepA_munch_hi FA len Astr nstr cps σ m m' W :
ageom FA len Astr nstr -> 0 < len -> arepA FA len cps σ m ->
munch W m m' -> wmono segs m m' -> Forall (fun iv => band_lo <= fst iv) W ->
arepA FA len cps σ m'.
Proof.
intros GE L AR MU WM HW.
pose proof (ageom_nums _ _ _ _ GE L) as NU. cbv zeta in NU.
destruct NU as (S1 & S2 & _ & A1 & A2 & T1 & T2 & B1 & B2 & L1 & L2 & _).
pose proof AR as ((CL & CF & CB) & (TL & TF & TA) & (BL & BF & BA) & (LL & LF & LA)).
assert (DJ : forall A n, A + n <= band_lo -> disjoint_from W A n).
{ intros A n HA. clear -HW HA. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
inversion HW as [|x l H1 H2]; subst. cbn in H1. split; [lia| apply IH; exact H2]. }
unfold arepA. split; [|split; [|split]].
- split; [exact CL|]. split; [exact CF|].
eapply bytes_at_transport; [exact CB| exact MU|]. rewrite u32s_length, length_map. unfold zlength in CL. apply DJ. lia.
- split; [exact TL|]. split; [exact TF|]. eapply u32arr_transport; [exact TA| exact MU| exact WM|]. rewrite length_map. unfold zlength in TL. apply DJ. lia.
- split; [exact BL|]. split; [exact BF|]. eapply u32arr_transport; [exact BA| exact MU| exact WM|]. rewrite length_map. unfold zlength in BL. apply DJ. lia.
- split; [exact LL|]. split; [exact LF|]. eapply u8arr_transport; [exact LA| exact MU| exact WM|]. rewrite length_map. unfold zlength in LL. apply DJ. lia.
Qed.

Lemma arepA_munch_nil FA cps σ m m' :
arepA FA 0 cps σ m -> wmono segs m m' -> arepA FA 0 cps σ m'.
Proof.
intros ((CL & CF & CB) & (TL & TF & [TB TW]) & (BL & BF & [BB BW]) & (LL & LF & [LB1 LW])) WM.
assert (E : forall (l : list Z), zlength l = 0 -> l = []) by (intros [|x l] H; [reflexivity| unfold zlength in H; cbn in H; lia]).
pose proof (E _ CL) as E1. pose proof (E _ TL) as E2. pose proof (E _ BL) as E3. pose proof (E _ LL) as E4.
assert (B0 : forall A m1 m2, bytes_at segs m1 A [] -> bytes_at segs m2 A []).
{ intros A m1 m2 (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros i Hi. cbn in Hi. lia. }
unfold arepA, u32arr, u8arr. rewrite E1, E2, E3, E4 in *. cbn [map u32s length Z.of_nat Z.mul] in *.
split; [| split; [| split]]; (split; [assumption|]); (split; [assumption|]).
- eapply B0; eassumption.
- split; [eapply B0; eassumption| eapply wr_at_transport; eauto].
- split; [eapply B0; eassumption| eapply wr_at_transport; eauto].
- split; [eapply B0; eassumption| eapply wr_at_transport; eauto].
Qed.

End AArr.

Arguments arepA segs {ptr} FA len cps σ m : simpl never.
Arguments arepA_lens {segs ptr FA len cps σ m} _.
Arguments arepA_len_nonneg {segs ptr FA len cps σ m} _.
Arguments arepA_cps_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_types_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_btypes_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_levels_range {segs ptr FA len cps σ m} i _ _.
Arguments arepA_ext {segs ptr FA len cps σ σ' m} _ _ _ _.
Arguments arepA_read_str {segs ptr FA len cps σ m} i a _ _ _.
Arguments arepA_read_types {segs ptr FA len cps σ m} i a _ _ _.
Arguments arepA_read_btypes {segs ptr FA len cps σ m} i a _ _ _.
Arguments arepA_store_types {BAND} {segs ptr FA len Astr nstr cps σ m} i v w _ _ _ _ _.
Arguments arepA_store_btypes {BAND} {segs ptr FA len Astr nstr cps σ m} i v w _ _ _ _ _.
Arguments arepA_munch_hi {BAND} {segs ptr FA len Astr nstr cps σ m m' W} _ _ _ _ _ _.
Arguments arepA_munch_nil {segs ptr FA cps σ m m'} _ _.

Ltac arr_getreg n :=
lazymatch goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
lazymatch v with
| Some ?w => w
| _ => fail "arr_getreg: register" n "not concrete"
end
end.
Ltac arr_lia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac arr_addr := unfold wa; f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; arr_lia.

Ltac areadA_fin H :=
let H2 := fresh "RD" in
lazymatch type of H with
| ?P1 -> ?P2 -> ?T => assert (H2 : T) by (apply H; [arr_lia | arr_addr]); clear H
end.
Tactic Notation "areadA_str" constr(AR) constr(rs) constr(k) :=
let a := arr_getreg rs in let H := fresh in pose proof (arepA_read_str k a AR) as H; areadA_fin H.
Tactic Notation "areadA_types" constr(AR) constr(rs) constr(k) :=
let a := arr_getreg rs in let H := fresh in pose proof (arepA_read_types k a AR) as H; areadA_fin H.
Tactic Notation "areadA_btypes" constr(AR) constr(rs) constr(k) :=
let a := arr_getreg rs in let H := fresh in pose proof (arepA_read_btypes k a AR) as H; areadA_fin H.
Ltac arr_clear := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.
Ltac anormA :=
repeat match goal with
| |- context [zx32 (Z_to_bv 64 ?v)] => rewrite (zx32_small v) by lia
| |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_small v) by lia
| |- context [zxb (Z_to_bv 8 ?v)] => rewrite (zxb_b8 v); rewrite (Z.mod_small v 256) by lia
| |- context [sxb (Z_to_bv 8 ?v)] => rewrite (sxb_b8 v) by lia
end.

Ltac astoreA H AR :=
let HS := fresh "HS" in let ARn := fresh "ARn" in
destruct H as [HS ARn];
step;
lazymatch type of ARn with
| arepA ?segs _ _ _ _ (write_to_mem ?m (wa ?a) ?bs) =>
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ ?mg _) => replace mg with (write_to_mem m (wa a) bs) by (first [reflexivity | f_equal; unfold wa; f_equal; lia])
end;
try (lazymatch goal with
| HI : mem_inv segs m |- _ => apply (mem_inv_store segs m (wa a) bs) in HI; [| simpl_sizes; exact HS]
end);
transport_chunks segs m a bs;
repeat match goal with
| ST : stk segs m ?lo ?hi |- _ => apply (stk_write segs m lo hi a bs) in ST; [| lia | simpl_sizes; slia]
| WM : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WM
| MU : munch ?Wq ?mq m |- _ =>
first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
| fail 100 "astoreA: store outside the declared footprint:" a ]
end;
clear HS; clear AR; rename ARn into AR;
let m' := fresh "m" in let E := fresh in
remember (write_to_mem m (wa a) bs) as m' eqn:E; clear E;
repeat match goal with
| Hx : ov_read_bytes _ m _ _ = Some _ |- _ => clear Hx
| Hx : store_ok _ m _ _ = true |- _ => clear Hx
end;
try clear m
end.
