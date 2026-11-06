From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04 YO0d_cf YO0n_cf.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05 YM0b PlaceCapW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition rb_live (b : rbound) : Z := rb_bytes b + rb_brk b + 4 * PGSZ * shcap (rb_hand b).
Lemma res_live s b : res_ok s b -> LIVE_UB s + area s <= rb_live b.
Proof using.
intros (HII & B1 & B2 & B3 & B4).
pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & _).
pose proof (shcap_ok s HII) as SC. pose proof (shcap_mono _ _ B3) as SM.
pose proof (Z.pow_pos_nonneg 2 (shift s) ltac:(lia) Hsh).
unfold rb_live, LIVE_UB, area. rewrite Hrt. unfold PGSZ in *. nia.
Qed.
Lemma roomcf_malloc_res s b n X : WF s -> res_ok s b -> room b n ->
rb_live b + 3 * PGSZ + Z.max MMAX (page_round (n + IB + UNIT)) <= X -> roomcf X (malloc n s).
Proof using.
intros HW HR HRm HX. pose proof (room_size n b HRm) as [_ Hn]. pose proof (res_live s b HR).
pose proof (res_room s b n HR HRm) as HR4. pose proof HR4 as (_ & _ & RA & RP).
assert (SL : SLOT_UB s + 5 <= MG_SLOTS).
{ destruct HR as (HII & B1 & B2 & B3 & B4). destruct HRm as (R0 & R1 & R2 & R3 & R5).
pose proof HII as (NN & Hsh & Hac & Hamc & Hrt & Hrc & _).
pose proof (shcap_ok s HII) as SC. pose proof (shcap_mono _ _ B3) as SM.
pose proof (Z.div_le_mono _ _ PGSZ ltac:(unfold PGSZ; lia) B4) as DB.
unfold SLOT_UB. lia. }
assert (GE : MG_SLOTS + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area s))).
{ apply slot_capW_ge. pose proof MMAX_le_REQ. assert (0 < MMAX) by (unfold MMAX; reflexivity). lia. }
apply (roomcf_malloc n s X (malloc_reqs_ok s n HW ltac:(lia)) (proj1 HR) ltac:(lia) HR4); [lia | intros _; lia].
Qed.
Lemma roomcf_free_res s b p n X : WF s -> In (p, n) (user_blocks s) -> res_ok s b -> rb_live b <= X ->
roomcf X (free (Some p) s).
Proof using.
intros HW Hin HR HX. pose proof (res_live s b HR). pose proof (area_nonneg s (proj1 HR)).
apply (roomcf_free (Some p) s X (free_reqs_ok s p n HW Hin) (proj1 HR)). lia.
Qed.
Lemma roomcf_mono {A} : forall (t : itree astate A) X Y, X <= Y -> roomcf X t -> roomcf Y t.
Proof using.
induction t as [a | q s k IH | e]; intros X Y HXY H; cbn in *; try exact I.
destruct H as [H1 [H2 H3]]. split; [intros Hc; specialize (H1 Hc); lia|]. split.
- intros Hs HYl. destruct (H2 Hs ltac:(lia)) as (S1 & S2 & S3). split; [lia | exact (conj S2 S3)].
- intros z Hz. exact (IH z X Y HXY (H3 z Hz)).
Qed.
End d.
