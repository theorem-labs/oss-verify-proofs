From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04 YO0d_cf YO0n_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YM0b.
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
apply (roomcf_malloc n s X (malloc_reqs_ok s n HW ltac:(lia)) (proj1 HR) ltac:(lia) (res_room s b n HR HRm)). lia.
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
destruct H as [H1 H2]. split; [intros Hc; specialize (H1 Hc); lia | intros z Hz; exact (IH z X Y HXY (H2 z Hz))].
Qed.
End d.
