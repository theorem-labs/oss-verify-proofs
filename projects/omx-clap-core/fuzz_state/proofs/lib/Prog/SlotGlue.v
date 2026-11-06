From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit HState HStateRoom KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition SLOT_OPS : nat := 200.
Definition SLOT_SIZE : Z := 2 ^ 25.

Lemma hs_rb_app : forall b o1 o2, hs_rb b (o1 ++ o2) = hs_rb (hs_rb b o1) o2.
Proof.
  intros b o1. revert b. induction o1 as [|[x|x] o1 IH]; intros b o2; cbn [app hs_rb]; [reflexivity | apply IH | apply IH].
Qed.

Lemma hs_room_app : forall b o1 o2, hs_room b (o1 ++ o2) -> hs_room b o1 /\ hs_room (hs_rb b o1) o2.
Proof.
  intros b o1. revert b. induction o1 as [|[x|x] o1 IH]; intros b o2 H; cbn [app hs_room hs_rb] in *.
  - split; [exact I | exact H].
  - destruct H as [H1 H2]. destruct (IH _ _ H2) as [H3 H4]. split; [split; assumption | exact H4].
  - exact (IH _ _ H).
Qed.

Lemma hs_small_app : forall S o1 o2, hs_small S o1 -> hs_small S o2 -> hs_small S (o1 ++ o2).
Proof. intros S o1 o2 H1 H2. unfold hs_small in *. apply Forall_app. split; assumption. Qed.

Lemma room_at : forall b0 N S ops ops2, hs_room_all b0 N S -> hs_small S ops -> hs_small S ops2 ->
  (length ops + length ops2 <= N)%nat -> hs_room (hs_rb b0 ops) ops2.
Proof.
  intros b0 N S ops ops2 H H1 H2 Hl.
  apply (proj2 (hs_room_app b0 ops ops2 (H (ops ++ ops2) ltac:(rewrite length_app; lia) (hs_small_app S _ _ H1 H2)))).
Qed.

Lemma room_all_at : forall b0 N S ops M, hs_room_all b0 N S -> hs_small S ops ->
  (length ops + M <= N)%nat -> hs_room_all (hs_rb b0 ops) M S.
Proof.
  intros b0 N S ops M H H1 Hl ops2 Hl2 H2. apply (room_at b0 N S ops ops2 H H1 H2). lia.
Qed.

Lemma statics_G : forall a, alloc_statics a <-> in_globals omx_G a.
Proof.
  intros a. unfold alloc_statics, in_globals, omx_G, G_LIVE, G_PEAK, G_COUNT, G_FAIL. split.
  - intros [H|[H|[H|H]]].
    + exists 0x33450, 8. split; [left; reflexivity | lia].
    + exists 0x33458, 8. split; [right; left; reflexivity | lia].
    + exists 0x33460, 8. split; [right; right; left; reflexivity | lia].
    + exists 0x231e0, 8. split; [right; right; right; left; reflexivity | lia].
  - intros (lo & len & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma omx_G_frame : forall a, in_globals omx_G a -> in_globals FrameAPI.frame_G a.
Proof.
  intros a Ha. apply statics_G in Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
  unfold in_globals, FrameAPI.frame_G.
  destruct Ha as [H|[H|[H|H]]];
    first [ exists 0x33450, 24; split; [right; left; reflexivity | lia]
          | exists 0x231e0, 8; split; [left; reflexivity | lia] ].
Qed.

Lemma pow_slack : forall x, 0 <= x -> 8 * ((x + 7) / 8) - x = (- x) mod 8.
Proof. intros x Hx. Z.div_mod_to_equations. lia. Qed.

Section Glue.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma globals_free_sub : forall G G', globals_free B API G -> (forall a, in_globals G' a -> in_globals G a) ->
  globals_free B API G'.
Proof. intros G G' H Hs a Ha. exact (H a (Hs a Ha)). Qed.

Lemma present_mbyte : forall mem a, present mem a -> exists b, mbyte (ms_segs B) mem a = Some b.
Proof. intros mem a (b & Hb). exists b. unfold mbyte. rewrite Hb. reflexivity. Qed.

Lemma slack_exists : forall L A mem md t k, block_slack_present B API -> MR L A mem md ->
  In (t, k) (blocks L A) -> 0 <= k ->
  exists slack, Z.of_nat (length slack) = (- (t + k)) mod 8 /\ Mem.bytes_at (ms_segs B) mem (t + k) slack.
Proof.
  intros L A mem md t k BS HM Hin Hk.
  pose proof Hin as Hin'. unfold blocks in Hin'. apply in_map_iff in Hin' as ([q k'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as E1 E2. subst k'.
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq) as R. rewrite E1 in R.
  pose proof alloc_ceiling_lt as Hc.
  set (s := (- (t + k)) mod 8).
  assert (Hs : 0 <= s < 8) by (unfold s; apply Z.mod_pos_bound; lia).
  assert (Hpr : forall i, 0 <= i < s -> present mem (t + k + i)).
  { intros i Hi. apply (BS L A mem md t k (t + k + i) HM Hin).
    pose proof (pow_slack (t + k) ltac:(lia)) as P. fold s in P. lia. }
  exists (map (fun i => match mbyte (ms_segs B) mem (t + k + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end)
            (seq 0 (Z.to_nat s))).
  rewrite length_map, length_seq. split; [lia|].
  split; [lia|]. rewrite length_map, length_seq. split; [lia|].
  intros i Hi.
  rewrite nth_error_map, nth_error_seq. destruct (i <? Z.to_nat s)%nat eqn:Lt; [|apply Nat.ltb_ge in Lt; lia].
  cbn [option_map]. rewrite Nat.add_0_l.
  destruct (present_mbyte mem (t + k + Z.of_nat i) (Hpr (Z.of_nat i) ltac:(lia))) as (bb & Hb).
  change (Mem.mrd (ms_segs B) mem (Mem.wa (t + k + Z.of_nat i))) with (mbyte (ms_segs B) mem (t + k + Z.of_nat i)).
  rewrite Hb. reflexivity.
Qed.

End Glue.
