(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/DriverSlots.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO0o YO03 YO04.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import
  AllocSI AllocGS AllocMB AllocMalloc AllocFree AllocMallocMB AllocFreeMB AllocSlots AllocRoom.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition DI (s : astate) : Prop := WF s /\ SI s /\ GS s /\ NL s /\ noraw s /\ MB s.
Lemma DI_init : DI init_state.
Proof using. exact (conj wf_init (conj SI_init (conj GS_init (conj NL_init (conj noraw_init MB_init))))). Qed.
Lemma DI_malloc : forall s n tr r s', DI s -> 0 <= n -> yields (malloc n s) tr (r, s') -> DI s'.
Proof using.
  intros s n tr r s' (HW & HS & HG & HN & HR & HM) Hn Hy.
  exact (conj (malloc_wf s n tr r s' HW Hn Hy) (conj (malloc_SI s n tr r s' HW HS Hn Hy)
    (conj (malloc_GS s n tr r s' HW HG Hn Hy) (conj (malloc_NL s n tr r s' HW HN Hn Hy)
    (conj (malloc_noraw s n tr r s' HR Hy) (malloc_MB s n tr r s' HW HM Hn Hy)))))).
Qed.
Lemma DI_free : forall s p n tr s', DI s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') -> DI s'.
Proof using.
  intros s p n tr s' (HW & HS & HG & HN & HR & HM) Hin Hy.
  exact (conj (free_wf s p n tr s' HW Hin Hy) (conj (free_SI s p n tr s' HW HS Hin Hy)
    (conj (free_GS s p n tr s' HW HG Hin Hy) (conj (free_NL s p n tr s' HW HN Hin Hy)
    (conj (free_noraw s p n tr s' HW Hin HR Hy) (free_MB s p n tr s' HW HM Hin Hy)))))).
Qed.
Lemma leaves_T {A : Type} : forall t : itree astate A, leaves (fun _ => True) t.
Proof using. induction t as [a | q s k IH | e]; cbn; auto. Qed.
Definition rd_inv (L : Z) (r : rd_result * astate) : Prop :=
  match fst r with
  | RdLoaded buf cap => DI (snd r) /\ nblocks (snd r) = 1 /\ ubytes (snd r) = cap /\
      In (buf, cap) (user_blocks (snd r)) /\ L < cap /\ cap < 2 * MAX_INPUT
  | _ => True
  end.
Lemma read_phase_slots : forall fuel L cap buf s,
  DI s -> nblocks s = 1 -> ubytes s = cap -> In (buf, cap) (user_blocks s) -> 0 < cap < 2 * MAX_INPUT ->
  leaves (rd_inv L) (read_phase fuel L cap buf s).
Proof using.
  induction fuel as [|fuel IH]; intros L cap buf s HD Hnb Hub Hin Hcap; cbn [read_phase].
  - apply leaves_ret. exact I.
  - destruct (L <? cap) eqn:E1.
    + apply leaves_ret. apply Z.ltb_lt in E1. unfold rd_inv. cbn [fst snd].
      refine (conj HD (conj Hnb (conj Hub (conj Hin (conj E1 _))))). lia.
    + destruct (MAX_INPUT <=? cap) eqn:E2; [apply leaves_ret; exact I|]. apply Z.leb_gt in E2.
      eapply leaves_mbind; [apply leaves_T|].
      intros [nb|] s1 tr1 Hy1 _; [|apply leaves_ret; exact I].
      pose proof (DI_malloc s (2 * cap) tr1 (Some nb) s1 HD ltac:(lia) Hy1) as HD1.
      destruct (malloc_blocks s (2 * cap) tr1 (Some nb) s1 (proj1 HD) ltac:(lia) Hy1) as (l1 & l2 & E3 & E4 & _).
      destruct (blocks_add_counts s s1 nb (2 * cap) l1 l2 E3 E4) as [C1 C2].
      assert (Hin1 : In (buf, cap) (user_blocks s1)).
      { rewrite E3. rewrite E4 in Hin. apply in_app_iff in Hin. apply in_app_iff. destruct Hin; [left | right; right]; assumption. }
      assert (Hnb1 : In (nb, 2 * cap) (user_blocks s1)) by (rewrite E3; apply in_app_iff; right; left; reflexivity).
      eapply leaves_mbind; [apply leaves_T|].
      intros [] s2 tr2 Hy2 _.
      pose proof (DI_free s1 buf cap tr2 s2 HD1 Hin1 Hy2) as HD2.
      destruct (free_blocks s1 buf cap tr2 s2 (proj1 HD1) Hin1 Hy2) as (m1 & m2 & E5 & E6).
      destruct (blocks_del_counts s1 s2 buf cap m1 m2 (proj1 HD1) E5 E6) as (D1 & D2 & _).
      apply IH; [exact HD2 | lia | lia | | lia].
      rewrite E6. rewrite E5 in Hnb1. apply in_app_iff in Hnb1. apply in_app_iff.
      destruct Hnb1 as [H|[H|H]]; [left; exact H | | right; exact H].
      exfalso. injection H as _ H. lia.
Qed.
Definition run_slots (b : sbound) (r : dleaf * astate) : Prop :=
  match fst r with
  | DL_run _ _ _ => res_ok_slots (snd r) b
  | _ => True
  end.
Definition drv_inv (r : dleaf * astate) : Prop :=
  match fst r with
  | DL_run _ _ _ => DI (snd r) /\ nblocks (snd r) <= 2 /\ ubytes (snd r) <= 2 ^ 28
  | _ => True
  end.
Lemma driver_inv data : leaves drv_inv (driver_tree data).
Proof using.
  unfold driver_tree, driver_m.
  eapply leaves_mbind; [apply leaves_T|].
  intros [b0|] s1 tr1 Hy1 _; [|apply leaves_ret; exact I].
  assert (HC0 : 0 <= CAP0) by (unfold CAP0; lia).
  pose proof (DI_malloc init_state CAP0 tr1 (Some b0) s1 DI_init HC0 Hy1) as HD1.
  destruct (malloc_blocks init_state CAP0 tr1 (Some b0) s1 wf_init HC0 Hy1) as (l1 & l2 & E1 & E2 & _).
  destruct (blocks_add_counts init_state s1 b0 CAP0 l1 l2 E1 E2) as [C1 C2].
  assert (N0 : nblocks init_state = 0 /\ ubytes init_state = 0) by (split; reflexivity).
  assert (Hin1 : In (b0, CAP0) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
  eapply leaves_mbind.
  { apply (read_phase_slots READ_FUEL (dlen data) CAP0 b0 s1 HD1 ltac:(lia) ltac:(lia) Hin1).
    unfold CAP0, MAX_INPUT. lia. }
  intros rd s2 tr2 Hy2 Hr. unfold rd_inv in Hr. cbn [fst snd] in Hr.
  destruct rd as [ | | buf cap]; [apply leaves_ret; exact I | apply leaves_ret; exact I |].
  destruct Hr as (HD2 & Hnb2 & Hub2 & Hin2 & HL & Hcap).
  destruct (dlen data <? HDR_MIN) eqn:E5; [apply leaves_ret; exact I|].
  destruct (dlen data <? HDR_MIN + config_len data) eqn:E6; [apply leaves_ret; exact I|].
  apply Z.ltb_ge in E6.
  assert (Hcl : 0 <= config_len data) by (unfold config_len; apply Z.mod_pos_bound; lia).
  assert (Hpl : 0 <= payload_len data < cap) by (unfold payload_len, HDR_MIN in *; lia).
  destruct (payload_len data =? 0) eqn:E7.
  { apply leaves_ret. unfold drv_inv. cbn [fst snd]. unfold MAX_INPUT in Hcap. split; [exact HD2 | lia]. }
  eapply leaves_mbind; [apply leaves_T|].
  intros [q|] s3 tr3 Hy3 _; apply leaves_ret; [|exact I].
  unfold drv_inv. cbn [fst snd].
  pose proof (DI_malloc s2 (payload_len data) tr3 (Some q) s3 HD2 (proj1 Hpl) Hy3) as HD3.
  destruct (malloc_blocks s2 (payload_len data) tr3 (Some q) s3 (proj1 HD2) (proj1 Hpl) Hy3) as (m1 & m2 & E8 & E9 & _).
  destruct (blocks_add_counts s2 s3 q (payload_len data) m1 m2 E8 E9) as [D1 D2].
  unfold MAX_INPUT in Hcap. split; [exact HD3 | lia].
Qed.
Definition SBD : sbound := SB 2 (2 ^ 28) CAPMAX.
Lemma res_ok_slots_SBD : forall s, res_ok s DRB -> DI s -> nblocks s <= 2 -> ubytes s <= 2 ^ 28 -> res_ok_slots s SBD.
Proof using.
  intros s HR (HW & HS & HG & HN & HNR & HM) Hnb Hub.
  destruct HR as (HII & _ & _ & Hh & _).
  unfold res_ok_slots, SBD, HCAP, CAPMAX, DRB in *. cbn [sb_live sb_bytes sb_cap rb_hand] in *.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
Theorem driver_slots data : leaves (run_slots SBD) (driver_tree data).
Proof using.
  eapply leaves_mono; [| exact (leaves_and _ _ _ (driver_res data) (driver_inv data))].
  intros [d s] [HR HI]. unfold run_slots, drv_inv in *. cbn [fst snd] in *.
  destruct d; try exact I. destruct HI as (HD & Hnb & Hub). exact (res_ok_slots_SBD s HR HD Hnb Hub).
Qed.
End a.
