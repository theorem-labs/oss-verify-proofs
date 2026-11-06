(* reac-pw/fuzz_link, image A: the shadow of the image globals a walk re-states after a callee.

   A callee's apost (link_amem.v) does not keep the shadow bytes of an image global: akept keeps the stack above
   the allocator's ceiling, the heap blocks, the image bytes and the side frames with their shadow, and a global's
   shadow is none of these. So a walk that calls two callees whose Pres both ask `range_addressable` /
   `shadow_hull_vis` of g_nl (reac_served_unmark_all: reac_link_alias_read then reac_link_alias_write; the alias
   callees: fuzz_if_nametoindex then nl_talk; nl_talk: fuzz_send then fuzz_recv) cannot carry those facts across
   the first call from the contracts. They hold at every allocator state by AR instead: AR's `am_zshadow`
   (Reusable/YG0n.v zshadow_ok) makes every row of `as_zero_shadow B` zero shadow, and the lib/A frame's instance
   fixes `as_zero_shadow B = Tfib_zero_shadow` (lib/A/AF0m.v PcapSyms field ts_zsh); the bytes of a shadow hull past
   a zero row are the instance's constant shadow cells (AR's `am_const`, AF0m.v ts_const), as lib/A/AE37.v
   shw_byte_present reads them. Every closed callee lemma of the frame takes `PcapSyms B`, so a walk's
   `Hypothesis TB : PcapSyms B` is discharged by the slot walk's B exactly as theirs are.

   - zsh_row_zero: a row of Tfib_zero_shadow is zero shadow at every AR state.
   - zsh_range_find / zsh_hull_find: [p, p + k) inside an 8-aligned row (found by `find_row`, checked by
     computation) is addressable, and its shadow hull is visible when every hull byte past the row is a constant
     cell (checked by computation over `all_from`).
   - the instances: g_nl [LA_G_NL, LA_G_NL + NK_SIZE) and errno [as_errno B, as_errno B + 4), at every AR state, in
     the `aview` and the `ard` (link_amem.v) forms.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the computed checks ---- *)
Definition row_ok (p k : Z) (r : Z * Z) : bool :=
  (fst r mod 8 =? 0) && ((fst r + snd r) mod 8 =? 0) && (fst r <=? p) && (p + k <=? fst r + snd r).
Definition find_row (p k : Z) : option (Z * Z) := find (row_ok p k) Tfib_zero_shadow.

Lemma find_row_sound : forall p k r, find_row p k = Some r ->
  In r Tfib_zero_shadow /\ fst r mod 8 = 0 /\ (fst r + snd r) mod 8 = 0 /\ fst r <= p /\ p + k <= fst r + snd r.
Proof.
  intros p k r H. unfold find_row in H. destruct (find_some _ _ H) as [Hin Hok]. unfold row_ok in Hok.
  apply andb_prop in Hok as [Hok H4]. apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. tauto.
Qed.

Fixpoint all_from (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => f a && all_from f (a + 1) n' end.

Lemma all_from_spec : forall f n a s, all_from f a n = true -> a <= s < a + Z.of_nat n -> f s = true.
Proof.
  intros f n. induction n as [|n IH]; intros a s H Hs; cbn [all_from] in H; [lia|].
  apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec s a) as [-> | Hne]; [exact H1|]. apply (IH (a + 1)); [exact H2 | lia].
Qed.

(* a byte that one of the instance's constant cells holds *)
Definition const_byte_b (ly : alayout) (s : Z) : bool :=
  match cell_lookup (Tfib_const ly) (ANum s) with
  | Some (ACell (ANum a') w (AV _)) => (a' =? s) && Nat.ltb 0 w
  | _ => false
  end.

(* the end of the shadow hull of [p, p + k) (YG0d.v shadow_hull_vis) *)
Definition hull_end (p k : Z) : Z := shadow_addr (p + k - 1) / 8 * 8 + 8.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma zsh_row_zero : forall ly S rd lo n, ARm B ly S rd -> In (lo, n) Tfib_zero_shadow ->
  zero_shadow rd SHADOW_OFF lo n.
Proof.
  intros ly S rd lo n HM Hin.
  pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S rd HM) (lo, n)
    ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh B TB); exact Hin)) as HZ.
  exact HZ.
Qed.

Lemma const_byte_vis : forall ly S rd s, ARm B ly S rd -> const_byte_b ly s = true -> rd s <> None.
Proof.
  intros ly S rd s HM Hb. unfold const_byte_b in Hb.
  destruct (cell_lookup (Tfib_const ly) (ANum s)) as [[ca w cv]|] eqn:HL; [|discriminate].
  destruct ca; try discriminate. destruct cv as [e|]; [|discriminate].
  apply andb_prop in Hb as [Ha Hw]. apply Z.eqb_eq in Ha. apply Nat.ltb_lt in Hw. subst z.
  pose proof (proj1 (Forall_forall (cell_holds B ly rd) (as_const B ly)) (am_const B ly S rd HM)
    (ACell (ANum s) w (AV e)) ltac:(rewrite (ts_const B TB ly); exact (cell_lookup_In _ _ _ HL))) as Hc.
  unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
  specialize (Hc 0%nat Hw). rewrite Z.add_0_r in Hc. rewrite Hc. discriminate.
Qed.

Lemma zsh_range_find : forall ly S rd p k r, ARm B ly S rd -> find_row p k = Some r ->
  range_addressable rd SHADOW_OFF p k.
Proof.
  intros ly S rd p k [lo n] HM Hf x Hx.
  destruct (find_row_sound p k (lo, n) Hf) as (Hin & H8 & H8' & Hlo & Hhi). cbn [fst snd] in *.
  pose proof (zsh_row_zero ly S rd lo n HM Hin) as HZ. unfold zero_shadow in HZ.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr in *.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + lo / 8 + (x / 8 - lo / 8)) by lia.
  apply HZ. lia.
Qed.

Lemma zsh_hull_find : forall ly S rd p k r, ARm B ly S rd -> find_row p k = Some r -> 0 < k ->
  shadow_addr (fst r) <= shadow_addr p / 8 * 8 ->
  all_from (const_byte_b ly) (shadow_addr (fst r) + snd r / 8)
    (Z.to_nat (hull_end p k - (shadow_addr (fst r) + snd r / 8))) = true ->
  shadow_hull_vis rd p k.
Proof.
  intros ly S rd p k [lo n] HM Hf Hk Hstart Hc s Hs.
  destruct (find_row_sound p k (lo, n) Hf) as (Hin & H8 & H8' & Hlo & Hhi). cbn [fst snd] in *.
  destruct (Z_lt_le_dec s (shadow_addr lo + n / 8)) as [Hrow | Hpast].
  - pose proof (zsh_row_zero ly S rd lo n HM Hin) as HZ. unfold zero_shadow, shadow_of_addr in HZ.
    unfold shadow_addr in *.
    replace s with (SHADOW_OFF + lo / 8 + (s - (SHADOW_OFF + lo / 8))) by lia.
    rewrite HZ by lia. discriminate.
  - apply (const_byte_vis ly S rd s HM).
    apply (all_from_spec _ _ (shadow_addr lo + n / 8) s Hc).
    unfold hull_end in *. lia.
Qed.

(* ---- the instances ---- *)
Lemma gnl_row : exists r, find_row LA_G_NL NK_SIZE = Some r /\
  shadow_addr (fst r) <= shadow_addr LA_G_NL / 8 * 8 /\
  (forall ly, all_from (const_byte_b ly) (shadow_addr (fst r) + snd r / 8)
     (Z.to_nat (hull_end LA_G_NL NK_SIZE - (shadow_addr (fst r) + snd r / 8))) = true).
Proof.
  let v := eval vm_compute in (find_row LA_G_NL NK_SIZE) in
  lazymatch v with Some ?r =>
    exists r; split; [vm_compute; reflexivity|]; split; [vm_compute; congruence|];
    intros ly; vm_compute; reflexivity
  end.
Qed.

Lemma errno_row : exists r, find_row TFIB_ERRNO 4 = Some r /\
  shadow_addr (fst r) <= shadow_addr TFIB_ERRNO / 8 * 8 /\
  (forall ly, all_from (const_byte_b ly) (shadow_addr (fst r) + snd r / 8)
     (Z.to_nat (hull_end TFIB_ERRNO 4 - (shadow_addr (fst r) + snd r / 8))) = true).
Proof.
  let v := eval vm_compute in (find_row TFIB_ERRNO 4) in
  lazymatch v with Some ?r =>
    exists r; split; [vm_compute; reflexivity|]; split; [vm_compute; congruence|];
    intros ly; vm_compute; reflexivity
  end.
Qed.

Lemma zsh_gnl_rd : forall ly S rd, ARm B ly S rd ->
  range_addressable rd SHADOW_OFF LA_G_NL NK_SIZE /\ shadow_hull_vis rd LA_G_NL NK_SIZE.
Proof.
  intros ly S rd HM. destruct gnl_row as (r & Hf & Hs & Hc).
  split; [exact (zsh_range_find ly S rd _ _ r HM Hf)|].
  apply (zsh_hull_find ly S rd _ _ r HM Hf); [unfold NK_SIZE; lia | exact Hs | exact (Hc ly)].
Qed.

Lemma zsh_errno_rd : forall ly S rd, ARm B ly S rd ->
  range_addressable rd SHADOW_OFF (as_errno B) 4 /\ shadow_hull_vis rd (as_errno B) 4.
Proof.
  intros ly S rd HM. rewrite (ts_errno B TB). destruct errno_row as (r & Hf & Hs & Hc).
  split; [exact (zsh_range_find ly S rd _ _ r HM Hf)|].
  apply (zsh_hull_find ly S rd _ _ r HM Hf); [lia | exact Hs | exact (Hc ly)].
Qed.

Section s.
Variable segs : list Segment.

Lemma zsh_gnl : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF LA_G_NL NK_SIZE /\
  shadow_hull_vis (aview segs (w_H W) mem) LA_G_NL NK_SIZE.
Proof. intros ly S W mem md (HM & _). exact (zsh_gnl_rd ly S _ HM). Qed.

Lemma zsh_errno : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (as_errno B) 4 /\
  shadow_hull_vis (aview segs (w_H W) mem) (as_errno B) 4.
Proof. intros ly S W mem md (HM & _). exact (zsh_errno_rd ly S _ HM). Qed.

(* the same in link_amem.v's `ard` form (ard_aview: ard segs (mrestrict (w_H W) mem) = aview segs (w_H W) mem) *)
Lemma zsh_gnl_ard : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (ard segs (mrestrict (w_H W) mem)) SHADOW_OFF LA_G_NL NK_SIZE /\
  shadow_hull_vis (ard segs (mrestrict (w_H W) mem)) LA_G_NL NK_SIZE.
Proof. intros ly S W mem md HAR. exact (zsh_gnl ly S W mem md HAR). Qed.

Lemma zsh_errno_ard : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (ard segs (mrestrict (w_H W) mem)) SHADOW_OFF (as_errno B) 4 /\
  shadow_hull_vis (ard segs (mrestrict (w_H W) mem)) (as_errno B) 4.
Proof. intros ly S W mem md HAR. exact (zsh_errno ly S W mem md HAR). Qed.
End s.
End a.
