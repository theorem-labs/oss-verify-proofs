(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ZXA.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Eof (regs : bvmap 5 word) (vals : list Z) : env :=
  fun n => if Nat.ltb n 32 then bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n))) else nth (n - 32) vals 0.

Definition sr_id : list zx :=
  [ZV 0; ZV 1; ZV 2; ZV 3; ZV 4; ZV 5; ZV 6; ZV 7;
   ZV 8; ZV 9; ZV 10; ZV 11; ZV 12; ZV 13; ZV 14; ZV 15;
   ZV 16; ZV 17; ZV 18; ZV 19; ZV 20; ZV 21; ZV 22; ZV 23;
   ZV 24; ZV 25; ZV 26; ZV 27; ZV 28; ZV 29; ZV 30; ZV 31].

(* [comment removed for export] *)
Definition vi_regs : vitab := repeat (Some (0, M64 - 1)) 32.

Section WithFP.
Context {fx : FPState}.

Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.

Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
  pose proof (u5_range r). rewrite Z2Nat.id by lia. apply bv_wrap_small.
  change (bv_modulus 5) with 32. lia.
Qed.

Lemma regs_ok_id : forall regs vals, regs_ok (Eof regs vals) sr_id regs.
Proof.
  intros regs vals r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - unfold wd, Eof. rewrite <- (ridx_roundtrip r) at 1.
    pose proof (ridx_range r) as Hlt.
    set (n := ridx r) in *. clearbody n.
    do 32 (destruct n as [|n]; [cbn; symmetry; apply Z_to_bv_bv_unsigned|]).
    exfalso. lia.
Qed.

Lemma regs_ok_pin : forall E sr regs (r : reg) e,
  regs_ok E sr regs -> getr regs r = wd E e -> regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
  intros E sr regs r e Hr Hv r'. unfold sr_get.
  destruct (bv_eqb r' 0) eqn:Hr0.
  - assert (r' = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r'. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
    + specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Fixpoint vi_user_ok (E : env) (k : nat) (vi : vitab) : Prop :=
  match vi with
  | [] => True
  | o :: t => match o with Some (lo, hi) => lo <= E k <= hi | None => True end /\ vi_user_ok E (S k) t
  end.

Lemma vi_user_ok_nth : forall E vi k n lo hi,
  vi_user_ok E k vi -> nth n vi None = Some (lo, hi) -> lo <= E (k + n)%nat <= hi.
Proof.
  intros E vi. induction vi as [|o t IH]; intros k n lo hi H Hn.
  - destruct n; discriminate.
  - cbn in H. destruct H as [Ho Ht]. destruct n as [|n].
    + cbn in Hn. subst o. rewrite Nat.add_0_r. exact Ho.
    + cbn in Hn. replace (k + S n)%nat with (S k + n)%nat by lia. eapply IH; eauto.
Qed.

Lemma vi_ok_Eof : forall regs vals uvi,
  vi_user_ok (Eof regs vals) 32 uvi -> vi_ok (Eof regs vals) (vi_regs ++ uvi).
Proof.
  intros regs vals uvi Hu n lo hi Hn.
  destruct (Nat.lt_ge_cases n 32) as [Hlt|Hge].
  - rewrite app_nth1 in Hn by (unfold vi_regs; rewrite repeat_length; exact Hlt).
    unfold vi_regs in Hn. rewrite nth_repeat_lt in Hn by exact Hlt. injection Hn as <- <-.
    unfold Eof. replace (Nat.ltb n 32) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
    pose proof (u64_range (getr regs (Z_to_bv 5 (Z.of_nat n)))). lia.
  - rewrite app_nth2 in Hn by (unfold vi_regs; rewrite repeat_length; exact Hge).
    unfold vi_regs in Hn. rewrite repeat_length in Hn.
    replace n with (32 + (n - 32))%nat by lia. eapply vi_user_ok_nth; eauto.
Qed.

(* [comment removed for export] *)
Fixpoint kn_conj (segs : list Segment) (E : env) (m : word -> option byte) (kn : list kcell) : Prop :=
  match kn with
  | [] => True
  | KC b k n v :: t => (flat E b k n /\ exists bs, rdn segs m (addr E b k) n = Some bs /\ bytes_le_to_Z bs = ev E v)
                       /\ kn_conj segs E m t
  end.

Lemma kn_conj_ok : forall segs E m kn, kn_conj segs E m kn -> kn_ok segs E m kn.
Proof.
  intros segs E m kn. induction kn as [|[b k n v] t IH]; intros H; [constructor|].
  cbn in H. destruct H as [H1 H2]. constructor; [exact H1 | apply IH, H2].
Qed.

Fixpoint kw_conj (segs : list Segment) (E : env) (m : word -> option byte) (kw : list kwin) : Prop :=
  match kw with
  | [] => True
  | KW b lo hi :: t => (0 <= ev E b + lo /\ ev E b + hi <= M64 /\
                        forall k n, lo <= k -> k + Z.of_nat n <= hi -> RiscvSemantics.store_ok segs m (addr E b k) n = true)
                       /\ kw_conj segs E m t
  end.

Lemma kw_conj_ok : forall segs E m kw, kw_conj segs E m kw -> kw_ok segs E m kw.
Proof.
  intros segs E m kw. induction kw as [|[b lo hi] t IH]; intros H; [constructor|].
  cbn in H. destruct H as [H1 H2]. constructor; [exact H1 | apply IH, H2].
Qed.

Fixpoint scs_conj (segs : list Segment) (E : env) (m : word -> option byte) (l : list zsc) : Prop :=
  match l with
  | [] => True
  | c :: t => sc_ok segs E m c /\ scs_conj segs E m t
  end.

Lemma scs_conj_ok : forall segs E m l, scs_conj segs E m l -> scs_ok segs E m l.
Proof.
  intros segs E m l. induction l as [|c t IH]; intros H; [constructor|].
  cbn in H. destruct H as [H1 H2]. constructor; [exact H1 | apply IH, H2].
Qed.

(* [comment removed for export] *)
Lemma kw_of_store_ok : forall segs E m b lo (N : nat),
  0 <= ev E b + lo -> ev E b + lo + Z.of_nat N <= M64 ->
  RiscvSemantics.store_ok segs m (Z_to_bv 64 (ev E b + lo)) N = true ->
  0 <= ev E b + lo /\ ev E b + (lo + Z.of_nat N) <= M64 /\
  forall k n, lo <= k -> k + Z.of_nat n <= lo + Z.of_nat N -> RiscvSemantics.store_ok segs m (addr E b k) n = true.
Proof.
  intros segs E m b lo N H1 H2 Hok. split; [lia|]. split; [lia|].
  intros k n Hk Hn. unfold addr. destruct n as [|n']; [reflexivity|].
  eapply (store_ok_sub segs m (Z_to_bv 64 (ev E b + lo)) _ N (S n')); try exact Hok;
    rewrite !u_Z2bv64, !Z.mod_small by (lia); lia.
Qed.

(* [comment removed for export] *)
Lemma zx_block : forall segs (C : ctx) fuel stops scr sr p st' scs regs vals uvi m rom,
  zrun segs C fuel true stops scr (ZS p sr []) [] = (st', scs) ->
  c_vi C = vi_regs ++ uvi ->
  let E := Eof regs vals in
  regs_ok E sr regs ->
  vi_user_ok E 32 uvi ->
  kn_conj segs E m (c_kn C) ->
  kw_conj segs E m (c_kw C) ->
  scs_conj segs E m scs ->
  exists regs', regs_ok E (z_rs st') regs' /\ log_flat E (z_log st') /\
    msteps segs (mkst regs (Z_to_bv 64 p) m rom)
                (mkst regs' (Z_to_bv 64 (z_pc st')) (mem_denot E m (z_log st')) rom).
Proof.
  intros segs C fuel stops scr sr p st' scs regs vals uvi m rom Hrun Hvi E Hregs Hu Hkn Hkw Hsc.
  eapply zrun_block; eauto.
  - split; [|split]; [rewrite Hvi; apply vi_ok_Eof; exact Hu | apply kn_conj_ok; exact Hkn | apply kw_conj_ok; exact Hkw].
  - apply scs_conj_ok. exact Hsc.
Qed.

End WithFP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sr_pins (sr : list zx) (pins : list (reg * zx)) : list zx :=
  match pins with
  | [] => sr
  | (r, e) :: t => sr_pins (sr_upd sr (ridx r) e) t
  end.

Section WithFP2.
Context {fx : FPState}.
Fixpoint pins_ok (E : env) (regs : bvmap 5 word) (pins : list (reg * zx)) : Prop :=
  match pins with
  | [] => True
  | (r, e) :: t => getr regs r = wd E e /\ pins_ok E regs t
  end.

Lemma regs_ok_pins : forall E regs pins sr, regs_ok E sr regs -> pins_ok E regs pins -> regs_ok E (sr_pins sr pins) regs.
Proof.
  intros E regs pins. induction pins as [|[r e] t IH]; intros sr Hsr Hp; [exact Hsr|].
  cbn in Hp. destruct Hp as [H1 H2]. cbn. apply IH; [|exact H2]. apply regs_ok_pin; assumption.
Qed.

Lemma zx_block_pins : forall segs (C : ctx) fuel stops scr (pins : list (reg * zx)) p st' scs regs vals uvi m rom,
  zrun segs C fuel true stops scr (ZS p (sr_pins sr_id pins) []) [] = (st', scs) ->
  c_vi C = vi_regs ++ uvi ->
  let E := Eof regs vals in
  pins_ok E regs pins ->
  vi_user_ok E 32 uvi ->
  kn_conj segs E m (c_kn C) ->
  kw_conj segs E m (c_kw C) ->
  scs_conj segs E m scs ->
  regs_ok E (sr_pins sr_id pins) regs /\
  exists regs', regs_ok E (z_rs st') regs' /\ log_flat E (z_log st') /\
    msteps segs (mkst regs (Z_to_bv 64 p) m rom)
                (mkst regs' (Z_to_bv 64 (z_pc st')) (mem_denot E m (z_log st')) rom).
Proof.
  intros.
  assert (HE : regs_ok (Eof regs vals) (sr_pins sr_id pins) regs) by (apply regs_ok_pins; [apply regs_ok_id | assumption]).
  split; [exact HE|]. eapply zx_block; eauto.
Qed.
End WithFP2.

(* [comment removed for export] *)
Ltac zx_run segs C fuel stops scr pins vals uvi regs m rom p :=
  let r := eval vm_compute in (zrun segs C fuel true stops scr (ZS p (sr_pins sr_id pins) []) []) in
  lazymatch r with
  | (?st', ?scs) =>
      let H := fresh "ZXB" in
      pose proof (zx_block_pins segs C fuel stops scr pins p st' scs regs vals uvi m rom
                    ltac:(vm_compute; reflexivity) eq_refl) as H;
      cbv zeta in H
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zx_cbn_in H :=
  cbn [pins_ok vi_user_ok kn_conj kw_conj scs_conj ZXA.sc_ok ZXA.cond_ok ZXA.log_flat
       ZXA.c_kn ZXA.c_kw ZXA.c_vi ZXA.z_rs ZXA.z_pc ZXA.z_log ZXA.mem_denot] in H;
  unfold ZXA.flat, ZXA.addr, ZXA.wd in H;
  cbn [ZXA.ev Eof Nat.ltb Nat.leb Nat.sub nth ZXA.zalu ZXA.zaluw Z.of_nat Pos.of_succ_nat Pos.succ N.of_nat] in H;
  rewrite ?Z.add_0_r in H.
Ltac zx_cbn :=
  cbn [pins_ok vi_user_ok kn_conj kw_conj scs_conj ZXA.sc_ok ZXA.cond_ok ZXA.log_flat
       ZXA.c_kn ZXA.c_kw ZXA.c_vi ZXA.z_rs ZXA.z_pc ZXA.z_log ZXA.mem_denot];
  unfold ZXA.flat, ZXA.addr, ZXA.wd;
  cbn [ZXA.ev Eof Nat.ltb Nat.leb Nat.sub nth ZXA.zalu ZXA.zaluw Z.of_nat Pos.of_succ_nat Pos.succ N.of_nat];
  rewrite ?Z.add_0_r.

(* [comment removed for export] *)
Ltac zx_use ZXB tacP tacV tacK tacW tacS :=
  lazymatch type of ZXB with
  | ?P1 -> ?P2 -> ?P3 -> ?P4 -> ?P5 -> _ =>
      let H1 := fresh "OP" in let H2 := fresh "OV" in let H3 := fresh "OK" in
      let H4 := fresh "OW" in let H5 := fresh "OS" in
      assert (H1 : P1); [zx_cbn; tacP|
      assert (H2 : P2); [zx_cbn; tacV|
      assert (H3 : P3); [cbn [kn_conj ZXA.c_kn]; tacK|
      assert (H4 : P4); [cbn [kw_conj ZXA.c_kw]; tacW|
      assert (H5 : P5); [zx_cbn; tacS|
      specialize (ZXB H1 H2 H3 H4 H5); clear H1 H2 H3 H4 H5;
      let regs' := fresh "regs" in
      destruct ZXB as (?ZE & regs' & ?ZR & ?ZF & ?ZM);
      zx_cbn_in ZM; zx_cbn_in ZF; cbn [ZXA.z_rs] in ZR ]]]]]
  end.

(* [comment removed for export] *)
Ltac zx_pins := repeat split; try assumption; try reflexivity; try (rewrite Z_to_bv_bv_unsigned; assumption); try (etransitivity; [eassumption | f_equal; lia]).
Ltac zx_lia := first [lia | repeat split; try lia].

Section KW2.
Context {fx : FPState}.
(* [comment removed for export] *)
Lemma kw_intro : forall segs E m b lo hi (base : Z) (N : nat),
  RiscvSemantics.store_ok segs m (Z_to_bv 64 base) N = true -> 0 <= base -> base + Z.of_nat N <= M64 ->
  base <= ev E b + lo -> ev E b + hi <= base + Z.of_nat N ->
  0 <= ev E b + lo /\ ev E b + hi <= M64 /\
  forall k n, lo <= k -> k + Z.of_nat n <= hi -> RiscvSemantics.store_ok segs m (addr E b k) n = true.
Proof.
  intros segs E m b lo hi base N Hok Hb HN Hlo Hhi. split; [lia|]. split; [lia|].
  intros k n Hk Hn. unfold addr. destruct n as [|n']; [reflexivity|].
  eapply (store_ok_sub segs m (Z_to_bv 64 base) _ N (S n')); try exact Hok;
    rewrite !u_Z2bv64, !Z.mod_small by lia; lia.
Qed.
End KW2.

Section KC2.
Context {fx : FPState}.
(* [comment removed for export] *)
Lemma kc_intro : forall segs E m b k n v a x,
  (exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ bytes_le_to_Z bs = x) ->
  (a = ev E b + k /\ x = ev E v /\ 0 <= a /\ a + Z.of_nat n <= M64 /\ (1 <= n)%nat) ->
  flat E b k n /\ exists bs, rdn segs m (addr E b k) n = Some bs /\ bytes_le_to_Z bs = ev E v.
Proof.
  intros segs E m b k n v a x H (-> & -> & Ha & Hb & Hn). split; [unfold flat; lia|]. unfold addr. exact H.
Qed.

(* [comment removed for export] *)
Lemma kw_intro' : forall segs E m b lo hi (base : Z) (N : nat),
  RiscvSemantics.store_ok segs m (Z_to_bv 64 base) N = true ->
  (0 <= base /\ base + Z.of_nat N <= M64 /\ base <= ev E b + lo /\ ev E b + hi <= base + Z.of_nat N) ->
  0 <= ev E b + lo /\ ev E b + hi <= M64 /\
  forall k n, lo <= k -> k + Z.of_nat n <= hi -> RiscvSemantics.store_ok segs m (addr E b k) n = true.
Proof. intros segs E m b lo hi base N Hok (H1 & H2 & H3 & H4). eapply kw_intro; eauto. Qed.
End KC2.

Section SCStore.
Context {fx : FPState}.
(* [comment removed for export] *)
Lemma sc_store_in : forall segs m (base : Z) (N : nat) a n,
  RiscvSemantics.store_ok segs m (Z_to_bv 64 base) N = true ->
  (0 <= base /\ base + Z.of_nat N <= M64 /\ base <= a /\ a + Z.of_nat n <= base + Z.of_nat N) ->
  RiscvSemantics.store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros segs m base N a n Hok (Hb & HN & H1 & H2). destruct n as [|n']; [reflexivity|].
  eapply (store_ok_sub segs m (Z_to_bv 64 base) _ N (S n')); try exact Hok; rewrite !u_Z2bv64, !Z.mod_small by lia; lia.
Qed.
End SCStore.

(* [comment removed for export] *)
Tactic Notation "zx_name" ident(R) :=
  lazymatch goal with H : ZXA.regs_ok _ (_ :: _) ?r |- _ => rename r into R end.
