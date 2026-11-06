(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ArtMem HeapIface HeapIfaceA HeapIfaceAEr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ukq_layout (segs : list Segment) : asan_layout :=
  AL segs 0 0 0 (fun _ => 0) 0 0 0 0 0 0 0 (fun _ => True) (fun _ => True) 0 0 0 0 0 0 0 0 0 0 0.
Definition ukq_run (top bot : Z) : asan_run := AR 0 top bot 0 0.

Section UKG.
Variable L : asan_layout.
Variable ar : asan_run.
#[local] Notation top := (ar_stack_top ar).
#[local] Notation bot := (ar_stack_bottom ar).
#[local] Notation cis := (cell_is (hl_segs L)).

Lemma mod8_sub : forall a k, a mod 8 = 0 -> (a - 8 * k) mod 8 = 0.
Proof. intros a k H. replace (a - 8 * k) with (a + (- k) * 8) by lia. rewrite Z_mod_plus_full. exact H. Qed.
Lemma mod8_gap : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> a < b -> a + 8 <= b.
Proof.
  intros a b Ha Hb Hab. pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Ha in Da. rewrite Hb in Db. lia.
Qed.

Lemma rchain_cells_frame : forall (M M' : word -> option byte) lo0 lo fp RC,
  HAR.rchain L ar M lo fp RC ->
  (HAR.fvalid ar lo fp -> lo0 <= fp - 16) ->
  (forall a v, lo0 <= a -> a + 8 <= top -> a mod 8 = 0 -> 0 <= v < 2 ^ 64 -> cis M a 8 v -> cis M' a 8 v) ->
  HAR.rchain L ar M' lo fp RC.
Proof.
  intros M M' lo0 lo fp RC H. induction H as [lo fp NV | lo fp pc1 V C P | lo fp ra fp' RC V C1 R1 C2 R2 H IH]; intros Hlo TR.
  - apply HAR.rc_stop. exact NV.
  - pose proof V as (V1 & V2 & V3). pose proof (Hlo V) as Hl.
    apply (HAR.rc_low L ar M' lo fp pc1 V); [|exact P].
    apply TR; [lia | lia | replace (fp - 8) with (fp - 8 * 1) by lia; apply mod8_sub; exact V3 | lia | exact C].
  - pose proof V as (V1 & V2 & V3). pose proof (Hlo V) as Hl.
    apply (HAR.rc_cons L ar M' lo fp ra fp' RC V); [| exact R1 | | exact R2 |].
    + apply TR; [lia | lia | replace (fp - 8) with (fp - 8 * 1) by lia; apply mod8_sub; exact V3 | lia | exact C1].
    + apply TR; [lia | lia | replace (fp - 16) with (fp - 8 * 2) by lia; apply mod8_sub; exact V3 | lia | exact C2].
    + apply IH; [|exact TR]. intros (W1 & W2 & W3). lia.
Qed.

Lemma rchain_total8 : forall (M : word -> option byte) lo0,
  (forall a, lo0 <= a -> a + 8 <= top -> a mod 8 = 0 -> exists v, 0 <= v < 2 ^ 64 /\ cis M a 8 v) ->
  forall (k : nat) lo fp, top - fp <= Z.of_nat k -> (HAR.fvalid ar lo fp -> lo0 <= fp - 16) -> exists RC, HAR.rchain L ar M lo fp RC.
Proof.
  intros M lo0 RD k. induction k as [|k IH]; intros lo fp Hk Hlo.
  - exists []. apply HAR.rc_stop. intros (V1 & V2 & V3). lia.
  - destruct (HAR.fvalid_dec ar lo fp) as [V|NV]; [|exists []; apply HAR.rc_stop; exact NV].
    pose proof V as (V1 & V2 & V3). pose proof (Hlo V) as Hl.
    destruct (RD (fp - 8) ltac:(lia) ltac:(lia) ltac:(replace (fp - 8) with (fp - 8 * 1) by lia; apply mod8_sub; exact V3)) as (ra & Rra & Cra).
    destruct (Z_lt_dec ra 4096) as [Lo|Hi]; [exists []; apply (HAR.rc_low L ar M lo fp ra V Cra); lia|].
    destruct (RD (fp - 16) ltac:(lia) ltac:(lia) ltac:(replace (fp - 16) with (fp - 8 * 2) by lia; apply mod8_sub; exact V3)) as (fp' & Rfp & Cfp).
    assert (X : exists RC, HAR.rchain L ar M fp fp' RC).
    { destruct (HAR.fvalid_dec ar fp fp') as [V'|NV']; [|exists []; apply HAR.rc_stop; exact NV'].
      apply IH; [|intros _; destruct V' as (W1 & W2 & W3); lia]. destruct V' as (W1 & W2 & W3). rewrite Nat2Z.inj_succ in Hk. lia. }
    destruct X as (RC & H).
    exists (ra :: RC). apply (HAR.rc_cons L ar M lo fp ra fp' RC V Cra ltac:(lia) Cfp Rfp H).
Qed.

Definition ukeyG (p0 : Z) (M0 : word -> option byte) (sp ra s0 : Z) (K : list Z) : Prop :=
  exists RC, K = HAR.akey p0 RC
    /\ forall M1 : word -> option byte,
         (forall a v, sp <= a -> a + 8 <= top -> a mod 8 = 0 -> 0 <= v < 2 ^ 64 -> cis M0 a 8 v -> cis M1 a 8 v) ->
         cis M1 (sp - 8) 8 ra -> cis M1 (sp - 16) 8 s0 ->
         HAR.rchain L ar M1 bot sp RC.

Lemma ukey_ukeyG : forall p0 (M0 : word -> option byte) sp ra s0 K,
  HAR.ukey L ar p0 M0 sp ra s0 K -> sp mod 8 = 0 -> 0 <= s0 < 2 ^ 64 -> ukeyG p0 M0 sp ra s0 K.
Proof.
  intros p0 M0 sp ra s0 K [(NV & ->) | [(V & Hra & ->) | (V & Hra & Hne & RC & H & ->)]] Hsp8 Hs0.
  - exists []. split; [reflexivity|]. intros M1 _ _ _. apply HAR.rc_stop. exact NV.
  - exists []. split; [reflexivity|]. intros M1 _ C8 _. apply (HAR.rc_low L ar M1 bot sp ra V C8 Hra).
  - exists (ra :: RC). split; [reflexivity|]. intros M1 TR C8 C16.
    apply (HAR.rc_cons L ar M1 bot sp ra s0 RC V C8 Hra C16 Hs0).
    apply (rchain_cells_frame M0 M1 sp sp s0 RC H); [|exact TR].
    intros (W1 & W2 & W3). pose proof (mod8_gap sp s0 Hsp8 W3 W1). pose proof (mod8_gap (sp + 8) s0 ltac:(replace (sp + 8) with (sp - 8 * (-1)) by lia; apply mod8_sub; exact Hsp8) W3 ltac:(lia)). lia.
Qed.

Lemma cis8_inj : forall (M : word -> option byte) a v w, cis M a 8 v -> cis M a 8 w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros M a v w C1 C2 Hv Hw. unfold cell_is in *. rewrite C1 in C2.
  apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
  rewrite !SeqExec.bytes_le_to_Z_8 in C2. rewrite !Z_to_bv_unsigned in C2. unfold bv_wrap in C2. change (bv_modulus 64) with (2 ^ 64) in C2.
  rewrite !Z.mod_small in C2 by lia. exact C2.
Qed.

Lemma ukeyG_total : forall p0 (M0 : word -> option byte) sp ra s0,
  16 <= sp -> sp < 2 ^ 63 -> sp mod 8 = 0 -> top < 2 ^ 64 -> 0 <= ra < 2 ^ 64 -> 0 <= s0 < 2 ^ 64 ->
  (forall a, sp <= a -> a + 8 <= top -> a mod 8 = 0 -> exists v, 0 <= v < 2 ^ 64 /\ cis M0 a 8 v) ->
  exists K, ukeyG p0 M0 sp ra s0 K.
Proof.
  intros p0 M0 sp ra s0 Hsp Hsp' Hsp8 Htop Hra Hs0 RD.
  set (MX := Wn 8 (Wn 8 M0 (sp - 16) s0) (sp - 8) ra).
  assert (CX8 : cis MX (sp - 8) 8 ra) by (apply (cell_Wn_hit (hl_segs L)); cbn; lia).
  assert (CX16 : cis MX (sp - 16) 8 s0).
  { apply (cell_Wn_other (hl_segs L)); [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]. apply (cell_Wn_hit (hl_segs L)); cbn; lia. }
  assert (CXU : forall a v, sp <= a -> a + 8 <= top -> cis M0 a 8 v -> cis MX a 8 v).
  { intros a v Ha Ha' C. apply (cell_Wn_other (hl_segs L)); [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |].
    apply (cell_Wn_other (hl_segs L)); [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]. exact C. }
  assert (RDX : forall a, sp - 16 <= a -> a + 8 <= top -> a mod 8 = 0 -> exists v, 0 <= v < 2 ^ 64 /\ cis MX a 8 v).
  { intros a Ha Ha' Ha8. destruct (Z_lt_dec a sp) as [Lo|Hi].
    - assert (E : a = sp - 16 \/ a = sp - 8).
      { destruct (Z.eq_dec a (sp - 16)) as [E|NE]; [left; exact E|]. right.
        pose proof (mod8_gap (sp - 16) a ltac:(replace (sp - 16) with (sp - 8 * 2) by lia; apply mod8_sub; exact Hsp8) Ha8 ltac:(lia)).
        pose proof (mod8_gap a sp Ha8 Hsp8 Lo). lia. }
      destruct E as [-> | ->]; [exists s0; split; [exact Hs0 | exact CX16] | exists ra; split; [exact Hra | exact CX8]].
    - destruct (RD a ltac:(lia) Ha' Ha8) as (v & Rv & Cv). exists v. split; [exact Rv|]. apply CXU; [lia | exact Ha' | exact Cv]. }
  destruct (rchain_total8 MX (sp - 16) RDX (Z.to_nat (top - sp)) bot sp ltac:(lia) ltac:(intros _; lia)) as (RC & CH).
  exists (HAR.akey p0 RC), RC. split; [reflexivity|]. intros M1 TR C8 C16.
  apply (rchain_cells_frame MX M1 (sp - 16) bot sp RC CH); [intros _; lia|].
  intros a v Ha Ha' Ha8 Rv Cv. destruct (Z_lt_dec a sp) as [Lo|Hi].
  - assert (E : a = sp - 16 \/ a = sp - 8).
    { destruct (Z.eq_dec a (sp - 16)) as [E|NE]; [left; exact E|]. right.
      pose proof (mod8_gap (sp - 16) a ltac:(replace (sp - 16) with (sp - 8 * 2) by lia; apply mod8_sub; exact Hsp8) Ha8 ltac:(lia)).
      pose proof (mod8_gap a sp Ha8 Hsp8 Lo). lia. }
    destruct E as [-> | ->].
    + rewrite (cis8_inj MX _ _ _ Cv CX16 Rv Hs0). exact C16.
    + rewrite (cis8_inj MX _ _ _ Cv CX8 Rv Hra). exact C8.
  - destruct (RD a ltac:(lia) Ha' Ha8) as (v0 & Rv0 & Cv0).
    rewrite (cis8_inj MX _ _ _ Cv (CXU a v0 ltac:(lia) Ha' Cv0) Rv Rv0). apply TR; [lia | exact Ha' | exact Ha8 | exact Rv0 | exact Cv0].
Qed.
End UKG.
