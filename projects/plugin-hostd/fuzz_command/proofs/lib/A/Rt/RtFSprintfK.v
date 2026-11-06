(* Kit of the sprintf walk: the frame invariant of a walk whose stack window is [lo, hi) and whose callees may also
   write a set XW (omx-clap-core/fuzz_manifest's FMsnprintfSk.v sw_frame / sw_init / sw_step / sw_run / sw_mono,
   restated over AR, that is with no user-poisoned range), interval facts, the argument words of a
   va area, and the step from a callee's post back to a symbolic state (st_ok_after_call) over a stack region the
   callee does not touch and read-only regions. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFupoison RtPFPf RtPFShared.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtFSprintfTbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- intervals ---- *)
Lemma zdisj_iff : forall a n b m, 0 < n -> 0 < m -> zdisjoint (a, n) (b, m) <-> (a + n <= b \/ b + m <= a).
Proof. intros a n b m Hn Hm. unfold zdisjoint. cbn [fst snd]. lia. Qed.
Lemma Forall_snp2 : forall (P : Z * Z -> Prop) K sp d w, Forall P (snp_out K sp d w) <-> P (sp - K, K) /\ P (d, w).
Proof.
intros P K sp d w. unfold snp_out. split.
- intros HF. inversion HF as [|? ? H1 HF2]; subst. inversion HF2; subst. split; assumption.
- intros [H1 H2]. constructor; [exact H1 | constructor; [exact H2 | constructor]].
Qed.

(* ---- words ---- *)
Lemma words_at_app : forall rd p l1 l2, words_at rd p l1 -> words_at rd (p + 8 * Z.of_nat (length l1)) l2 ->
  words_at rd p (l1 ++ l2).
Proof.
intros rd p l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 i Hlt).
- rewrite app_nth2 by exact Hge. specialize (H2 (i - length l1)%nat ltac:(lia)).
  replace (p + 8 * Z.of_nat i) with (p + 8 * Z.of_nat (length l1) + 8 * Z.of_nat (i - length l1)) by lia. exact H2.
Qed.
Lemma words_at_same : forall (rd rd' : reader) p ws,
  (forall a, p <= a < p + 8 * Z.of_nat (length ws) -> rd' a = rd a) -> words_at rd p ws -> words_at rd' p ws.
Proof.
intros rd rd' p ws Hk Hw i Hi. specialize (Hw i Hi). unfold rdword in *.
assert (E : forall k, 0 <= k < 8 -> rd' (p + 8 * Z.of_nat i + k) = rd (p + 8 * Z.of_nat i + k)) by (intros k Hk8; apply Hk; lia).
rewrite (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7) by lia.
replace (p + 8 * Z.of_nat i) with (p + 8 * Z.of_nat i + 0) at 1 by lia. rewrite (E 0) by lia. rewrite Z.add_0_r. exact Hw.
Qed.
Lemma rdword_same : forall (rd rd' : reader) p v,
  (forall a, p <= a < p + 8 -> rd' a = rd a) -> rdword rd p = Some v -> rdword rd' p = Some v.
Proof.
intros rd rd' p v Hk Hw. assert (W1 : words_at rd p [v]) by (intros i Hi; destruct i; [rewrite Z.add_0_r; exact Hw | cbn in Hi; lia]).
pose proof (words_at_same rd rd' p [v] ltac:(cbn [length]; intros a Ha; apply Hk; lia) W1 0%nat ltac:(cbn; lia)) as X.
rewrite Z.add_0_r in X. exact X.
Qed.
(* six words read from val_mem facts, the rest from the caller *)
Lemma words6 : forall (H : word -> bool) (mem : word -> option byte) p (w0 w1 w2 w3 w4 w5 : Z),
  0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 -> 0 <= w2 < 2 ^ 64 -> 0 <= w3 < 2 ^ 64 -> 0 <= w4 < 2 ^ 64 -> 0 <= w5 < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H mem) (p + 0) 8 w0 -> val_mem tfibsegs (mrestrict H mem) (p + 8) 8 w1 ->
  val_mem tfibsegs (mrestrict H mem) (p + 16) 8 w2 -> val_mem tfibsegs (mrestrict H mem) (p + 24) 8 w3 ->
  val_mem tfibsegs (mrestrict H mem) (p + 32) 8 w4 -> val_mem tfibsegs (mrestrict H mem) (p + 40) 8 w5 ->
  words_at (aview tfibsegs H mem) p [w0; w1; w2; w3; w4; w5].
Proof.
intros H mem p w0 w1 w2 w3 w4 w5 R0 R1 R2 R3 R4 R5 V0 V1 V2 V3 V4 V5 i Hi. cbn [length] in Hi.
destruct i as [|[|[|[|[|[|i]]]]]]; cbn [nth].
- replace (p + 8 * Z.of_nat 0) with (p + 0) by lia. exact (val_mem_rdword H mem _ _ R0 V0).
- replace (p + 8 * Z.of_nat 1) with (p + 8) by lia. exact (val_mem_rdword H mem _ _ R1 V1).
- replace (p + 8 * Z.of_nat 2) with (p + 16) by lia. exact (val_mem_rdword H mem _ _ R2 V2).
- replace (p + 8 * Z.of_nat 3) with (p + 24) by lia. exact (val_mem_rdword H mem _ _ R3 V3).
- replace (p + 8 * Z.of_nat 4) with (p + 32) by lia. exact (val_mem_rdword H mem _ _ R4 V4).
- replace (p + 8 * Z.of_nat 5) with (p + 40) by lia. exact (val_mem_rdword H mem _ _ R5 V5).
- lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
#[local] Notation H W := (w_H W).

(* ---- the frame of a walk with stack window [lo, hi) and callee-written set XW ---- *)
Definition fr_inv (ly : alayout) (S : astate) (W : world tfibsegs) (mem0 : word -> option byte) (md0 : Model)
  (lo hi : Z) (XW : Z -> Prop) (mem : word -> option byte) (md : Model) : Prop :=
  AR tfibsegs B ly S W mem md /\ same_but_materialized md0 md /\
  (forall a, lo <= a < hi -> apresent (H W) mem a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ XW a ->
     aview tfibsegs (H W) mem a = aview tfibsegs (H W) mem0 a) /\
  (forall a, apresent (H W) mem0 a -> apresent (H W) mem a).
Section f.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (mem0 : word -> option byte) (md0 : Model)
  (lo hi : Z) (XW : Z -> Prop).
Hypothesis Hlo : ly_stk_lo ly <= lo.
Hypothesis Hhi : hi <= ly_stk_hi ly.
Lemma fr_init : AR tfibsegs B ly S W mem0 md0 -> (forall a, lo <= a < hi -> apresent (H W) mem0 a) ->
  fr_inv ly S W mem0 md0 lo hi XW mem0 md0.
Proof.
intros HA Hp. split; [exact HA|]. split; [apply same_but_materialized_refl|]. split; [exact Hp|].
split; [intros; reflexivity | intros a Ha; exact Ha].
Qed.
Lemma fr_step : forall mem md mem' md',
  fr_inv ly S W mem0 md0 lo hi XW mem md ->
  AR tfibsegs B ly S W mem' md' -> same_but_materialized md md' ->
  (forall a, lo <= a < hi -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ XW a ->
     aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a) ->
  fr_inv ly S W mem0 md0 lo hi XW mem' md'.
Proof.
intros mem md mem' md' (HA & Hsb & Hp & Hfr & Hpm) HA' Hsb' Hp' Hfr' Hpm'.
split; [exact HA'|]. split; [exact (same_but_materialized_trans md0 md md' Hsb Hsb')|]. split; [exact Hp'|].
split; [intros a Hr H1 H2; rewrite (Hfr' a Hr H1 H2); exact (Hfr a Hr H1 H2)|].
intros a Ha. apply Hpm'. apply Hpm. exact Ha.
Qed.
(* a run of the walk's own code whose writable windows lie in [lo, hi) *)
Lemma fr_run : forall mem md memB mat E rs,
  fr_inv ly S W mem0 md0 lo hi XW mem md ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  frame_of E rs mem memB ->
  (forall a, lo <= a < hi -> apresent (H W) memB a) ->
  fr_inv ly S W mem0 md0 lo hi XW memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros mem md memB mat E rs HF Hwin Hfo HpB.
pose proof HF as (HA & Hsb & Hp & Hfr & Hpm).
pose proof (stk_kHighMemBeg B ly S _ (proj1 HA)) as [K1 K2].
unfold kHighMemEnd in K2.
assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> memB (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hb. apply Hfo. rewrite unsigned_lit_small by lia. intros Hin. exact (Hb (Hwin a Hin)). }
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  aview tfibsegs (H W) memB a = aview tfibsegs (H W) mem a).
{ intros a Ha Hb. apply aview_same. exact (OUT a Ha Hb). }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
apply (fr_step mem md memB _ HF).
- apply (al_frame _ _ LAWS ly S W mem md memB _ HA).
  + intros a Hr Hown. apply AVB; [exact Hr|]. intros Hb.
    exact (al_stack _ _ LAWS ly S W mem md a HA ltac:(lia) Hown).
  + intros a Hv. rewrite (AE2y.aview_mod (H W) memB a).
    rewrite (AE2y.aview_mod (H W) mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [L1|L1]; [rewrite AVB by lia; exact Hv|].
    destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [L2|L2]; [| rewrite AVB by lia; exact Hv].
    apply aview_some_of_apresent. apply HpB. lia.
  + apply MF. + apply MF. + apply MF.
  + intros a Ha Hh. unfold YG0d.w64.
    assert (Har : 0 <= a < kHighMemBeg)
      by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    apply OUT; [unfold kHighMemBeg in *; lia | unfold kHighMemBeg in *; lia].
- apply with_vm_backing_same.
- exact HpB.
- intros a Hr H1 H2. apply AVB; assumption.
- intros a Hpa. rewrite (AE2y.apresent_mod _ memB a). rewrite (AE2y.apresent_mod _ mem a) in Hpa.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [L1|L1];
    [apply (apresent_same (H W) mem memB _); [exact (OUT _ Hr ltac:(lia)) | exact Hpa]|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [L2|L2]; [apply HpB; lia|].
  apply (apresent_same (H W) mem memB _); [exact (OUT _ Hr ltac:(lia)) | exact Hpa].
Qed.
Lemma fr_mono : forall (XW' : Z -> Prop) mem md, fr_inv ly S W mem0 md0 lo hi XW mem md ->
  (forall a, XW a -> XW' a) -> fr_inv ly S W mem0 md0 lo hi XW' mem md.
Proof.
intros XW' mem md (HA & Hsb & Hp & Hfr & Hpm) Hx. split; [exact HA|]. split; [exact Hsb|]. split; [exact Hp|].
split; [|exact Hpm]. intros a Hr H1 H2. apply Hfr; [exact Hr | exact H1 | intros X; exact (H2 (Hx a X))].
Qed.
End f.

(* ---- the step back to a symbolic state after a callee ---- *)
(* a stack region based at atom 2 that the callee leaves alone, and the read-only regions *)
Lemma kept_stack : forall (W : world tfibsegs) E (m m' : word -> option byte) sp lo wlo cs,
  bv_unsigned (ew E 2) = sp -> 0 <= sp + lo -> sp <= 2 ^ 64 -> lo <= wlo ->
  (forall a, sp + lo <= a < sp -> aview tfibsegs (H W) m' a = aview tfibsegs (H W) m a) ->
  (forall a, sp + wlo <= a < sp -> apresent (H W) m' a) ->
  region_kept tfibsegs E (mrestrict (H W) m) (mrestrict (H W) m') (YP09.mkRegion (Some 2%nat) lo 0 wlo 0 cs).
Proof.
intros W E m m' sp lo wlo cs E2 L1 L2 L3 Hv Hp. split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite E2; intros a Ha.
- apply mbyte_of_aview. apply Hv. lia.
- intros _. apply apresent_writable. apply Hp. lia.
Qed.
Lemma kept_ro : forall (W : world tfibsegs) E (m m' : word -> option byte) r,
  In r (map ro_region spf_rodata) ->
  (forall a, 0x10000 <= a < 0x200000 -> aview tfibsegs (H W) m' a = aview tfibsegs (H W) m a) ->
  region_kept tfibsegs E (mrestrict (H W) m) (mrestrict (H W) m') r.
Proof.
intros W E m m' r Hr Hv. destruct (spf_ro_low r Hr) as (_ & Hb & Hl & Hh & Hw).
split; rewrite Hb; cbn [base_val]; intros a Ha.
- apply mbyte_of_aview. apply Hv. lia.
- lia.
Qed.
(* aregs_preserved gives the callee-saved half of st_ok_after_call *)
Lemma regs_preserved_of_a : forall regs regs', aregs_preserved regs regs' -> YO0d.regs_preserved regs regs'.
Proof. intros regs regs' HP r Hr. apply HP. unfold acallee_saved. exact Hr. Qed.
(* a byte stays writable when its presence is kept (fuzz_manifest's FMsnprintfGt0.v writable_xfer) *)
Lemma writable_xfer : forall (Hd : word -> bool) (m m' : word -> option byte) a,
  writable_at tfibsegs (mrestrict Hd m) a -> (apresent Hd m a -> apresent Hd m' a) ->
  writable_at tfibsegs (mrestrict Hd m') a.
Proof.
intros Hd m m' a Hw Hp. unfold writable_at, wview, mrestrict in *.
destruct (Hd (Z_to_bv 64 a)) eqn:Eh; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj Eh (ex_intro _ b Em))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
End k.
