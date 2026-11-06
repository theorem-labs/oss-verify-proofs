(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 112 of its 162 lines of code are new or changed and 2912 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the call-site form of lib/Reusable/YCbq.v's aj_bcmp_at (lines 2262-2310), restated
   for the strcmp wrapper's contract astrcmp_realizes of lib/Reusable/AStrcmpDef.v (fuzz_identity's text, module paths
   changed): the same journal threading through ecall_pre_at and ajournal_after_write, with the strcmp contract's
   str_meet premise and its strcmp_res result in place of bcmp's n-byte compare. The string lemmas below are new. *)
(* reac-pw/fuzz_role calls the strcmp wrapper (the 4-byte jump at 0x41ad0 of fuzz_role.asan) from three program
   functions: reac_role_prop_parse (the key against "reac.cfg.role"), check_answer and check_code (a string against
   a literal of the same text). This file gives what each call site needs:
   - aj_strcmp_at: the call inside a caller's journal. The wrapper uses 2 ESTACK below the caller's sp; the journal
     after the call is the caller's, with every byte outside that window kept, and a0 = strcmp_res c1 c2.
   - str_meet_of_cstr: two NUL-terminated strings in the view (cstr_at) meet at an index kk no larger than either
     length, and strcmp_res c1 c2 = 0 exactly when the two texts are equal.
   - the range lemmas shrink the facts of a whole string [a, a + len + 1) to the bytes [a, a + kk + 1) the wrapper
     reads; rl_cstr_args gives them from RPgBase's rl_cstr. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* ============================ the call inside a caller's journal ============================ *)
Lemma aj_strcmp_at : forall pc, astrcmp_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 -> y + kk + 1 <= 2 ^ 63 ->
str_meet segs W memT x y kk c1 c2 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x (kk + 1) -> src_ok segs W regsT memT y (kk + 1) ->
(forall a, x <= a <= x + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (kk + 1) -> amem_range y (kk + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kk + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kk + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (kk + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (kk + 1) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2' => W2 = W /\ exists regs2 mem2 md2,
c2' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ same_io mdc md2 /\ getr regs2 10 = w64 (strcmp_res c1 c2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 o raw
HJ Ha0 Ha1 Hx0 Hy0 Hkk Hxk Hyk Hmeet Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y kk c1 c2 HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hkk Hxk Hyk Hmeet Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [apply same_io_materialized; exact Hsame|].
split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ============================ two strings meet ============================ *)
(* A NUL-terminated string in the view: the bytes s at a (each nonzero), then the NUL. *)
Definition cstr_at (W : world segs) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs (w_H W) mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs (w_H W) mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s.

Lemma strcmp_res_0 : forall c1 c2, strcmp_res c1 c2 = 0 <-> c1 = c2.
Proof.
intros c1 c2. unfold strcmp_res.
destruct (Z.eqb_spec c1 c2) as [E|E]; [tauto|].
destruct (c1 <? c2); split; intros H; first [discriminate H | exfalso; exact (E H)].
Qed.

Lemma cstr_at_cons : forall W mem a b s, cstr_at W mem a (b :: s) ->
aview segs (w_H W) mem a = Some b /\ 0 < b < 256 /\ cstr_at W mem (a + 1) s.
Proof.
intros W mem a b s (Hc & Hn & Hf). inversion Hf as [|b' s' Hb Hs]; subst.
cbn [length] in Hc, Hn. rewrite Nat2Z.inj_succ in Hc, Hn.
split; [specialize (Hc 0 ltac:(lia)); rewrite Z.add_0_r in Hc; exact Hc|].
split; [exact Hb|].
split; [|split; [replace (a + 1 + Z.of_nat (length s)) with (a + Z.succ (Z.of_nat (length s))) by lia; exact Hn | exact Hs]].
intros i Hi. specialize (Hc (i + 1) ltac:(lia)). replace (a + (i + 1)) with (a + 1 + i) in Hc by lia.
rewrite Hc. f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma cstr_at_nil : forall W mem a, cstr_at W mem a [] -> aview segs (w_H W) mem a = Some 0.
Proof. intros W mem a (_ & Hn & _). cbn [length Z.of_nat] in Hn. rewrite Z.add_0_r in Hn. exact Hn. Qed.

Lemma str_meet_of_cstr : forall s W mem x t y,
cstr_at W mem x s -> cstr_at W mem y t ->
exists kk c1 c2, str_meet segs W mem x y kk c1 c2 /\ 0 <= kk <= Z.of_nat (length s) /\ kk <= Z.of_nat (length t) /\
(strcmp_res c1 c2 = 0 <-> s = t).
Proof.
induction s as [|b s IH]; intros W mem x t y Hx Hy.
- pose proof (cstr_at_nil W mem x Hx) as X0.
  destruct t as [|b' t].
  + pose proof (cstr_at_nil W mem y Hy) as Y0.
    exists 0, 0, 0. split; [|cbn [length Z.of_nat]; split; [lia|]; split; [lia|]; rewrite strcmp_res_0; tauto].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. right; reflexivity.
  + destruct (cstr_at_cons W mem y b' t Hy) as (Y0 & Hb' & _).
    exists 0, 0, b'. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite strcmp_res_0; split; [lia | discriminate]].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. right; reflexivity.
- destruct (cstr_at_cons W mem x b s Hx) as (X0 & Hb & Hx').
  destruct t as [|b' t].
  + pose proof (cstr_at_nil W mem y Hy) as Y0.
    exists 0, b, 0. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite strcmp_res_0; split; [lia | discriminate]].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. left; lia.
  + destruct (cstr_at_cons W mem y b' t Hy) as (Y0 & Hb' & Hy').
    destruct (Z.eq_dec b b') as [<-|Hne].
    * destruct (IH W mem (x + 1) t (y + 1) Hx' Hy') as (kk & c1 & c2 & (Hk0 & Heq & Hc1 & Hc2 & Hend) & Hks & Hkt & Hres).
      exists (kk + 1), c1, c2. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite Hres; split; [intros ->; reflexivity | intros H; injection H; tauto]].
      split; [lia|].
      split; [|split; [replace (x + (kk + 1)) with (x + 1 + kk) by lia; exact Hc1|];
              split; [replace (y + (kk + 1)) with (y + 1 + kk) by lia; exact Hc2 | exact Hend]].
      intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
      { exists b. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. lia. }
      destruct (Heq (i - 1) ltac:(lia)) as (bb & B1 & B2 & B3).
      exists bb. replace (x + i) with (x + 1 + (i - 1)) by lia. replace (y + i) with (y + 1 + (i - 1)) by lia. tauto.
    * exists 0, b, b'. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite strcmp_res_0; split; [intros E; exfalso; exact (Hne E) | intros E; injection E; intros _ E'; exfalso; exact (Hne E')]].
      split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. left; exact Hne.
Qed.

(* ============================ the bytes the wrapper reads ============================ *)
Lemma range_addressable_sub : forall rd Bo a n m, m <= n -> range_addressable rd Bo a n -> range_addressable rd Bo a m.
Proof. intros rd Bo a n m Hm H x Hx. apply H. lia. Qed.

Lemma shadow_hull_vis_sub : forall rd a n m, 0 < m <= n -> shadow_hull_vis rd a n -> shadow_hull_vis rd a m.
Proof.
intros rd a n m Hm H s Hs. apply H. split; [lia|].
pose proof (shadow_mono (a + m - 1) (a + n - 1) ltac:(lia)) as M.
assert (shadow_addr (a + m - 1) / 8 * 8 <= shadow_addr (a + n - 1) / 8 * 8)
by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]). lia.
Qed.

Lemma amem_range_sub : forall p n m, 0 <= m <= n -> amem_range p n -> amem_range p m.
Proof. intros p n m Hm [H|[H1 H2]]; [left; lia | right; split; lia]. Qed.

Lemma src_ok_sub : forall W regs mem s n m, m <= n -> src_ok segs W regs mem s n -> src_ok segs W regs mem s m.
Proof. intros W regs mem s n m Hm H a Ha. apply H. lia. Qed.

Lemma cstr_at_of_rl_cstr : forall W mem a s, rl_cstr segs (w_H W) mem a s -> cstr_at W mem a s.
Proof. intros W mem a s (Hc & Hn & Hf & _). split; [exact Hc|]. split; [exact Hn | exact Hf]. Qed.

(* The facts of a string [a, a + len + 1) give the wrapper's premises on [a, a + kk + 1), kk <= len, when no byte
   of the string lies in the wrapper's stack window below the caller's sp. *)
Lemma rl_cstr_args : forall W regs mem a s kk,
rl_cstr segs (w_H W) mem a s -> 0 <= kk <= Z.of_nat (length s) ->
(forall b, a <= b <= a + Z.of_nat (length s) -> ~ (spZ regs - ESTACK <= b < spZ regs)) ->
0 < a /\ a + kk + 1 <= 2 ^ 63 /\ src_ok segs W regs mem a (kk + 1) /\ amem_range a (kk + 1) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a (kk + 1) /\ shadow_hull_vis (aview segs (w_H W) mem) a (kk + 1).
Proof.
intros W regs mem a s kk (Hc & Hn & Hf & Ha0 & Hhi & _ & Ham & Hra & Hhv) Hk Hst.
split; [exact Ha0|]. split; [lia|].
split; [|split; [eapply amem_range_sub; [|exact Ham]; lia|];
        split; [eapply range_addressable_sub; [|exact Hra]; lia | eapply shadow_hull_vis_sub; [|exact Hhv]; lia]].
intros b Hb. split; [|apply Hst; lia].
destruct (Z.eq_dec b (a + Z.of_nat (length s))) as [->|Hne]; [rewrite Hn; discriminate|].
replace b with (a + (b - a)) by lia. rewrite (Hc (b - a) ltac:(lia)). discriminate.
Qed.
End c.
End b.
