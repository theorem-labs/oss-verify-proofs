(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bCall.v at f3898085bda (w7_strlen_at,
   as hb1_strlen_at), RPgW7bKit.v at f3898085bda (w7_strok_cstr, as hb1_strok_cstr; that file is [Apache-2.0 OR
   MIT], used here under Apache-2.0), RPgW6aTail.v at f3898085bda (tl_atom, tl_in, as hb1_atom, hb1_in),
   RPgW6aC2h.v at f3898085bda (c2_all256, as hb1_chk256), RPgW6bC1a.v at f3898085bda (c1_reg, as hb1_reg) and
   RPgMem.v at f3898085bda (rm_nth_map, as hb1_nth_map) for
   reac-pw/fuzz_headamp's image B: image B's segments (lib/AU/Img0U.v rsegs, HPgSteps.img_segs_low and
   same_io_wvb), the strlen wrapper at its image-B trampoline StrlenDef.STRLEN_ENTRY_B, the 256-value check stated
   for any value function. The cb_* helpers this file first took from RPgW7bBase.v,
   RPgW7bKit.v, RPgCfgChanges.v, RPgW6aTail.v, RPgW6aC2h.v and RPgW7bIter.v at f3898085bda are lib/AU/HPgCaseB.v's
   since the dedup. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the kit of the walk of case 1
   of ent_build's `switch (kind % 10)` (pod.h:285-296) inside LLVMFuzzerTestOneInput (0x80c40), the block lemma
   HPgW6bBase.hw6b_c1 (lib/AU/HPgW6bC1a.v, HPgW6bC1b.v, HPgW6bC1.v). Proves no function (kind: segment lemma).
   The cb_* helpers below are defined in lib/AU/HPgCaseB.v (the dedup moved them there); the hb1_* ones here.
   - cb_post: the post of one block of the walk (the journal kept with the world, the I/O state kept, every
     register outside clob kept, every byte outside Wr kept, every present byte present, and R);
     cb_post_of_run: that post from the engine's last state.
   - cb_kept_run: a run keeps every byte outside a zone its write windows lie in.
   - cb_kept / cb_hull / cb_ra_kept / cb_hull_kept: a memory step that keeps the shadow hull of a range keeps its
     addressability and its readable shadow.
   - cb_val_at / hb1_atom: a chunk of a region and a register of the engine's last state.
   - hb1_chk256: a symbolic value over one input byte, checked for all 256 values by computation.
   - hb1_strlen_at: the strlen wrapper (StrlenDef.astrlen_realizes at STRLEN_ENTRY_B 0x41c18, the `jal` target of
     case 1 at 0x82134) in the journal form, keeping the I/O state. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma hb1_chk256 : forall (e : sv) (f : Z -> Z) m,
  forallb (fun z => bv_eqb (sv_denot (cb_envz z) e) (Z_to_bv 64 (f z))) (map Z.of_nat (seq 0 256)) = true ->
  0 <= m < 256 -> sv_denot (cb_envz m) e = Z_to_bv 64 (f m).
Proof.
intros e f m H Hm. apply bv_eqb_true_iff.
exact (cb_all256 (fun z => bv_eqb (sv_denot (cb_envz z) e) (Z_to_bv 64 (f z))) H m Hm).
Qed.

Lemma hb1_nth_map : forall (l : list byte) j,
  nth j (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hb1_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

(* an image string: HPgBase.hd_cstr, which carries the tail of the NUL's word, above the callees' stack *)
Lemma hb1_strok_cstr : forall W m R x (l : list byte),
  hd_cstr rsegs (w_H W) m x (hd_zbytes l) ->
  x + Z.of_nat (length l) < R - 2 * ESTACK -> (length l <= 64)%nat ->
  cb_strok W m R x l.
Proof.
intros W m R x l (Hb & Hn & Hz & H0 & Hhi & Himg & Ham & Hra & Hhv & Htl) Hst Hl.
unfold hd_zbytes in *. rewrite length_map in Hb, Hn, Hhi, Himg, Ham, Hra, Hhv, Htl.
split; [exact H0|]. split; [lia|]. split; [lia|].
split.
{ intros j Hj. specialize (Hb (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in Hb.
  rewrite hb1_nth_map in Hb. split; [exact Hb|].
  rewrite Forall_forall in Hz. specialize (Hz (bv_unsigned (nth j l (Z_to_bv 8 0)))).
  assert (0 < bv_unsigned (nth j l (Z_to_bv 8 0)) < 256); [|lia].
  apply Hz. rewrite <- hb1_nth_map. apply nth_In. rewrite length_map. exact Hj. }
split; [exact Hn|]. split; [exact Htl|].
split; [intros a Ha; lia|].
split; [exact (hd_amem_range_le x (Z.of_nat (length l) + 1) (Z.of_nat (length l) + 8) ltac:(lia) Ham)|].
split; [exact Hra | exact Hhv].
Qed.

Section d.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* ---- the strlen wrapper in the journal form [RPgW7bCall.v w7_strlen_at] ---- *)
Lemma hb1_strlen_at : astrlen_realizes rsegs B STRLEN_ENTRY_B ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte rsegs W memT x (k + 1) 0 k ->
src_ok rsegs W regsT memT x (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview rsegs (w_H W) memT) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview rsegs (w_H W) memT a <> None) ->
aro_unowned rsegs B (aview rsegs (w_H W) memT) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 STRLEN_ENTRY_B) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x k HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
    ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS img_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact (same_io_materialized _ _ Hsame)|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End d.
End b.

(* a register of the engine's last state, its symbolic value computed [RPgW6bC1a.v c1_reg] *)
Ltac hb1_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity)
  end.
(* a chunk of a computed region *)
Ltac hb1_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Print Assumptions hb1_chk256.
Print Assumptions hb1_atom.
Print Assumptions hb1_strok_cstr.
Print Assumptions hb1_strlen_at.
