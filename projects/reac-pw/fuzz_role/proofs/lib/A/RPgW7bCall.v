(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/ACes.v:275-278
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/A/ACfk.v:194-195 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh9.v:115-118 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v at origin/ossv/recipes 2d2ff01bb6f2 (aj_strlen_at, as w7_strlen_at, over reac-pw/fuzz_role's image A: SEGS := rsegs, pa_segs_low := w7_segs_low, and the post also keeps the I/O state, same_io from the wrapper's same_but_materialized); the rest of the file is new. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the strlen call site of the walk of
   LLVMFuzzerTestOneInput from 0x80d14 (lib/A/RPgW7bBase.v) and the string facts its blocks use. Proves no function
   (kind: segment lemma).

   - w7_strlen_at: the strlen wrapper (lib/A/Rt/StrlenDef.v astrlen_realizes) in the journal form.
   - w7_tail_strs / w7_tail_img: the ten strings the head-amp key reads (HPFX, the two separators, the eight
     param[] strings): the bytes from each string's NUL to the end of the NUL's 8-byte word lie in the read-only
     PT_LOAD [0x10000, 0x2f634), so every reader sees them whatever the memory.
   - w7_chs_nonzero: the key's first part (the decimal text of c mod 64 or odd_ch[c mod 14]) has no zero byte.
   - w7_param_cell / w7_param_str / w7_param_tail, w7_hpfx_str, w7_sep_str / w7_sep_tail: the image's param table
     cells (ent_headamp_key.param at 0x9a620) and strings against the model's param list, HPFX and the separators. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgW7bBase RPgImgA RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges RPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the ten strings the head-amp key reads: (address, length without the NUL) ---- *)
Definition w7_tail_strs : list (Z * Z) := [(0x20f00, 13); (0x21200, 0); (0x21420, 1); (0x21340, 7); (0x21360, 3);
 (0x21380, 4); (0x213a0, 3); (0x213c0, 5); (0x213e0, 9); (0x21400, 5)].
(* the strings param[j] points to (ent_headamp_key.param, 0x9a620 + 8 j) *)
Definition w7_pptr (j : Z) : Z := nth (Z.to_nat j) [0x21340; 0x21360; 0x21380; 0x213a0; 0x213c0; 0x21200; 0x213e0; 0x21400] 0.

(* the image's read-only bytes the readers fall back to *)
Definition w7_rom_some (a : Z) : bool := match seg_rom rsegs (Z_to_bv 64 a) with Some _ => true | None => false end.
(* the addresses after a string's NUL to the end of the NUL's 8-byte word *)
Definition w7_tail_addrs (x len : Z) : list Z :=
map (fun i => x + len + 1 + Z.of_nat i) (seq 0 (Z.to_nat (7 - (x + len) mod 8))).
Lemma w7_tail_chk : forallb (fun p => forallb w7_rom_some (w7_tail_addrs (fst p) (snd p))) w7_tail_strs = true.
Proof. vm_compute. reflexivity. Qed.

(* the digits of c mod 64 and the odd_ch strings have no zero byte *)
Lemma w7_dec64_chk : forallb (fun n => no_nul (dec64 (Z.of_nat n))) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w7_no_nul_Forall : forall l, no_nul l = true -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. unfold no_nul in H.
pose proof (proj1 (forallb_forall _ _) H b Hb) as Hq. cbn beta in Hq.
apply negb_true_iff, Z.eqb_neq in Hq. exact Hq.
Qed.
Lemma w7_dec64_nz : forall v, 0 <= v < 64 -> Forall (fun b : byte => bv_unsigned b <> 0) (dec64 v).
Proof.
intros v Hv. apply w7_no_nul_Forall.
pose proof (proj1 (forallb_forall _ _) w7_dec64_chk (Z.to_nat v) ltac:(apply in_seq; lia)) as Hq.
cbn beta in Hq. rewrite Z2Nat.id in Hq by lia. exact Hq.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.


(* ---- the bytes to the end of each string's NUL word are image bytes ---- *)
Lemma w7_tail_img : forall x len, In (x, len) w7_tail_strs -> forall a, x + len < a < x + len - (x + len) mod 8 + 8 ->
forall (H : word -> bool) mem, aview rsegs H mem a <> None.
Proof.
intros x len Hin a Ha H mem.
pose proof (proj1 (forallb_forall _ _) w7_tail_chk (x, len) Hin) as Hq. cbn [fst snd] in Hq.
assert (Hm : 0 <= (x + len) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Ha' : In a (w7_tail_addrs x len)).
{ unfold w7_tail_addrs. apply in_map_iff. exists (Z.to_nat (a - (x + len + 1))). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. revert Ha Hm. generalize ((x + len) mod 8). intros m Ha Hm. lia. }
pose proof (proj1 (forallb_forall _ _) Hq a Ha') as Hr. unfold w7_rom_some in Hr.
unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom rsegs (Z_to_bv 64 a)); [discriminate | discriminate Hr].
Qed.

(* ---- the key's first part has no zero byte ---- *)
Lemma w7_odd_nz : forall n, no_nul (nth n odd_ch []) = true.
Proof.
intros n. pose proof tables_no_nul as Ht. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [_ Ho].
destruct (nth_in_or_default n odd_ch []) as [Hin | ->].
- exact (proj1 (forallb_forall _ _) Ho _ Hin).
- reflexivity.
Qed.
Lemma w7_chs_nonzero : forall rr chs pb r, (chs, pb, r) = rs_g_of rr -> Forall (fun b : byte => bv_unsigned b <> 0) chs.
Proof.
intros rr chs pb r H.
assert (Hc : chs = fst (fst (rs_g_of rr))) by (rewrite <- H; reflexivity).
clear H. subst chs. unfold rs_g_of.
destruct (Cursor.fuzz_u8 rr) as [k0 r1]. destruct (Cursor.fuzz_u8 r1) as [c r2]. destruct (Cursor.fuzz_u8 r2) as [pb' r3].
cbn [fst]. destruct (c <? 200).
- apply w7_dec64_nz. apply Z.mod_pos_bound. lia.
- apply w7_no_nul_Forall. exact (w7_odd_nz (Z.to_nat (c mod 14))).
Qed.

(* ---- the image's param table, strings and separators against the model ---- *)
Ltac w7_in := repeat (first [left; vm_compute; reflexivity | right]).
Lemma w7_param_cell : forall j, 0 <= j < 8 -> In (0x9a620 + 8 * j, w7_pptr j) role_A_cells.
Proof.
intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
unfold role_A_cells; cbn [In].
repeat (destruct E as [E|E]; [subst j; w7_in|]). subst j. w7_in.
Qed.
Lemma w7_param_str : forall j, 0 <= j < 8 -> In (w7_pptr j, map (fun b : byte => bv_unsigned b) (nth (Z.to_nat j) param [])) role_A_strs.
Proof.
intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
unfold role_A_strs; cbn [In].
repeat (destruct E as [E|E]; [subst j; w7_in|]). subst j. w7_in.
Qed.
Lemma w7_param_tail : forall j, 0 <= j < 8 -> In (w7_pptr j, Z.of_nat (length (nth (Z.to_nat j) param []))) w7_tail_strs.
Proof.
intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
unfold w7_tail_strs; cbn [In].
repeat (destruct E as [E|E]; [subst j; w7_in|]). subst j. w7_in.
Qed.
Lemma w7_hpfx_str : In (0x20f00, map (fun b : byte => bv_unsigned b) HPFX) role_A_strs.
Proof. unfold role_A_strs; cbn [In]. w7_in. Qed.
Lemma w7_sep_str : forall p, In (w7_sep p, map (fun b : byte => bv_unsigned b) (if Z.testbit p 7 then [] else DOT)) role_A_strs.
Proof. intros p. unfold w7_sep, role_A_strs. destruct (Z.testbit p 7); cbn [In]; w7_in. Qed.
Lemma w7_sep_tail : forall p, In (w7_sep p, Z.of_nat (length (if Z.testbit p 7 then [] else DOT))) w7_tail_strs.
Proof. intros p. unfold w7_sep, w7_tail_strs. destruct (Z.testbit p 7); cbn [In]; w7_in. Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* The strlen wrapper in the journal form (as reac_box_catalogue_defect.v's aj_strcmp_at for strcmp). *)
Lemma w7_strlen_at : forall pc, astrlen_realizes rsegs B pc ->
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
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using LAWS.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
pose proof w7_segs_low as Hsegs.
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
{ eapply (ajournal_after_write rsegs B LAWS w7_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
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
