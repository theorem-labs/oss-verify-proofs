(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/ACes.v:275-278
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/A/ACfk.v:194-195 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh9.v:115-118 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v at origin/ossv/recipes 2d2ff01bb6f2 (aj_strlen_at, as w7_strlen_at, over reac-pw/fuzz_role's image A: SEGS := rsegs, pa_segs_low := w7_segs_low, and the post also keeps the I/O state, same_io from the wrapper's same_but_materialized); the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bCall.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the ten strings, the param table and its pointers, and the read-only PT_LOAD are rate's; role_A_cells / role_A_strs / rl_cstr / RPgMem.rm_val1_aview are lib/A/RtPgImgA.v rate_A_cells / rate_A_strs, lib/A/RtPgBase.v rt_cstr and lib/A/RtPgMem.v rtm_val1_aview; the strlen wrapper's contract is this unit's lib/A/Rt/StrlenDef.v astrlen_realizes (STRLEN_ENTRY 0x42194) with lib/A/Rt/WrapRo.v aro_unowned. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bCall.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the param table is image B's 0x9bee0 (its eight pointers and the ten strings are at image A's addresses, checked against image B's record lib/AU/RtPgImgB.v rate_B_cells / rate_B_strs); rtm_val1_aview is lib/AU/RtPgMemB.v rtmb_val1_aview; rs_g_of is lib/AU/RtPgSegB.v rsb_g_of; the strlen wrapper is image B's 0x421ec; the bodies of lib/A/Rt/WrapRo.v aro_unowned and lib/A/Rt/StrlenDef.v astrlen_realizes (both at 7362983f76f9, both parametric in the segments and the entry pc) are restated here as w7b_aro_unowned and w7b_astrlen_realizes, word for word, for the image-B wrapper contract that is not yet a file of image B; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the strlen call site of the walk of
   LLVMFuzzerTestOneInput from 0x8160c (lib/AU/RtPgW7bBaseB.v) and the string facts its blocks use. Proves no
   function (kind: segment lemma).

   - w7b_aro_unowned / w7b_astrlen_realizes: the read-only premise and the contract of the strlen wrapper, the text
     of lib/A/Rt/WrapRo.v and lib/A/Rt/StrlenDef.v (parametric in segs and pc); the walk takes the contract at image
     B's entry 0x421ec (`jal` 0x816a4, the strlen wrapper) as a Section hypothesis.
   - w7b_strlen_at: the strlen wrapper in the journal form.
   - w7b_first_byte_cstr / w7b_first_byte_bytes: first_byte of a NUL-terminated string, from rt_cstr or its bytes.
   - w7b_tail_strs / w7b_tail_img: the ten strings the head-amp key reads (HPFX, the two separators, the eight
     param[] strings): the bytes from each string's NUL to the end of the NUL's 8-byte word lie in the read-only
     PT_LOAD [0x10000, 0x2fa0c), so every reader sees them whatever the memory.
   - w7b_chs_nonzero: the key's first part (the decimal text of c mod 64 or odd_ch[c mod 14]) has no zero byte.
   - w7b_param_cell / w7b_param_str / w7b_param_tail, w7b_hpfx_str, w7b_sep_str / w7b_sep_tail: image B's param
     table cells (ent_headamp_key.param at 0x9bee0) and strings against the model's param list, HPFX and the
     separators.
   - w7b_strlen_cstr: one strlen call on a string of the image (rt_cstr) at the call site's stack. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB RtPgImgB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgMemB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ---- the strlen wrapper's premise and contract (lib/A/Rt/WrapRo.v, lib/A/Rt/StrlenDef.v: segs, pc parameters) ---- *)
Definition w7b_aro_unowned (segs : list Segment) (B : asyms) (rd : reader) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition w7b_astrlen_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x k,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
w7b_aro_unowned segs B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End s.

(* ---- the ten strings the head-amp key reads: (address, length without the NUL) ---- *)
Definition w7b_tail_strs : list (Z * Z) := [(0x20fe0, 13); (0x212e0, 0); (0x21500, 1); (0x21420, 7); (0x21440, 3);
 (0x21460, 4); (0x21480, 3); (0x214a0, 5); (0x214c0, 9); (0x214e0, 5)].
(* the strings param[j] points to (ent_headamp_key.param, 0x9bee0 + 8 j) *)
Definition w7b_pptr (j : Z) : Z := nth (Z.to_nat j) [0x21420; 0x21440; 0x21460; 0x21480; 0x214a0; 0x212e0; 0x214c0; 0x214e0] 0.

(* the image's read-only bytes the readers fall back to *)
Definition w7b_rom_some (a : Z) : bool := match seg_rom rsegs (Z_to_bv 64 a) with Some _ => true | None => false end.
(* the addresses after a string's NUL to the end of the NUL's 8-byte word *)
Definition w7b_tail_addrs (x len : Z) : list Z :=
map (fun i => x + len + 1 + Z.of_nat i) (seq 0 (Z.to_nat (7 - (x + len) mod 8))).
Lemma w7b_tail_chk : forallb (fun p => forallb w7b_rom_some (w7b_tail_addrs (fst p) (snd p))) w7b_tail_strs = true.
Proof. vm_compute. reflexivity. Qed.

(* the digits of c mod 64 and the odd_ch strings have no zero byte *)
Lemma w7b_dec64_chk : forallb (fun n => no_nul (dec64 (Z.of_nat n))) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w7b_no_nul_Forall : forall l, no_nul l = true -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. unfold no_nul in H.
pose proof (proj1 (forallb_forall _ _) H b Hb) as Hq. cbn beta in Hq.
apply negb_true_iff, Z.eqb_neq in Hq. exact Hq.
Qed.
Lemma w7b_dec64_nz : forall v, 0 <= v < 64 -> Forall (fun b : byte => bv_unsigned b <> 0) (dec64 v).
Proof.
intros v Hv. apply w7b_no_nul_Forall.
pose proof (proj1 (forallb_forall _ _) w7b_dec64_chk (Z.to_nat v) ltac:(apply in_seq; lia)) as Hq.
cbn beta in Hq. rewrite Z2Nat.id in Hq by lia. exact Hq.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- first_byte of a NUL-terminated string ---- *)
Lemma w7b_first_byte_cstr : forall (W : world rsegs) mem x s, rt_cstr rsegs (w_H W) mem x s ->
first_byte rsegs W mem x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W mem x s (Hb & Hnul & Hrng & _).
split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) s 0). split; [exact (Hb i Hi)|].
  assert (Hin : In (nth (Z.to_nat i) s 0) s) by (apply nth_In; lia).
  pose proof (proj1 (Forall_forall _ _) Hrng _ Hin) as Hr. cbn beta in Hr. lia.
- intros _. exact Hnul.
Qed.

Lemma w7b_first_byte_bytes : forall (W : world rsegs) mem x (s : list byte),
garr8 rsegs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) (s ++ [Cursor.NUL])) ->
Forall (fun b : byte => bv_unsigned b <> 0) s ->
first_byte rsegs W mem x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W mem x s Hg Hnz.
assert (Hlen : length (map (fun b : byte => bv_unsigned b) (s ++ [Cursor.NUL])) = S (length s))
  by (rewrite length_map, length_app; cbn [length]; lia).
assert (Hnth : forall j, (j <= length s)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) (s ++ [Cursor.NUL])) 0 = bv_unsigned (nth j (s ++ [Cursor.NUL]) Cursor.NUL)).
{ intros j Hj.
  rewrite (nth_indep _ 0 (bv_unsigned Cursor.NUL)) by (rewrite Hlen; lia).
  rewrite map_nth. reflexivity. }
assert (Hv : forall j, (j <= length s)%nat ->
  aview rsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j (s ++ [Cursor.NUL]) Cursor.NUL))).
{ intros j Hj. destruct (Hg j ltac:(rewrite Hlen; lia)) as [Hm Hr].
  rewrite (Hnth j Hj) in Hm, Hr.
  exact (RtPgMemB.rtmb_val1_aview rsegs (w_H W) mem _ _ Hm Hr). }
split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) (s ++ [Cursor.NUL]) Cursor.NUL)).
  split.
  + replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply Hv. lia.
  + rewrite app_nth1 by lia. apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _. rewrite (Hv (length s) ltac:(lia)). rewrite nth_middle. reflexivity.
Qed.

(* ---- the bytes to the end of each string's NUL word are image bytes ---- *)
Lemma w7b_tail_img : forall x len, In (x, len) w7b_tail_strs -> forall a, x + len < a < x + len - (x + len) mod 8 + 8 ->
forall (H : word -> bool) mem, aview rsegs H mem a <> None.
Proof.
intros x len Hin a Ha H mem.
pose proof (proj1 (forallb_forall _ _) w7b_tail_chk (x, len) Hin) as Hq. cbn [fst snd] in Hq.
assert (Hm : 0 <= (x + len) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Ha' : In a (w7b_tail_addrs x len)).
{ unfold w7b_tail_addrs. apply in_map_iff. exists (Z.to_nat (a - (x + len + 1))). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. revert Ha Hm. generalize ((x + len) mod 8). intros m Ha Hm. lia. }
pose proof (proj1 (forallb_forall _ _) Hq a Ha') as Hr. unfold w7b_rom_some in Hr.
unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom rsegs (Z_to_bv 64 a)); [discriminate | discriminate Hr].
Qed.

(* ---- the key's first part has no zero byte ---- *)
Lemma w7b_odd_nz : forall n, no_nul (nth n odd_ch []) = true.
Proof.
intros n. pose proof tables_no_nul as Ht. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [_ Ho].
destruct (nth_in_or_default n odd_ch []) as [Hin | ->].
- exact (proj1 (forallb_forall _ _) Ho _ Hin).
- reflexivity.
Qed.
Lemma w7b_chs_nonzero : forall rr chs pb r, (chs, pb, r) = rsb_g_of rr -> Forall (fun b : byte => bv_unsigned b <> 0) chs.
Proof.
intros rr chs pb r H.
assert (Hc : chs = fst (fst (rsb_g_of rr))) by (rewrite <- H; reflexivity).
clear H. subst chs. unfold rsb_g_of.
destruct (Cursor.fuzz_u8 rr) as [k0 r1]. destruct (Cursor.fuzz_u8 r1) as [c r2]. destruct (Cursor.fuzz_u8 r2) as [pb' r3].
cbn [fst]. destruct (c <? 200).
- apply w7b_dec64_nz. apply Z.mod_pos_bound. lia.
- apply w7b_no_nul_Forall. exact (w7b_odd_nz (Z.to_nat (c mod 14))).
Qed.

(* ---- image B's param table, strings and separators against the model ---- *)
Ltac w7b_in := repeat (first [left; vm_compute; reflexivity | right]).
Lemma w7b_param_cell : forall j, 0 <= j < 8 -> In (0x9bee0 + 8 * j, w7b_pptr j) rate_B_cells.
Proof.
intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
unfold rate_B_cells; cbn [In].
repeat (destruct E as [E|E]; [subst j; w7b_in|]). subst j. w7b_in.
Qed.
Lemma w7b_param_str : forall j, 0 <= j < 8 -> In (w7b_pptr j, map (fun b : byte => bv_unsigned b) (nth (Z.to_nat j) param [])) rate_B_strs.
Proof.
intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
unfold rate_B_strs; cbn [In].
repeat (destruct E as [E|E]; [subst j; w7b_in|]). subst j. w7b_in.
Qed.
Lemma w7b_param_tail : forall j, 0 <= j < 8 -> In (w7b_pptr j, Z.of_nat (length (nth (Z.to_nat j) param []))) w7b_tail_strs.
Proof.
intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
unfold w7b_tail_strs; cbn [In].
repeat (destruct E as [E|E]; [subst j; w7b_in|]). subst j. w7b_in.
Qed.
Lemma w7b_hpfx_str : In (0x20fe0, map (fun b : byte => bv_unsigned b) HPFX) rate_B_strs.
Proof. unfold rate_B_strs; cbn [In]. w7b_in. Qed.
Lemma w7b_sep_str : forall p, In (w7b_sep p, map (fun b : byte => bv_unsigned b) (if Z.testbit p 7 then [] else DOT)) rate_B_strs.
Proof. intros p. unfold w7b_sep, rate_B_strs. destruct (Z.testbit p 7); cbn [In]; w7b_in. Qed.
Lemma w7b_sep_tail : forall p, In (w7b_sep p, Z.of_nat (length (if Z.testbit p 7 then [] else DOT))) w7b_tail_strs.
Proof. intros p. unfold w7b_sep, w7b_tail_strs. destruct (Z.testbit p 7); cbn [In]; w7b_in. Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* The strlen wrapper in the journal form (as reac_box_catalogue_defect.v's aj_strcmp_at for strcmp). *)
Lemma w7b_strlen_at : forall pc, w7b_astrlen_realizes rsegs B pc ->
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
w7b_aro_unowned rsegs B (aview rsegs (w_H W) memT) ->
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
pose proof w7b_segs_low as Hsegs.
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
{ eapply (ajournal_after_write rsegs B LAWS w7b_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
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

(* One strlen call on a string of the image at the call site's stack. *)
Lemma w7b_strlen_cstr : w7b_astrlen_realizes rsegs B W7B_STRLEN ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x s (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
rt_cstr rsegs (w_H W) memT x s -> In (x, Z.of_nat (length s)) w7b_tail_strs ->
(forall a, x <= a <= x + Z.of_nat (length s) -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
w7b_aro_unowned rsegs B (aview rsegs (w_H W) memT) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 W7B_STRLEN) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length s)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using LAWS.
intros AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x s o raw
HJ Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcs Htail Hbx Hro.
pose proof Hcs as (Hb & Hnul & Hrng & Hx0 & Hxk & _ & Hmx & Hrx & Hhx).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hk1 : Z.of_nat (length s) + 1 < 2 ^ 32).
{ unfold w7b_tail_strs in Htail. cbn [In] in Htail.
  repeat (destruct Htail as [Htail|Htail]; [injection Htail as _ Hl; lia|]). destruct Htail. }
apply (w7b_strlen_at W7B_STRLEN AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x (Z.of_nat (length s)) o raw
  HJ Ha0 Hx0 ltac:(lia) Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw).
- exact (w7b_first_byte_cstr W memT x s Hcs).
- intros a Ha. split.
  + destruct (Z.eq_dec a (x + Z.of_nat (length s))) as [->|Hne].
    * rewrite Hnul. discriminate.
    * replace a with (x + (a - x)) by lia. rewrite (Hb (a - x) ltac:(lia)). discriminate.
  + rewrite Hsp'. intros Hs. apply (Hbx a ltac:(lia)). lia.
- exact Hbx.
- exact Hmx.
- exact Hrx.
- exact Hhx.
- intros a Ha. exact (w7b_tail_img x (Z.of_nat (length s)) Htail a Ha (w_H W) memT).
- exact Hro.
Qed.
End d.
End b.

Print Assumptions w7b_strlen_at.
Print Assumptions w7b_strlen_cstr.
Print Assumptions w7b_first_byte_bytes.
Print Assumptions w7b_chs_nonzero.
Print Assumptions w7b_param_cell.
Print Assumptions w7b_param_str.
Print Assumptions w7b_param_tail.
Print Assumptions w7b_hpfx_str.
