(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 214 of its 271 lines of code are new or changed and 721 lines of the source are left out. *)
(* fuzz_preset, slice S6 (BPjGet of h-rw-pre-5, for WalkS6's image-A pj_get and image B's): the IMAGE-FREE pieces of
   pj_get's member loop, generic over the program listing {L}, its image facts {PA : PAImg L}, the generated image
   record {PI : PrhImg} and the allocator relation ARx with its laws at the harness head (LAWS : AR_laws_x .. cf_head).
   (1) the per-string premises of the strcmp rule (YGcallMx.v aj_strcmp_at_x; the same premises in family 1b's
       YGcallMxmn.v aj_strcmp_at_xrom, 3c08bbab8292 at the cut), bundled as pjs_str_pre: for the key k from cstr_ok
       (pjs_k_strcmp_pre) and for a member key in a live harness block (pjs_key_strcmp_pre);
   (2) the strcmp result as list equality (pjs_strcmp_iff);
   (3) the tree facts: the i-th member's key word, key string and node (pjs_mems_nth, plain lib/Prog/pj_get.v:123
       gp_mems_nth restated over pj_memsR), the harness block facts (pjs_lam_blk), and the two prhPj_get_res
       assemblies (pjs_res_found, pjs_res_none).
   Kit: the kit texts as the kit's cut 7cdbb61b5fa0 carries them (first fitted at the walk kit
   (the #102 kit tip): the m-form posts over YAkMemnorm; the Batch-2 ledger prh_ledger .. most own, which pjs_lam_blk /
   pjs_key_strcmp_pre / section (4) carry; re-fit 2026-10-29 from the walk kit PREVIEW 04388d628fb), which keep
   the pj_cstrR of preset-tree-at-2026-10-29T10-39-06Z.tsv (sha256 1452ee1ee024; internal record) (PRH_Reader.v 4266e709561a :113-116 at the cut) with the reader's name bound
   `Z.of_nat (length s) + 1 < 2 ^ 32` (h-hpreset-7 ruling 09:19Z): pjs_key_strcmp_pre takes the strcmp rule's member-key
   bound from it. Section (4) at the end: tpj_get_specXP, tpj_get_str_specXP and their conversions to the texts.
   Numerals: 56 / 24 / 8 (LENGTH: node, kids field, word), 16 (LENGTH: CfParams_preset's cf_head, the harness head
   and block alignment), 8 / 7 (LENGTH: granule), 4096 (DERIVED: the blocks law's floor), 2 ^ 32 / 2 ^ 63 / 2 ^ 64
   (DERIVED: the strcmp rule's bounds). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnPj CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- no state ---- *)
(* cgif YCbq.v:1945 shadow_hull_vis_of_block, for any covering hull (FuzzStrdupB.v sd_hull_sub) *)
Lemma pjs_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* the names before i differ from kname, one more member *)
Lemma pjs_pre_step : forall (l : list (list Z * jv)) kname i nm u,
  (forall j nm' u', (j < i)%nat -> nth_error l j = Some (nm', u') -> nm' <> kname) ->
  nth_error l i = Some (nm, u) -> nm <> kname ->
  forall j nm' u', (j < S i)%nat -> nth_error l j = Some (nm', u') -> nm' <> kname.
Proof.
intros l kname i nm u Hpre Ei Hne j nm' u' Hj Ej. destruct (Nat.eq_dec j i) as [->|Hne'].
- rewrite Ei in Ej. injection Ej as <- _. exact Hne.
- apply (Hpre j nm' u'); [lia | exact Ej].
Qed.
(* every name differs, from the names before length l *)
Lemma pjs_none_all : forall (l : list (list Z * jv)) kname,
  (forall j nm u, (j < length l)%nat -> nth_error l j = Some (nm, u) -> nm <> kname) ->
  forall nm u, In (nm, u) l -> nm <> kname.
Proof.
intros l kname H nm u Hin. apply In_nth_error in Hin. destruct Hin as (j & Ej).
apply (H j nm u); [|exact Ej]. apply nth_error_Some. rewrite Ej. discriminate.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ L PA).

(* ---- bytes ---- *)
Lemma pjs_garr8_aview : forall (W : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma pjs_apresent_aview : forall (W : world SEGS) m a, apresent (w_H W) m a -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn [option_map]. discriminate.
Qed.

(* ---- the per-string premises of aj_strcmp_at_x at a call state whose sp is spZ regs ---- *)
Definition pjs_str_pre (W : world SEGS) (regs : bvmap 5 word) (m : word -> option byte) (x kx : Z) : Prop :=
  0 < x /\ 0 <= kx /\ kx + 1 < 2 ^ 32 /\ x + kx + 1 <= 2 ^ 63 /\
  first_byte SEGS W m x (kx + 1) 0 kx /\ src_ok SEGS W regs m x (kx + 1) /\
  (forall a, x <= a <= x + kx -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
  YGcallMx.amem_range8 x (kx + 1) /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x (kx + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) m) x (kx + 1) /\
  (forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview SEGS (w_H W) m a <> None).

(* first_byte and src_ok of a NUL-terminated byte list whose bytes are nonzero *)
Lemma pjs_first_byte : forall (W : world SEGS) m p cs, garr8 SEGS (mrestrict (w_H W) m) p (cs ++ [0]) ->
  Forall (fun c => c <> 0) cs -> first_byte SEGS W m p (Z.of_nat (length cs) + 1) 0 (Z.of_nat (length cs)).
Proof.
intros W m p cs Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cs 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (pjs_garr8_aview W m p (cs ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _. rewrite (pjs_garr8_aview W m p (cs ++ [0]) (length cs) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma pjs_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (pjs_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* (1a) the key k: cstr_ok holds every premise; the call's 2 * ESTACK window lies above YM05.alloc_ceiling *)
Lemma pjs_k_strcmp_pre : forall (W : world SEGS) regs m k kname,
  cstr_ok (PA := PA) W m k kname -> YM05.alloc_ceiling + 2 * ESTACK <= spZ regs ->
  pjs_str_pre W regs m k (Z.of_nat (length kname)).
Proof.
intros W regs m k kname ((Hg & Hnz) & H4096 & Hceil & H32 & Hamr & HRA & HH & Hv) Hsp.
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
split; [exact (pjs_first_byte W m k kname Hg Hnz)|].
split.
{ replace (Z.of_nat (length kname) + 1) with (Z.of_nat (length (kname ++ [0]))) by (rewrite length_app; cbn [length]; lia).
  apply (pjs_src_ok W regs m k _ Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. lia. }
split; [intros a Ha; lia|].
split; [unfold YGcallMx.amem_range8; unfold YGcfStr.amem_range8 in Hamr; exact Hamr|].
split; [exact HRA|]. split; [exact HH | exact Hv].
Qed.

Section l.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).

(* a live harness block of the ledger: aligned, above the blocks law's floor by its head, below YM05.alloc_ceiling, in
   application memory; a block shadow and a visible hull over its user bytes; its bytes present; its tail granule
   visible *)
Lemma pjs_lam_blk : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := PI) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam ->
  a mod 16 = 0 /\ 4096 <= a - 16 /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\ in_app (a - 16) (k + 16) /\
  In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp /\
  block_shadow (aview SEGS (w_H W) mem) SHADOW_OFF a k /\ (0 < k -> shadow_hull_vis (aview SEGS (w_H W) mem) a k) /\
  (forall x, a <= x < a + k -> apresent (w_H W) mem x) /\
  (forall x, a + k <= x < (a + k + 7) / 8 * 8 -> aview SEGS (w_H W) mem x <> None).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & Hhp & Ha16 & _).
change (@cf_head CP) with 16 in Hab, Hhp.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & Happ & Hpr & _).
rewrite gs_req in Hc, Happ, Hpr by lia.
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab Hhp) as [Hbs Hhu].
change (@cf_head CP) with 16 in Hbs, Hhu. rewrite gs_req in Hbs, Hhu by lia.
replace (a - 16 + 16) with a in Hbs, Hhu by lia. replace (k + 16 - 16) with k in Hbs, Hhu by lia.
split; [exact Ha16|]. split; [lia|]. split; [exact Hk0|]. split; [lia|]. split; [exact Happ|].
split; [exact Hab|]. split; [exact Hhp|]. split; [exact Hbs|]. split; [intros Hk; apply Hhu; lia|].
split; [intros x Hx; exact (proj1 (Hpr x ltac:(lia)))|].
intros x Hx. apply (alx_blocks_tail SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) x HAR Hab).
rewrite gs_req by lia. replace (a - 16 + (k + 16)) with (a + k) by lia. exact Hx.
Qed.

(* (1b) a member key: its string lies in a live harness block of the ledger; pj_cstrR gives its length bound *)
Lemma pjs_key_strcmp_pre : forall ly S Hp (W : world SEGS) mem md regs Lam peak cnt fail ran most own x kb nm,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := PI) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  pj_cstrR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) x kb nm ->
  YM05.alloc_ceiling + 2 * ESTACK <= spZ regs ->
  pjs_str_pre W regs mem x (Z.of_nat (length nm)).
Proof.
intros ly S Hp W mem md regs Lam peak cnt fail ran most own x kb nm HAR HL (Hlb & Hlen & H32 & Hnz & Hg) Hsp.
unfold prh_lin in Hlb.
destruct (pjs_lam_blk ly S Hp W mem md Lam peak cnt fail ran most own x kb HAR HL Hlb)
  as (Hx16 & H4096 & Hk0 & Hc & Happ & _ & _ & Hbs & Hhu & Hpr & Htl).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (kx := Z.of_nat (length nm)) in *.
assert (Hnz' : Forall (fun c => c <> 0) nm) by (eapply Forall_impl; [|exact Hnz]; cbv beta; intros c Hc'; lia).
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
split; [exact (pjs_first_byte W mem x nm Hg Hnz')|].
split.
{ replace (kx + 1) with (Z.of_nat (length (nm ++ [0]))) by (subst kx; rewrite length_app; cbn [length]; lia).
  apply (pjs_src_ok W regs mem x _ Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. lia. }
split; [intros a Ha; lia|].
split; [unfold YGcallMx.amem_range8; unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ; rewrite C4, C5; lia|].
split; [exact (block_shadow_range _ _ x kb x (kx + 1) Hbs ltac:(lia) ltac:(lia))|].
split; [exact (pjs_hull_sub _ x kb x (kx + 1) (Hhu ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))|].
intros a Ha. pose proof (Z.mod_pos_bound (x + kx) 8 ltac:(lia)) as Hm.
destruct (Z_lt_le_dec a (x + kb)) as [Hin|Hout].
- apply pjs_apresent_aview. apply Hpr. lia.
- apply Htl. split; [exact Hout|].
  pose proof (Z.div_mod (x + kx) 8 ltac:(lia)) as D1.
  assert (Hq : (x + kx) / 8 <= (x + kb + 7) / 8 - 1).
  { assert ((x + kx) / 8 * 8 + 8 <= x + kb + 7) by lia.
    assert ((x + kx) / 8 + 1 <= (x + kb + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  lia.
Qed.

End l.

(* (2) the strcmp result: the two strings agree byte for byte over equal lengths exactly when the names are equal *)
Lemma pjs_strcmp_iff : forall (W : world SEGS) m x nm k kname,
  garr8 SEGS (mrestrict (w_H W) m) x (nm ++ [0]) -> garr8 SEGS (mrestrict (w_H W) m) k (kname ++ [0]) ->
  (Z.of_nat (length nm) = Z.of_nat (length kname) /\
   forall i, 0 <= i < Z.of_nat (length nm) -> aview SEGS (w_H W) m (x + i) = aview SEGS (w_H W) m (k + i)) <->
  nm = kname.
Proof.
intros W m x nm k kname Hx Hk. split.
- intros (Hl & He). assert (Hl' : length nm = length kname) by lia.
  apply (nth_ext nm kname 0 0 Hl'). intros j Hj.
  specialize (He (Z.of_nat j) ltac:(lia)).
  rewrite (pjs_garr8_aview W m x (nm ++ [0]) j Hx) in He by (rewrite length_app; cbn; lia).
  rewrite (pjs_garr8_aview W m k (kname ++ [0]) j Hk) in He by (rewrite length_app; cbn; lia).
  rewrite !app_nth1 in He by lia. injection He as He. exact He.
- intros <-. split; [reflexivity|]. intros i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (pjs_garr8_aview W m x (nm ++ [0]) (Z.to_nat i) Hx) by (rewrite length_app; cbn; lia).
  rewrite (pjs_garr8_aview W m k (nm ++ [0]) (Z.to_nat i) Hk) by (rewrite length_app; cbn; lia).
  reflexivity.
Qed.

(* (3) the i-th member: its key word in keys, its key string, its node in kids (plain lib/Prog/pj_get.v:123
   gp_mems_nth, over pj_memsR); the key block and the node's blocks are blocks of the whole *)
Lemma pjs_mems_nth : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  pj_memsR SEGS m lblk P a ka l D -> nth_error l i = Some (nm, u) ->
  exists x k D1, rd_u64 SEGS m (ka + 8 * Z.of_nat i) x /\ pj_cstrR SEGS m lblk x k nm /\
    P (a + 56 * Z.of_nat i) u D1 /\ incl D1 D /\ In (x, k) D.
Proof.
intros m lblk P l. induction l as [|[nm0 u0] l IH]; intros a ka D i nm u H E; [destruct i; discriminate|].
cbn [pj_memsR] in H. destruct H as (x & k & D1 & D2 & -> & Hx & Hc & Hp & Hr).
destruct i as [|i]; cbn [nth_error] in E.
- injection E as <- <-. exists x, k, D1. cbn [Z.of_nat]. rewrite !Z.mul_0_r, !Z.add_0_r.
  split; [exact Hx|]. split; [exact Hc|]. split; [exact Hp|]. split; [|left; reflexivity].
  intros y Hy. right. apply in_or_app. left. exact Hy.
- destruct (IH _ _ _ _ _ _ Hr E) as (x' & k' & D1' & H1 & H2 & H3 & H4 & H5).
  exists x', k', D1'. replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
  + intros y Hy. right. apply in_or_app. right. exact (H4 y Hy).
  + right. apply in_or_app. right. exact H5.
Qed.

(* the found result: the first member whose name is kname, at kids + 56 i *)
Lemma pjs_res_found : forall m lblk o members D kname num kids keys n cap Di i v,
  pj_hdrR SEGS m o 6 num 0 kids keys n cap ->
  D = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di ->
  pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys members Di ->
  nth_error members i = Some (kname, v) ->
  (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) ->
  prhPj_get_res (PA := PA) m lblk o (JObj members) D kname (kids + 56 * Z.of_nat i).
Proof.
intros m lblk o members D kname num kids keys n cap Di i v Hh ED HM Ei Hpre.
destruct (pjs_mems_nth _ _ _ _ _ _ _ _ _ _ HM Ei) as (x & kx & D1 & _ & _ & Hp & Hinc & _).
unfold prhPj_get_res. right. exists i, v, kids, D1.
split; [exact Ei|]. split; [exact Hpre|]. split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hh)))))|].
split; [reflexivity|]. split; [exact Hp|].
intros y Hy. rewrite ED. apply in_or_app. right. apply Hinc. exact Hy.
Qed.

(* the result when no member's name is kname *)
Lemma pjs_res_none : forall m lblk o members D kname,
  (forall j nm u, (j < length members)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) ->
  prhPj_get_res (PA := PA) m lblk o (JObj members) D kname 0.
Proof.
intros m lblk o members D kname H. unfold prhPj_get_res. left. split; [exact (pjs_none_all members kname H) | reflexivity].
Qed.
End c.

(* ======== (4) the keep of a memory invariant P (2026-10-29, the layering hold: the m-form over a generic P) ======== *)
(* tpj_get_specXP / tpj_get_str_specXP: the tpj_get_specX / tpj_get_str_specX (PRH_FnPj.v:1289-1319 on this tree; blob 5aca5cbe2cfb :810-840 at
   the kit's cut 7cdbb61b5fa0; first stated at walk kit preview 2d523216ac5) with `fpostm .. Q` = `fpost .. (fQmn mem Q)`
   generalised to
   `fpost .. (fun .. => Q .. /\ (P mem -> P mem'))`: a generalisation of the kit's text, equal to it by conversion at
   P := the memnorm of fQmn (tpj_get_specX_of_P / tpj_get_str_specX_of_P, at the kit's YAk spelling, walk kit
   (the #102 kit tip)). The premises and
   the inner Q are the text's, character for character, except that prhPj_rslot, a definition of PRH_FnPj's section, takes
   the section variable B explicitly here. *)
Section xp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition tpj_get_specXP (P : (word -> option byte) -> Prop) : Prop :=
  forall ly S Hp W regs mem md ch o k (kname : list Z) (t : PjTree.jv) D Lam peak cnt fail ran most own,
  fpre B ARx STK_pj_get ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 k ->
  (o = 0 \/ pj_nodeR segs (rdW W mem) (prh_lin Lam) o t D /\ prhPj_rslot B STK_pj_get ly S W regs mem o) ->
  cstr_ok W mem k kname ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_pj_get) regs mem md)
    (fpost B ARx SK STK_pj_get [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
      (Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (room_live_cf S -> room_live_cf S') /\
       (o = 0 /\ getr regs' 10 = w64 0 \/
        o <> 0 /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam) o t D /\
        exists z, getr regs' 10 = w64 z /\ prhPj_get_res (rdW W' mem') (prh_lin Lam) o t D kname z)) /\
      (P mem -> P mem'))).
Definition tpj_get_str_specXP (P : (word -> option byte) -> Prop) : Prop :=
  forall ly S Hp W regs mem md ch o k (kname : list Z) (t : PjTree.jv) D Lam peak cnt fail ran most own,
  fpre B ARx STK_pj_get_str ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 k ->
  (o = 0 \/ pj_nodeR segs (rdW W mem) (prh_lin Lam) o t D /\ prhPj_rslot B STK_pj_get_str ly S W regs mem o) ->
  cstr_ok W mem k kname ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_pj_get_str) regs mem md)
    (fpost B ARx SK STK_pj_get_str [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
      (Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (room_live_cf S -> room_live_cf S') /\
       (o = 0 /\ getr regs' 10 = w64 0 \/
        o <> 0 /\ pj_nodeR segs (rdW W' mem') (prh_lin Lam) o t D /\
        exists z, getr regs' 10 = w64 z /\ prhPj_get_str_res (rdW W' mem') (prh_lin Lam) o t D kname z)) /\
      (P mem -> P mem'))).
(* The kit's texts are the instances at fQmn's invariant (PRH_Base.v ef7c8ca98529 at the kit's cut 7cdbb61b5fa0, fQmn over
   YAkMemnorm.memnorm), by conversion *)
Lemma tpj_get_specX_of_P : tpj_get_specXP (YAkMemnorm.memnorm segs) -> tpj_get_specX B ARx SK.
Proof. intros H. exact H. Qed.
Lemma tpj_get_str_specX_of_P : tpj_get_str_specXP (YAkMemnorm.memnorm segs) -> tpj_get_str_specX B ARx SK.
Proof. intros H. exact H. Qed.
End xp.
