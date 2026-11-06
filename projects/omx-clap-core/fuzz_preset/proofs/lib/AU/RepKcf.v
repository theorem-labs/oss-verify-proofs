(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepKcf.v (commit 4d286b2e618d, file sha256 8c630d7d5e16) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepKcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 978502dfd302) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (the internal file accept.tsv, re-measured each run): _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm+0xb0 (lui-in-section: CONSTANT (size; enters a store base only as a scaled count into a runtime array): kUserMapSize = 0x40000)), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, RepF1Arm2): the report arm's composition kit, at the model level and for the
   glue between the symbolic states and the errbuf calls.  No machine code runs in this file.
   rule 24: proves no function (kind: model and glue lemmas of PopulateFreeArray's class-full report arm).
   - [printf_ipost]: RepIFcf.printf_spec_cf with the K-trick (RepModel2cf.amreal_ibind_ipost, an IFail guard decided by
     [rk_pdec]), so the call's continuation also learns a post P of errb_append_cf at its returned state.
   - [append_grows]: errb_append_cf never shortens st_secs (the layout_le chain across the two appends).
   - [post1_P] / [post2_P] with [post1_ipost] / [post2_ipost]: only_secs, the growth, and the errbuf extent (append_first,
     append_keeps_xs); [xs_mid] and [AOX_mid]: the intermediate state's AOX set is the entry's or the final one's
     ([aowned_lay] by YG0scf.AR_layout_law_ok_cf and YFeu.aowned_same_cf).
   - [exh_cell_set]: the exhausted-byte cell after the store of 1 and exh_set; [rep_img_frame]: rep_img_facts reads only
     image bytes; [room1] / [room2]: the two appends' rooms from one ERRB_ROOM; [exh_cell_same]: the cells kept by a
     reader that agrees off the class's byte and holds the model's value there (RepLeafcf.leaf_G_fail's HCX).
   - [aregs_regs], [wvb_self], [st_ok_cfg]: register-set, model and machine-state glue. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality Classical_Prop IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG06cf YG0ncf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RepModelcf RepModel2cf RepIFcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YB1v YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0scf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0l YO0d.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section rk. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Local Open Scope am_scope.


Lemma rk_pdec (P : Prop) : {P} + {~ P}.
Proof.
destruct (constructive_indefinite_description (fun b : bool => if b then P else ~ P)) as [b Hb].
- destruct (classic P) as [H|H]; [exists true; exact H | exists false; exact H].
- destruct b; [left; exact Hb | right; exact Hb].
Qed.

Lemma printf_ipost : forall (P : astate -> Prop) (R : Type) Hp ly S W regs mem md fmt (out : list Z) lk (K : astate -> itree astate R) Q,
  RepIFcf.printf_spec_cf B ->
  YGcfXs.cfx_ipost (YG00cf.errb_append_cf (Z.of_nat (length out)) S) (fun r => P (snd r)) ->
  RepIFcf.errb_call_pre B lk Hp ly S W mem md -> RepIFcf.errb_room_for S (Z.of_nat (length out)) ->
  RepIFcf.errb_call_regs B RepIFcf.PR_STK ly W regs mem -> getr regs 10 = w64 fmt ->
  ((fmt = RepIFcf.FMT_OOM1 /\ getr regs 11 = w64 RepIFcf.A_TOOLNAME /\ out = RepIFcf.render1) \/
   (exists c sz, fmt = RepIFcf.FMT_OOM2 /\ 1 <= c <= 31 /\ sz = class_size c /\ getr regs 11 = w64 RepIFcf.REGION_MB /\
      getr regs 12 = w64 c /\ getr regs 13 = w64 sz /\ out = RepIFcf.render2 c sz)) ->
  Z.of_nat (length out) < 400 ->
  (forall S' W' c', P S' -> RepIFcf.errb_call_post B lk RepIFcf.PR_STK (Z.of_nat (length out)) Hp ly S S' W regs mem md W' c' ->
     amreal YB1v.tfibsegs (K S') W' c' Q) ->
  amreal YB1v.tfibsegs (ibind (YG00cf.errb_append_cf (Z.of_nat (length out)) S) (fun r => K (snd r)))
    W (cfg_at YB1v.tfibsegs RepIFcf.A_PRINTF regs mem md) Q.
Proof.
intros P R Hp ly S W regs mem md fmt out lk K Q HPR HIP HPRE HROOM HREGS HA0 HFMT HLEN HK.
set (K' := fun S' => if rk_pdec (P S') then K S' else @IFail astate R FFuel).
apply (RepModel2cf.amreal_ibind_ipost YB1v.tfibsegs _ (fun r => P (snd r)) (fun r => K (snd r)) (fun r => K' (snd r)) W _ Q HIP).
- intros r Hr. unfold K'. destruct (rk_pdec (P (snd r))) as [_|N]; [reflexivity | contradiction].
- apply (HPR R Hp ly S W regs mem md fmt out lk K' Q HPRE HROOM HREGS HA0 HFMT HLEN).
  intros S' W' c' HPOST. unfold K'. destruct (rk_pdec (P S')) as [HP|_]; [exact (HK S' W' c' HP HPOST) | exact I].
Qed.


(* The errbuf steps only add section entries: st_secs never shrinks (map / lupd keep the length, app adds). *)
Definition grows (s0 s : astate) : Prop := (length (st_secs s0) <= length (st_secs s))%nat.
Definition gr_step {A : Type} (m : M A) : Prop :=
  forall s0 s, grows s0 s -> YGcfXs.cfx_ipost (m s) (fun r => grows s0 (snd r)).

Lemma gr_bind : forall {A C} (m : M A) (k : A -> M C), gr_step m -> (forall a, gr_step (k a)) -> gr_step (bind m k).
Proof.
intros A C m k Hm Hk s0 s H. apply ipost_bind. eapply YGcfXs.cfx_ipost_mono; [|exact (Hm s0 s H)].
intros [a s1] H1. exact (Hk a s0 s1 H1).
Qed.
Lemma gr_get : forall {C} (k : astate -> M C), (forall x, gr_step (k x)) -> gr_step (bind get k).
Proof. intros C k Hk s0 s H. exact (Hk s s0 s H). Qed.
Lemma gr_ret : forall {A} (a : A), gr_step (ret a).
Proof. intros A a s0 s H. exact H. Qed.
Lemma gr_spin : forall {A} pc, gr_step (@spin A pc).
Proof. intros A pc s0 s H. exact I. Qed.
Lemma gr_askz : forall q, gr_step (askz q).
Proof. intros q s0 s H z. exact H. Qed.
Lemma rk_lupd_length : forall {X : Type} (l : list X) i v, length (lupd l i v) = length l.
Proof. intros X l. induction l as [|h t IH]; intros [|i] v; cbn [lupd length]; auto. Qed.
Lemma gr_tick : gr_step tick.
Proof. intros s0 s H. unfold tick, modify. cbn [YGcfXs.cfx_ipost snd]. exact H. Qed.
Lemma gr_retire : gr_step YG00cf.errb_retire.
Proof.
intros s0 s H. unfold YG00cf.errb_retire, modify. cbn [YGcfXs.cfx_ipost snd]. unfold grows in *.
cbn [set_secs YG00.st_secs]. rewrite length_map. exact H.
Qed.
Lemma gr_set_size : forall ns, gr_step (YG00cf.errb_set_size ns).
Proof.
intros ns s0 s H. unfold YG00cf.errb_set_size, modify. cbn [YGcfXs.cfx_ipost snd]. unfold grows in *.
destruct (find_sz (YG00.st_secs s) 0); cbn [set_secs YG00.st_secs].
- rewrite rk_lupd_length. exact H.
- rewrite length_app. cbn [length]. lia.
Qed.
Lemma gr_map : forall want, gr_step (YG00cf.errb_map_cf want).
Proof.
intros want. unfold YG00cf.errb_map_cf. cbv zeta.
apply gr_bind; [exact gr_tick | intros u].
apply gr_bind; [apply gr_askz | intros z].
destruct (z =? 0); [apply gr_spin |].
apply gr_bind; [exact gr_retire | intros u'].
intros s0 s H. unfold modify. cbn [YGcfXs.cfx_ipost snd]. unfold grows in *.
cbn [set_secs YG00.st_secs]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma append_grows : forall L s, YGcfXs.cfx_ipost (YG00cf.errb_append_cf L s) (fun r => grows s (snd r)).
Proof.
intros L s. assert (G : gr_step (YG00cf.errb_append_cf L)).
{ unfold YG00cf.errb_append_cf. apply gr_get. intros x.
  destruct (negb (YG00cf.errb_mapped_cf x)).
  - apply gr_bind; [apply gr_map | intros u]. apply gr_get. intros x1.
    apply gr_bind; [| intros u'; apply gr_set_size].
    destruct (YG00cf.errb_cap_cf x1 <? L); [apply gr_map | apply gr_ret].
  - cbv zeta. apply gr_bind; [| intros u; apply gr_set_size].
    destruct (YG00cf.errb_cap_cf x <? YG00cf.errb_size_cf x + L); [apply gr_map | apply gr_ret]. }
exact (G s s (le_n _)).
Qed.


(* The class's exhausted byte set to 1 and the model flag set together (the store at 0x37100 and set_exh_cf). *)
Lemma exh_cell_set : forall ly S (rd rd' : reader) c, 1 <= c <= 31 -> c <> kBatchClass ->
  (Z.to_nat c < length (st_regions S))%nat -> cf_exh_off = 68 ->
  exh_cell_cf B ly S rd ->
  (forall c', 1 <= c' <= 31 -> c' <> c ->
     rd' (ly_space ly + kRegionInfoOff + 128 * c' + 68) = rd (ly_space ly + kRegionInfoOff + 128 * c' + 68)) ->
  rd' (ly_space ly + kRegionInfoOff + 128 * c + 68) = Some 1 ->
  exh_cell_cf B ly (exh_set c S) rd'.
Proof.
intros ly S rd rd' c Hc Hb Hl HO [HE HK] Hoth Hc1. split.
- intros c' Hc'. specialize (HE c' Hc'). unfold cell_holds in HE |- *. cbn [c_at c_w c_val z1 c1] in HE |- *.
  assert (EA : aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c')) cf_exh_off) = ly_space ly + kRegionInfoOff + 128 * c' + 68)
    by (cbn [aeval aoff]; rewrite HO; lia).
  rewrite EA in HE |- *. intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (HE 0%nat Hk).
  cbn [Z.of_nat] in HE |- *. rewrite Z.add_0_r in HE |- *.
  rewrite (exh_set_mem c c' S (proj1 Hc) Hl).
  destruct (Z.eqb_spec c' c) as [->|Hne].
  + rewrite Hc1. reflexivity.
  + rewrite (Hoth c' Hc' Hne). exact HE.
- rewrite (exh_set_mem c kBatchClass S (proj1 Hc) Hl).
  destruct (Z.eqb_spec kBatchClass c) as [E|_]; [exfalso; apply Hb; symmetry; exact E | exact HK].
Qed.


Lemma rk_val_frame : forall (H : word -> bool) (m m' : word -> option byte) a (nb : nat) v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat nb -> m' x = m x) ->
  val_mem YB1v.tfibsegs (mrestrict H m) a nb v -> val_mem YB1v.tfibsegs (mrestrict H m') a nb v.
Proof.
intros H m m' a nb v A0 A1 E Hv. apply (val_mem_ext (mrestrict H m)); [|exact Hv].
intros k Hk. unfold mbyte, mrestrict. rewrite (E (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
rewrite unsigned_lit_small by lia. lia.
Qed.

(* rep_img_facts reads image bytes only: a memory that agrees on the image keeps it. *)
Lemma rep_img_frame : forall (W : world YB1v.tfibsegs) (m m' : word -> option byte), rep_img_facts W m ->
  (forall x : word, YF0x.TFIB_IMG_LO <= bv_unsigned x < YF0x.TFIB_IMG_END -> m' x = m x) -> rep_img_facts W m'.
Proof.
intros W m m' [T1 T2 T3 [V1 V2 V3 V4 V5]] E.
assert (F : forall a nb v, YF0x.TFIB_IMG_LO <= a -> a + Z.of_nat nb <= YF0x.TFIB_IMG_END ->
  val_mem YB1v.tfibsegs (mrestrict (w_H W) m) a nb v -> val_mem YB1v.tfibsegs (mrestrict (w_H W) m') a nb v).
{ intros a nb v A1 A2 Hv. apply (rk_val_frame _ m); [unfold YF0x.TFIB_IMG_LO in A1; lia | unfold YF0x.TFIB_IMG_END in A2; lia | | exact Hv].
  intros x Hx. apply E. lia. }
assert (FR : forall a s, YF0x.TFIB_IMG_LO <= a -> a + Z.of_nat (length s) <= YF0x.TFIB_IMG_END ->
  ro_bytes (mrestrict (w_H W) m) a s -> ro_bytes (mrestrict (w_H W) m') a s).
{ intros a s A1 A2 Hs i Hi. apply F; [lia | lia | exact (Hs i Hi)]. }
constructor.
- apply F; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact T1].
- apply F; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact T2].
- apply F; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact T3].
- constructor.
  + apply FR; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact V1].
  + apply FR; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact V2].
  + apply FR; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact V3].
  + apply F; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact V4].
  + apply F; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact V5].
Qed.


(* ---- owned sets and the errbuf extent across the arm's model steps ---- *)
Lemma aowned_lay : forall Hp W mem md ly ly' S S' a,
  ARcf YB1v.tfibsegs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  st_chunks S' = st_chunks S -> st_fs S' = st_fs S ->
  aowned B ly' S' a -> aowned B ly S a.
Proof.
intros Hp W mem md ly ly' S S' a HAR HL Hc Hf Ho.
pose proof (YG0scf.AR_layout_law_ok_cf YB1v.tfibsegs B ly S Hp W mem md ly' HAR HL) as (_ & _ & HO).
apply (proj1 (HO a)). exact (YFeu.aowned_same_cf B ly' S S' a Hc Hf Ho).
Qed.

Lemma aowned_lay_inv : forall Hp W mem md ly ly' S S' a,
  ARcf YB1v.tfibsegs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  st_chunks S' = st_chunks S -> st_fs S' = st_fs S ->
  aowned B ly S a -> aowned B ly' S' a.
Proof.
intros Hp W mem md ly ly' S S' a HAR HL Hc Hf Ho.
pose proof (YG0scf.AR_layout_law_ok_cf YB1v.tfibsegs B ly S Hp W mem md ly' HAR HL) as (_ & _ & HO).
apply (YFeu.aowned_same_cf B ly' S' S a (eq_sym Hc) (eq_sym Hf)). exact (proj2 (HO a) Ho).
Qed.

(* An intermediate state's AOX set lies in the entry's or the final one's. *)
Lemma AOX_mid : forall Hp W mem md ly ly2 ly3 S S' S'' a,
  ARcf YB1v.tfibsegs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly2 ->
  st_chunks S' = st_chunks S -> st_fs S' = st_fs S ->
  (YG0ncf.xs_cf ly2 S' = YG0ncf.xs_cf ly S \/ YG0ncf.xs_cf ly2 S' = YG0ncf.xs_cf ly3 S'') ->
  AOX_cf B ly2 S' a -> AOX_cf B ly S a \/ AOX_cf B ly3 S'' a.
Proof.
intros Hp W mem md ly ly2 ly3 S S' S'' a HAR HL Hc Hf Hxs Hx.
unfold AOX_cf, YGcfMallocCompose.AOXm_cf in *. destruct Hx as [Ho|Hx].
- left. left. exact (aowned_lay Hp W mem md ly ly2 S S' a HAR HL Hc Hf Ho).
- destruct Hxs as [E|E]; rewrite E in Hx; [left; right; exact Hx | right; right; exact Hx].
Qed.

Lemma AOX_exh_set : forall ly S c a, AOX_cf B ly (exh_set c S) a <-> AOX_cf B ly S a.
Proof. intros ly S c a. reflexivity. Qed.

Lemma xs_exh_set : forall ly S c, YG0ncf.xs_cf ly (exh_set c S) = YG0ncf.xs_cf ly S.
Proof. intros ly S c. reflexivity. Qed.

(* ---- the rooms of the two appends ---- *)
Lemma exh_len2_le : forall c, 1 <= c <= 31 -> 0 <= exh_len2 c <= 100.
Proof.
intros c Hc.
assert (A : forallb (fun c => (0 <=? exh_len2 c) && (exh_len2 c <=? 100)) (map Z.of_nat (seq 1 31)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A c). rewrite andb_true_iff, !Z.leb_le in A. apply A.
apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma room1 : forall S c, ERRB_ROOM S -> errb_room_for (exh_set c S) (Z.of_nat (length render1)).
Proof.
intros S c H. unfold errb_room_for, ERRB_ROOM in *. rewrite rep_exh_size, len_render1. unfold exh_len1. lia.
Qed.

Lemma room2 : forall S S' c, 1 <= c <= 31 -> ERRB_ROOM S ->
  errb_size_cf S' <= errb_size_cf (exh_set c S) + Z.of_nat (length render1) ->
  errb_room_for S' (Z.of_nat (length (render2 c (class_size c)))).
Proof.
intros S S' c Hc H Hs. unfold errb_room_for, ERRB_ROOM in *. rewrite rep_exh_size, len_render1 in Hs.
rewrite (len_render2 c Hc). pose proof (exh_len2_le c Hc). unfold exh_len1 in Hs. lia.
Qed.

(* ---- what the continuations of the two Printf calls are told about the model (the K-trick predicates) ---- *)
Definition post1_P (S1 : astate) (L2 : Z) (S' : astate) : Prop :=
  only_secs S1 S' /\ grows S1 S' /\ (xs_same S1 S' \/ errb_room L2 S').
Definition post2_P (L2 : Z) (S' S'' : astate) : Prop :=
  only_secs S' S'' /\ grows S' S'' /\ (errb_room L2 S' -> xs_same S' S'').

Lemma post1_ipost : forall S1 L1 L2, 0 <= L1 -> 0 <= L2 -> L1 + L2 <= kPage ->
  errb_size_cf S1 <= errb_cap_cf S1 -> errb_cap_cf S1 mod kPage = 0 ->
  YGcfXs.cfx_ipost (YG00cf.errb_append_cf L1 S1) (fun r => post1_P S1 L2 (snd r)).
Proof.
intros S1 L1 L2 H1 H2 H12 Hsc Hal. unfold post1_P.
apply (cfx_ipost_conj _ (fun r => only_secs S1 (snd r)) (fun r => grows S1 (snd r) /\ (xs_same S1 (snd r) \/ errb_room L2 (snd r)))).
- apply append_only_secs.
- apply (cfx_ipost_conj _ (fun r => grows S1 (snd r)) (fun r => xs_same S1 (snd r) \/ errb_room L2 (snd r))).
  + apply append_grows.
  + exact (append_first L1 L2 S1 H1 H2 H12 Hsc Hal).
Qed.

Lemma post2_ipost : forall S' L2, 0 <= L2 ->
  YGcfXs.cfx_ipost (YG00cf.errb_append_cf L2 S') (fun r => post2_P L2 S' (snd r)).
Proof.
intros S' L2 H2. unfold post2_P.
apply (cfx_ipost_conj _ (fun r => only_secs S' (snd r)) (fun r => grows S' (snd r) /\ (errb_room L2 S' -> xs_same S' (snd r)))).
- apply append_only_secs.
- apply (cfx_ipost_conj _ (fun r => grows S' (snd r)) (fun r => errb_room L2 S' -> xs_same S' (snd r))).
  + apply append_grows.
  + destruct (rk_pdec (errb_room L2 S')) as [Hr|Hr].
    * eapply YGcfXs.cfx_ipost_mono; [| exact (append_keeps_xs L2 S' H2 Hr)]. intros r Hx _. exact Hx.
    * eapply YGcfXs.cfx_ipost_mono; [| exact (append_grows L2 S')]. intros r _ Hx. contradiction.
Qed.

(* The errbuf extents the frames need, from the two predicates and the layout steps. *)
Lemma xs_mid : forall ly ly2 ly3 S c S' S'' L2,
  post1_P (exh_set c S) L2 S' -> post2_P L2 S' S'' ->
  layout_le (length (st_secs S)) ly ly2 -> layout_le (length (st_secs S')) ly2 ly3 ->
  YG0ncf.xs_cf ly2 S' = YG0ncf.xs_cf ly S \/ YG0ncf.xs_cf ly2 S' = YG0ncf.xs_cf ly3 S''.
Proof.
intros ly ly2 ly3 S c S' S'' L2 (_ & _ & [X1|R1]) (_ & _ & X2) L12 L23.
- left. rewrite (xs_cf_same ly ly2 (exh_set c S) S' X1 L12). reflexivity.
- right. symmetry. exact (xs_cf_same ly2 ly3 S' S'' (X2 R1) L23).
Qed.


(* ---- machine glue ---- *)
Lemma aregs_regs : forall regs regs', aregs_preserved regs regs' -> YO0d.regs_preserved regs regs'.
Proof. intros regs regs' H r Hr. apply H. unfold acallee_saved. unfold YO0d.callee_saved in Hr. lia. Qed.

Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (vmst_materialized (m_vm md)) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma st_ok_cfg : forall E ss H ms, YP0l.st_ok YB1v.tfibsegs E ss (YK04.restrict H ms) -> YP0l.ss_resv ss = None ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (YP0l.ss_pc ss)) (ms_mem ms) (seg_rom YB1v.tfibsegs).
Proof.
intros E ss H ms HS HR. destruct ms as [r f p sv rv fc m rom].
unfold YP0l.st_ok, YK04.restrict in HS. cbn in HS. destruct HS as (F & P & Sv & Rv & Fc & Ro & _).
rewrite HR in Rv. cbn in Rv. subst. reflexivity.
Qed.

(* The class's exhausted-byte cells kept by a reader that agrees on the other classes' bytes and holds the model's
   value at the class's own byte. *)
Lemma exh_cell_same : forall ly S (rd rd' : reader) c, 1 <= c <= 31 -> cf_exh_off = 68 ->
  exh_cell_cf B ly S rd ->
  (forall c', 1 <= c' <= 31 -> c' <> c ->
     rd' (ly_space ly + kRegionInfoOff + 128 * c' + 68) = rd (ly_space ly + kRegionInfoOff + 128 * c' + 68)) ->
  rd' (ly_space ly + kRegionInfoOff + 128 * c + 68) = Some (if exh_mem_cf S c then 1 else 0) ->
  exh_cell_cf B ly S rd'.
Proof.
intros ly S rd rd' c Hc HO [HE HK] Hoth Hc1. split; [|exact HK].
intros c' Hc'. specialize (HE c' Hc'). unfold cell_holds in HE |- *. cbn [c_at c_w c_val z1 c1] in HE |- *.
assert (EA : aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c')) cf_exh_off) = ly_space ly + kRegionInfoOff + 128 * c' + 68)
  by (cbn [aeval aoff]; rewrite HO; lia).
rewrite EA in HE |- *. intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (HE 0%nat Hk).
cbn [Z.of_nat] in HE |- *. rewrite Z.add_0_r in HE |- *.
destruct (Z.eqb_spec c' c) as [->|Hne].
- rewrite Hc1. destruct (exh_mem_cf S c); reflexivity.
- rewrite (Hoth c' Hc' Hne). exact HE.
Qed.


End rk.
