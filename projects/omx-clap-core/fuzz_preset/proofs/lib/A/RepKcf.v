(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepKcf.v (commit eb934de95d13, blob 35eea3a7223a) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepModelcf RepModel2cf RepIFcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v AFeu.
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
     amreal AB1v.tfibsegs (K S') W' c' Q) ->
  amreal AB1v.tfibsegs (ibind (YG00cf.errb_append_cf (Z.of_nat (length out)) S) (fun r => K (snd r)))
    W (cfg_at AB1v.tfibsegs RepIFcf.A_PRINTF regs mem md) Q.
Proof.
intros P R Hp ly S W regs mem md fmt out lk K Q HPR HIP HPRE HROOM HREGS HA0 HFMT HLEN HK.
set (K' := fun S' => if rk_pdec (P S') then K S' else @IFail astate R FFuel).
apply (RepModel2cf.amreal_ibind_ipost AB1v.tfibsegs _ (fun r => P (snd r)) (fun r => K (snd r)) (fun r => K' (snd r)) W _ Q HIP).
- intros r Hr. unfold K'. destruct (rk_pdec (P (snd r))) as [_|N]; [reflexivity | contradiction].
- apply (HPR R Hp ly S W regs mem md fmt out lk K' Q HPRE HROOM HREGS HA0 HFMT HLEN).
  intros S' W' c' HPOST. unfold K'. destruct (rk_pdec (P S')) as [HP|_]; [exact (HK S' W' c' HP HPOST) | exact I].
Qed.

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
  val_mem AB1v.tfibsegs (mrestrict H m) a nb v -> val_mem AB1v.tfibsegs (mrestrict H m') a nb v.
Proof.
intros H m m' a nb v A0 A1 E Hv. apply (val_mem_ext (mrestrict H m)); [|exact Hv].
intros k Hk. unfold mbyte, mrestrict. rewrite (E (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
rewrite unsigned_lit_small by lia. lia.
Qed.

Lemma rep_img_frame : forall (W : world AB1v.tfibsegs) (m m' : word -> option byte), rep_img_facts W m ->
  (forall x : word, AF0x.TFIB_IMG_LO <= bv_unsigned x < AF0x.TFIB_IMG_END -> m' x = m x) -> rep_img_facts W m'.
Proof.
intros W m m' [T1 T2 T3 [V1 V2 V3 V4 V5]] E.
assert (F : forall a nb v, AF0x.TFIB_IMG_LO <= a -> a + Z.of_nat nb <= AF0x.TFIB_IMG_END ->
  val_mem AB1v.tfibsegs (mrestrict (w_H W) m) a nb v -> val_mem AB1v.tfibsegs (mrestrict (w_H W) m') a nb v).
{ intros a nb v A1 A2 Hv. apply (rk_val_frame _ m); [unfold AF0x.TFIB_IMG_LO in A1; lia | unfold AF0x.TFIB_IMG_END in A2; lia | | exact Hv].
  intros x Hx. apply E. lia. }
assert (FR : forall a s, AF0x.TFIB_IMG_LO <= a -> a + Z.of_nat (length s) <= AF0x.TFIB_IMG_END ->
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

Lemma aowned_lay : forall Hp W mem md ly ly' S S' a,
  ARcf AB1v.tfibsegs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  st_chunks S' = st_chunks S -> st_fs S' = st_fs S ->
  aowned B ly' S' a -> aowned B ly S a.
Proof.
intros Hp W mem md ly ly' S S' a HAR HL Hc Hf Ho.
pose proof (YG0scf.AR_layout_law_ok_cf AB1v.tfibsegs B ly S Hp W mem md ly' HAR HL) as (_ & _ & HO).
apply (proj1 (HO a)). exact (AFeu.aowned_same_cf B ly' S S' a Hc Hf Ho).
Qed.

Lemma aowned_lay_inv : forall Hp W mem md ly ly' S S' a,
  ARcf AB1v.tfibsegs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
  st_chunks S' = st_chunks S -> st_fs S' = st_fs S ->
  aowned B ly S a -> aowned B ly' S' a.
Proof.
intros Hp W mem md ly ly' S S' a HAR HL Hc Hf Ho.
pose proof (YG0scf.AR_layout_law_ok_cf AB1v.tfibsegs B ly S Hp W mem md ly' HAR HL) as (_ & _ & HO).
apply (AFeu.aowned_same_cf B ly' S' S a (eq_sym Hc) (eq_sym Hf)). exact (proj2 (HO a) Ho).
Qed.

Lemma AOX_mid : forall Hp W mem md ly ly2 ly3 S S' S'' a,
  ARcf AB1v.tfibsegs B ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly2 ->
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

Lemma xs_mid : forall ly ly2 ly3 S c S' S'' L2,
  post1_P (exh_set c S) L2 S' -> post2_P L2 S' S'' ->
  layout_le (length (st_secs S)) ly ly2 -> layout_le (length (st_secs S')) ly2 ly3 ->
  YG0ncf.xs_cf ly2 S' = YG0ncf.xs_cf ly S \/ YG0ncf.xs_cf ly2 S' = YG0ncf.xs_cf ly3 S''.
Proof.
intros ly ly2 ly3 S c S' S'' L2 (_ & _ & [X1|R1]) (_ & _ & X2) L12 L23.
- left. rewrite (xs_cf_same ly ly2 (exh_set c S) S' X1 L12). reflexivity.
- right. symmetry. exact (xs_cf_same ly2 ly3 S' S'' (X2 R1) L23).
Qed.

Lemma aregs_regs : forall regs regs', aregs_preserved regs regs' -> YO0d.regs_preserved regs regs'.
Proof. intros regs regs' H r Hr. apply H. unfold acallee_saved. unfold YO0d.callee_saved in Hr. lia. Qed.

Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (vmst_materialized (m_vm md)) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma st_ok_cfg : forall E ss H ms, YP0l.st_ok AB1v.tfibsegs E ss (YK04.restrict H ms) -> YP0l.ss_resv ss = None ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (YP0l.ss_pc ss)) (ms_mem ms) (seg_rom AB1v.tfibsegs).
Proof.
intros E ss H ms HS HR. destruct ms as [r f p sv rv fc m rom].
unfold YP0l.st_ok, YK04.restrict in HS. cbn in HS. destruct HS as (F & P & Sv & Rv & Fc & Ro & _).
rewrite HR in Rv. cbn in Rv. subst. reflexivity.
Qed.

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
