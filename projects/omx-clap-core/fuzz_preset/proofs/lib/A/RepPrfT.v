(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepPrfT.v (commit eb934de95d13, blob 958717083ea1) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0qcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MnRefillLocpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepIFcf.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

Lemma aregs_of_regs_preserved : forall regs regs', regs_preserved regs regs' -> aregs_preserved regs regs'.
Proof. intros regs regs' H r Hr. exact (H r Hr). Qed.

Lemma regs_of_aregs_preserved : forall regs regs', aregs_preserved regs regs' -> regs_preserved regs regs'.
Proof. intros regs regs' H r Hr. exact (H r Hr). Qed.

Lemma rp_w64u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma rp_aview_at : forall (H : word -> bool) mem mem' a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma rp_aview_low : forall L (H : word -> bool) mem mem' a,
  (forall z, 0 <= z < L -> mem' (Z_to_bv 64 z) = mem (Z_to_bv 64 z)) -> 0 <= a < L ->
  aview tfibsegs H mem' a = aview tfibsegs H mem a.
Proof. intros L H mem mem' a E Ha. apply rp_aview_at. exact (E a Ha). Qed.

Lemma rp_val_mem_low : forall L (H : word -> bool) mem mem' a n v,
  (forall z, 0 <= z < L -> mem' (Z_to_bv 64 z) = mem (Z_to_bv 64 z)) -> 0 <= a -> a + Z.of_nat n <= L ->
  val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H mem') a n v.
Proof.
intros L H mem mem' a n v E H0 H1 V k Hk. specialize (V k Hk). unfold mbyte, mrestrict in *.
rewrite (E (a + Z.of_nat k)) by lia. exact V.
Qed.

Lemma rp_ro_bytes_low : forall L (H : word -> bool) mem mem' a s,
  (forall z, 0 <= z < L -> mem' (Z_to_bv 64 z) = mem (Z_to_bv 64 z)) -> 0 <= a -> a + Z.of_nat (length s) <= L ->
  ro_bytes (mrestrict H mem) a s -> ro_bytes (mrestrict H mem') a s.
Proof.
intros L H mem mem' a s E H0 H1 R i Hi.
apply (rp_val_mem_low L H mem mem' (a + Z.of_nat i) 1 (nth i s 0) E); [lia | lia | exact (R i Hi)].
Qed.

Lemma rp_rep_img_low : forall (W : world tfibsegs) mem mem' L, 0x144e00 <= L ->
  (forall z, 0 <= z < L -> mem' (Z_to_bv 64 z) = mem (Z_to_bv 64 z)) ->
  rep_img_facts W mem -> rep_img_facts W mem'.
Proof.
intros W mem mem' L HL E [R1 R2 R3 [V1 V2 V3 V4 V5]].
assert (HL' : forall c, (c <=? 0x144e00) = true -> c <= L).
{ intros c Hc. apply Z.leb_le in Hc. exact (Z.le_trans _ _ _ Hc HL). }
unfold C_TOOLNAME, C_PFCB, C_SILENT, FMT_OOM1, FMT_OOM2, A_TOOLNAME in *.
constructor; [eapply rp_val_mem_low; [exact E | | | exact R1] | eapply rp_val_mem_low; [exact E | | | exact R2] |
  eapply rp_val_mem_low; [exact E | | | exact R3] | constructor;
  [eapply rp_ro_bytes_low; [exact E | | | exact V1] | eapply rp_ro_bytes_low; [exact E | | | exact V2] |
   eapply rp_ro_bytes_low; [exact E | | | exact V3] | eapply rp_val_mem_low; [exact E | | | exact V4] |
   eapply rp_val_mem_low; [exact E | | | exact V5]]].
all: first [apply HL'; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity].
Qed.

Lemma rp_vis_of_window : forall (H : word -> bool) lo hi mem mem',
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
  (forall a, lo <= a < hi -> apresent H mem' a) ->
  forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None.
Proof.
intros H lo hi mem mem' F P a V.
destruct (Z_le_dec lo (bv_unsigned (Z_to_bv 64 a))) as [L1|L1].
- destruct (Z_lt_dec (bv_unsigned (Z_to_bv 64 a)) hi) as [L2|L2].
  + destruct (P _ (conj L1 L2)) as [Hh [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hh, Hb.
    unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
  + rewrite (rp_aview_at H mem mem' a); [exact V|]. apply F. lia.
- rewrite (rp_aview_at H mem mem' a); [exact V|]. apply F. lia.
Qed.

Lemma rp_vis_of_apresent : forall (H : word -> bool) mem mem',
  (forall a, apresent H mem a -> apresent H mem' a) ->
  forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None.
Proof.
intros H mem mem' P a V. unfold aview, mbyte, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- exact V.
- destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Hm.
  + destruct (P a (conj Hh (ex_intro _ b Hm))) as [_ [b' Hb']]. rewrite Hb'. cbn. discriminate.
  + destruct (mem' (Z_to_bv 64 a)) as [b'|]; [cbn; discriminate | exact V].
Qed.

Lemma rp_held_low : forall lk L (mem mem' : word -> option byte),
  (forall z, 0 <= z < L -> mem' (Z_to_bv 64 z) = mem (Z_to_bv 64 z)) ->
  forall z, 0 <= z < L -> held_mem lk mem' (Z_to_bv 64 z) = held_mem lk mem (Z_to_bv 64 z).
Proof.
intros lk L mem mem' E z Hz. destruct lk as [b|]; cbn [held_mem]; [|exact (E z Hz)].
destruct (in8 b (Z_to_bv 64 z)); [reflexivity | exact (E z Hz)].
Qed.

Lemma rp_vis_held : forall lk (H : word -> bool) (mem mem' : word -> option byte),
  (forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None) ->
  forall a, aview tfibsegs H (held_mem lk mem) a <> None -> aview tfibsegs H (held_mem lk mem') a <> None.
Proof.
intros lk H mem mem' V a. destruct lk as [b|]; cbn [held_mem]; [|exact (V a)].
specialize (V a). unfold aview, mbyte, mrestrict in *. cbv beta in *.
destruct (H (Z_to_bv 64 a)) eqn:Eh; [intros N; exact N|].
destruct (in8 b (Z_to_bv 64 a)); [intros _; cbn; discriminate | exact V].
Qed.

Lemma rp_stk_bounds : forall ly, layout_ok ly ->
  0x10007fff8000 <= ly_stk_lo ly /\ ly_stk_lo ly <= ly_stk_hi ly /\ ly_stk_hi ly <= 0x800000000000 /\
  alloc_ceiling <= ly_stk_lo ly.
Proof.
intros ly LY. pose proof (lo_top ly LY) as (T1 & T2 & _ & T4 & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as C.
unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.

Lemma rp_space_bounds : forall ly, layout_ok ly ->
  0 <= ly_space ly /\ 0 < kRegionInfoOff /\ ly_space ly + kRegionInfoOff + 4096 <= alloc_ceiling.
Proof.
intros ly LY. pose proof (lo_space_in ly LY) as [S1 S2]. pose proof (lo_high ly LY) as [H1 H2].
unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma rp_layout_le_stk : forall n ly ly', layout_le n ly ly' ->
  ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & _). split; [exact L1 | exact L2]. Qed.

Lemma rp_pre_keep : forall lk Hp ly S (W : world tfibsegs) mem md mem' md',
  errb_call_pre B lk Hp ly S W mem md ->
  (forall z, 0 <= z < ly_stk_lo ly -> mem' (Z_to_bv 64 z) = mem (Z_to_bv 64 z)) ->
  (forall a, aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  errb_call_pre B lk Hp ly S W mem' md'.
Proof.
intros lk Hp ly S W mem md mem' md' (OB & EO & LY & IC & TS & TSD & (LK & AR & LV) & XM & WP & QL & EX & EB & RI & HT) LE VIS Hvm Hlz He.
pose proof (rp_stk_bounds ly LY) as (K1 & K2 & K3 & K4).
pose proof (rp_space_bounds ly LY) as (P1 & P2 & P3).
pose proof (rp_held_low lk (ly_stk_lo ly) mem mem' LE) as LEh.
unfold errb_call_pre.
split; [exact OB|]. split; [exact EO|]. split; [exact LY|]. split; [exact IC|]. split; [exact TS|].
split; [exact TSD|].
split.
{ split; [exact LK|]. split.
  2:{ destruct lk as [b|]; [|exact I].
      unfold lk_ok in LK. destruct LK as [LK|(c & Hc & LK)]; [discriminate LK|].
      injection LK as Eb. subst b. unfold region_lock_addr in *.
      apply (rp_val_mem_low (ly_stk_lo ly) (w_H W) mem mem'); [exact LE | | | exact LV];
        unfold kRegionInfoOff in *; lia. }
  apply (YG0qcf.AR_frame_law_ok_cf tfibsegs B ly S Hp W (held_mem lk mem) md (held_mem lk mem') md' AR).
  - intros a Ha Ho. pose proof (YG0scf.AR_owned_low_law_ok_cf tfibsegs B ly S Hp W (held_mem lk mem) md a AR Ho) as Hl.
    apply (rp_aview_low (ly_stk_lo ly)); [exact LEh | lia].
  - exact (rp_vis_held lk (w_H W) mem mem' VIS).
  - exact Hvm.
  - exact Hlz.
  - exact He.
  - intros a Hb _. apply LEh.
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb. lia. }
split.
{ unfold xs_mapped_cf in *. intros e Hin. rewrite Hvm. exact (XM e Hin). }
split; [exact WP|].
split; [exact QL|].
split.
{ apply (YGcfInstBase.exh_cell_cf_frame B ly ly S S (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') EX).
  - intros c. reflexivity.
  - intros c Hc. apply (rp_aview_low (ly_stk_lo ly)); [exact LE|]. cbn [aeval aoff]. rewrite EO. lia. }
split.
{ apply (YGcfInstBase.errb_cells_cf_frame B ly ly S S (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') EB);
    try reflexivity.
  - intros a Ha. apply (rp_aview_low (ly_stk_lo ly)); [exact LE|]. rewrite OB in Ha. unfold C_ERRBUF in Ha. lia.
  - exact VIS. }
split; [apply (rp_rep_img_low W mem mem' (ly_stk_lo ly)); [lia | exact LE | exact RI] | exact HT].
Qed.

Lemma pre_stack_keep : forall lk Hp ly S (W : world tfibsegs) mem md mem' md' lo hi,
  errb_call_pre B lk Hp ly S W mem md ->
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem' a) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  errb_call_pre B lk Hp ly S W mem' md'.
Proof.
intros lk Hp ly S W mem md mem' md' lo hi PRE L1 L2 F P Hvm Hlz He.
assert (LY : layout_ok ly) by (destruct PRE as (_ & _ & LY & _); exact LY).
pose proof (rp_stk_bounds ly LY) as (K1 & K2 & K3 & K4).
apply (rp_pre_keep lk Hp ly S W mem md mem' md' PRE);
  [| exact (rp_vis_of_window _ lo hi mem mem' F P) | exact Hvm | exact Hlz | exact He].
intros z Hz. apply F. rewrite rp_w64u by lia. lia.
Qed.

Corollary pre_stack_keep_wvb : forall lk Hp ly S (W : world tfibsegs) mem md mem' (mat : list word) lo hi,
  errb_call_pre B lk Hp ly S W mem md ->
  ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem' a) ->
  errb_call_pre B lk Hp ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros lk Hp ly S W mem md mem' mat lo hi PRE L1 L2 F P.
apply (pre_stack_keep lk Hp ly S W mem md mem' (with_vm_backing (m_vm_lazy md) mat md) lo hi PRE L1 L2 F P).
- exact (m_vmmaps_wvb (m_vm_lazy md) mat md).
- exact (m_vm_lazy_wvb (m_vm_lazy md) mat md).
- exact (eager_used_wvb mat md).
Qed.

Lemma rp_stack_not_AOX : forall lk Hp ly S (W : world tfibsegs) mem md a,
  errb_call_pre B lk Hp ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX_cf B ly S a.
Proof.
intros lk Hp ly S W mem md a PRE Ha.
destruct PRE as (_ & _ & _ & _ & _ & _ & (_ & AR & _) & _).
intros [O|X].
- exact (YG0scf.AR_stack_law_ok_cf tfibsegs B ly S Hp W (held_mem lk mem) md a AR Ha O).
- pose proof (YG0ncf.xs_placed_of_ARcf tfibsegs B ly S Hp W (held_mem lk mem) md AR) as XP.
  unfold xs_placed_cf in XP. rewrite Forall_forall in XP.
  apply Exists_exists in X. destruct X as (e & He & Hin).
  destruct (XP e He) as (_ & _ & _ & D). rewrite Forall_forall in D.
  assert (Z1 : zdisjoint e (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
  { apply D. apply in_or_app. right. apply in_or_app. left. unfold static_extents. apply in_or_app. right. left.
    reflexivity. }
  unfold zdisjoint in Z1. unfold in_zr in Hin. cbn [fst snd] in Z1, Hin. lia.
Qed.

Lemma post_compose : forall lk len Hp ly S S' (W W' : world tfibsegs) regs mem md mem1 md1 regs1 regs2 mem2 md2 mem3 md3 regs3,
  errb_call_pre B lk Hp ly S W mem md -> errb_call_regs B PR_STK ly W regs mem ->
  (forall x : word, ~ (spZ regs - PR_STK <= bv_unsigned x < spZ regs) -> mem1 x = mem x) ->
  (forall a, spZ regs - PR_STK <= a < spZ regs -> apresent (w_H W) mem1 a) ->
  same_io md md1 ->
  spZ regs - PR_STK <= spZ regs1 - APP_STK -> spZ regs1 <= spZ regs ->
  errb_call_post B lk APP_STK len Hp ly S S' W regs1 mem1 md1 W' (cfg_at tfibsegs (raZ regs1) regs2 mem2 md2) ->
  (forall x : word, ~ (spZ regs - PR_STK <= bv_unsigned x < spZ regs) -> mem3 x = mem2 x) ->
  (forall a, apresent (w_H W') mem2 a -> apresent (w_H W') mem3 a) ->
  m_vmmaps md3 = m_vmmaps md2 -> m_vm_lazy md3 = m_vm_lazy md2 -> eager_used md3 = eager_used md2 -> same_io md2 md3 ->
  aregs_preserved regs regs3 ->
  errb_call_post B lk PR_STK len Hp ly S S' W regs mem md W' (cfg_at tfibsegs (raZ regs) regs3 mem3 md3).
Proof.
intros lk len Hp ly S S' W W' regs mem md mem1 md1 regs1 regs2 mem2 md2 mem3 md3 regs3
  PRE RG F1 P1 IO1 WL WH POST F3 P3 Hvm Hlz He IO3 AR3.
destruct POST as (ly' & r2 & m2 & d2 & Ec & PRE2 & SZ & LL & WLE & AR2 & IO2 & AV2 & MF2 & MN2 & P2).
assert (Em : mem2 = m2) by exact (f_equal (fun c => ms_mem (cfg_ms c)) Ec).
assert (Ed : md2 = d2) by exact (f_equal cfg_model Ec).
subst m2 d2.
assert (LY : layout_ok ly) by (destruct PRE as (_ & _ & LY & _); exact LY).
destruct RG as (_ & _ & _ & _ & _ & RLo & RHi & _).
pose proof (rp_stk_bounds ly LY) as (K1 & K2 & K3 & K4).
destruct (rp_layout_le_stk _ _ _ LL) as [Llo Lhi].
unfold errb_call_post.
exists ly', regs3, mem3, md3.
split; [reflexivity|].
split.
{ apply (rp_pre_keep lk Hp ly' S' W' mem2 md2 mem3 md3 PRE2);
    [| exact (rp_vis_of_apresent _ _ _ P3) | exact Hvm | exact Hlz | exact He].
  intros z Hz. apply F3. rewrite rp_w64u by lia. lia. }
split; [exact SZ|].
split; [exact LL|].
split; [exact WLE|].
split; [exact AR3|].
split.
{ unfold same_io in *. destruct IO1 as (A1 & A2 & A3 & A4). destruct IO2 as (B1 & B2 & B3 & B4).
  destruct IO3 as (C1 & C2 & C3 & C4).
  split; [congruence|]. split; [congruence|]. split; congruence. }
split.
{ intros a Ha N1 N2 Nw.
  rewrite (rp_aview_at (w_H W') mem2 mem3 a) by (apply F3; rewrite rp_w64u by lia; exact Nw).
  rewrite (AV2 a Ha N1 N2) by lia.
  apply rp_aview_at. apply F1. rewrite rp_w64u by lia. exact Nw. }
split.
{ intros x N1 N2 Nw.
  rewrite (F3 x Nw). rewrite (MF2 x N1 N2) by lia. exact (F1 x Nw). }
split.
{ assert (K1m : MemnormT.memnorm_keep tfibsegs mem mem1).
  { apply (MemnormT.memnorm_frame tfibsegs (fun a => spZ regs - PR_STK <= a < spZ regs)); [|exact F1].
    intros x Hx. cbv beta in Hx. apply (MnRefillLocpreset.mn_safe_stack ly x LY). lia. }
  assert (K3m : MemnormT.memnorm_keep tfibsegs mem2 mem3).
  { apply (MemnormT.memnorm_frame tfibsegs (fun a => spZ regs - PR_STK <= a < spZ regs)); [|exact F3].
    intros x Hx. cbv beta in Hx. apply (MnRefillLocpreset.mn_safe_stack ly x LY). lia. }
  intros MN. exact (K3m (MN2 (K1m MN))). }
intros a Ha.
assert (OUT : ~ (spZ regs1 - APP_STK <= a < spZ regs1) -> apresent (w_H W') mem2 a).
{ intros NA. destruct (P1 a Ha) as [Hh [b Hb]]. split.
  - destruct (w_H W' (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. unfold wle, hsub in WLE.
    rewrite (WLE _ Eh) in Hh. discriminate.
  - exists b. rewrite <- Hb. apply MF2; rewrite rp_w64u by lia.
    + apply (rp_stack_not_AOX lk Hp ly S W mem md); [exact PRE | lia].
    + apply (rp_stack_not_AOX lk Hp ly' S' W' mem2 md2); [exact PRE2 | lia].
    + exact NA. }
destruct (Z_le_dec (spZ regs1 - APP_STK) a) as [A1|A1].
- destruct (Z_lt_dec a (spZ regs1)) as [A2|A2].
  + apply P3. apply P2. lia.
  + apply P3. apply OUT. lia.
- apply P3. apply OUT. lia.
Qed.

End a.
