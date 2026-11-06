(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngGM AXG_ntfm AXG_ntfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS AXF_eez AXG_nQ AXG_ntfP AXG_ntf MngMk_c1 MngGeo MngRel MngNCh MngFree MngFreeMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_p4z AXF_tfz AXF_t0a AXG_ffstep AXG_ffpost.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngPost.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require MngFreeProA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_nQ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ntfP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ntf OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMk_c1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngRel OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNCh OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeMem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreePro OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_tfz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_t0a OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ffpost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreeGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngPost OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.MngFreeM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngFreeProA.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_ff3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefMemcpyLib.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section T0M.
Variables (m : word -> option byte) (p : Z).
Hypothesis Hp : 3 <= p <= 2^63.

#[using="Hp"] Lemma t0_mem_out : forall x, 0 <= x < 2^64 -> ~ (p - 3 <= x < p) -> t0_mem m p (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hp : LiaFast.U) => LiaFast.u0). intros x Hx H. unfold t0_mem. do 2 peel. reflexivity. Qed.

#[using="Hp"] Lemma t0_mem_p3 : t0_mem m p (wa (p - 3)) = Some (Z_to_bv 8 255).
Proof. LiaFast.lf_pins (fun (Hp : LiaFast.U) => LiaFast.u0). unfold t0_mem. peel. replace (p - 3) with (p + -3) by ring. rewrite wbytes_at_wa0 by (cbn; lia). f_equal. apply bv_eq. reflexivity. Qed.

#[using="Hp"] Lemma t0_mem_p2 : forall k, (k < 2)%nat -> t0_mem m p (wa (p - 2 + Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (Hp : LiaFast.U) => LiaFast.u0). intros k Hk. unfold t0_mem. replace (p - 2) with (p + -2) by ring. rewrite wbytes_at_wa by (cbn; lia). destruct k as [|[|k]]; [reflexivity | reflexivity | lia]. Qed.

#[using="Type"] Lemma t0_mem_grows : mem_grows m (t0_mem m p).
Proof. LiaFast.lf_pins LiaFast.u0. unfold t0_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
End T0M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NC_next_env : forall L X EXC X' EXC' s s' m m' sp0 K,
  NC L X EXC s m sp0 K -> repr_x L s' (bview SEGS m') EXC' -> EXC_z X' s' EXC' -> (forall x, In x X' -> exists a, MT s' x = Some (MUsed a)) ->
  RS L s' s -> KS s' -> mem_grows m m' -> nenv m' -> keys s' = keys s -> NC L X' EXC' s' m' sp0 K.
Proof.
  intros L X EXC X' EXC' s s' m m' sp0 K N HR' HEX' HZU' HRS HK' Hg Henv' Hkeys. destruct N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  constructor; try assumption.
  - exact (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg).
  - exact (cplace_RS L (sp0 - K) s' s HRS HC).
  - rewrite Hkeys. exact HMP.
  - rewrite Hkeys. exact HMD.
Qed.

Lemma NC_shift : forall L X EXC s m sp0 K d, NC L X EXC s m sp0 K -> 0 <= d -> d mod 16 = 0 -> 1024 <= K - d -> NC L X EXC s m (sp0 - d) (K - d).
Proof.
  intros L X EXC s m sp0 K d N Hd Hd16 HKd. destruct N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  replace (sp0 - d - (K - d)) with (sp0 - K) by ring.
  constructor; try assumption.
  - apply stk_ok_shift; [exact HSTK | exact Hd | lia | lia].
  - replace (sp0 - d - (K - d)) with (sp0 - K) by ring. exact Hsp1.
  - lia.
  - rewrite Zminus_mod, Hsp3, Hd16. reflexivity.
  - intros c Hc. replace (sp0 - d - (K - d)) with (sp0 - K) by ring. exact (HC c Hc).
  - intros q Hq. replace (sp0 - d - (K - d)) with (sp0 - K) by ring. exact (HMP q Hq).
Qed.

(* [comment removed for export] *)
Lemma rel_HR2g : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) ->
  ((am_prev (rel_meta am i fr), am_next (rel_meta am i fr)) <> (None, None) ->
   active_hd (s_rel s g am i fr) (am_sc (rel_meta am i fr)) <> Some g -> am_freed (rel_meta am i fr) <> 0).
Proof.
  intros s g am i fr HW HF. destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  assert (Ux : usedX [] s g am) by exact (proj1 (used_metas_usedX s g am HW) Hu).
  pose proof (inv_groups HW g am Ux) as (_ & _ & _ & Gcl & _).
  change (am_prev (rel_meta am i fr), am_next (rel_meta am i fr)) with (am_prev am, am_next am).
  change (am_freed (rel_meta am i fr)) with (am_freed am). change (am_sc (rel_meta am i fr)) with (am_sc am).
  change (active_hd (s_rel s g am i fr) (am_sc am)) with (active_hd s (am_sc am)).
  intros HL Hnh. destruct Gcl as [(H63 & _) | (Hsc & _)].
  - exfalso. destruct (inv_rings HW) as (_ & _ & D). destruct (D g am Ux H63) as [P N]. apply HL. rewrite P, N. reflexivity.
  - destruct (ring_facts [] None U0 s g am HW Ux ltac:(lia) ltac:(lia)) as (_ & _ & RF3). apply RF3; [exact HL | exact Hnh | intros; discriminate].
Qed.

Lemma fneed_48 : forall sc, 0 <= sc -> Z.of_nat (fneed sc) <= 48.
Proof. intros sc Hsc. unfold fneed. destruct (sc <? 48) eqn:E; [apply Z.ltb_lt in E; rewrite Z2Nat.id by lia; lia | lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RUN.
Context {fx : FPState}.

#[using="Type"] Theorem free_ntf_run : forall L s (regs : bvmap 5 word) m rom g am i fr,
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  ly_ctx L = 0x97c98 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  rdn SEGS m (wa 416600) 8 = Some (word_to_le_bytes 8 (wa 0x97c00)) ->
  (exists can, 0 <= can <= 2^64 - 1 /\ rdn SEGS m (wa 621568) 8 = Some (word_to_le_bytes 8 (wa can))) ->
  2^20 + 8192 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 8192 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 8192) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  let sp := bv_unsigned (getr regs 2) in
  let pa := loc_addr L (LMem (frame_ptr am i fr)) in
  let m1 := t0_mem (p4_mem m regs) pa in
  exists R m2 mi s',
    msteps SEGS (mkst regs (wa 0x52f88) m rom) (mkst R (wa 0x53a58) m2 rom) /\
    getr R 1 = wa 0x53520 /\ getr R 2 = wa (sp - 48) /\ getr R 10 = wa (mi_base L mi) /\ getr R 11 = wa (mi_len mi) /\
    (forall n, In n [3;4;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))) /\
    rdn SEGS m2 (wa (sp + -8)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs 1)))) /\
    rdn SEGS m2 (wa (sp + -16)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs 8)))) /\
    rdn SEGS m2 (wa (sp + -24)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs 9)))) /\
    rdn SEGS m2 (wa (sp + -32)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs 18)))) /\
    rdn SEGS m2 (wa (sp + -40)) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (getr regs 19)))) /\
    0 <= mi_base L mi <= 2^64-1 /\ 0 <= mi_len mi <= 2^64-1 /\
    nontrivial_free NEST_FUEL g i (s_rel s g am i fr) = IRet (mi, s') /\
    NC L [] [] s' m2 sp 8192 /\ MKS s' (s_rel s g am i fr) /\ st_regions s' = st_regions s /\ st_areas s' = st_areas s /\
    mem_grows m m1 /\ mem_grows m1 m2 /\
    (forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> (sp - 48 <= x < sp) \/ (pa - 3 <= x < pa)) /\
    FRM L (s_rel s g am i fr) (sp - 48) (8192 - 48) m1 m2 /\
    NC L [] [] (s_rel s g am i fr) m1 sp 8192.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr (HW & HR & HM) HF Hk Hctx HP Hnl Htab Hgot Hcan Rsp Asp HSTK8 HFP8 HAP Hnt sp pa m1.
  assert (Rsp' : 2^20 <= bv_unsigned (getr regs 2) <= 2^47) by (clear - Rsp; lia).
  assert (HSTK : stk_ok SEGS m (getr regs 2) 1024) by exact (stk_ok_mono' m (getr regs 2) 8192 1024 HSTK8 ltac:(lia)).
  assert (HFP : forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) by (intros rg Hrg; pose proof (HFP8 rg Hrg); lia).
  destruct (free_prologue_any L s regs m rom g am i fr (conj HW (conj HR HM)) HF Hk Hctx HP Hnl Htab Rsp' Asp HSTK HFP HAP) as (R1 & Hms1 & PRO & TP & FC).
  pose proof FC as [Rav Rfr RG RW D5 Mav Mfr MW Wmeta A2 A3].
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hland & _ & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  destruct (frame_shape s g am i fr HW HF) as (Rl0 & Rs0 & Rm0 & _ & _ & _).
  assert (Rsc : 0 <= am_last am <= 31 /\ 0 <= am_sc am <= 63) by (split; assumption).
  destruct (meta_bits_fields am Rl0 Rs0 Rm0) as (EW & _ & _).
  set (G := loc_addr L (LMem g)) in *.
  pose proof HR as (HL & HC & HFM).
  destruct (free_cells_geom L s g am i fr (bv_unsigned (getr regs 2)) HW HL HF HFP) as (Gp & GG1 & GG2 & HpG).
  (* [comment removed for export] *)
  destruct (t0_arm R1 (p4_mem m regs) rom G (meta_bits am) i pa (am_avail am) (am_freed am) _ _ _ _ _ _ TP Rav Rfr)
    as (R2 & Hms2 & R2_1 & R2_2 & R2_8 & R2_9 & R2_10 & R2_11 & R2k).
  { rewrite p4_rdn_other by (first [exact Rsp' | clear - D5 RG; lia]). exact Mav. }
  { rewrite p4_rdn_other by (first [exact Rsp' | clear - D5 RG; lia]). exact Mfr. }
  { rewrite p4_rdn_other by (first [exact Rsp' | clear - D5 RG; lia]). exact MW. }
  { rewrite p4_rdn_other by (first [exact Rsp' | clear - Rsp'; lia]). exact Hnl. }
  { intros d k Hd Hk2. apply (store_ok_mono SEGS k m); [apply p4_mem_grows|].
    replace (G + 28 + d) with (G + 24 + (4 + d)) by ring. apply Wmeta; clear - Hd Hk2; lia. }
  { exact A2. }
  { exact A3. }
  { destruct Hnt as [E|E]; [left; exact E|]. destruct (Z.eq_dec (am_freed am) 0) as [E0|E0]; [left; exact E0|].
    right. split; [exact E0|]. rewrite EW, Z.lor_comm. unfold bit, ones in E. exact E. }
  (* [comment removed for export] *)
  assert (ESP : getr regs 2 = wa sp) by (unfold sp; rewrite wa_u; reflexivity).
  assert (M1OUT : forall x, 0 <= x < 2^64 -> ~ (sp - 40 <= x < sp) -> ~ (pa - 3 <= x < pa) -> m1 (wa x) = m (wa x)).
  { intros x Hx H1 H2. unfold m1. rewrite t0_mem_out by (first [exact Hx | exact H2 | clear - Gp Rsp'; lia]). apply p4_mem_out; [exact Rsp' | exact Hx | exact H1]. }
  assert (G1 : mem_grows m m1) by (unfold m1; eapply mem_grows_trans; [apply p4_mem_grows | apply t0_mem_grows]).
  assert (CH1 : forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> (sp - 48 <= x < sp) \/ (pa - 3 <= x < pa)).
  { intros x Hx Hne. destruct (decide (sp - 48 <= x < sp)) as [A|A]; [left; exact A|]. destruct (decide (pa - 3 <= x < pa)) as [B|B]; [right; exact B|].
    exfalso. apply Hne. apply M1OUT; [exact Hx | clear - A; lia | exact B]. }
  pose proof (tp_IH _ _ _ _ _ _ _ _ _ _ _ _ TP) as IHp.
  assert (ENV1 : nenv m1).
  { destruct Hcan as (can & Rcan & Mcan). split; [|split].
    - rewrite (rdn_frame_n m m1 416600 8) by (try lia; intros x Hx; apply M1OUT; cbn in Hx; clear - Hx Rsp' IHp; lia). exact Hgot.
    - intros sc Hsc. rewrite (rdn_frame_n m m1 (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply M1OUT; cbn in Hx; clear - Hx Hsc Rsp' IHp; lia). exact (Htab sc Hsc).
    - exists can. split; [exact Rcan|]. rewrite (rdn_frame_n m m1 621568 8) by (try lia; intros x Hx; apply M1OUT; cbn in Hx; clear - Hx Rsp' IHp; lia). exact Mcan. }
  (* [comment removed for export] *)
  assert (N0 : NC L [] [] s m sp 8192).
  { apply (NC_of_heap L s m sp 8192 HW HR Hctx).
    - destruct Hcan as (can & Rcan & Mcan). split; [exact Hgot|]. split; [exact Htab|]. exists can. split; [exact Rcan | exact Mcan].
    - rewrite <- ESP. exact HSTK8.
    - lia. - clear - Rsp; unfold sp; lia. - clear - Rsp; unfold sp; lia. - exact Asp.
    - exact HFP8.
    - exact HAP. }
  set (sR := s_rel s g am i fr).
  assert (RX1 : repr_x L sR (bview SEGS m1) []).
  { apply (rel_repr_x SEGS L s m m1 g am i fr (sp - 8192) HW HR HF HFP8 (fun x E => bview_grow_n m m1 x G1 E)).
    - fold pa. intros x Hx Hn. destruct (Z_lt_le_dec x 0) as [Hneg|Hneg].
      { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hneg). reflexivity. }
      apply MngWb.bview_ext. apply M1OUT; [clear - Hx Hneg Rsp'; lia | clear - Hx; lia | exact Hn].
    - fold pa. rewrite (bview_some_byte SEGS m1 (pa - 3) (Z_to_bv 8 255) ltac:(clear - Gp Rsp'; lia)); [reflexivity|]. unfold m1. apply t0_mem_p3. clear - Gp Rsp'; lia.
    - fold pa. intros k Hk2. rewrite (bview_some_byte SEGS m1 (pa - 2 + Z.of_nat k) (Z_to_bv 8 0) ltac:(clear - Gp Rsp' Hk2; lia)); [reflexivity|].
      unfold m1. apply t0_mem_p2; [clear - Gp Rsp'; lia | exact Hk2]. }
  assert (HKR : KS sR) by (apply KS_set_meta; [exact (KS_of_WF s HW) | eapply MT_keys; exact (proj1 (used_metas_iff s g am (proj1 (inv_keys HW))) Hu)]).
  assert (KR : keys sR = keys s) by (apply keys_set_meta; eapply MT_keys; exact (proj1 (used_metas_iff s g am (proj1 (inv_keys HW))) Hu)).
  assert (NR : NC L [] [] sR m1 sp 8192).
  { apply (NC_next_env L [] [] [] [] s sR m m1 sp 8192 N0 RX1 ltac:(intros l []) ltac:(intros x []) ltac:(exists (rel_extra L am i fr); exact (rel_RS L s g am i fr HW HF))
             HKR G1 ENV1 KR). }
  pose proof (NC_shift L [] [] sR m1 sp 8192 48 NR ltac:(lia) eq_refl ltac:(lia)) as NR48.
  destruct (rel_Inv s g am i fr HW HF Hk) as (HIR & UR).
  assert (HU0 : forall c, 0 <= U0 c <= 2^40) by (intros c; unfold U0; lia).
  pose proof (fneed_48 (am_sc (rel_meta am i fr)) ltac:(change (am_sc (rel_meta am i fr)) with (am_sc am); lia)) as F48.
  destruct (ntf_contract NEST_FUEL L [] [] U0 sR m1 R2 rom (sp - 48) (8192 - 48) g i (rel_meta am i fr) NR48 R2_2 R2_10 R2_11 HIR UR HU0
              (rel_HR2g s g am i fr HW HF) (fneed_le (am_sc am) ltac:(clear - Rsc; lia)) ltac:(clear - F48; lia))
    as (R3 & m2 & mi & s' & Hms3 & Hex3 & Rb3 & Rl3 & Ht3 & N3 & HRS3 & HZ3 & Hg3 & FR3 & MK3 & RG3 & AR3).
  pose proof Hex3 as (E3_1 & E3_2 & _ & _ & _ & _ & E3_10 & E3_11 & E3k).
  (* [comment removed for export] *)
  assert (TOP : forall x, sp - 48 <= x < sp -> m2 (wa x) = m1 (wa x)).
  { intros x Hx. destruct (decide (m2 (wa x) = m1 (wa x))) as [E|E]; [exact E|]. exfalso.
    pose proof (nc_cells _ _ _ _ _ _ _ NR48) as HC48.
    destruct (FR3 x ltac:(clear - Hx Rsp'; unfold sp in *; lia) E) as [A|(c & Hc & _ & Hin)]; [clear - A Hx; lia|].
    pose proof (HC48 c Hc) as (P1 & P2 & _). unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. clear - Hin P2 Hx; lia. }
  assert (SAVE : forall a v, sp - 40 <= a -> a + 8 <= sp -> rdn SEGS (p4_mem m regs) (wa a) 8 = Some (word_to_le_bytes 8 (wa v)) ->
                   rdn SEGS m2 (wa a) 8 = Some (word_to_le_bytes 8 (wa v))).
  { intros a v B1 B2 Hv. rewrite (rdn_frame_n m1 m2 a 8) by (first [ (clear - B1 B2 Rsp'; unfold sp in *; cbn; lia) | (intros x Hx; apply TOP; cbn in Hx; clear - Hx B1 B2; lia) ]).
    unfold m1. rewrite (rdn_frame_n (p4_mem m regs) (t0_mem (p4_mem m regs) pa) a 8) by (first [ (clear - B1 B2 Rsp'; unfold sp in *; cbn; lia) |
      (intros x Hx; apply t0_mem_out; [clear - Gp Rsp'; lia | clear - Hx B1 B2 Rsp'; unfold sp in *; cbn in Hx; lia | clear - Hx B1 Gp; cbn in Hx; lia]) ]).
    exact Hv. }
  pose proof TP as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Mra Ms0 Ms1 Ms2 Ms3 _ _ _ _ _ _].
  exists R3, m2, mi, s'.
  split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
  split; [rewrite E3_1, R2_1, wa_u; reflexivity|].
  split; [exact E3_2|]. split; [exact E3_10|]. split; [exact E3_11|].
  split.
  { destruct PRO as (_ & _ & _ & _ & _ & Poth). intros n Hn. rewrite (E3k n Hn). rewrite R2k by (clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]).
    apply Poth. clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]. }
  split; [apply SAVE; [clear; lia | clear; lia | exact Mra]|].
  split; [apply SAVE; [clear; lia | clear; lia | exact Ms0]|].
  split; [apply SAVE; [clear; lia | clear; lia | exact Ms1]|].
  split; [apply SAVE; [clear; lia | clear; lia | exact Ms2]|].
  split; [apply SAVE; [clear; lia | clear; lia | exact Ms3]|].
  split; [exact Rb3|]. split; [exact Rl3|]. split; [exact Ht3|].
  split.
  { apply (NC_unshift L [] [] s' m2 sp 8192 48 N3); [| clear - Rsp; unfold sp in *; lia | exact Asp | lia].
    exact (stk_ok_grows SEGS m m2 (wa sp) 8192 ltac:(rewrite <- ESP; exact HSTK8) (mem_grows_trans _ _ _ G1 Hg3)). }
  split; [exact MK3|]. split; [exact RG3|]. split; [exact AR3|].
  split; [exact G1|]. split; [exact Hg3|]. split; [exact CH1|]. split; [exact FR3 | exact NR].
Qed.
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma markers_width' : forall s c, In c (markers s) -> (1 <= mc_w c)%nat.
Proof.
  intros s c Hc. destruct (In_markers_inv s c Hc) as [(g & am & i & fr & _ & _ & Hc') | (g & am & _ & ->)]; [|cbn; lia].
  unfold marker_cells in Hc'. destruct Hc' as [<-|Hc']; [cbn; lia|]. apply in_app_iff in Hc' as [Hc'|Hc'].
  - destruct (0 <? _); [destruct Hc' as [<-|[]]; cbn; lia | destruct Hc'].
  - destruct (5 <=? _); [destruct Hc' as [<-|[<-|[]]]; cbn; lia | destruct Hc'].
Qed.

Lemma markers_fast_rel : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) -> markers (s_rel s g am i fr) = markers (s_fast s g am i fr).
Proof.
  intros s g am i fr HW HF. unfold s_rel, s_fast.
  rewrite <- (set_meta_twice s g (MUsed (fast_meta am i fr)) (MUsed (rel_meta am i fr))).
  apply (markers_set_meta (set_meta s g (MUsed (fast_meta am i fr))) g (fast_meta am i fr) (rel_meta am i fr)); [apply MT_set_same | reflexivity].
Qed.

Theorem ntf_markers : forall L s (m m1 m2 : word -> option byte) g am i fr s' sp,
  WF s -> repr L s (bview SEGS m) -> markers_hold L s (bview SEGS m) -> In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  ly_ctx L = 0x97c98 -> 2^20 + 8192 <= sp ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= sp - 8192) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  (forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> (sp - 48 <= x < sp) \/ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr)))) ->
  FRM L (s_rel s g am i fr) (sp - 48) (8192 - 48) m1 m2 -> MKS s' (s_rel s g am i fr) ->
  markers_hold L s' (bview SEGS m2).
Proof.
  intros L s m m1 m2 g am i fr s' sp HW HR HM HF Hk Hctx Hsp HFP HAP CH1 FR3 MK.
  pose proof HR as (HL & _ & _).
  assert (HFP1 : forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= sp - 1024) by (intros rg Hrg; pose proof (HFP rg Hrg); lia).
  assert (BV : forall x, ~ (sp - 1024 <= x < sp) -> ~ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) ->
             (forall a, In a (st_areas s) -> ~ (loc_addr L (LMem a) <= x < loc_addr L (LMem a) + 4096)) ->
             ~ (ly_ctx L <= x < ly_ctx L + CTX_SIZE) -> bview SEGS m1 x = bview SEGS m x).
  { intros x H1 H2 _ _. destruct (Z_lt_le_dec x 0) as [Hn|Hn].
    { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn). reflexivity. }
    destruct (Z_lt_le_dec x (2^64)) as [Hx|Hx].
    2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx). reflexivity. }
    apply MngWb.bview_ext. destruct (decide (m1 (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (CH1 x ltac:(lia) E) as [A|A]; [apply H1; lia | exact (H2 A)]. }
  pose proof (freed_slot_markers_gen SEGS L s m m1 g am i fr sp HW HR HM HF Hk HFP1 BV) as MK1.
  unfold markers_hold in MK1. rewrite <- (markers_fast_rel s g am i fr HW HF) in MK1.
  destruct (rel_Inv s g am i fr HW HF Hk) as (HIR & _).
  apply Forall_forall. intros c Hc. pose proof (MK c Hc) as HcR.
  apply (cell_holds_frame L (bview SEGS m1) (bview SEGS m2) c (markers_width' _ c HcR) (proj1 (Forall_forall _ _) MK1 c HcR)).
  intros a Ha. destruct (Z_lt_le_dec a 0) as [Hn|Hn].
  { unfold bview. replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn). reflexivity. }
  destruct (Z_lt_le_dec a (2^64)) as [Hx|Hx].
  2:{ unfold bview. replace ((0 <=? a) && (a <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx). reflexivity. }
  apply MngWb.bview_ext. destruct (decide (m2 (wa a) = m1 (wa a))) as [E|E]; [exact E|]. exfalso.
  destruct (marker_region (Some (g, i)) U0 (s_rel s g am i fr) HIR c HcR) as (qc & rg & Eq & Hr & Kr & Lr & Oq & Wq).
  assert (Fin : In (LMem (SP (prid qc) 0), rg_len rg) (footprint (s_rel s g am i fr))) by (apply footprint_region_In; assumption).
  change (footprint (s_rel s g am i fr)) with (footprint s) in Fin.
  pose proof (HFP _ Fin) as B. cbn [fst snd loc_addr] in B.
  unfold in_rng, cell_range in Ha. cbn [fst snd] in Ha. rewrite Eq in Ha. destruct qc as [rq oq]. cbn [loc_addr prid poff] in *.
  destruct (FR3 a ltac:(lia) E) as [A|(c' & Hc' & Hw & Hin)]; [lia|].
  pose proof (markers_vs_wide (Some (g, i)) U0 (s_rel s g am i fr) HIR L c c' (layout_ok_set_meta L s g _ HL) Hctx HAP HcR Hc' Hw) as D.
  unfold ranges_disjoint, in_rng, cell_range in D, Hin. cbn [fst snd] in D, Hin. rewrite Eq in D. cbn [loc_addr] in D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section T1.
Context {fx : FPState}.

#[using="Type"] Lemma t1_scs_a : forall regs m sp0 BASE LEN ERR ra s0 s1 s2 s3, 2^20 <= sp0 <= 2^47 -> 0 <= BASE <= 2^64-1 -> 0 <= ERR <= 2^32-1 ->
  0 <= ra <= 2^64-1 -> 0 <= s0 <= 2^64-1 -> 0 <= s1 <= 2^64-1 -> 0 <= s2 <= 2^64-1 -> 0 <= s3 <= 2^64-1 -> LEN = 0 ->
  scs_denot SEGS m (Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1.RES_pt1a)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 Rsp RB RE Rra Rs0 Rs1 Rs2 Rs3 EL. subst LEN.
  set (E := Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.VALS_t1 sp0 BASE 0 ERR ra s0 s1 s2 s3)).
  assert (Z35 : bv_unsigned (ev E 35) = 0) by (apply zatom; [reflexivity | reflexivity | lia]).
  cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1.RES_pt1a fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
  all: apply sc_br_z; cbn [zeval edenot]. all: rewrite ?Z35. all: rewrite ?br_eq_z. reflexivity.
Qed.

#[using="Type"] Lemma t1_scs_b : forall regs m sp0 BASE LEN ERR ra s0 s1 s2 s3, 2^20 <= sp0 <= 2^47 -> 0 <= BASE <= 2^64-1 -> 0 <= ERR <= 2^32-1 ->
  0 <= ra <= 2^64-1 -> 0 <= s0 <= 2^64-1 -> 0 <= s1 <= 2^64-1 -> 0 <= s2 <= 2^64-1 -> 0 <= s3 <= 2^64-1 -> 1 <= LEN <= 2^64-1 ->
  scs_denot SEGS m (Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1.RES_pt1b)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 Rsp RB RE Rra Rs0 Rs1 Rs2 Rs3 RL.
  set (E := Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | lia]).
  cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1.RES_pt1b fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
  all: apply sc_br_z; cbn [zeval edenot]. all: rewrite ?Z35. all: rewrite ?br_eq_z. litmods.
  rewrite Z.mod_small by lia. apply Z.eqb_neq. lia.
Qed.
End T1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_read4 : forall m a, 0 <= a -> a + 4 <= 2^64 ->
  (forall j, 0 <= j < 4 -> exists b, Mem.mrd SEGS m (wa (a + j)) = Some b) ->
  exists v, 0 <= v <= 2^32 - 1 /\ rdn SEGS m (wa a) 4 = Some (word_to_le_bytes 4 (wa v)).
Proof.
  intros m a Ha Ha4 H.
  destruct (rdn_defined SEGS m 4 (wa a)) as (bs & Hbs & Hlen).
  - rewrite u_wa_small by lia. lia.
  - intros j Hj. unfold rd1. rewrite u_wa_small by lia.
    destruct (H (Z.of_nat j) ltac:(lia)) as (b & Hb). unfold Mem.mrd in Hb. change (Mem.wa (a + Z.of_nat j)) with (wa (a + Z.of_nat j)) in Hb.
    change (Z_to_bv 64 (a + Z.of_nat j)) with (wa (a + Z.of_nat j)). rewrite Hb. discriminate.
  - pose proof (bytes_le_to_Z_nonneg bs) as N1. pose proof (PropExec.bytes_le_to_Z_bound bs) as N2. rewrite Hlen in N2. cbn in N2.
    exists (bytes_le_to_Z bs). split; [lia|]. rewrite Hbs. f_equal. unfold word_to_le_bytes. rewrite u_wa_small by lia.
    rewrite <- Hlen. symmetry. apply RefMemcpyLib.Z_to_le_bytes_lez.
Qed.

Lemma ntf_path_frame : forall L s g am i fr (m m1 m2 : word -> option byte) sp,
  WF s -> layout_ok L s -> In (g, am, i, fr) (frames s) ->
  (forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> (sp - 48 <= x < sp) \/ (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr)))) ->
  FRM L (s_rel s g am i fr) (sp - 48) (8192 - 48) m1 m2 ->
  forall x, 0 <= x < 2^64 -> ~ (sp - 8192 <= x < sp) -> (forall c, In c (image s) -> ~ in_rng (cell_range L c) x) -> m2 (wa x) = m (wa x).
Proof.
  intros L s g am i fr m m1 m2 sp HW HL HF CH1 FR x Hx Hs Hc.
  assert (E1 : m1 (wa x) = m (wa x)).
  { destruct (decide (m1 (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (CH1 x Hx E) as [A|A]; [clear - A Hs; lia|].
    destruct (free_cells_img L s g am i fr x HW HL HF (or_introl A)) as (c & Hc' & Hr). exact (Hc c Hc' Hr). }
  rewrite <- E1. destruct (decide (m2 (wa x) = m1 (wa x))) as [E|E]; [exact E|]. exfalso.
  destruct (FR x Hx E) as [A|(c & Hc' & _ & Hr)]; [clear - A Hs; lia|].
  destruct (RS_range L (s_rel s g am i fr) s c (ex_intro _ (rel_extra L am i fr) (rel_RS L s g am i fr HW HF)) Hc') as (c0 & Hc0 & Er).
  apply (Hc c0 Hc0). rewrite Er. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma static_not_cell : forall L s m sp x, NC L [] [] s m sp 8192 -> 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) ->
  forall c, In c (image s) -> ~ in_rng (cell_range L c) x.
Proof.
  intros L s m sp x N Hx Hn c Hc Hr. pose proof (nc_cells _ _ _ _ _ _ _ N c Hc) as (P1 & P2 & P3).
  unfold in_rng, cell_range in Hr. cbn [fst snd] in Hr. clear - Hx Hn Hr P3. lia.
Qed.

Ltac fixreg T n := match type of T with getr _ ?r = _ => replace (Z_to_bv 5 (Z.of_nat n)) with r by (apply bv_eq; reflexivity) end.
Ltac fixgoal n := match goal with |- getr _ ?r = _ => replace r with (Z_to_bv 5 (Z.of_nat n)) by (apply bv_eq; reflexivity) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section GRP0.
Context {fx : FPState}.

#[using="Type"] Theorem free_grp0_step : forall L s (regs : bvmap 5 word) m rom g am i fr s',
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  ly_ctx L = 0x97c98 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) -> getr regs 4 = wa 489872 ->
  rdn SEGS m (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  rdn SEGS m (wa 416600) 8 = Some (word_to_le_bytes 8 (wa 0x97c00)) ->
  (exists can, 0 <= can <= 2^64 - 1 /\ rdn SEGS m (wa 621568) 8 = Some (word_to_le_bytes 8 (wa can))) ->
  rdn SEGS m (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0)) ->
  (forall j, 0 <= j < 4 -> exists b, Mem.mrd SEGS m (wa (0x778ec + j)) = Some b) ->
  2^20 + 8192 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 8192 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 8192) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  free (Some (frame_ptr am i fr)) s = IRet (tt, s') ->
  exists R m', msteps SEGS (mkst regs (wa 0x52f88) m rom) (mkst R (wa 0x53574) m' rom)
     /\ AXF_ff3.callee_same R regs /\ Heap0 L s' m' /\ kf_of s' = kf_of s
     /\ (forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 8192 <= x < bv_unsigned (getr regs 2)) ->
           (forall c, In c (image s) -> ~ in_rng (cell_range L c) x) -> m' (wa x) = m (wa x))
     /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr s' H0 HF Hk Hnt Hctx HP HR4 Hnl Htab Hgot Hcan Hlk Her Rsp Asp HSTK8 HFP8 HAP Hfree.
  pose proof H0 as (HW & HR & HM). pose proof HR as (HL & _ & _).
  destruct (free_ntf_run L s regs m rom g am i fr H0 HF Hk Hctx HP Hnl Htab Hgot Hcan Rsp Asp HSTK8 HFP8 HAP Hnt)
    as (R3 & m2 & mi & s2 & Hms & E1 & E2 & E10 & E11 & Ek & S1 & S2 & S3 & S4 & S5 & Rb & Rl & Ht & N3 & MK & RG & AR & G1 & G2 & CH1 & FR & NR).
  set (sp := bv_unsigned (getr regs 2)) in *.
  (* [comment removed for export] *)
  destruct mi as [[r len]|].
  { rewrite (free_ntf_some s g am i fr s2 r len HW HF Hnt Ht) in Hfree. discriminate Hfree. }
  rewrite (free_ntf_none s g am i fr s2 HW HF Hnt Ht) in Hfree. injection Hfree as ->.
  assert (ESP : getr regs 2 = wa sp) by (unfold sp; rewrite wa_u; reflexivity).
  pose proof (NC_of_heap L s m sp 8192 HW HR Hctx
               ltac:(destruct Hcan as (can & Rcan & Mcan); split; [exact Hgot|]; split; [exact Htab|]; exists can; split; [exact Rcan | exact Mcan])
               ltac:(rewrite <- ESP; exact HSTK8) ltac:(lia) ltac:(clear - Rsp; unfold sp; lia) ltac:(clear - Rsp; unfold sp; lia) Asp HFP8 HAP) as N0.
  pose proof (ntf_path_frame L s g am i fr m _ m2 sp HW HL HF CH1 FR) as KP.
  assert (ST : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m2 (wa x) = m (wa x)).
  { intros x Hx Hn. apply KP; [clear - Hx; lia | clear - Hx Rsp; unfold sp in *; lia |]. exact (static_not_cell L s m sp x N0 Hx Hn). }
  destruct (rdn_read4 m 0x778ec ltac:(lia) ltac:(lia) Her) as (ERR & RERR & HERR).
  (* [comment removed for export] *)
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_t1z.t1_pt1a R3 m2 rom sp (mi_base L None) (mi_len None) ERR (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8))
              (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)))
    as (R4 & Hms4 & T1 & T2 & T4 & T8 & T9 & T10 & T11 & T18 & T19 & Tk).
  { constructor.
    - exact E1.
    - rewrite E2. first [reflexivity | f_equal; ring].
    - fixgoal 4%nat. rewrite (Ek 4%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). fixreg HR4 4%nat. exact HR4.
    - exact E10.
    - exact E11.
    - exact (stk_ok_mono' m2 (wa sp) 8192 1024 (nc_stk _ _ _ _ _ _ _ N3) ltac:(lia)).
    - clear - Rsp; unfold sp in *; lia.
    - cbn; lia.
    - cbn; lia.
    - exact RERR.
    - pose proof (bv_unsigned_in_range _ (getr regs 1)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 8)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 9)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 18)) as B. unfold bv_modulus in B. lia.
    - pose proof (bv_unsigned_in_range _ (getr regs 19)) as B. unfold bv_modulus in B. lia.
    - exact Asp.
    - rewrite (rdn_frame_n m m2 (0 + 621712) 4) by (first [lia | intros x Hx; cbn in Hx; apply ST; lia]). exact Hlk.
    - rewrite (rdn_frame_n m m2 (0 + 489708) 4) by (first [lia | intros x Hx; cbn in Hx; apply ST; lia]). exact HERR.
    - exact S1. - exact S2. - exact S3. - exact S4. - exact S5.
    - clear - Rsp; unfold sp in *; lia.
    - clear - Rsp; unfold sp in *; lia. }
  { apply t1_scs_a; try (cbn; lia); try (clear - Rsp; unfold sp in *; lia); try exact RERR.
    all: match goal with |- context [bv_unsigned ?w] => pose proof (bv_unsigned_in_range _ w) as B end; unfold bv_modulus in B; lia. }
  exists R4, m2. split; [eapply msteps_trans; [exact Hms | exact Hms4]|].
  split.
  { intros n Hn. cbn [In] in Hn.
    destruct Hn as [<-|[<-|Hn]].
    { fixreg T1 1%nat. rewrite T1, wa_u. reflexivity. }
    { fixreg T2 2%nat. rewrite T2. exact (eq_sym ESP). }
    destruct Hn as [<-|[<-|Hn]].
    { rewrite (Tk 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact (Ek 3%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). }
    { fixreg T4 4%nat. rewrite T4. fixreg HR4 4%nat. exact (eq_sym HR4). }
    destruct Hn as [<-|[<-|[<-|[<-|Hn]]]].
    { fixreg T8 8%nat. rewrite T8, wa_u. reflexivity. }
    { fixreg T9 9%nat. rewrite T9, wa_u. reflexivity. }
    { fixreg T18 18%nat. rewrite T18, wa_u. reflexivity. }
    { fixreg T19 19%nat. rewrite T19, wa_u. reflexivity. }
    assert (Hn' : In n [3;4;20;21;22;23;24;25;26;27]%nat) by (clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]).
    rewrite (Tk n ltac:(clear - Hn; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). exact (Ek n Hn'). }
  assert (HK' : kf_of s' = kf_of s).
  { pose proof (free_kf s (Some (frame_ptr am i fr))) as RK. rewrite (free_ntf_none s g am i fr s' HW HF Hnt Ht) in RK. exact RK. }
  split; [split; [|split]|].
  - destruct (in_frames_inv s g am i fr HF) as (Hu' & Hi' & Hfri').
    assert (Hb : In (frame_ptr am i fr, fr_n fr) (user_blocks s)).
    { unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hu'|]. cbn [snd]. apply in_flat_map.
      exists i. split; [apply In_zseq; lia|]. rewrite Hfri', Hk. left. reflexivity. }
    apply (free_wf s (frame_ptr am i fr) (fr_n fr) [] s' HW Hb). rewrite (free_ntf_none s g am i fr s' HW HF Hnt Ht). reflexivity.
  - exact (repr_of_repr_x L s' _ (nc_repr _ _ _ _ _ _ _ N3)).
  - exact (ntf_markers L s m _ m2 g am i fr s' sp HW HR HM HF Hk Hctx ltac:(clear - Rsp; unfold sp in *; lia) HFP8 HAP CH1 FR MK).
  - split; [exact HK'|]. split; [exact KP|]. exact (mem_grows_trans _ _ _ G1 G2).
Qed.
End GRP0.
