(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepPrfE.v (commit eb934de95d13, blob c961bf225c6f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB15 AF0m AF0x AFl0 AFl2 AFl3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepIFcf RepPrfD RepPrfS.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma SEED_ok : forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte),
  layout_ok ly ->
  val_mem tfibsegs (mrestrict (w_H W) mem) C_PFCB 8 A_APPEND ->
  val_mem tfibsegs (mrestrict (w_H W) mem) C_SILENT 8 1 ->
  spZ regs mod 16 = 0 -> ly_stk_lo ly <= spZ regs - PR_STK -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - PR_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  st_ok tfibsegs (Ereg regs []) SS_P0 (restrict (w_H W) (mkst regs (w64 A_PRINTF) mem (seg_rom tfibsegs))).
Proof.
intros W ly regs mem LY V_cb V_sil A16 Hlo Hhi P_stk.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
assert (SR : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs).
{ rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). reflexivity. }
assert (WR : forall a, spZ regs - PR_STK <= a < spZ regs -> writable_at tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply apresent_writable; [| apply P_stk; exact Ha].
  clear - Ha Hlo T7 SR. unfold PR_STK, APP_STK, TFIB_IMG_END, kHighMemBeg in *. lia. }
assert (NB : kHighMemBeg + PR_STK <= spZ regs) by (clear - Hlo T7; lia).
clear P_stk.
rewrite restrict_mkst_fx. unfold SS_P0. apply (YI04.entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold PMEM0, PCONST, R_LOW, R_NB, R_TOP. cbn [app].
  apply Forall_cons.
  { apply (AFl3.region_ok_window _ _ 2%nat (spZ regs)); [exact E2 | clear - NB; unfold kHighMemBeg in NB; lia | clear - SR; lia |].
    intros a Ha. apply WR. clear - Ha. lia. }
  apply Forall_cons.
  { apply (AFl3.region_ok_window _ _ 2%nat (spZ regs)); [exact E2 | clear - NB; unfold PR_STK, APP_STK, kHighMemBeg in NB; lia | clear - SR; lia |].
    intros a Ha. apply WR. clear - Ha. unfold PR_STK, APP_STK. lia. }
  apply Forall_cons.
  { apply (AFl3.region_ok_window _ _ 2%nat (spZ regs)); [exact E2 | clear - NB; unfold PR_STK, APP_STK, kHighMemBeg in NB; lia | clear - SR; lia |].
    intros a Ha. apply WR. clear - Ha. unfold PR_STK, APP_STK. lia. }
  apply Forall_cons.
  { apply (AFl3.region_ok_lit _ _ C_PFCB 8 A_APPEND V_cb); clear; unfold C_PFCB, A_APPEND; cbn; lia. }
  apply Forall_cons; [| apply Forall_nil].
  { apply (AFl3.region_ok_lit _ _ C_SILENT 8 1 V_sil); clear; unfold C_SILENT; cbn; lia. }
- apply pairwise_disjoint_of_extents.
  unfold PMEM0, PCONST, R_LOW, R_NB, R_TOP, AFl2.lit8, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  clear - NB SR. unfold PR_STK, APP_STK, kHighMemBeg, C_PFCB, C_SILENT in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [| split; exact I]. unfold PFF. cbn [f_atoms atoms_ok]. split; [| exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16.
  clear - NB SR A16 Hhi T4. repeat split; lia.
Qed.

Lemma imemset_stretch_stk : forall (W : world tfibsegs) (k : nat) (E : env) ss ms md (d len retpc : Z)
    (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x64ab8 ->
  ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
  getr (ms_regs ms) 10 = w64 d -> getr (ms_regs ms) 11 = w64 170 -> getr (ms_regs ms) 12 = w64 len ->
  getr (ms_regs ms) 1 = w64 retpc ->
  0 <= len -> TFIB_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
  (forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
  (forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d
     \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r \/ YP09.r_hi r <= YP09.r_lo r) ->
  (forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a
     < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
  (forall regs' mem' mat',
     st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13]%bv))
       (ss_after_stretch ss (ss_mem ss) k [11; 12; 13]%bv retpc)
       (restrict (w_H W) (mkst regs' (w64 retpc) mem' (seg_rom tfibsegs))) ->
     getr regs' 10 = w64 d ->
     (forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr (ms_regs ms) r) ->
     (forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
     (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
     SRr tfibsegs W (mkCfg (mkst regs' (w64 retpc) mem' (seg_rom tfibsegs))
       (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H11 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 HK.
assert (D0 : 0 <= d) by (unfold TFIB_IMG_END in Hd; lia).
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
assert (SOK : store_ok tfibsegs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 d) (Z.to_nat len) = true).
{ apply store_ok_of_all; rewrite unsigned_lit_small by lia; [lia|]. intros x Hx.
  assert (Hw : writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned x)).
  { apply apresent_writable; [lia | apply Hpres; lia]. }
  unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
set (mr := mrestrict (w_H W) (ms_mem ms)) in *.
assert (RET : YK0s.ret_ok (Z_to_bv 64 retpc)).
{ apply YK0s.ret_ok_even. rewrite unsigned_lit_small by lia. apply Znumtheory.Zmod_divide in Hrpc; [|lia]. apply Znumtheory.Zdivide_mod.
  apply (Z.divide_trans _ 4); [exists 2; reflexivity | exact Hrpc]. }
destruct (tfib_imemset mr (Z_to_bv 64 d) (Z_to_bv 64 170) len (seg_rom tfibsegs) (ms_regs ms) (Z_to_bv 64 retpc)
  Hlen ltac:(rewrite unsigned_lit_small by lia; lia) SOK ltac:(intros _ _; rewrite unsigned_lit_small by lia; lia) RET H1 H10 H11 H12)
  as (regs' & Hms & Hagree).
change (bv_unsigned (Z_to_bv 64 170)) with 170 in Hms.
set (bs := repeat (Z_to_bv 8 170) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q).
{ rewrite restrict_mkst_fx. change (Z_to_bv 64 0x64ab8) with (Z_to_bv 64 (bv_unsigned tfib_imemset_entry)).
  rewrite Z_to_bv_bv_unsigned. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
  - apply wbytes_below; rewrite unsigned_lit_small by lia; lia.
  - apply wbytes_above; rewrite unsigned_lit_small by lia; lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
assert (Hfr : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr (ms_regs ms) r).
{ intros r N1 N2 N3. apply Hagree. unfold imemset_clob. cbn. intros [X|[X|[X|[]]]]; congruence. }
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
  unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
  apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13]%bv HS Hrv);
  [ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
  | exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
  + intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr. apply Hfr; intros ->; apply Hr; tauto.
  + apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
    * intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
      rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
    * intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact (eq_trans (Hfr 10%bv ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) H10).
- exact Hfr.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
  rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
  assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
  destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
Qed.

End a.
