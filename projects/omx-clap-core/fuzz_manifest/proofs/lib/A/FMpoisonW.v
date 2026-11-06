(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0r.v, with its module paths changed; 530 of its 590 lines of code are new or changed and 384 lines of the source are left out. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN32 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMpoisonS FMpoisonR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* The walk of __asan_poison_memory_region (h, 16): the head's two shadow bytes become 0xf7 and (h, 16) joins the
   user-poisoned ranges U of ARU (A/FMupoison.v). Design: a Theorem Labs lane's design/POISON.md section 7. *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma po_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_po FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_po tbl_po_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma st_ok_add_fact0 : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.
Lemma val_mem1_of_aview : forall H mem a v, aview tfibsegs H mem a = Some v -> val_mem tfibsegs (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv. destruct (aview_byte_ex H mem a v Hv) as (b & Hb & -> & Hr). intros k Hk. replace k with 0%nat by lia.
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. unfold le_byte, YG0f.le_byte, YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma aview_of_val_mem1 : forall H mem a v, val_mem tfibsegs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview tfibsegs H mem a = Some v.
Proof.
intros H mem a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. rewrite X.
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold le_byte, YG0f.le_byte, YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma XS_denot : forall E d hv, bv_unsigned (ew E 10) = hv -> 0 <= hv -> 0 <= d -> hv + d < 2 ^ 64 ->
sv_denot E (XS d) = Z_to_bv 64 (SHADOW_OFF + (hv + d) / 8).
Proof.
intros E d hv HE H0 Hd Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (XS d))). f_equal.
change (bv_unsigned (sv_denot E (XS d))) with (U E (XS d)). rewrite (U_zev E (XS d)) by (vm_compute; reflexivity).
unfold XS. cbn [zev zalu_raw]. unfold rho_of. rewrite HE. change (Z.land (zcanon 3) 63) with 3. change (zcanon 2147450880) with 2147450880.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (hv + d) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (hv + d) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (hv + d)) by lia. rewrite (zcanon_small ((hv + d) / 8)) by lia. unfold SHADOW_OFF. apply zcanon_small. lia.
Qed.
Lemma XS0_denot : forall E d hv, bv_unsigned (ew E 10) = hv -> 0 <= hv -> 0 <= d -> hv + d < 2 ^ 64 ->
sv_denot E (XS0 d) = Z_to_bv 64 (SHADOW_OFF + (hv + d) / 8).
Proof.
intros E d hv HE H0 Hd Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (XS0 d))). f_equal.
change (bv_unsigned (sv_denot E (XS0 d))) with (U E (XS0 d)). rewrite (U_zev E (XS0 d)) by (vm_compute; reflexivity).
unfold XS0, XS. cbn [zev zalu_raw]. unfold rho_of. rewrite HE. change (Z.land (zcanon 3) 63) with 3. change (zcanon 2147450880) with 2147450880.
change (zcanon 0) with 0. rewrite Z.add_0_r.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (hv + d) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (hv + d) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (hv + d)) by lia. rewrite (zcanon_small ((hv + d) / 8)) by lia. unfold SHADOW_OFF.
rewrite (zcanon_small (2147450880 + (hv + d) / 8)) by lia. apply zcanon_small. lia.
Qed.
End d.
Lemma env_agree_Ereg_app' : forall regs l1 l2 k, (k <= 32 + length l1)%nat -> env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma vis_apresent' : forall H mem a v, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H mem a = Some v -> apresent H mem a.
Proof. intros H mem a v Ha Hv. destruct (aview_byte_ex H mem a v Hv) as (b & Hb & _). exact (AF0x.mbyte_high_apresent H mem a b Ha Hb). Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
(* The image cells the walk reads are below the shadow, so they read the same with or without the user poison. *)
Lemma po_rodata_okU : forall ly S U W mem md E, ARU tfibsegs B ly S U W mem md ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) (map ro_region po_rodata).
Proof.
intros ly S U W mem md E HU.
pose proof (ARU_ARm tfibsegs B ly S U W mem md HU) as M.
pose proof (po_rodata_chk ly) as Hc. pose proof po_rodata_low as Hlow.
unfold rodata_chk in Hc. rewrite forallb_forall in Hc, Hlow. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). specialize (Hlow _ Hin). cbn [fst snd] in Hc, Hlow. rewrite forallb_forall in Hlow.
apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi]. apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off nb] v] Hc'.
specialize (Hcs _ Hc'). specialize (Hlow _ Hc'). cbn [fst snd] in Hcs, Hlow. apply andb_prop in Hlow as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfibsegs E _ 0 (base + off) nb (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l.
pose proof (tfib_const_lookup B TB ly S (w_H W) (unpoison U mem) (base + off) (N.to_nat nb) v M (const_chk_sound _ _ _ _ H1)) as VM.
apply (AF0x.val_mem_ext (mrestrict (w_H W) (unpoison U mem))); [|exact VM].
intros k Hk. unfold mbyte, mrestrict. rewrite (ARU_mem_low tfibsegs B ly S U W mem md _ HU); [reflexivity|].
rewrite wz by (unfold TFIB_IMG_END in *; lia). unfold TFIB_IMG_END, SHADOW_OFF in *. lia.
Qed.
(* The windows of the walk's symbolic states: its stack frame, and the head's two shadow bytes after phase A. *)
Lemma winsA_cases : forall E rs a, windows rs = WinsA -> in_wrange E rs a -> bv_unsigned (ew E 2) - PO_WIN <= a < bv_unsigned (ew E 2).
Proof.
intros E rs a HW Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi' & Ht & Hw). rewrite HW in Ht. unfold WinsA in Ht.
repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; unfold PO_WIN; first [lia | exfalso; lia] |]). destruct Ht.
Qed.
Lemma wins_cases : forall E rs a, windows rs = Wins -> in_wrange E rs a ->
bv_unsigned (ew E 2) - PO_WIN <= a < bv_unsigned (ew E 2) \/ bv_unsigned (ew E 32) <= a < bv_unsigned (ew E 32) + 2.
Proof.
intros E rs a HW Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi' & Ht & Hw). rewrite HW in Ht. unfold Wins in Ht.
repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; unfold PO_WIN; first [left; lia | right; lia | exfalso; lia] |]). destruct Ht.
Qed.
Theorem tfib_poison16 : apoison16_realizes tfibsegs B PO_ENTRY.
Proof.
unfold apoison16_realizes.
intros ly S U W regs mem md h p n HPRE G10 G11 OK' Hb Hp Hn.
pose proof HPRE as (HPE & OK & PO).
pose proof HPE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact OK | exact PO]]).
pose proof AF0x.Hwx_tfa as Hwx.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as LSC. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Lbeg Lhi Hslo Htop; unfold kHighMemBeg, kHighMemEnd in *; lia).
assert (LbN : 17594333495296 + 4096 <= sp0) by (clear - Lbeg Hslo; unfold kHighMemBeg in *; lia).
assert (HIGHM : forall a, kHighMemBeg <= a < 2 ^ 64 -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. apply unpoison_out. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
  rewrite (wz a ltac:(unfold kHighMemBeg in Ha; lia)) in E. pose proof (ush_facts tfibsegs B ly S U W mem md a HU E) as (_ & _ & L). lia. }
assert (Hpres : forall a, sp0 - 4096 <= a < sp0 -> apresent H mem a).
{ intros a Ha. apply (AF0x.apresent_same H (unpoison U mem) mem a); [symmetry; apply HIGHM; lia | apply HpresE; exact Ha]. }
destruct (upoison_ok_cons16 B ly S h U OK') as (H8 & (p' & n' & Hb' & Hp' & Hn') & AL & DJ & _).
pose proof (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as (P16 & P4096 & PC & PAPP & _).
assert (ZONE : exists hi : bool, hLO hi <= h <= hHI hi).
{ pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. unfold in_app in PAPP. destruct PAPP as [PA1 [PA2 | (PA2 & PA3)]].
  - exists false. unfold hLO, hHI, kLowShadowBeg in *. lia.
  - exists true. unfold hLO, hHI, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
destruct ZONE as [hi HZ].
assert (Hh : 4096 <= h < 2 ^ 47) by (destruct hi; unfold hLO, hHI, kHighMemBeg, kHighMemEnd, kLowShadowBeg in HZ; lia).
set (SH := shadow_addr h).
assert (HSH : SH = SHADOW_OFF + h / 8) by reflexivity.
assert (SHr : shLO hi <= SH <= shHI hi).
{ rewrite HSH. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. rewrite Hq, Z.div_mul by lia.
  destruct hi; unfold shLO, shHI, hLO, hHI, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg, kHighMemEnd in *; lia. }
assert (SHb : kLowShadowBeg <= SH /\ SH + 3 <= kHighMemBeg)
  by (clear - SHr; destruct hi; unfold shLO, shHI, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg in *; lia).
assert (SHnum : 2147446784 <= SH /\ SH + 3 <= 17594333495296) by (clear - SHb; unfold kLowShadowBeg, kHighMemBeg in SHb; lia).
assert (SH2 : shadow_addr (h + 16) = SH + 2).
{ rewrite HSH. unfold shadow_addr. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 8 + 16) with ((q + 2) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
assert (HV0 : forall j, 0 <= j < 2 -> aview tfibsegs H mem (SH + j) = Some 0).
{ intros j Hj.
  assert (G : aview tfibsegs H (unpoison U mem) (shadow_addr (h + 8 * j)) = Some 0).
  { apply (block_granule0 tfibsegs B LAWS ly S W (unpoison U mem) md p' n' (h + 8 * j) HAR Hb'); [|lia|lia].
    pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. rewrite Hq. replace (q * 8 + 8 * j) with ((q + j) * 8) by lia. apply Z.mod_mul. lia. }
  assert (E1 : shadow_addr (h + 8 * j) = SH + j).
  { rewrite HSH. unfold shadow_addr. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 8 + 8 * j) with ((q + j) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  rewrite E1 in G. rewrite <- G. symmetry. apply aview_unpoison_out.
  rewrite wz by (clear - SHb Hj; unfold kLowShadowBeg, kHighMemBeg in *; lia). apply (ush16_out h U _ H8 AL DJ). fold SH. lia. }
assert (HV2 : exists VB, aview tfibsegs H mem (SH + 2) = Some VB).
{ destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as [(P8 & N0 & BS) _].
  pose proof P8 as P8'. apply Z.mod_divide in P8' as [a8 Ha8]; [|lia]. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia].
  assert (I1 : (h + 16 - p) / 8 = q + 2 - a8) by (rewrite Hq, Ha8; replace (q * 8 + 16 - a8 * 8) with ((q + 2 - a8) * 8) by lia; apply Z.div_mul; lia).
  assert (I2 : 0 <= (h + 16 - p) / 8 < (req_size n + 7) / 8).
  { rewrite I1. split; [lia|]. apply Z.lt_le_trans with (q + 3 - a8); [lia|]. apply Z.div_le_lower_bound; lia. }
  pose proof (BS _ I2) as BSv.
  assert (I3 : shadow_of_addr SHADOW_OFF p + (h + 16 - p) / 8 = SH + 2).
  { rewrite <- SH2. unfold shadow_of_addr, shadow_addr. rewrite I1, Ha8, Hq. replace (q * 8 + 16) with ((q + 2) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  rewrite I3 in BSv.
  destruct (in_ush U (bv_unsigned (Z_to_bv 64 (SH + 2)))) eqn:Ei.
  - exists 247. rewrite wz in Ei by (clear - SHb; unfold kLowShadowBeg, kHighMemBeg in *; lia). exact (PO _ Ei).
  - eexists. rewrite <- (aview_unpoison_out tfibsegs H U mem _ Ei). exact BSv. }
destruct HV2 as [VB HVB].
pose proof (aview_byte_ex H mem (SH + 2) VB HVB) as (bVB & _ & _ & HVBr).
(* ---- phase A: entry to the load of shadow (h) ---- *)
set (E0 := AE2y.Env regs []).
assert (E0reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (E02 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0reg 2%nat 2%bv eq_refl); reflexivity).
assert (E010 : bv_unsigned (ew E0 10) = h) by (rewrite (E0reg 10%nat 10%bv eq_refl), G10; unfold w64; apply wz; lia).
assert (HS0 : st_ok tfibsegs E0 (ssA PO_ENTRY hi) (restrict H (mkst regs (Z_to_bv 64 PO_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssA.
  apply (AF0x.st_ok_pin_reg E0 (ssA0 PO_ENTRY hi) _ 11%bv (SLit 16)); [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
  unfold ssA0. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold memA. apply Forall_cons; [|exact (po_rodata_okU ly S U W mem md E0 HU)].
    unfold stkA, PO_WIN. apply (region_ok_stack tfibsegs E0 _ 2 sp0 (- 64)); [exact E02 | lia | lia |].
    intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents. unfold memA, stkA, po_rodata, icpt_rodata, ro_region, extent_of_region, PO_WIN.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E02.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E02, E010.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia; first [exact Hal16 | exact H8 | idtac]. }
eapply SRr_bind; [apply (po_phase W E0 _ _ _ _ _ HS0 (pr_A hi))|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
change (st_ok tfibsegs E0 (peA hi) (restrict H msA)) in HSA.
assert (MEQA : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ms_mem msA z = mem z).
{ intros z Hz. apply HFA. intros Hin. pose proof (winsA_cases E0 _ _ (pA_win hi) Hin) as X. rewrite E02 in X. unfold PO_WIN in X. lia. }
clear HFA HFrA.
destruct (pA_facts hi) as (PA1 & PA2 & PA3 & PA4 & PA5 & PA6).
pose proof (st_ok_restrict_mkst tfibsegs H E0 _ _ HSA PA2) as HshA. rewrite PA1 in HshA.
assert (RDA : forall (r : bv 5) v, reg_is (peA hi) (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E0 (peA hi) msA r HSA). }
assert (G9A : getr (ms_regs msA) 9 = Z_to_bv 64 SH).
{ rewrite (RDA 9%bv _ PA4). rewrite (XS0_denot E0 0 h E010) by lia. rewrite Z.add_0_r. reflexivity. }
assert (G10A : getr (ms_regs msA) 10 = Z_to_bv 64 SH).
{ rewrite (RDA 10%bv _ PA5). rewrite (XS_denot E0 0 h E010) by lia. rewrite Z.add_0_r. reflexivity. }
(* ---- phase B: the head's shadow bytes as a region at the new atom aSH, the end byte as atom aV ---- *)
set (EB := AE2y.Env regs [SH; VB]).
assert (AGR : env_agree 32 E0 EB) by (unfold E0, EB, AE2y.Env; cbn [map]; apply (env_agree_Ereg_app' regs [] [Z_to_bv 64 SH; Z_to_bv 64 VB] 32); cbn; lia).
assert (EBreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EB i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EB2 : bv_unsigned (ew EB 2) = sp0) by (rewrite (EBreg 2%nat 2%bv eq_refl); reflexivity).
assert (EB10 : bv_unsigned (ew EB 10) = h) by (rewrite (EBreg 10%nat 10%bv eq_refl), G10; unfold w64; apply wz; lia).
assert (UB32 : bv_unsigned (ew EB 32) = SH) by (pose proof (AE2y.Env_x regs [SH; VB] 0 SH eq_refl) as X; cbn [Nat.add] in X; change (AE2y.Env regs [SH; VB]) with EB in X; rewrite X; apply wz; clear - SHb; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (UB33 : bv_unsigned (ew EB 33) = VB) by (pose proof (AE2y.Env_x regs [SH; VB] 1 VB eq_refl) as X; cbn [Nat.add] in X; change (AE2y.Env regs [SH; VB]) with EB in X; rewrite X; apply wz; lia).
assert (VM1 : forall a v, ~ (sp0 - 64 <= a < sp0) -> 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a = Some v ->
  val_mem tfibsegs (mrestrict H (ms_mem msA)) a 1 v).
{ intros a v Ha Hr Hv. apply (AF0x.val_mem_ext (mrestrict H mem)); [| apply val_mem1_of_aview; exact Hv].
  intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite MEQA; [reflexivity|]. rewrite wz by lia. lia. }
assert (SHnS : forall j, 0 <= j < 3 -> ~ (sp0 - 64 <= SH + j < sp0)) by (intros j Hj; clear - SHb Hslo Lbeg Hj; lia).
assert (SHr64 : forall j, 0 <= j < 3 -> TFIB_IMG_END <= SH + j < 2 ^ 64) by (intros j Hj; clear - SHb Hj; unfold TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *; lia).
rewrite HshA in HSA. rewrite restrict_mkst_fx in HSA.
assert (HSB0 : st_ok tfibsegs EB (pB hi) (restrict H (mkst (ms_regs msA) (Z_to_bv 64 P_LDA) (ms_mem msA) (seg_rom tfibsegs)))).
{ rewrite <- (pB_eq hi). unfold ppB. rewrite PA1. rewrite restrict_mkst_fx.
  apply st_ok_add_fact0; [| reflexivity | unfold aV; rewrite UB33; lia].
  apply st_ok_add_fact0; [| reflexivity | unfold aSH; rewrite UB32; exact SHr].
  apply (st_ok_set_regs_mem tfibsegs 32 E0 EB (peA hi) (ms_regs msA) (ms_regs msA) (Z_to_bv 64 P_LDA) P_LDA
    (mrestrict H (ms_mem msA)) (mrestrict H (ms_mem msA)) (memB (peA hi) 0 0) updB HSA AGR PA3).
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - unfold updB. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
    + rewrite G9A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
    + rewrite G10A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
  - pose proof (st_ok_agree tfibsegs 32 E0 EB (peA hi) _ HSA AGR PA3) as HSA'.
    pose proof (st_ok_mem_ok tfibsegs EB (peA hi) _ HSA') as (WFA & ROKA & PDA).
    split; [rewrite memB_eq; vm_compute; reflexivity|]. split.
    + unfold memB. rewrite PA6 in ROKA. apply Forall_cons; [exact (Forall_inv ROKA)|]. apply Forall_cons; [|exact (Forall_inv_tail ROKA)].
      unfold rSH, aSH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UB32.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (AF0x.apresent_writable H); [apply SHr64; lia|].
        apply (AF0x.apresent_same H mem); [apply MEQA; rewrite wz by (pose proof (SHr64 o ltac:(lia)); lia); apply SHnS; lia|].
        exact (vis_apresent' H mem (SH + o) 0 (SHr64 o ltac:(lia)) (HV0 o ltac:(lia))). }
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val tfibsegs EB _ SH 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        apply VM1; [apply SHnS; lia | pose proof (SHr64 0 ltac:(lia)); lia | exact (HV0 0 ltac:(lia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 1 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        apply VM1; [apply SHnS; lia | pose proof (SHr64 1 ltac:(lia)); lia | exact (HV0 1 ltac:(lia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 2 1%N (SOff aV 0) VB); [cbn [sv_denot]; unfold aV; rewrite UB33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        apply VM1; [apply SHnS; lia | pose proof (SHr64 2 ltac:(lia)); lia | exact HVB].
    + apply pairwise_disjoint_of_extents. rewrite memB_eq. let l' := eval vm_compute in memBc in change memBc with l'.
      unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EB2, ?UB32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - SHb Hsp Hslo Lbeg. unfold kLowShadowBeg, kHighMemBeg in *. repeat split; lia. }
rewrite HshA.
eapply SRr_bind; [apply (po_phase W EB (pB hi) _ _ _ _ HSB0 (pr_B hi))|].
cbv beta. intros Wb cb _ (-> & msB & matB & -> & HSB & HFB & HFrB). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (peB hi) (restrict H msB)) in HSB.
assert (MEQB : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msB z = ms_mem msA z).
{ intros z Hz1 Hz2. apply HFB. intros Hin. pose proof (wins_cases EB _ _ (pB_win hi) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. lia. }
clear HFB HFrB.
destruct (pB_facts hi) as (PB1 & PB2 & PB3 & PB4).
pose proof (st_ok_restrict_mkst tfibsegs H EB _ _ HSB PB2) as HshB. rewrite PB1 in HshB.
assert (RDB : forall (r : bv 5) v, reg_is (peB hi) (bv_unsigned r) v = true -> getr (ms_regs msB) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (peB hi) msB r HSB). }
assert (G18B : getr (ms_regs msB) 18 = Z_to_bv 64 (SH + 2)).
{ rewrite (RDB 18%bv _ PB4). rewrite (XS0_denot EB 16 h EB10) by lia. rewrite <- SH2. reflexivity. }
rewrite HshB in HSB. rewrite restrict_mkst_fx in HSB.
assert (HSC0 : st_ok tfibsegs EB (pC hi) (restrict H (mkst (ms_regs msB) (Z_to_bv 64 P_LDB) (ms_mem msB) (seg_rom tfibsegs)))).
{ rewrite <- (pC_eq hi). unfold ppC. rewrite PB1. rewrite restrict_mkst_fx.
  apply (st_ok_set_regs_mem tfibsegs 34 EB EB (peB hi) (ms_regs msB) (ms_regs msB) (Z_to_bv 64 P_LDB) P_LDB
    (mrestrict H (ms_mem msB)) (mrestrict H (ms_mem msB)) (ss_mem (peB hi)) [((18%bv : bv 5), SOff aSH 2)] HSB).
  - split; [intros; reflexivity | reflexivity].
  - exact PB3.
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G18B. cbn [sv_denot]. unfold aSH. rewrite UB32. reflexivity.
  - exact (st_ok_mem_ok tfibsegs EB (peB hi) _ HSB). }
rewrite HshB.
eapply SRr_bind; [apply (po_phase W EB (pC hi) _ _ _ _ HSC0 (pr_C hi))|].
cbv beta. intros Wc cc _ (-> & msC & matC & -> & HSC & HFC & HFrC). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (peC hi) (restrict H msC)) in HSC.
assert (MEQC : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msC z = ms_mem msB z).
{ intros z Hz1 Hz2. apply HFC. intros Hin. pose proof (wins_cases EB _ _ (pC_win hi) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. lia. }
clear HFC HFrC.
(* ---- phase D: the end-granule test, both ways ---- *)
assert (HSD : exists tk, st_ok tfibsegs EB (pD hi tk) (restrict H msC)).
{ destruct (branch_taken BC_GE (sv_denot EB (SLit 0)) (sv_denot EB V1)) eqn:Hbr.
  - exists true. exact (st_ok_add_cond tfibsegs EB (peC hi) _ BC_GE (SLit 0) V1 HSC Hbr).
  - exists false. exact (st_ok_add_cond_neg tfibsegs EB (peC hi) _ BC_GE (SLit 0) V1 HSC Hbr). }
destruct HSD as [tk HSD].
eapply SRr_bind; [apply (po_phase W EB (pD hi tk) _ _ _ _ HSD (pr_D hi tk))|].
cbv beta. intros Wd cd _ (-> & msD & matD & -> & HSDf & HFD & HFrD). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (peD hi tk) (restrict H msD)) in HSDf.
assert (MEQD : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = ms_mem msC z).
{ intros z Hz1 Hz2. apply HFD. intros Hin. pose proof (wins_cases EB _ _ (pD_win hi tk) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. lia. }
clear HFD HFrD.
assert (MEQ : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = mem z).
{ intros z Hz1 Hz2. rewrite (MEQD z Hz1 Hz2), (MEQC z Hz1 Hz2), (MEQB z Hz1 Hz2). exact (MEQA z Hz1). }
clear MEQA MEQB MEQC MEQD.
destruct (pD_facts hi tk) as (PD1 & PD2 & NR0 & NR1).
pose proof (pD_resv hi tk) as RVD.
eapply (SRr_ret_at tfibsegs tbl_po tbl_po_ok Hwx W EB); [exact HSDf | exact RVD | rewrite PD1; exact po_ret_word |].
intros mat'. rewrite wvb_wvb.
assert (RDD : forall (r : bv 5) v, reg_is (peD hi tk) (bv_unsigned r) v = true -> getr (ms_regs msD) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (peD hi tk) msD r HSDf). }
assert (RKD : forall rz, In rz KEPT -> getr (ms_regs msD) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. unfold final_ok in PD2. apply andb_prop in PD2 as [_ FB]. rewrite forallb_forall in FB. specialize (FB rz Hrz). cbn beta in FB.
  assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; unfold KEPT in Hrz; cbn in Hrz; lia).
  assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
  rewrite (RDD (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB].
  cbn [sv_denot]. rewrite (EBreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RKD 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs msD) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs msD), (ms_mem msD), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs EB (peD hi tk) _ HSDf) as (_ & ROKD & _). change (ms_mem (restrict H msD)) with (mrestrict H (ms_mem msD)) in ROKD.
pose proof (proj1 (Forall_forall _ _) ROKD _ (nth_error_In _ _ NR1)) as OKSH.
destruct pSH_shape as (BSH & WSH1 & WSH2 & CSH0 & CSH1). destruct pSTK_shape as (BS0 & WS01 & WS02).
unfold region_ok in OKSH. rewrite BSH in OKSH. cbn [base_val] in OKSH. unfold aSH in OKSH. rewrite UB32 in OKSH.
destruct OKSH as (_ & _ & _ & CHSH).
assert (P0 : aview tfibsegs H (ms_mem msD) SH = Some 247).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 0 1%N (SLit 247) 247 (proj1 (Forall_forall _ _) CHSH _ CSH0) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VMx.
  rewrite Z.add_0_r in VMx. exact (aview_of_val_mem1 H (ms_mem msD) SH 247 VMx ltac:(lia)). }
assert (P1 : aview tfibsegs H (ms_mem msD) (SH + 1) = Some 247).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 1 1%N (SLit 247) 247 (proj1 (Forall_forall _ _) CHSH _ CSH1) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VMx.
  exact (aview_of_val_mem1 H (ms_mem msD) (SH + 1) 247 VMx ltac:(lia)). }
assert (PW : forall b, (sp0 - 64 <= b < sp0 \/ SH <= b < SH + 2) -> apresent H (ms_mem msD) b).
{ intros b [Hbw|Hbw].
  - apply (st_ok_window_apresent H EB (peD hi tk) msD 0 pSTK b HSDf NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EB2; unfold PO_WIN; lia | unfold TFIB_IMG_END; lia].
  - apply (st_ok_window_apresent H EB (peD hi tk) msD 1 pSH b HSDf NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite UB32; lia | pose proof (SHr64 0 ltac:(lia)); pose proof (SHr64 2 ltac:(lia)); lia]. }
assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> ~ (SH <= a < SH + 2) -> aview tfibsegs H (ms_mem msD) a = aview tfibsegs H mem a).
{ intros a Ha N1 N2. apply AF0x.aview_same. apply MEQ; rewrite wz by exact Ha; assumption. }
assert (HB' : forall a, in_band_rw a -> H (w64 a) = true -> ms_mem msD (w64 a) = mem (w64 a)).
{ intros a Hbd Hh'. unfold w64 in *. assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hbd; lia).
  apply MEQ; rewrite wz by exact Ha; intros Hin; [ pose proof (PW a (or_introl Hin)) as (Hx & _) | pose proof (PW a (or_intror Hin)) as (Hx & _) ]; rewrite Hx in Hh'; discriminate Hh'. }
assert (HARU : ARU tfibsegs B ly S ((h, 16) :: U) W (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat' md)).
{ apply (ARU_poison_step tfibsegs B LAWS ly S U W mem md h (ms_mem msD) _ (sp0 - 64) sp0 HU OK'); [lia | lia | exact FR | | exact P0 | exact P1 | apply MF | apply MF | apply MF | exact HB'].
  intros a Ha. apply AE2y.aview_some_of_apresent. apply PW. left. exact Ha. }
split; [exact HARU|].
split; [|split; [apply with_vm_backing_same|split; [exact FR|]]].
- intros r Hr. unfold acallee_saved in Hr. apply RKD. clear - Hr. unfold KEPT. cbn. lia.
- split.
  + intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [L|L].
    * apply (AF0x.apresent_same H mem); [apply MEQ; rewrite wz by lia; lia | apply Hpres; lia].
    * apply PW. left. lia.
  + intros a HPa. rewrite (AE2y.apresent_mod _ (ms_mem msD) a). rewrite (AE2y.apresent_mod _ mem a) in HPa.
    assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (a' := a mod 2 ^ 64) in *. clearbody a'.
    destruct (Z_lt_le_dec a' (sp0 - 64)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L2|L2]]; [| apply PW; left; lia |].
    all: destruct (Z_lt_le_dec a' SH) as [S1|S1]; [|destruct (Z_lt_le_dec a' (SH + 2)) as [S2|S2]].
    all: first [apply PW; right; lia | apply (AF0x.apresent_same H mem); [apply MEQ; rewrite wz by lia; lia | exact HPa]].
Qed.
Theorem tfib_unpoison16 : aunpoison16_realizes tfibsegs B UP_ENTRY.
Proof.
unfold aunpoison16_realizes.
intros ly S U W regs mem md h p n HPRE G10 G11 Hb Hp Hn.
pose proof HPRE as (HPE & OK & PO).
pose proof HPE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
assert (HU : ARU tfibsegs B ly S ((h, 16) :: U) W mem md) by (split; [exact HAR | split; [exact OK | exact PO]]).
pose proof AF0x.Hwx_tfa as Hwx.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as LSC. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Lbeg Lhi Hslo Htop; unfold kHighMemBeg, kHighMemEnd in *; lia).
assert (LbN : 17594333495296 + 4096 <= sp0) by (clear - Lbeg Hslo; unfold kHighMemBeg in *; lia).
assert (HIGHM : forall a, kHighMemBeg <= a < 2 ^ 64 -> unpoison ((h, 16) :: U) mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. apply unpoison_out. destruct (in_ush ((h, 16) :: U) (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
  rewrite (wz a ltac:(unfold kHighMemBeg in Ha; lia)) in E. pose proof (ush_facts tfibsegs B ly S ((h, 16) :: U) W mem md a HU E) as (_ & _ & L). lia. }
assert (Hpres : forall a, sp0 - 4096 <= a < sp0 -> apresent H mem a).
{ intros a Ha. apply (AF0x.apresent_same H (unpoison ((h, 16) :: U) mem) mem a); [symmetry; apply HIGHM; lia | apply HpresE; exact Ha]. }
destruct (upoison_ok_cons16 B ly S h U OK) as (H8 & (p' & n' & Hb' & Hp' & Hn') & AL & DJ & OKU).
pose proof (al_blocks _ _ LAWS ly S W (unpoison ((h, 16) :: U) mem) md p n HAR Hb) as (P16 & P4096 & PC & PAPP & _).
assert (ZONE : exists hi : bool, hLO hi <= h <= hHI hi).
{ pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. unfold in_app in PAPP. destruct PAPP as [PA1 [PA2 | (PA2 & PA3)]].
  - exists false. unfold hLO, hHI, kLowShadowBeg in *. lia.
  - exists true. unfold hLO, hHI, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
destruct ZONE as [hi HZ].
assert (Hh : 4096 <= h < 2 ^ 47) by (destruct hi; unfold hLO, hHI, kHighMemBeg, kHighMemEnd, kLowShadowBeg in HZ; lia).
set (SH := shadow_addr h).
assert (HSH : SH = SHADOW_OFF + h / 8) by reflexivity.
assert (SHr : shLO hi <= SH <= shHI hi).
{ rewrite HSH. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. rewrite Hq, Z.div_mul by lia.
  destruct hi; unfold shLO, shHI, hLO, hHI, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg, kHighMemEnd in *; lia. }
assert (SHb : kLowShadowBeg <= SH /\ SH + 3 <= kHighMemBeg)
  by (clear - SHr; destruct hi; unfold shLO, shHI, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg in *; lia).
assert (SHnum : 2147446784 <= SH /\ SH + 3 <= 17594333495296) by (clear - SHb; unfold kLowShadowBeg, kHighMemBeg in SHb; lia).
assert (SH2 : shadow_addr (h + 16) = SH + 2).
{ rewrite HSH. unfold shadow_addr. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 8 + 16) with ((q + 2) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
assert (HV0 : forall j, 0 <= j < 2 -> aview tfibsegs H mem (SH + j) = Some 247).
{ intros j Hj. apply PO. rewrite in_ush_cons16. change (shadow_addr h) with SH. apply Bool.orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (HV2 : exists VB, aview tfibsegs H mem (SH + 2) = Some VB).
{ destruct (al_shadow _ _ LAWS ly S W (unpoison ((h, 16) :: U) mem) md p n HAR Hb) as [(P8 & N0 & BS) _].
  pose proof P8 as P8'. apply Z.mod_divide in P8' as [a8 Ha8]; [|lia]. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|lia].
  assert (I1 : (h + 16 - p) / 8 = q + 2 - a8) by (rewrite Hq, Ha8; replace (q * 8 + 16 - a8 * 8) with ((q + 2 - a8) * 8) by lia; apply Z.div_mul; lia).
  assert (I2 : 0 <= (h + 16 - p) / 8 < (req_size n + 7) / 8).
  { rewrite I1. split; [lia|]. apply Z.lt_le_trans with (q + 3 - a8); [lia|]. apply Z.div_le_lower_bound; lia. }
  pose proof (BS _ I2) as BSv.
  assert (I3 : shadow_of_addr SHADOW_OFF p + (h + 16 - p) / 8 = SH + 2).
  { rewrite <- SH2. unfold shadow_of_addr, shadow_addr. rewrite I1, Ha8, Hq. replace (q * 8 + 16) with ((q + 2) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  rewrite I3 in BSv.
  destruct (in_ush ((h, 16) :: U) (bv_unsigned (Z_to_bv 64 (SH + 2)))) eqn:Ei.
  - exists 247. rewrite wz in Ei by (clear - SHb; unfold kLowShadowBeg, kHighMemBeg in *; lia). exact (PO _ Ei).
  - eexists. rewrite <- (aview_unpoison_out tfibsegs H ((h, 16) :: U) mem _ Ei). exact BSv. }
destruct HV2 as [VB HVB].
pose proof (aview_byte_ex H mem (SH + 2) VB HVB) as (bVB & _ & _ & HVBr).
(* ---- phase A: entry to the load of shadow (h) ---- *)
set (E0 := AE2y.Env regs []).
assert (E0reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (E02 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0reg 2%nat 2%bv eq_refl); reflexivity).
assert (E010 : bv_unsigned (ew E0 10) = h) by (rewrite (E0reg 10%nat 10%bv eq_refl), G10; unfold w64; apply wz; lia).
assert (HS0 : st_ok tfibsegs E0 (ssA UP_ENTRY hi) (restrict H (mkst regs (Z_to_bv 64 UP_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssA.
  apply (AF0x.st_ok_pin_reg E0 (ssA0 UP_ENTRY hi) _ 11%bv (SLit 16)); [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
  unfold ssA0. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold memA. apply Forall_cons; [|exact (po_rodata_okU ly S ((h, 16) :: U) W mem md E0 HU)].
    unfold stkA, PO_WIN. apply (region_ok_stack tfibsegs E0 _ 2 sp0 (- 64)); [exact E02 | lia | lia |].
    intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents. unfold memA, stkA, po_rodata, icpt_rodata, ro_region, extent_of_region, PO_WIN.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E02.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E02, E010.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia; first [exact Hal16 | exact H8 | idtac]. }
eapply SRr_bind; [apply (po_phase W E0 _ _ _ _ _ HS0 (ur_A hi))|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
change (st_ok tfibsegs E0 (ueA hi) (restrict H msA)) in HSA.
assert (MEQA : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ms_mem msA z = mem z).
{ intros z Hz. apply HFA. intros Hin. pose proof (winsA_cases E0 _ _ (uA_win hi) Hin) as X. rewrite E02 in X. unfold PO_WIN in X. lia. }
clear HFA HFrA.
destruct (uA_facts hi) as (PA1 & PA2 & PA3 & PA4 & PA5 & PA6).
pose proof (st_ok_restrict_mkst tfibsegs H E0 _ _ HSA PA2) as HshA. rewrite PA1 in HshA.
assert (RDA : forall (r : bv 5) v, reg_is (ueA hi) (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E0 (ueA hi) msA r HSA). }
assert (G9A : getr (ms_regs msA) 19 = Z_to_bv 64 SH).
{ rewrite (RDA 19%bv _ PA4). rewrite (XS0_denot E0 0 h E010) by lia. rewrite Z.add_0_r. reflexivity. }
assert (G10A : getr (ms_regs msA) 10 = Z_to_bv 64 SH).
{ rewrite (RDA 10%bv _ PA5). rewrite (XS_denot E0 0 h E010) by lia. rewrite Z.add_0_r. reflexivity. }
(* ---- phase B: the head's shadow bytes as a region at the new atom aSH, the end byte as atom aV ---- *)
set (EB := AE2y.Env regs [SH; VB]).
assert (AGR : env_agree 32 E0 EB) by (unfold E0, EB, AE2y.Env; cbn [map]; apply (env_agree_Ereg_app' regs [] [Z_to_bv 64 SH; Z_to_bv 64 VB] 32); cbn; lia).
assert (EBreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EB i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EB2 : bv_unsigned (ew EB 2) = sp0) by (rewrite (EBreg 2%nat 2%bv eq_refl); reflexivity).
assert (EB10 : bv_unsigned (ew EB 10) = h) by (rewrite (EBreg 10%nat 10%bv eq_refl), G10; unfold w64; apply wz; lia).
assert (UB32 : bv_unsigned (ew EB 32) = SH) by (pose proof (AE2y.Env_x regs [SH; VB] 0 SH eq_refl) as X; cbn [Nat.add] in X; change (AE2y.Env regs [SH; VB]) with EB in X; rewrite X; apply wz; clear - SHb; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (UB33 : bv_unsigned (ew EB 33) = VB) by (pose proof (AE2y.Env_x regs [SH; VB] 1 VB eq_refl) as X; cbn [Nat.add] in X; change (AE2y.Env regs [SH; VB]) with EB in X; rewrite X; apply wz; lia).
assert (VM1 : forall a v, ~ (sp0 - 64 <= a < sp0) -> 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a = Some v ->
  val_mem tfibsegs (mrestrict H (ms_mem msA)) a 1 v).
{ intros a v Ha Hr Hv. apply (AF0x.val_mem_ext (mrestrict H mem)); [| apply val_mem1_of_aview; exact Hv].
  intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite MEQA; [reflexivity|]. rewrite wz by lia. lia. }
assert (SHnS : forall j, 0 <= j < 3 -> ~ (sp0 - 64 <= SH + j < sp0)) by (intros j Hj; clear - SHb Hslo Lbeg Hj; lia).
assert (SHr64 : forall j, 0 <= j < 3 -> TFIB_IMG_END <= SH + j < 2 ^ 64) by (intros j Hj; clear - SHb Hj; unfold TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *; lia).
rewrite HshA in HSA. rewrite restrict_mkst_fx in HSA.
assert (HSB0 : st_ok tfibsegs EB (uB hi) (restrict H (mkst (ms_regs msA) (Z_to_bv 64 U_LDA) (ms_mem msA) (seg_rom tfibsegs)))).
{ rewrite <- (uB_eq hi). unfold upB. rewrite PA1. rewrite restrict_mkst_fx.
  apply st_ok_add_fact0; [| reflexivity | unfold aV; rewrite UB33; lia].
  apply st_ok_add_fact0; [| reflexivity | unfold aSH; rewrite UB32; exact SHr].
  apply (st_ok_set_regs_mem tfibsegs 32 E0 EB (ueA hi) (ms_regs msA) (ms_regs msA) (Z_to_bv 64 U_LDA) U_LDA
    (mrestrict H (ms_mem msA)) (mrestrict H (ms_mem msA)) (memB (ueA hi) 247 247) updUB HSA AGR PA3).
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - unfold updUB. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
    + rewrite G9A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
    + rewrite G10A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
  - pose proof (st_ok_agree tfibsegs 32 E0 EB (ueA hi) _ HSA AGR PA3) as HSA'.
    pose proof (st_ok_mem_ok tfibsegs EB (ueA hi) _ HSA') as (WFA & ROKA & PDA).
    split; [rewrite memUB_eq; vm_compute; reflexivity|]. split.
    + unfold memB. rewrite PA6 in ROKA. apply Forall_cons; [exact (Forall_inv ROKA)|]. apply Forall_cons; [|exact (Forall_inv_tail ROKA)].
      unfold rSH, aSH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UB32.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (AF0x.apresent_writable H); [apply SHr64; lia|].
        apply (AF0x.apresent_same H mem); [apply MEQA; rewrite wz by (pose proof (SHr64 o ltac:(lia)); lia); apply SHnS; lia|].
        exact (vis_apresent' H mem (SH + o) 247 (SHr64 o ltac:(lia)) (HV0 o ltac:(lia))). }
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val tfibsegs EB _ SH 0 1%N (SLit 247) 247); [reflexivity | cbn; lia | cbn; lia |].
        apply VM1; [apply SHnS; lia | pose proof (SHr64 0 ltac:(lia)); lia | exact (HV0 0 ltac:(lia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 1 1%N (SLit 247) 247); [reflexivity | cbn; lia | cbn; lia |].
        apply VM1; [apply SHnS; lia | pose proof (SHr64 1 ltac:(lia)); lia | exact (HV0 1 ltac:(lia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 2 1%N (SOff aV 0) VB); [cbn [sv_denot]; unfold aV; rewrite UB33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        apply VM1; [apply SHnS; lia | pose proof (SHr64 2 ltac:(lia)); lia | exact HVB].
    + apply pairwise_disjoint_of_extents. rewrite memUB_eq. let l' := eval vm_compute in memUBc in change memUBc with l'.
      unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EB2, ?UB32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - SHb Hsp Hslo Lbeg. unfold kLowShadowBeg, kHighMemBeg in *. repeat split; lia. }
rewrite HshA.
eapply SRr_bind; [apply (po_phase W EB (uB hi) _ _ _ _ HSB0 (ur_B hi))|].
cbv beta. intros Wb cb _ (-> & msB & matB & -> & HSB & HFB & HFrB). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (ueB hi) (restrict H msB)) in HSB.
assert (MEQB : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msB z = ms_mem msA z).
{ intros z Hz1 Hz2. apply HFB. intros Hin. pose proof (wins_cases EB _ _ (uB_win hi) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. lia. }
clear HFB HFrB.
destruct (uB_facts hi) as (PB1 & PB2 & PB3 & PB4).
pose proof (st_ok_restrict_mkst tfibsegs H EB _ _ HSB PB2) as HshB. rewrite PB1 in HshB.
assert (RDB : forall (r : bv 5) v, reg_is (ueB hi) (bv_unsigned r) v = true -> getr (ms_regs msB) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (ueB hi) msB r HSB). }
assert (G18B : getr (ms_regs msB) 9 = Z_to_bv 64 (SH + 2)).
{ rewrite (RDB 9%bv _ PB4). rewrite (XS0_denot EB 16 h EB10) by lia. rewrite <- SH2. reflexivity. }
rewrite HshB in HSB. rewrite restrict_mkst_fx in HSB.
assert (HSC0 : st_ok tfibsegs EB (uC hi) (restrict H (mkst (ms_regs msB) (Z_to_bv 64 U_LDB) (ms_mem msB) (seg_rom tfibsegs)))).
{ rewrite <- (uC_eq hi). unfold upC. rewrite PB1. rewrite restrict_mkst_fx.
  apply (st_ok_set_regs_mem tfibsegs 34 EB EB (ueB hi) (ms_regs msB) (ms_regs msB) (Z_to_bv 64 U_LDB) U_LDB
    (mrestrict H (ms_mem msB)) (mrestrict H (ms_mem msB)) (ss_mem (ueB hi)) [((9%bv : bv 5), SOff aSH 2)] HSB).
  - split; [intros; reflexivity | reflexivity].
  - exact PB3.
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G18B. cbn [sv_denot]. unfold aSH. rewrite UB32. reflexivity.
  - exact (st_ok_mem_ok tfibsegs EB (ueB hi) _ HSB). }
rewrite HshB.
eapply SRr_bind; [apply (po_phase W EB (uC hi) _ _ _ _ HSC0 (ur_C hi))|].
cbv beta. intros Wc cc _ (-> & msD & matC & -> & HSDf & HFC & HFrC). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (ueC hi) (restrict H msD)) in HSDf.
assert (MEQC : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = ms_mem msB z).
{ intros z Hz1 Hz2. apply HFC. intros Hin. pose proof (wins_cases EB _ _ (uC_win hi) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. lia. }
clear HFC HFrC.
assert (MEQ : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = mem z).
{ intros z Hz1 Hz2. rewrite (MEQC z Hz1 Hz2), (MEQB z Hz1 Hz2). exact (MEQA z Hz1). }
clear MEQA MEQB MEQC.
destruct (uC_facts hi) as (PD1 & PD2 & RVD & NR0 & NR1).
eapply (SRr_ret_at tfibsegs tbl_po tbl_po_ok Hwx W EB); [exact HSDf | exact RVD | rewrite PD1; exact up_ret_word |].
intros mat'. rewrite wvb_wvb.
assert (RDD : forall (r : bv 5) v, reg_is (ueC hi) (bv_unsigned r) v = true -> getr (ms_regs msD) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (ueC hi) msD r HSDf). }
assert (RKD : forall rz, In rz KEPT -> getr (ms_regs msD) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. unfold final_ok in PD2. apply andb_prop in PD2 as [_ FB]. rewrite forallb_forall in FB. specialize (FB rz Hrz). cbn beta in FB.
  assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; unfold KEPT in Hrz; cbn in Hrz; lia).
  assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
  rewrite (RDD (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB].
  cbn [sv_denot]. rewrite (EBreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RKD 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs msD) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs msD), (ms_mem msD), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs EB (ueC hi) _ HSDf) as (_ & ROKD & _). change (ms_mem (restrict H msD)) with (mrestrict H (ms_mem msD)) in ROKD.
pose proof (proj1 (Forall_forall _ _) ROKD _ (nth_error_In _ _ NR1)) as OKSH.
destruct uSH_shape as (BSH & WSH1 & WSH2 & CSH0 & CSH1). destruct uSTK_shape as (BS0 & WS01 & WS02).
unfold region_ok in OKSH. rewrite BSH in OKSH. cbn [base_val] in OKSH. unfold aSH in OKSH. rewrite UB32 in OKSH.
destruct OKSH as (_ & _ & _ & CHSH).
assert (P0 : aview tfibsegs H (ms_mem msD) SH = Some 0).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 0 1%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHSH _ CSH0) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VMx.
  rewrite Z.add_0_r in VMx. exact (aview_of_val_mem1 H (ms_mem msD) SH 0 VMx ltac:(lia)). }
assert (P1 : aview tfibsegs H (ms_mem msD) (SH + 1) = Some 0).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 1 1%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHSH _ CSH1) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VMx.
  exact (aview_of_val_mem1 H (ms_mem msD) (SH + 1) 0 VMx ltac:(lia)). }
assert (PW : forall b, (sp0 - 64 <= b < sp0 \/ SH <= b < SH + 2) -> apresent H (ms_mem msD) b).
{ intros b [Hbw|Hbw].
  - apply (st_ok_window_apresent H EB (ueC hi) msD 0 uSTK b HSDf NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EB2; unfold PO_WIN; lia | unfold TFIB_IMG_END; lia].
  - apply (st_ok_window_apresent H EB (ueC hi) msD 1 uSH b HSDf NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite UB32; lia | pose proof (SHr64 0 ltac:(lia)); pose proof (SHr64 2 ltac:(lia)); lia]. }
assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> ~ (SH <= a < SH + 2) -> aview tfibsegs H (ms_mem msD) a = aview tfibsegs H mem a).
{ intros a Ha N1 N2. apply AF0x.aview_same. apply MEQ; rewrite wz by exact Ha; assumption. }
assert (HB' : forall a, in_band_rw a -> H (w64 a) = true -> ms_mem msD (w64 a) = mem (w64 a)).
{ intros a Hbd Hh'. unfold w64 in *. assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hbd; lia).
  apply MEQ; rewrite wz by exact Ha; intros Hin; [ pose proof (PW a (or_introl Hin)) as (Hx & _) | pose proof (PW a (or_intror Hin)) as (Hx & _) ]; rewrite Hx in Hh'; discriminate Hh'. }
assert (HARU : ARU tfibsegs B ly S U W (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat' md)).
{ apply (ARU_unpoison_step tfibsegs B LAWS ly S U W mem md h (ms_mem msD) _ (sp0 - 64) sp0 HU); [lia | lia | exact FR | | exact P0 | exact P1 | apply MF | apply MF | apply MF | exact HB'].
  intros a Ha. apply AE2y.aview_some_of_apresent. apply PW. left. exact Ha. }
split; [exact HARU|].
split; [|split; [apply with_vm_backing_same|split; [exact P0|split; [exact P1|split; [exact FR|]]]]].
- intros r Hr. unfold acallee_saved in Hr. apply RKD. clear - Hr. unfold KEPT. cbn. lia.
- split.
  + intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [L|L].
    * apply (AF0x.apresent_same H mem); [apply MEQ; rewrite wz by lia; lia | apply Hpres; lia].
    * apply PW. left. lia.
  + intros a HPa. rewrite (AE2y.apresent_mod _ (ms_mem msD) a). rewrite (AE2y.apresent_mod _ mem a) in HPa.
    assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (a' := a mod 2 ^ 64) in *. clearbody a'.
    destruct (Z_lt_le_dec a' (sp0 - 64)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L2|L2]]; [| apply PW; left; lia |].
    all: destruct (Z_lt_le_dec a' SH) as [S1|S1]; [|destruct (Z_lt_le_dec a' (SH + 2)) as [S2|S2]].
    all: first [apply PW; right; lia | apply (AF0x.apresent_same H mem); [apply MEQ; rewrite wz by lia; lia | exact HPa]].
Qed.
End f.
