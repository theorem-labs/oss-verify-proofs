(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 175 of its 236 lines of code are new or changed and 1271 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the name a selector picked (Sel.v w_name: NULL, g_names[k] or odd[j]) as a
   string argument of a callee, at any state of the walk's journal (shared by op_read, op_write,
   op_mark, which hand the name to model_read / model_write / index_of / reac_link_alias_read / _write /
   mark_quietly).
   - lf_name_core: the name is a C string at its pointer, at most 11 bytes, in application memory below the image
     top, addressable with its shadow visible, the bytes up to its 8-byte granule end present, and each of its
     bytes an image byte that is no runtime static and no errno byte (the pattern of Mdl.v lf_tab_core);
   - lf_name_strcmp: the strcmp wrapper's facts (index_of_c.v astrcmp_arg) at a call with sp = lf_sp1 cx;
   - lf_name_akb: its bytes are akb bytes of any state (a read set's image clause).
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro PcapRelroA YC4b link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi
  LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR
  LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c index_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the six odd strings, each a kp_kstr_b string of the image (kp_img_b checks four of them) *)
Lemma nm_odd_checks :
  forallb (fun i => let e := nth i KP_ODD (0, []) in kp_kstr_b tfibsegs Tfib_owned_static TFIB_ERRNO (fst e) (snd e))
    (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nm_zb_neq : forall z, 0 < z < 256 -> Z_to_bv 8 z <> Z_to_bv 8 0.
Proof.
  intros z Hz H. apply (f_equal bv_unsigned) in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 8) with 256 in H.
  rewrite (Z.mod_small z) in H by lia. rewrite Z.mod_0_l in H by lia. lia.
Qed.

(* g_names[k]'s text: "nl" and k's digits, no NUL, at most 4 bytes *)
Lemma nm_gname_nz : forall k, 0 <= k < 100 -> ~ In (zb 0) (lf_gname k).
Proof.
  intros k Hk H. unfold lf_gname in H. apply in_map_iff in H as (z & Hz & Hin).
  apply (nm_zb_neq z); [|exact Hz].
  unfold lf_gname_z, lf_dec2 in Hin.
  pose proof (Z.div_pos k 10 ltac:(lia) ltac:(lia)) as Hq0.
  pose proof (Z.mod_pos_bound k 10 ltac:(lia)) as Hr.
  assert (Hd : k / 10 < 10) by (apply Z.div_lt_upper_bound; lia).
  destruct (k <? 10) eqn:E; cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [lia|]); destruct Hin.
Qed.

Lemma nm_gname_len : forall k, (length (lf_gname k) <= 4)%nat.
Proof. intros k. unfold lf_gname, lf_gname_z, lf_dec2. rewrite length_map. destruct (k <? 10); cbn [length]; lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma nm_odd_here : forall j, (j < 6)%nat ->
  kp_kstr_b SEGS (as_owned_static B) (as_errno B) (fst (nth j KP_ODD (0, []))) (snd (nth j KP_ODD (0, []))) = true.
Proof.
  intros j Hj. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB).
  exact (proj1 (forallb_forall _ _) nm_odd_checks j ltac:(apply in_seq; lia)).
Qed.

(* the tail of a string through its granule's end, from a kp_somes_b check after its NUL *)
Lemma nm_tail_of_somes : forall (W : world SEGS) mem p n,
  kp_somes_b SEGS (p + n + 1) (Z.to_nat ((- (p + n + 1)) mod 8)) = true ->
  forall a, p + n < a < p + n - (p + n) mod 8 + 8 -> ard SEGS (rdW W mem) a <> None.
Proof.
  intros W mem p n Hsl a Ha.
  assert (Hk : 0 <= a - (p + n + 1) < (- (p + n + 1)) mod 8).
  { pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)).
    assert (Eq8 : (- (p + n + 1)) mod 8 = 7 - (p + n) mod 8).
    { symmetry. apply Z.mod_unique_pos with (q := - ((p + n) / 8) - 1); [lia|].
      pose proof (Z.div_mod (p + n) 8 ltac:(lia)). lia. }
    rewrite Eq8. lia. }
  destruct (kp_somes_mbyte SEGS (rdW W mem) _ _ Hsl (Z.to_nat (a - (p + n + 1)))
    ltac:(rewrite <- (Z2Nat.id ((- (p + n + 1)) mod 8)) in Hk by lia; lia)) as (bb & Hbb).
  rewrite ard_aview. unfold aview.
  replace (p + n + 1 + Z.of_nat (Z.to_nat (a - (p + n + 1)))) with a in Hbb by lia.
  rewrite Hbb. discriminate.
Qed.

(* a kp_kstr_b string of the image, as a string argument *)
Lemma nm_kstr_core : forall ly S (W : world SEGS) mem mdl q l,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  kp_kstr_b SEGS (as_owned_static B) (as_errno B) q l = true ->
  let n := Z.of_nat (length (map (Z_to_bv 8) l)) in
  0 < q /\ amem_range q (n + 1) /\
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF q (n + 1) /\
  shadow_hull_vis (ard SEGS (rdW W mem)) q (n + 1) /\
  (forall a, q + n < a < q + n - (q + n) mod 8 + 8 -> ard SEGS (rdW W mem) a <> None) /\
  q + n + 8 <= YImgTop.IMG_TOP /\
  (forall y, q <= y < q + n + 1 ->
     in_img SEGS y /\ ~ Exists (in_zr y) (as_owned_static B) /\ ~ (as_errno B <= y < as_errno B + 4)).
Proof.
  intros ly S W mem mdl q l HAR HRO Hks n. pose proof HAR as (M & _).
  destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hks) as (_ & Hpt0 & Hptl).
  unfold n. rewrite length_map. clear n.
  unfold kp_kstr_b in Hks.
  repeat match type of Hks with (_ && _)%bool = true => apply andb_prop in Hks as [Hks ?] end.
  match goal with Hh : kp_hull_b _ _ = true |- _ => rename Hh into Hh0 end.
  match goal with Hh : kp_ra_b _ _ = true |- _ => rename Hh into Hra0 end.
  match goal with Hh : kp_bytes_b _ _ _ _ _ = true |- _ => rename Hh into Hby end.
  match goal with Hh : kp_somes_b _ _ _ = true |- _ => rename Hh into Hsl0 end.
  split; [exact Hpt0|].
  split; [unfold amem_range; left; unfold LA_G_NL, kLowMemEnd in *; lia|].
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M Hra0)|].
  split; [rewrite ard_aview; exact (kp_hull B TB ly S _ _ _ M Hh0)|].
  split; [exact (nm_tail_of_somes W mem q (Z.of_nat (length l)) Hsl0)|].
  split; [unfold LA_G_NL, YImgTop.IMG_TOP in *; lia|].
  intros y Hy. pose proof (kp_bytes_place B HSEGS _ _ Hby (Z.to_nat (y - q))) as Hr.
  rewrite length_app in Hr. cbn [length] in Hr.
  specialize (Hr ltac:(lia)). replace (q + Z.of_nat (Z.to_nat (y - q))) with y in Hr by lia.
  exact Hr.
Qed.

(* the name a selector picked, as a string *)
Lemma lf_name_core : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs s x,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  w_name s (Some x) ->
  acstr_at SEGS (rdW W mem) s x /\ (length x <= 11)%nat /\
  0 < s /\ amem_range s (Z.of_nat (length x) + 1) /\
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF s (Z.of_nat (length x) + 1) /\
  shadow_hull_vis (ard SEGS (rdW W mem)) s (Z.of_nat (length x) + 1) /\
  (forall a, s + Z.of_nat (length x) < a < s + Z.of_nat (length x) - (s + Z.of_nat (length x)) mod 8 + 8 ->
     ard SEGS (rdW W mem) a <> None) /\
  s + Z.of_nat (length x) + 8 <= YImgTop.IMG_TOP /\
  (forall y, s <= y < s + Z.of_nat (length x) + 1 ->
     in_img SEGS y /\ ~ Exists (in_zr y) (as_owned_static B) /\ ~ (as_errno B <= y < as_errno B + 4)).
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs s x HB HJ HRO HD Hw.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (_ & _ & _ & _ & _ & _ & HAR).
  pose proof HAR as (M & _).
  pose proof HB as (_ & _ & _ & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & _).
  destruct Hw as [(_ & Hn) | [(kk & Hk & -> & Hx) | (j & Hj & -> & Hx)]]; [discriminate| |].
  - (* g_names[kk] *)
    injection Hx as Hx; subst x.
    destruct HD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dgn & _).
    destruct (Dgn kk Hk) as (rest & Hab & Hl8).
    pose proof (nm_gname_len kk) as Hlen. rewrite length_app in Hl8. cbn [length] in Hl8.
    assert (Hcs : acstr_at SEGS (rdW W mem) (LA_G_NAMES + 8 * kk) (lf_gname kk)).
    { split; [|exact (nm_gname_nz kk ltac:(lia))].
      destruct Hab as (A0 & A1 & A2). split; [exact A0|]. split.
      - rewrite length_app in *. cbn [length] in *. lia.
      - intros ii Hii. rewrite length_app in Hii. cbn [length] in Hii.
        rewrite (A2 ii) by (rewrite length_app; cbn [length]; lia).
        destruct (Nat.lt_ge_cases ii (length (lf_gname kk))) as [Hl | Hl].
        + rewrite !nth_error_app1 by lia. reflexivity.
        + assert (ii = length (lf_gname kk)) by lia. subst ii.
          rewrite !nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    pose proof md_gnames_checks as GC. apply andb_prop in GC as [GR GH].
    set (p := LA_G_NAMES + 8 * kk) in *.
    assert (Hp8 : p mod 8 = 0).
    { unfold p, LA_G_NAMES. replace (0x62fac0 + 8 * kk) with ((810840 + kk) * 8) by lia. apply Z_mod_mult. }
    assert (Hpl : LA_G_NAMES <= p /\ p + 8 <= LA_G_NAMES + 512) by (unfold p, LA_G_NAMES in *; lia).
    split; [exact Hcs|]. split; [lia|].
    split; [unfold p, LA_G_NAMES; lia|].
    split; [unfold amem_range; left; unfold LA_G_NAMES, kLowMemEnd in *; lia|].
    split; [rewrite ard_aview; apply (md_ra_sub _ LA_G_NAMES 512); [exact (kp_ra B TB ly S _ _ _ M GR) | lia | lia]|].
    split; [rewrite ard_aview; apply (md_hull_sub _ LA_G_NAMES 512); [exact (kp_hull B TB ly S _ _ _ M GH) | lia | lia | lia]|].
    split.
    { intros a Ha. pose proof md_gnames_somes as GS. rewrite <- HSEGS in GS.
      assert (Hm : (p + Z.of_nat (length (lf_gname kk))) mod 8 = Z.of_nat (length (lf_gname kk))).
      { rewrite Z.add_mod, Hp8 by lia. rewrite Z.add_0_l, !Z.mod_mod by lia. apply Z.mod_small. lia. }
      rewrite Hm in Ha.
      destruct (kp_somes_mbyte SEGS (rdW W mem) LA_G_NAMES 512 GS (Z.to_nat (a - LA_G_NAMES)) ltac:(unfold LA_G_NAMES in *; lia))
        as (bb & Hbb).
      rewrite ard_aview. unfold aview. replace (LA_G_NAMES + Z.of_nat (Z.to_nat (a - LA_G_NAMES))) with a in Hbb by lia.
      rewrite Hbb. discriminate. }
    split; [unfold LA_G_NAMES, YImgTop.IMG_TOP in *; lia|].
    intros y Hy. apply IMG. right; left. unfold LA_G_NAMES, G_NAMES_SIZE in *; lia.
  - (* odd[j] *)
    rewrite (sel_odd_strs j Hj) in Hx. injection Hx as Hx; subst x.
    assert (Hs : nth j ODD_PTRS 0 = fst (nth j KP_ODD (0, []))).
    { unfold ODD_PTRS. do 6 (destruct j as [|j]; [reflexivity|]). lia. }
    assert (Hl11 : (length (map (Z_to_bv 8) (snd (nth j KP_ODD (0%Z, [])))) <= 11)%nat).
    { rewrite length_map. do 6 (destruct j as [|j]; [cbn; lia|]). lia. }
    rewrite Hs. split; [|split; [exact Hl11 | exact (nm_kstr_core ly S W mem mdl _ _ HAR HRO (nm_odd_here j Hj))]].
    exact (proj1 (kp_kstr_acstr B (w_H W) mem _ _ HRO (nm_odd_here j Hj))).
Qed.

(* the name as the strcmp wrapper's argument at a call made with sp = lf_sp1 cx *)
Lemma lf_name_strcmp : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs s x (regs : bvmap 5 word) K,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  spZ regs = lf_sp1 cx -> 0 <= K <= LLVMF_STK - 448 ->
  w_name s (Some x) ->
  astrcmp_arg SEGS regs K (rdW W mem) s x.
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs s x regs K HB HJ HRO HD Hsp HK Hw.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (_ & Hceil & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (Hs1 & _ & Hlo & _).
  destruct (lf_name_core cx fp ly S W mem mdl k md mk kbs mbs gbs s x HB HJ HRO HD Hw)
    as (_ & Hl & C1 & C3 & C4 & C5 & CT & C6 & _).
  split; [exact C1|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
  split; [|exact CT].
  unfold apart_frame. left. rewrite Hsp. unfold YImgTop.IMG_TOP, LLVMF_STK in *. lia.
Qed.

(* the name's bytes through its NUL, as akb *)
Lemma lf_name_akb : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs s x ly' S' slo shi y,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  w_name s (Some x) -> s <= y <= s + Z.of_nat (length x) ->
  akb SEGS B ly' S' slo shi y.
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs s x ly' S' slo shi y HB HJ HRO HD Hw Hy.
  destruct (lf_name_core cx fp ly S W mem mdl k md mk kbs mbs gbs s x HB HJ HRO HD Hw)
    as (_ & _ & _ & _ & _ & _ & _ & _ & C7).
  destruct (C7 y ltac:(lia)) as (I1 & I2 & I3).
  right; right; left. exact (conj I1 (conj I2 I3)).
Qed.

End b.
End a.
