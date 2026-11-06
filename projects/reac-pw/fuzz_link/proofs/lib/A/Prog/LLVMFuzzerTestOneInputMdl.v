(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 516 of its 573 lines of code are new or changed and 347 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the parts of
   model_read's and model_write's Pre (lib/A/Prog/model_read_c.v, model_write_c.v) that do not depend on the call
   site, at any call made with a0 = the model block and sp = lf_sp1 cx on the walk's journal; shared by the arm
   lanes (op_unmark 0x82fd8 / 0x83008, op_mark 0x833d4, op_read 0x8368c, op_write 0x83858).
   - lf_tab_strcmp: every interface-table name, as the strcmp wrapper asks (astrcmp_arg), and in the image;
   - lf_mdl_block: the model block and g_nl's ranges the two Pres ask;
   - lf_mark_strcmp: a mark slot of the model block as a name argument.
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
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c index_of_c LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

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

(* g_names' 512 bytes: addressable, and their shadow visible *)
Lemma md_gnames_checks : (kp_ra_b LA_G_NAMES 512 && kp_hull_b LA_G_NAMES 512)%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma md_gnames_somes : kp_somes_b tfibsegs LA_G_NAMES 512 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma md_hull_sub : forall (rd : reader) x n y k, shadow_hull_vis rd x n -> x <= y -> y + k <= x + n -> 0 < k ->
  shadow_hull_vis rd y k.
Proof.
  intros rd x n y k H Hxy Hyk Hk s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + y / 8) / 8)
    by (apply Z.div_le_mono; [lia | apply Z.add_le_mono_l, Z.div_le_mono; lia]).
  assert (A2 : (SHADOW_OFF + (y + k - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8)
    by (apply Z.div_le_mono; [lia | apply Z.add_le_mono_l, Z.div_le_mono; lia]).
  lia.
Qed.

Lemma md_ra_sub : forall (rd : reader) x n y k, range_addressable rd SHADOW_OFF x n -> x <= y -> y + k <= x + n ->
  range_addressable rd SHADOW_OFF y k.
Proof. intros rd x n y k H H1 H2 z Hz. apply H. lia. Qed.

(* the bytes a kp_bytes_b check reads: read-only, not a runtime static, not errno *)
Lemma kp_bytes_place : forall a l, kp_bytes_b SEGS (as_owned_static B) (as_errno B) a l = true ->
  forall i, (i < length l)%nat ->
  in_img SEGS (a + Z.of_nat i) /\ ~ Exists (in_zr (a + Z.of_nat i)) (as_owned_static B) /\
  ~ (as_errno B <= a + Z.of_nat i < as_errno B + 4).
Proof.
  intros a l Hb i Hi.
  pose proof (kp_forallb_seq _ _ Hb i Hi) as Hx. cbv beta in Hx.
  apply andb_prop in Hx as [Hro _]. unfold kp_ro_b in Hro.
  apply andb_prop in Hro as [Hro Herr]. apply andb_prop in Hro as [Hseg Hown].
  set (x := a + Z.of_nat i) in *.
  split; [|split].
  - apply orb_prop in Hseg as [Hs | Hs].
    + apply existsb_exists in Hs as (s & Hin & Hs). apply andb_prop in Hs as [Hs Hhi]. apply andb_prop in Hs as [_ Hlo].
      apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. exists s. split; [exact Hin | lia].
    + apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      exact (ar_relro_img HSEGS x ltac:(lia)).
  - intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz. apply negb_true_iff in Hown.
    assert (Hx : existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) (as_owned_static B) = true)
      by (apply existsb_exists; exists r; split; [exact Hr|];
          apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hx in Hown. discriminate.
  - intros Hx. apply negb_true_iff in Herr.
    assert (Ht : ((as_errno B <=? x) && (x <? as_errno B + 4))%bool = true)
      by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Ht in Herr. discriminate.
Qed.

(* an interface-table name at its pointer: the strcmp wrapper's facts but the frame, below g_nl's end, in the image *)
Lemma lf_tab_core : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  forall i n2 ix p, nth_error lf_tab i = Some (n2, ix) ->
    au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
    0 < p /\ Z.of_nat (length n2) + 1 < 2 ^ 32 /\ amem_range p (Z.of_nat (length n2) + 1) /\
    range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF p (Z.of_nat (length n2) + 1) /\
    shadow_hull_vis (ard SEGS (rdW W mem)) p (Z.of_nat (length n2) + 1) /\
    (forall a, p + Z.of_nat (length n2) < a < p + Z.of_nat (length n2) - (p + Z.of_nat (length n2)) mod 8 + 8 ->
       ard SEGS (rdW W mem) a <> None) /\
    p + Z.of_nat (length n2) + 1 <= YImgTop.IMG_TOP /\
    (forall x, p <= x < p + Z.of_nat (length n2) + 1 ->
       in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)).
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs HB HJ HRO HD i n2 ix p Hn Hp Rp.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof HAR as (M & _).
  pose proof HB as (_ & _ & _ & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & _).
  destruct HD as (_ & _ & Htab & _ & _ & _ & _ & _ & _ & _ & _ & Difp & _).
  pose proof Htab as (_ & _ & Htent).
  destruct (Htent i n2 ix Hn) as (_ & p0 & Hp0 & _ & Hs0 & _).
  assert (Hi64 : (i < 64)%nat).
  { assert (Hl : (i < length lf_tab)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
    pose proof lf_tab_len as LL. lia. }
  destruct (Difp (Z.of_nat i) ltac:(lia)) as (qq & Hqq & Hqlo & Hqhi).
  pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as Ep. pose proof (kp_vm8_mod _ _ _ _ _ Hp0 Hqq) as E0.
  rewrite (Z.mod_small p) in Ep by exact Rp.
  assert (R0 : 0 <= p0 < 2 ^ 64) by (destruct Hs0 as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; clia).
  rewrite (Z.mod_small p0) in E0 by exact R0.
  assert (Epp : p = p0) by congruence. rewrite <- Epp in Hs0. clear E0.
  pose proof (eq_refl (as_owned_static B)) as Ho. pose proof (eq_refl (as_errno B)) as He.
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with Hh : forallb _ (seq 1 4) = true |- _ => rename Hh into KOdd end.
  pose proof (lf_tab_names_short) as Hsh. rewrite forallb_forall in Hsh.
  specialize (Hsh (n2, ix) (nth_error_In _ _ Hn)). apply Nat.leb_le in Hsh. cbn [fst] in Hsh.
  destruct (Z_lt_le_dec (Z.of_nat i) 60) as [Hlt | Hge].
  - (* a name in g_names *)
    rewrite (Hqlo Hlt) in Ep. rewrite Z.mod_small in Ep by (unfold LA_G_NAMES; clia).
    assert (Hlen : (length n2 <= 4)%nat).
    { pose proof lf_tab_gnames_short as Hg. rewrite forallb_forall in Hg.
      specialize (Hg (n2, ix)). apply Nat.leb_le. apply Hg.
      apply (nth_error_In _ i). rewrite nth_error_firstn. destruct (Nat.ltb_spec i 60); [exact Hn | clia]. }
    pose proof md_gnames_checks as GC. apply andb_prop in GC as [GR GH].
    assert (Hpl : LA_G_NAMES <= p /\ p + Z.of_nat (length n2) + 1 <= LA_G_NAMES + 512)
      by (unfold LA_G_NAMES in *; clia).
    split; [unfold LA_G_NAMES in *; clia|]. split; [clia|]. split; [unfold amem_range; left; unfold LA_G_NAMES in *; clia|].
    split; [rewrite ard_aview; apply (md_ra_sub _ LA_G_NAMES 512); [exact (kp_ra B TB ly S _ _ _ M GR) | clia | clia]|].
    split; [rewrite ard_aview; apply (md_hull_sub _ LA_G_NAMES 512); [exact (kp_hull B TB ly S _ _ _ M GH) | clia | clia | clia]|].
    split.
    { intros a Ha. pose proof md_gnames_somes as GS. rewrite <- HSEGS in GS.
      assert (Hp8 : p mod 8 = 0).
      { rewrite Ep. unfold LA_G_NAMES. replace (6486720 + 8 * (Z.of_nat i + Z.of_nat i / 15)) with
          ((810840 + (Z.of_nat i + Z.of_nat i / 15)) * 8) by lia. apply Z_mod_mult. }
      assert (Hm : (p + Z.of_nat (length n2)) mod 8 = Z.of_nat (length n2)).
      { rewrite Z.add_mod, Hp8 by lia. rewrite Z.add_0_l, !Z.mod_mod by lia. apply Z.mod_small. clia. }
      rewrite Hm in Ha.
      destruct (kp_somes_mbyte SEGS (rdW W mem) LA_G_NAMES 512 GS (Z.to_nat (a - LA_G_NAMES)) ltac:(unfold LA_G_NAMES in *; clia))
        as (bb & Hbb).
      rewrite ard_aview. unfold aview. replace (LA_G_NAMES + Z.of_nat (Z.to_nat (a - LA_G_NAMES))) with a in Hbb by clia.
      rewrite Hbb. discriminate. }
    split; [unfold LA_G_NAMES, YImgTop.IMG_TOP in *; clia|].
    intros x Hx. apply IMG. right; left. unfold LA_G_NAMES, G_NAMES_SIZE in *; clia.
  - (* an odd-table name *)
    specialize (Hqhi Hge). set (j := (i - 59)%nat).
    assert (Hj : (1 <= j < 5)%nat) by (unfold j; clia).
    pose proof (proj1 (forallb_forall _ _) KOdd j ltac:(apply in_seq; clia)) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw Hks].
    pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw) as Hv.
    replace (LA_ODD + 8 * (Z.of_nat i - 59)) with (LA_ODD + 8 * Z.of_nat j) in Hqhi by (unfold j; clia).
    pose proof (kp_vm8_mod _ _ _ _ _ Hqhi Hv) as Eq.
    destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hks) as (Hst & Hpt0 & Hptl).
    assert (Hpq : p = fst (nth j KP_ODD (0, []))).
    { rewrite <- (Z.mod_small p (2 ^ 64)) by exact Rp. rewrite <- (Z.mod_small (fst (nth j KP_ODD (0, []))) (2 ^ 64))
        by (unfold LA_G_NL in Hptl; clia).
      pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as E1. rewrite E1, Eq. reflexivity. }
    rewrite Hpq in Hs0. clear Ep.
    pose proof (kp_acstr_unique _ _ _ _ _ Hs0 Hst) as En. subst n2. rewrite Hpq. rewrite length_map in *.
    unfold kp_kstr_b in Hks.
    repeat match type of Hks with (_ && _)%bool = true => apply andb_prop in Hks as [Hks ?] end.
    match goal with Hh : kp_hull_b _ _ = true |- _ => rename Hh into Hh0 end.
    match goal with Hh : kp_ra_b _ _ = true |- _ => rename Hh into Hra0 end.
    match goal with Hh : kp_bytes_b _ _ _ _ _ = true |- _ => rename Hh into Hby end.
    try rewrite length_map.
    split; [exact Hpt0|]. split; [clia|]. split; [unfold amem_range; left; unfold LA_G_NL in *; clia|].
    split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M Hra0)|].
    split; [rewrite ard_aview; exact (kp_hull B TB ly S _ _ _ M Hh0)|].
    split.
    { match goal with Hh : kp_somes_b _ _ _ = true |- _ => rename Hh into Hsl0 end.
      intros a Ha. set (q := fst (nth j KP_ODD (0, []))) in *. set (l := snd (nth j KP_ODD (0, []))) in *.
      assert (Hk : 0 <= a - (q + Z.of_nat (length l) + 1) < (- (q + Z.of_nat (length l) + 1)) mod 8).
      { pose proof (Z.mod_pos_bound (q + Z.of_nat (length l)) 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length l) + 1)) 8 ltac:(lia)).
        assert (Eq8 : (- (q + Z.of_nat (length l) + 1)) mod 8 = 7 - (q + Z.of_nat (length l)) mod 8).
        { rewrite Z.mod_eq by lia. rewrite (Z.mod_eq (q + Z.of_nat (length l))) by lia.
          assert (Hd : - (q + Z.of_nat (length l) + 1) / 8 = - ((q + Z.of_nat (length l)) / 8) - 1).
          { pose proof (Z.div_mod (q + Z.of_nat (length l)) 8 ltac:(lia)).
            pose proof (Z.mod_pos_bound (q + Z.of_nat (length l)) 8 ltac:(lia)).
            symmetry. apply Z.div_unique with (r := 7 - (q + Z.of_nat (length l)) mod 8); lia. }
          rewrite Hd. pose proof (Z.mod_eq (q + Z.of_nat (length l)) 8 ltac:(lia)). lia. }
        rewrite Eq8. lia. }
      destruct (kp_somes_mbyte SEGS (rdW W mem) _ _ Hsl0 (Z.to_nat (a - (q + Z.of_nat (length l) + 1)))
        ltac:(rewrite <- (Z2Nat.id ((- (q + Z.of_nat (length l) + 1)) mod 8)) in Hk by lia; lia)) as (bb & Hbb).
      rewrite ard_aview. unfold aview.
      replace (q + Z.of_nat (length l) + 1 + Z.of_nat (Z.to_nat (a - (q + Z.of_nat (length l) + 1)))) with a in Hbb by lia.
      rewrite Hbb. discriminate. }
    split; [unfold LA_G_NL, YImgTop.IMG_TOP in *; clia|].
    intros x Hx. pose proof (kp_bytes_place _ _ Hby (Z.to_nat (x - fst (nth j KP_ODD (0, [])))))
      as Hr. rewrite length_app in Hr. cbn [length] in Hr.
    specialize (Hr ltac:(clia)). replace (fst (nth j KP_ODD (0, [])) + Z.of_nat (Z.to_nat (x - fst (nth j KP_ODD (0, [])))))
      with x in Hr by clia.
    exact Hr.
Qed.

Lemma lf_tab_strcmp : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs (regs : bvmap 5 word) K,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  spZ regs = lf_sp1 cx -> 0 <= K <= LLVMF_STK - 448 ->
  forall i n2 ix p, nth_error lf_tab i = Some (n2, ix) ->
    au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
    astrcmp_arg SEGS regs K (rdW W mem) p n2 /\
    (forall x, p <= x < p + Z.of_nat (length n2) + 1 -> in_img SEGS x).
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs regs K HB HJ HRO HD Hsp HK i n2 ix p Hn Hp Rp.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (_ & Hceil & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (Hs1 & _ & Hlo & _).
  destruct (lf_tab_core cx fp ly S W mem mdl k md mk kbs mbs gbs HB HJ HRO HD i n2 ix p Hn Hp Rp)
    as (C1 & C2 & C3 & C4 & C5 & CT & C6 & C7).
  split; [|intros x Hx; exact (proj1 (C7 x Hx))].
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
  split; [|exact CT].
  unfold apart_frame. left. rewrite Hsp. unfold YImgTop.IMG_TOP, LLVMF_STK in *. lia.
Qed.

(* a range inside the model block: addressable, its shadow visible, in application memory, apart from the callee's
   window *)
Lemma lf_md_sub : forall cx fp ly S (W : world SEGS) mem mdl k md mk T3 (regs : bvmap 5 word) K p n,
  BASEF cx -> JRN cx fp ly S W mem mdl k -> lf_blocks B cx md mk T3 ly S (rdW W mem) ->
  spZ regs = lf_sp1 cx -> 0 <= K <= LLVMF_STK - 448 ->
  md <= p -> p + n <= md + MD_SIZE -> 0 < n ->
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF p n /\ shadow_hull_vis (ard SEGS (rdW W mem)) p n /\
  amem_range p n /\ apart_frame regs K p n.
Proof.
  intros cx fp ly S W mem mdl k md mk T3 regs K p n HB HJ Hblk Hsp HK H1 H2 H3.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (Hs1 & _ & Hlo & _).
  pose proof Hblk as (Bmd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bram & _ & Bamm & _).
  destruct (al_blocks _ _ LAWS ly S W mem mdl md MD_SIZE HAR Bmd) as (_ & Bm4096 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil. unfold MD_SIZE in *. unfold LLVMF_STK in *.
  split; [exact (md_ra_sub _ md 8856 p n Bram H1 H2)|].
  split; [rewrite ard_aview; eapply shadow_hull_vis_of_block; [eassumption | eassumption | exact Bmd | clia |
    change (req_size 8856) with 8856; clia | clia]|].
  split; [unfold amem_range in *; clia|].
  unfold apart_frame. left. rewrite Hsp. clia.
Qed.

(* the tail of a string in the model block: the rest of its last granule is readable *)
Lemma lf_md_tail : forall cx fp ly S (W : world SEGS) mem mdl k md mk T3 p n,
  BASEF cx -> JRN cx fp ly S W mem mdl k -> lf_blocks B cx md mk T3 ly S (rdW W mem) ->
  md <= p -> p + n <= md + MD_SIZE -> 0 < n ->
  forall a, p + (n - 1) < a < p + (n - 1) - (p + (n - 1)) mod 8 + 8 -> ard SEGS (rdW W mem) a <> None.
Proof.
  intros cx fp ly S W mem mdl k md mk T3 p n HB HJ Hblk H1 H2 H3 a Ha.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (_ & _ & _ & _ & _ & _ & HAR).
  pose proof Hblk as (Bmd & _ & _ & _ & _ & _ & Bm16 & _).
  destruct (al_blocks _ _ LAWS ly S W mem mdl md MD_SIZE HAR Bmd) as (_ & _ & _ & _ & Hpres & _).
  change (req_size MD_SIZE) with 8856 in Hpres. unfold MD_SIZE in *.
  assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc8); rewrite Hc8;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  assert (Hg : p + (n - 1) - (p + (n - 1)) mod 8 + 8 <= md + 8856).
  { pose proof (Z.div_mod (p + (n - 1)) 8 ltac:(lia)) as D. pose proof (Z.div_mod md 8 ltac:(lia)) as Dm.
    rewrite Hmd8, Z.add_0_r in Dm.
    assert (Q : (p + (n - 1)) / 8 < md / 8 + 1107) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite ard_aview. apply aview_some_of_apresent. apply (proj1 (Hpres a ltac:(lia))).
Qed.

(* the model block and g_nl's ranges the two Pres ask *)
Lemma lf_mdl_block : forall cx fp ly S (W : world SEGS) mem mdl k md mk T3 (regs : bvmap 5 word) K,
  BASEF cx -> JRN cx fp ly S W mem mdl k -> lf_blocks B cx md mk T3 ly S (rdW W mem) ->
  spZ regs = lf_sp1 cx -> 0 <= K <= LLVMF_STK - 448 ->
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length lf_tab)) /\
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length lf_tab)) /\
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF md MD_SIZE /\
  shadow_hull_vis (ard SEGS (rdW W mem)) md MD_SIZE /\ amem_range md MD_SIZE /\
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF (LA_G_NL + NK_CHUNK) NK_N_CHUNKS /\
  shadow_hull_vis (ard SEGS (rdW W mem)) (LA_G_NL + NK_CHUNK) NK_N_CHUNKS /\
  apart_gnl LA_G_NL md MD_SIZE /\ apart_frame regs K md MD_SIZE.
Proof.
  intros cx fp ly S W mem mdl k md mk T3 regs K HB HJ Hblk Hsp HK.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (_ & _ & _ & _ & _ & _ & HAR).
  destruct (zsh_gnl_ard B TB SEGS ly S W mem mdl HAR) as (Gra & Ghv).
  destruct (lf_md_sub cx fp ly S W mem mdl k md mk T3 regs K md MD_SIZE HB HJ Hblk Hsp HK ltac:(lia) ltac:(lia)
    ltac:(unfold MD_SIZE; lia)) as (R1 & R2 & R3 & R4).
  pose proof Hblk as (_ & _ & _ & _ & _ & _ & _ & _ & Bmt & _).
  rewrite lf_tab_len.
  split; [apply (md_ra_sub _ LA_G_NL NK_SIZE); [exact Gra | unfold NK_IF_NAME; lia | unfold NK_IF_NAME, NK_SIZE; lia]|].
  split; [apply (md_ra_sub _ LA_G_NL NK_SIZE); [exact Gra | unfold NK_IF_INDEX; lia | unfold NK_IF_INDEX, NK_SIZE; lia]|].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [apply (md_ra_sub _ LA_G_NL NK_SIZE); [exact Gra | unfold NK_CHUNK; lia | unfold NK_CHUNK, NK_N_CHUNKS, NK_SIZE; lia]|].
  split; [apply (md_hull_sub _ LA_G_NL NK_SIZE); [exact Ghv | unfold NK_CHUNK; lia | unfold NK_CHUNK, NK_N_CHUNKS, NK_SIZE; lia
    | unfold NK_N_CHUNKS; lia]|].
  split; [|exact R4]. unfold apart_gnl. unfold off_img in Bmt.
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_NL, NK_SIZE, MD_SIZE in *. lia.
Qed.

Lemma md_apart_of_disj : forall a n b k, 0 < n -> 0 < k ->
  (forall x, a <= x < a + n -> b <= x < b + k -> False) -> apart a n b k.
Proof.
  intros a n b k Hn Hk H. unfold apart.
  destruct (Z_le_gt_dec (a + n) b) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (b + k) a) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.

(* the call's own side frame: its place, its bytes and shadow present, apart from every block, off the image *)
Lemma lf_frame_place : forall cx fp ly S (W : world SEGS) mem mdl k,
  BASEF cx -> JRN cx fp ly S W mem mdl k -> frames S = [(LF_CID, fp)] ->
  frame_addr ly LF_CID fp = lf_F cx fp /\
  lf_F cx fp mod 32 = 0 /\ 4096 <= lf_F cx fp /\ lf_F cx fp + 1024 <= alloc_ceiling /\
  in_app (lf_F cx fp) 1024 /\
  (forall a, lf_F cx fp <= a < lf_F cx fp + 1024 -> apresent (w_H W) mem a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (lf_SH cx fp + i)) /\
  (forall b n, In (b, n) (ablocks B ly S) -> zdisjoint (b, req_size n) (lf_F cx fp, 1024)).
Proof.
  intros cx fp ly S W mem mdl k HB HJ Hfr.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem
    mdl k HB HJ) as (_ & _ & _ & _ & _ & _ & HAR).
  assert (Hfa : forall c q, frame_addr ly c q = frame_addr (c_ly cx) c q) by (eapply aj_frame_addr; exact HJ).
  assert (Hin : In (LF_CID, fp) (frames S)) by (rewrite Hfr; left; reflexivity).
  assert (HF : frame_addr ly LF_CID fp = lf_F cx fp) by (unfold lf_F; apply Hfa).
  destruct (al_frames _ _ LAWS ly S W mem mdl LF_CID fp HAR Hin) as (F32 & Fapp & Fpres & Fsh).
  pose proof (al_sep _ _ LAWS ly S W mem mdl HAR) as (Hsep & Hfs).
  destruct (pairwise_app_inv _ _ _ Hsep) as (_ & _ & Hx).
  rewrite Forall_forall in Hfs. specialize (Hfs (LF_CID, fp) Hin). cbn [fst snd] in Hfs.
  change (fs_frame_bytes LF_CID) with 1024 in *. rewrite HF in *.
  split; [reflexivity|]. split; [exact F32|]. split; [lia|]. split; [lia|]. split; [exact Fapp|].
  split.
  { intros a Ha. split; [exact (proj1 (Fpres a Ha))|].
    apply (al_client_img _ _ LAWS ly S W mem mdl a HAR). right; left. exists LF_CID, fp. split; [exact Hin|].
    change (fs_frame_bytes LF_CID) with 1024. rewrite HF. exact Ha. }
  split.
  { intros i Hi. destruct (Fsh i ltac:(change (1024 / 8) with 128; lia)) as (Hp & _).
    unfold lf_SH, shadow_of_addr. unfold shadow_addr in Hp. exact Hp. }
  intros b n Hbn.
  exact (Hx (b, req_size n) (lf_F cx fp, 1024)
    ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) _ _ Hbn))
    ltac:(rewrite <- HF; change 1024 with (fs_frame_bytes (fst (LF_CID, fp)));
          apply (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hin))).
Qed.

(* errno's four bytes are image bytes *)
Lemma md_errno_img_b : forallb (fun i => existsb (fun s => (Z.of_N (seg_base s) <=? TFIB_ERRNO + Z.of_nat i) &&
    (TFIB_ERRNO + Z.of_nat i <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma md_errno_img : forall x, as_errno B <= x < as_errno B + 4 -> in_img SEGS x.
Proof.
  intros x Hx. rewrite (ts_errno B TB) in Hx. pose proof md_errno_img_b as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - TFIB_ERRNO)) ltac:(apply in_seq; lia)).
  apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite HSEGS. exists s. split; [exact Hs | lia].
Qed.

(* the read set's table strings, as akb *)
Lemma lf_tab_akb : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs slo shi,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  forall bs i p s x, anlk_at SEGS (rdW W mem) LA_G_NL bs -> 0 <= i < nk_n_if bs ->
    au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * i) p -> acstr_at SEGS (rdW W mem) p s ->
    p <= x <= p + Z.of_nat (length s) -> akb SEGS B ly S slo shi x.
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs slo shi HB HJ HRO HD bs i p s x Hbs Hi Hp Hs Hx.
  pose proof HD as (Dk & _ & Htab & _).
  assert (Ebs : bs = kbs).
  { destruct Hbs as ((A1 & _) & L1). destruct Dk as ((A2 & _) & L2). apply (lf_abytes_unique _ _ _ _ A1 A2). lia. }
  subst bs. pose proof Htab as (Hn1 & Hn2 & Htent).
  rewrite lf_tab_len in Hn1. rewrite Hn1 in Hi.
  destruct (nth_error lf_tab (Z.to_nat i)) as [[n2 ix]|] eqn:Hn;
    [| exfalso; apply nth_error_None in Hn; rewrite lf_tab_len in Hn; lia].
  destruct (Htent _ _ _ Hn) as (_ & p0 & Hp0 & _ & Hs0 & _).
  rewrite Z2Nat.id in Hp0 by lia.
  pose proof (kp_vm8_mod _ _ _ _ _ Hp Hp0) as E0.
  assert (Rp : 0 <= p < 2 ^ 64) by (destruct Hs as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; lia).
  assert (R0 : 0 <= p0 < 2 ^ 64) by (destruct Hs0 as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; lia).
  rewrite !Z.mod_small in E0 by assumption. rewrite <- E0 in Hs0.
  pose proof (kp_acstr_unique _ _ _ _ _ Hs Hs0) as Es. subst s.
  assert (Hp' : au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat (Z.to_nat i)) p)
    by (rewrite Z2Nat.id by lia; exact Hp).
  destruct (lf_tab_core cx fp ly S W mem mdl k md mk kbs mbs gbs HB HJ HRO HD _ _ _ _ Hn Hp' Rp)
    as (_ & _ & _ & _ & _ & _ & _ & C7).
  destruct (C7 x ltac:(lia)) as (I1 & I2 & I3).
  right; right; left. exact (conj I1 (conj I2 I3)).
Qed.

(* a byte of a block of the state, as akb *)
Lemma lf_blk_akb : forall ly S slo shi b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n ->
  akb SEGS B ly S slo shi x.
Proof. intros ly S slo shi b n x Hin Hx. right; left. exists b, n. split; [exact Hin | exact Hx]. Qed.

(* a byte of a side frame of the state, as akb *)
Lemma lf_frm_akb : forall ly S slo shi cid pos x, In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid -> akb SEGS B ly S slo shi x.
Proof.
  intros ly S slo shi cid pos x Hin Hx. right; right; right. exists cid, pos. split; [exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

(* the cut after a callee whose writes are the model block and bytes of the frame's body (model_read,
   model_write, and the like): every piece kept but the model, which the callee's post gives *)
Lemma lf_model_after : forall cx fp K ly3 S3 ly2 S2 (W3 : world SEGS) ms3 md3 (W2 : world SEGS) ms2 md2 (E : Z -> Prop)
    k2 ev mo wl lv md mk kbs mbs gbs mbs' T3 own P N sh,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) (lf_data_fp_w md mk) ->
  (length sh <= 128)%nat ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 sh -> lf_slots cx md mk fp W3 ms3 ->
  lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  amodel_at SEGS (rdW W2 (ms_mem ms2)) md mbs' -> model_wf mbs' ->
  md_n_mark mbs' = md_n_mark mbs -> md_marks mbs' = md_marks mbs ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 sh /\ lf_slots cx md mk fp W2 ms2 /\
  lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs mbs' gbs (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp K ly3 S3 ly2 S2 W3 ms3 md3 W2 ms2 md2 E k2 ev mo wl lv md mk kbs mbs gbs mbs' T3 own P N sh
    HB HJ Hfr LC HE Fd Fs Pmd Pmk WC Hshl Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat Hmd' Hmwf' Hnm' Hmm'.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (_ & _ & _ & _ & _ & _ & HAR3).
  destruct (lf_frame_place cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr)
    as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & Hnul & HRO & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4 & Bkceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil. change (req_size MK_SIZE) with 516 in Bkceil.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (Fsep md MD_SIZE Bmd) as DmF. pose proof (Fsep mk MK_SIZE Bmk) as DkF.
  unfold zdisjoint in DmF, DkF. cbn [fst snd] in DmF, DkF. change (req_size MD_SIZE) with 8856 in DmF.
  change (req_size MK_SIZE) with 516 in DkF.
  pose proof (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  pose proof LC as (HK0 & HKc & _).
  assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg).
  { rewrite HFS. assert (D1 : 4096 / 8 <= lf_F cx fp / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : lf_F cx fp / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. lia. }
  (* E misses everything but the model block and the frame's body *)
  assert (EImg : forall a, E a -> ~ in_img SEGS a).
  { intros a Ha Hi. destruct (HE a Ha) as [H | H].
    - apply (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 a HAR3); [|exact Hi]. left. exists md, MD_SIZE.
      split; [exact Bmd|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in H. lia.
    - exact (proj2 (Fpres a ltac:(lia)) Hi). }
  assert (ERo : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a).
  { intros a Hro Ha. apply (EImg a Ha). destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
    exact (RIMG a Hr). }
  assert (EHi : forall a, E a -> a < alloc_ceiling) by (intros a Ha; destruct (HE a Ha); unfold MD_SIZE in *; lia).
  assert (ESh : forall a, lf_SH cx fp <= a < lf_SH cx fp + 128 -> ~ E a).
  { intros a Ha HEa. destruct (HE a HEa) as [H | H].
    - unfold amem_range in *. pose proof Hblk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bamm & _).
      unfold amem_range, MD_SIZE, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
    - unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
  assert (EImgfp : forall a, lf_img_fp MS la_nul a -> ~ E a) by (intros a Ha HEa; exact (EImg a HEa (proj1 (IMG a Ha)))).
  set (LXE := lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E) in *.
  assert (NImg : forall a, lf_img_fp MS la_nul a -> ~ LXE a)
    by (intros a Ha; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha (EImgfp a Ha))).
  assert (NSide : forall a, (lf_F cx fp <= a < lf_F cx fp + 24 \/ lf_F cx fp + 1016 <= a < lf_F cx fp + 1024 \/
     lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ LXE a).
  { intros a Ha. apply (lfx_side B cx fp K ly3 S3 ly2 S2 E a Hin Hfa).
    - destruct Ha as [Ha | [Ha | Ha]]; [left; lia | left; lia | right; exact Ha].
    - intros HEa. destruct Ha as [Ha | [Ha | Ha]].
      + destruct (HE a HEa) as [H | H]; [unfold MD_SIZE in *; lia | lia].
      + destruct (HE a HEa) as [H | H]; [unfold MD_SIZE in *; lia | lia].
      + exact (ESh a Ha HEa). }
  assert (NBlkE : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + m -> (b, m) <> (md, MD_SIZE) -> ~ E a).
  { intros b m a Hbm Ha Hne HEa.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b m HAR3 Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
    assert (Rm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    destruct (HE a HEa) as [H | H].
    - pose proof (sep_blocks _ _ LAWS _ _ _ _ _ b m md MD_SIZE HAR3 Hbm Bmd Hne) as D. unfold zdisjoint in D.
      cbn [fst snd] in D. change (req_size MD_SIZE) with 8856 in D. unfold MD_SIZE in H. lia.
    - pose proof (Fsep b m Hbm) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
  assert (NBlk : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + m -> (b, m) <> (md, MD_SIZE) -> ~ LXE a)
    by (intros b m a Hbm Ha Hne; exact (lfx_blk B ly3 S3 ly2 S2 _ _ E b m a Hbm Ha (NBlkE b m a Hbm Ha Hne))).
  assert (Hmkmd : (mk, MK_SIZE) <> (md, MD_SIZE)) by (intros Hq; injection Hq as _ Hq; discriminate).
  (* the pieces *)
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. unfold lf_saved_fp in Ha. pose proof (EHi a HEa). unfold LLVMF_STK in *. lia. }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. unfold lf_slots_fp in Ha. pose proof (EHi a HEa). unfold LLVMF_STK in *. lia. }
  assert (Hcur2 : lf_cur cx W2 ms2 P N).
  { apply (lf_cur_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N LC); [|exact Hcur].
    intros a Ha HEa. unfold lf_cur_fp in Ha. pose proof (EHi a HEa). unfold LLVMF_STK in *. lia. }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha HEa. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha.
    destruct (HE a HEa) as [H | H]; [unfold MD_SIZE in *; lia | lia]. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 sh).
  { apply (lf_fshadow_keep LXE cx fp W3 ms3 W2 ms2 sh KG); [|exact Hfsh].
    intros a Ha. apply NSide. right; right. unfold lf_fshadow_fp in Ha. lia. }
  assert (Hblk2 : lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)))
    by exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC Pmd Pmk Hblk).
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)))
    by exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC ERo HRO).
  assert (HNUL2 : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0).
  { apply (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E IMG LC); [|exact Hnul].
    apply EImgfp. right; right; right; right; right; left. lia. }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn)).
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own).
  { apply (lf_jbk_callee B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E
      IMG RIMG LC); [| exact ERo | exact HPB | exact Fd | exact Fs | exact HNUL2 | exact Hjbk].
    intros a Ha HEa. destruct Ha as [Ha | Ha].
    - destruct Ha as [Ha | [Ha | (f & n & Hfn & Ha)]].
      + exact (EImgfp a ltac:(right; right; right; left; exact Ha) HEa).
      + exact (EImgfp a ltac:(right; right; right; right; left; exact Ha) HEa).
      + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n.
        assert (Hne : (f, AMF_BLOCK) <> (md, MD_SIZE)) by (intros Hq; rewrite Hq in Hfn; exact (BmT Hfn)).
        exact (NBlkE f AMF_BLOCK a HfnT ltac:(unfold AMF_BLOCK in *; lia) Hne HEa).
    - assert (Hn : 0 < c_n cx) by lia.
      assert (Hne : (c_p cx, c_n cx) <> (md, MD_SIZE)) by (intros Hq; apply Bmc; rewrite <- Hq; destruct HPRE as (_ & _ & _ & _ & Hpn & _); destruct Hpn as [(Hn0 & _) | (_ & Hin0)]; [lia | exact Hin0]).
      exact (NBlkE _ _ a (HPB Hn) Ha Hne HEa). }
  (* lf_data at the model the callee left *)
  pose proof Hdat as Hdat0.
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & (Dmn & Dmm) & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  assert (WB : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) ->
    wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) a n)
    by (intros a n Hf; exact (wcarry_on_sub _ _ _ a n WC Hf)).
  assert (NImgR : forall a lo n, lo <= a < lo + n -> (forall x, lo <= x < lo + n -> lf_img_fp MS la_nul x) -> ~ LXE a)
    by (intros a lo n Ha Hf; exact (NImg a (Hf a Ha))).
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  assert (Hdat2 : lf_data cx md mk kbs mbs' gbs (rdW W2 (ms_mem ms2))).
  { refine (conj _ (conj Dwf (conj _ (conj Dop (conj Dmis (conj Doc (conj Hmd' (conj Hmwf' (conj _ (conj Dkwf
      (conj _ (conj _ (conj _ (conj _ (conj Hodd2 (conj Htx2 _)))))))))))))))).
    - apply (anlk_keep _ LXE _ _ LA_G_NL kbs KG); [| |exact Dk].
      + apply WB. intros i Hi. left. lia.
      + intros i Hi. apply NImg. left. lia.
    - apply (aiftab_keep _ LXE _ _ LA_G_NL kbs lf_tab KG); [| | |exact Dtab].
      + intros i Hi kk Hk. apply NImg. left. unfold NK_IF_NAME, NK_SIZE. lia.
      + intros i Hi kk Hk. apply NImg. left. unfold NK_IF_INDEX, NK_SIZE. lia.
      + intros i nm ix p Hn Hp Hs jj Hjj.
        assert (Rp : 0 <= p < 2 ^ 64) by (destruct Hs as ((A1 & A2 & _) & _); rewrite length_app in A2;
          cbn [length] in A2; lia).
        destruct (lf_tab_core cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 md mk kbs mbs gbs HB HJ HRO Hdat0 i nm ix p Hn Hp Rp)
          as (_ & _ & _ & _ & _ & _ & _ & C7).
        destruct (C7 (p + jj) ltac:(lia)) as (I1 & I2 & I3).
        exact (lfx_img B ly3 S3 ly2 S2 _ _ E (p + jj) I1 I2 I3 (fun HEa => EImg _ HEa I1)).
    - apply (amarks_keep _ LXE _ _ mk gbs KG); [| |exact Dmk].
      + apply WB. intros i Hi. right; right; right; right. unfold MK_SIZE in *. lia.
      + intros i Hi. apply (NBlk mk MK_SIZE (mk + i) Bmk); [lia | exact Hmkmd].
    - split; [rewrite Hnm'; exact Dmn | rewrite Hmm'; exact Dmm].
    - apply (lf_ifp_keep_ro LXE _ _ 64 KG); [lia | | |exact Difp].
      + intros a Ha. apply NImg. left. exact Ha.
      + intros a Ha. apply NImg. right; right; right; right; right; right. exact Ha.
    - apply (lf_gnames_at_keep LXE _ _ 64 KG); [lia | |exact Dgn].
      intros a Ha. apply NImg. right; left. exact Ha.
    - apply (lf_gnames_w_keep LXE _ _ KG); [| |exact Dgw].
      + apply WB. intros i Hi. right; left. unfold G_NAMES_SIZE in *. lia.
      + intros a Ha. apply NImg. right; left. exact Ha.
    - apply (lf_la_at_keep_ns LXE _ _ KG); [| | exact (lf_la_slack_any HSEGS _) | exact Dla].
      + apply WB. intros i Hi. right; right; left. lia.
      + intros a Ha. apply NImg. right; right; left. exact Ha. }
  refine (conj Hsv2 (conj Hhd2 (conj Hfsh2 (conj Hsl2 (conj Hcur2 (conj Hjbk2 (conj Hblk2 (conj Hdat2 HRO2)))))))).
Qed.

End b.
End a.
