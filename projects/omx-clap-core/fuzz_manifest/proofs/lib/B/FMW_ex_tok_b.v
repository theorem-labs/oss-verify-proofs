(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 230 of its 274 lines of code are new or changed and 223 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_b.v, with its module paths, module names and numbers changed; 39 of its 255 lines of code are new or changed and 58 lines of the source are left out. *)
(* G4 IMAGE B: tk_seg_B (lib/B/FMW_ex_tok_base.v): expected's ex_token left boundary test (fuzz_manifest.c:109) at
   TK_B 0x817c8 .. 0x81830 of B's expected (listing lines 341-367): a0 = s1 - 1 = text + j - 1, the ASan check of its
   shadow byte, lb a0, -1(s1), then nine class branches: '.', c >= 128, '\\', '%', ':', '-', '_', a digit, a letter go
   to TK_N 0x817a4 (no token at j); else fall to TK_E 0x81834. Twin of image A's lib/A/FMW_ex_tok_b.v (06d82004dc3):
   B's instructions are A's 0x815dc .. 0x81644 with s1 for A's s7 (text + j).
   The run writes nothing and reads only s1, s9 and the byte text[j - 1]: its symbolic state keeps every register as
   its own atom (sr_atoms), s9 = extra atom 32 (the shadow base), the byte = extra atom 33 in a 1-byte region at
   s1 - 1. The class branches are decided on the byte alone by closed evaluation (FMW_plain.v pl_D pattern).
   No UBSan guard on this path (0x817c4, before TK_B, is FMW_ex_tok_lh.v's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_tok_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the symbolic state at TK_B: registers as atoms, s9 = atom 32 (the shadow base), text[j - 1] = atom 33 ---- *)
Definition tb_regs : list sv := sr_set sr_atoms 25%bv (SOff 32 0).
Definition tb_byte : YP09.region :=
  YP09.mkRegion (Some 9%nat) (-1) 0 (-1) (-1) [YP09.mkChunk (-1) (CVal 1 (SOff 33 0))].
Definition tb_facts : facts :=
  mkFacts [(9%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF FW_SB FW_SB 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_B : sstate := mkSS TK_B tb_regs [tb_byte] None tb_facts.
Definition TB_SH : list shent := [mkSHE 9 (-1) 0].
Definition tb_extra (c : Z) : list word := [Z_to_bv 64 FW_SB; Z_to_bv 64 c].

(* ---- the nine class branches as the walk stops at them (0x817e8 .. 0x81830), decided on the byte c alone: a closed
   valuation with c at atom 33 (FMW_plain.v pl_D / pl_cls_all) ---- *)
Definition tb_sx : sv := SExt true 8 (SOff 33 0).
Definition tb_lo : sv := SAlu ALU_AND tb_sx (SLit 255).
Definition tb_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition tb_Ec (c : Z) : env := ewset tb_E00 33 (Z_to_bv 64 c).
Definition tb_D (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (tb_Ec c) a) (sv_denot (tb_Ec c) b).
(* the boundary test's answer: a name character or '.' (token_at's j-case, fuzz_manifest.c:109) *)
Definition tb_ok (c : Z) : bool := ManifestModel.name_char c || (c =? 46).
Definition tb_cls_ok (c : Z) : bool :=
  let d1 := tb_D BC_EQ tb_lo (SLit 46) c in let d2 := tb_D BC_LT tb_sx (SLit 0) c in
  let d3 := tb_D BC_EQ tb_lo (SLit 92) c in let d4 := tb_D BC_EQ tb_lo (SLit 37) c in
  let d5 := tb_D BC_EQ tb_lo (SLit 58) c in let d6 := tb_D BC_EQ tb_lo (SLit 45) c in
  let d7 := tb_D BC_EQ tb_lo (SLit 95) c in
  let d8 := tb_D BC_LTU (SAlu ALU_ADD tb_lo (SLit (-48))) (SLit 10) c in
  let d9 := tb_D BC_LTU (SAlu ALU_ADD (SAlu ALU_AND tb_sx (SLit 223)) (SLit (-65))) (SLit 26) c in
  implb d1 (tb_ok c) &&
  implb (negb d1 && d2) (tb_ok c) &&
  implb (negb d1 && negb d2 && d3) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && d4) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4 && d5) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4 && negb d5 && d6) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4 && negb d5 && negb d6 && d7) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4 && negb d5 && negb d6 && negb d7 && d8) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4 && negb d5 && negb d6 && negb d7 && negb d8 && d9) (tb_ok c) &&
  implb (negb d1 && negb d2 && negb d3 && negb d4 && negb d5 && negb d6 && negb d7 && negb d8 && negb d9)
    (negb (tb_ok c)).
Lemma tb_cls_all : forall c, 0 <= c < 256 -> tb_cls_ok c = true.
Proof.
  intros c Hc.
  assert (H : forallb tb_cls_ok (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Lemma tb_D_of : forall E c cnd a b, ew E 33 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 33) a = true -> sv_atoms_in (Nat.eqb 33) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = tb_D cnd a b c.
Proof.
  intros E c cnd a b HE Ha Hb. unfold tb_D.
  assert (HA : env_agree_on (Nat.eqb 33) E (tb_Ec c)).
  { intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold tb_Ec. rewrite ew_ewset_same. symmetry. exact HE. }
  rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.
(* a branch hypothesis in closed form *)
Ltac tb_dec HS E33 c Hc :=
  let H33 := fresh "H33" in
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (H33 : ew Ex 33 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E33) end;
  erewrite (tb_D_of _ _ _ _ _ H33) in Hc by reflexivity; clear H33.
(* a leaf: the branches taken so far decide tb_ok c *)
Ltac tb_leaf c Rc :=
  let X := fresh "X" in
  lazymatch goal with |- _ = ?v => change (tb_ok c = v) end;
  pose proof (tb_cls_all c Rc) as X; unfold tb_cls_ok, tb_lo, tb_sx in X;
  repeat match goal with H : tb_D _ _ _ c = _ |- _ => rewrite H in X; clear H end;
  cbn [negb andb implb] in X; destruct (tb_ok c); first [reflexivity | discriminate X].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma tb_entry : forall regs3 (W3 : world tfibsegs) mem3 P c,
  getr regs3 9 = Z_to_bv 64 P -> getr regs3 25 = Z_to_bv 64 SHADOW_OFF ->
  4097 <= P <= 2 ^ 47 - 16 -> 0 <= c <= 255 ->
  val_mem tfibsegs (rdW W3 mem3) (P - 1) 1 c ->
  st_ok tfibsegs (Ereg regs3 (tb_extra c)) ss_B
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_B) mem3 (seg_rom tfibsegs))).
Proof.
  intros regs3 W3 mem3 P c R9 R25 HP Hc Vc.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (tb_extra c)).
  assert (E9 : ew E 9 = Z_to_bv 64 P) by (subst E; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  unfold ss_B. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (tb_extra c)) with E.
  - unfold tb_regs. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32, R25. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tb_byte.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ P (-1) 1 (SOff 33 0) c);
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
    replace (P + -1) with (P - 1) by lia. exact Vc.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok tb_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E32, E33, !unsigned_lit_small by (unfold FW_SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold FW_SB. repeat split; lia.
Qed.

(* the registers the run keeps (it writes only a0, a1, a2) *)
Definition tb_kept (regs3 regs4 : bvmap 5 word) : Prop :=
  getr regs4 2 = getr regs3 2 /\ getr regs4 3 = getr regs3 3 /\ getr regs4 4 = getr regs3 4 /\
  getr regs4 6 = getr regs3 6 /\ getr regs4 8 = getr regs3 8 /\ getr regs4 9 = getr regs3 9 /\
  getr regs4 16 = getr regs3 16 /\ getr regs4 17 = getr regs3 17 /\ getr regs4 18 = getr regs3 18 /\
  getr regs4 19 = getr regs3 19 /\ getr regs4 20 = getr regs3 20 /\ getr regs4 21 = getr regs3 21 /\
  getr regs4 22 = getr regs3 22 /\ getr regs4 23 = getr regs3 23 /\ getr regs4 24 = getr regs3 24 /\
  getr regs4 25 = getr regs3 25 /\ getr regs4 26 = getr regs3 26 /\ getr regs4 27 = getr regs3 27.

(* tk_mem, tk_regs, tk_cr and tk_jr across the run: the view is unchanged everywhere, the kept registers are equal *)
Lemma tb_keep : forall cx p j ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  tk_mem B cx p ly3 S3 W3 regs3 mem3 md3 -> tk_regs cx p regs3 -> tk_cr regs3 -> tk_jr cx j regs3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  tb_kept regs3 regs4 ->
  tk_mem B cx p ly3 S3 W3 regs4 mem4 md4 /\ tk_regs cx p regs4 /\ tk_cr regs4 /\ tk_jr cx j regs4.
Proof.
  intros cx p j ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HM HR HCR HJR HJ4 AV
    (K2 & K3 & K4 & K6 & K8 & K9 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof HM as (HX & HC & _).
  pose proof HX as (HB & _).
  pose proof (tk_bounds B cx HB) as (HFm & HFlo & HFhi & HF46 & _).
  pose proof asan_consts as (C1 & _).
  pose proof HC as (_ & _ & _ & Rsp & Rgp & Rtp & R25 & _).
  assert (HSTK : STK_expected = 240 + 8224) by reflexivity.
  split; [|split; [|split]].
  - apply (tk_mem_move B cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 (cx_F cx) HM HJ4).
    + lia.
    + intros a Ha _. exact (AV a Ha).
    + rewrite K2. exact Rsp.
    + rewrite K3. exact Rgp.
    + rewrite K4. exact Rtp.
    + rewrite K25. exact R25.
  - unfold tk_regs in *. rewrite K8, K19, K27, K23, K20, K21, K18, K22, K16. exact HR.
  - unfold tk_cr in *. rewrite K17, K6. exact HCR.
  - unfold tk_jr in *. rewrite K24, K26. exact HJR.
Qed.

(* text[j - 1] a name character or '.': no token at j (token_at's left boundary fails), TK_N *)
Lemma tb_to_N : forall cx p j' ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  tk_at_B B cx p (S j') ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  tb_kept regs3 regs4 ->
  (ManifestModel.name_char (nth j' (cx_tb cx) 0) || (nth j' (cx_tb cx) 0 =? 46)) = true ->
  tk_at_N B cx p (S j') ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx p j' ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HA HJ4 AV HK Hcl.
  destruct HA as (HM & HR & HCR & HJR & R9 & Hj & Hb & Hn & Hmid).
  destruct (tb_keep cx p (S j') ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HM HR HCR HJR HJ4 AV HK)
    as (HM4 & HR4 & HCR4 & HJR4).
  pose proof HM as (HX & _).
  split; [exact HM4|]. split; [exact HR4|]. split; [exact HCR4|]. split; [exact HJR4|]. split; [exact Hb|].
  apply (tk_none_S cx p (S j') Hn).
  rewrite (tk_at_mid B cx p (S j') HX Hb Hmid). unfold tk_leftb, ManifestModel.byte_at.
  revert Hcl. destruct (ManifestModel.name_char (nth j' (cx_tb cx) 0)), (nth j' (cx_tb cx) 0 =? 46);
    cbn [negb andb orb]; intros Hcl; first [reflexivity | discriminate Hcl].
Qed.

(* else the left boundary holds at j: TK_E *)
Lemma tb_to_E : forall cx p j' ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  tk_at_B B cx p (S j') ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  tb_kept regs3 regs4 ->
  (ManifestModel.name_char (nth j' (cx_tb cx) 0) || (nth j' (cx_tb cx) 0 =? 46)) = false ->
  tk_at_E B cx p (S j') ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx p j' ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HA HJ4 AV HK Hcl.
  destruct HA as (HM & HR & HCR & HJR & R9 & Hj & Hb & Hn & Hmid).
  destruct (tb_keep cx p (S j') ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HM HR HCR HJR HJ4 AV HK)
    as (HM4 & HR4 & HCR4 & HJR4).
  split; [exact HM4|]. split; [exact HR4|]. split; [exact HCR4|]. split; [exact HJR4|]. split; [exact Hb|].
  split; [exact Hn|]. split; [exact Hmid|].
  unfold tk_leftb, ManifestModel.byte_at.
  revert Hcl. destruct (ManifestModel.name_char (nth j' (cx_tb cx) 0)), (nth j' (cx_tb cx) 0 =? 46);
    cbn [negb andb orb]; intros Hcl; first [reflexivity | discriminate Hcl].
Qed.

(* the run's end state keeps the registers tb_kept names: each is its own atom (s9 the shadow atom 32) *)
Ltac tb_kept_tac HS EE E32 R25 :=
  unfold tb_kept; repeat match goal with |- _ /\ _ => split end;
  tk_g HS; first [rewrite E32, R25; reflexivity | apply EE; reflexivity].
(* an exit: run to stop (TK_N / TK_E), then the continuation KK through the exit lemma LEM (tb_to_N / tb_to_E) *)
Ltac tb_exit stop KK LEM HS HJ SHOK AV HA EE E32 R25 c Rc W3 mem3 ly3 S3 :=
  aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan stop; [awr_ok_tac|];
  tk_av W3 mem3; tk_mk HS;
  apply (KK ly3 S3 W3);
  apply (LEM _ _ _ _ _ _ _ _ _ _ _ _ HA HJ AV);
  [tb_kept_tac HS EE E32 R25 | tb_leaf c Rc].
(* the nine class branches: taken goes to TK_N; the ninth not taken falls to TK_E *)
Ltac tb_walk n KN KE HS HJ SHOK AV HA EE E32 E33 R25 c Rc W3 mem3 ly3 S3 :=
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan;
  [ lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ => tb_dec HS E33 c Hc end;
    tb_exit TK_N KN tb_to_N HS HJ SHOK AV HA EE E32 R25 c Rc W3 mem3 ly3 S3
  | lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      tb_dec HS E33 c Hc; let D := fresh "D" in rename Hc into D end;
    lazymatch n with
    | O => tb_exit TK_E KE tb_to_E HS HJ SHOK AV HA EE E32 R25 c Rc W3 mem3 ly3 S3
    | S ?m => aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan;
        [awr_ok_tac | tk_av W3 mem3; tb_walk m KN KE HS HJ SHOK AV HA EE E32 E33 R25 c Rc W3 mem3 ly3 S3]
    end ].

Theorem tk_seg_B_holds : tk_seg_B B.
Proof.
  intros cx p j KN KE ly3 S3 W3 regs3 mem3 md3 HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HA as (HM & HR & HCR & HJR & R9 & Hj & Hb & Hn & Hmid).
  pose proof HM as (HX & HC & HSL & _).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HCt as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold tk_bound in Hb.
  destruct j as [|j']; [lia|].
  destruct (HGa j' ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  rewrite app_nth1 in Vc, Rc by lia.
  set (c := nth j' (cx_tb cx) 0) in *.
  set (P := cx_t cx + Z.of_nat (S j')) in *.
  assert (Vc' : val_mem tfibsegs (rdW W3 mem3) (P - 1) 1 c) by (replace (P - 1) with (cx_t cx + Z.of_nat j') by lia; exact Vc).
  pose proof (tb_entry regs3 W3 mem3 P c R9 R25 ltac:(lia) ltac:(lia) Vc') as HS.
  remember (Ereg regs3 (tb_extra c)) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hq; rewrite HE; apply ew_Ereg_nat; exact Hq).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E9 : ew E 9 = Z_to_bv 64 P) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  clear HE.
  assert (SHOK : sh_ok tfibsegs EX_Bx TB_SH E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_B) mem3 (seg_rom tfibsegs))))).
  { constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E EX_Bx 9 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1) P (-1) 0).
    - exact HRA.
    - unfold EX_Bx. rewrite (U_atom E 32 FW_SB E32) by (unfold FW_SB; lia). reflexivity.
    - rewrite (U_atom E 9 P E9) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_B) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 TK_B) with (Z_to_bv 64 TK_B).
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  tk_av W3 mem3.
  tb_walk 8%nat KN KE HS HJ SHOK AV HA EE E32 E33 R25 c Rc W3 mem3 ly3 S3.
Qed.
End W.

Print Assumptions tk_seg_B_holds.
