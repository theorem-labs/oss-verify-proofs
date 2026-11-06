(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 330 of its 382 lines of code are new or changed and 352 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm, the middle of one turn of the per-mark loop
   (+0x808 .. +0x838): model_read's answer tested, the bcmp wrapper (0x82ff0) on the alias against .str.11,
   model_write (0x83008) when both pass, to the join u_j_inv at +0x838.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputOp3B.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ABCMP : forall fy : YK11.FPState, @abcmp_realizes fy rc SEGS B (pa_sigma LS___interceptor_trampoline_bcmp).
  (* AE2s.v bcmp_icpt_contract *)

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Definition LU_mr : Z := AF_LLVMFuzzerTestOneInput + 0x808.   (* 0x82fdc, model_read's return *)

(* the runner's state at the loop head: the frame's shadow, its window the 32 bytes of F + 0x20 *)
Definition u_fs_rg : YP09.region := YP09.mkRegion (Some 19%nat) 0 112 4 36 [].
Definition u_l_facts : facts := mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2)] [] [].
Definition u_l_ss : sstate := mkSS LU_body sr_atoms [u_fs_rg] None u_l_facts.

(* the frame's shadow with the object F + 0x20 in scope *)
Definition LU_join : Z := AF_LLVMFuzzerTestOneInput + 0x838.   (* 0x8300c *)
Definition LU_bc : Z := AF_LLVMFuzzerTestOneInput + 0x820.     (* 0x82ff4, the bcmp wrapper's return *)

(* +0x838: this mark's calls are done; the object F + 0x20 is still in scope *)
Definition u_j_inv (i j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LU_join ms3 /\
  getr (ms_regs ms3) 23 = w64 (md + MD_MARK + MARK_LEN * j) /\ getr (ms_regs ms3) 20 = w64 j /\
  getr (ms_regs ms3) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK)) /\
  u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 ms3 md3 /\
  0 <= j < md_n_mark mbs /\ nk_n_sent kbs = 0 /\
  unmark_walk lf_tab (skipn (Z.to_nat (j + 1)) (mk_names gbs)) (md_reqs mbs) (md_kstate mbs kbs) =
    unmark lf_tab (mk_names gbs) [] (nk_kstate kbs).

(* +0x820: the bcmp wrapper has returned; a0 is 0 exactly when the alias model_read read is "reac-pw:served" *)
Definition u_b_inv (i j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (nm : list byte) (reqs0 : list (list byte))
    (K0 : kstate),
  lf_shape fy LU_bc ms3 /\
  getr (ms_regs ms3) 23 = w64 (md + MD_MARK + MARK_LEN * j) /\ getr (ms_regs ms3) 20 = w64 j /\
  getr (ms_regs ms3) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK)) /\
  u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 ms3 md3 /\
  0 <= j < md_n_mark mbs /\ nk_n_sent kbs = 0 /\
  nth_error (mk_names gbs) (Z.to_nat j) = Some nm /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (md + MD_MARK + MARK_LEN * j) nm /\ (length nm < 16)%nat /\
  unmark_walk lf_tab (skipn (Z.to_nat j) (mk_names gbs)) reqs0 K0 = unmark lf_tab (mk_names gbs) [] (nk_kstate kbs) /\
  md_reqs mbs = r_reqs (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) /\
  md_kstate mbs kbs = r_state (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) /\
  r_rc (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) = 0 /\
  (getr (ms_regs ms3) 10 = w64 0 <-> r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) = S_SERVED).

Definition u_r_ss : sstate := mkSS LU_mr sr_atoms [] None (mkFacts [] [] []).

(* a bnez on a register holding a small value *)
Lemma u_bne0 : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof.
  intros E n v H Hv. rewrite branch_ne_U, U_SOff, H, U_lit by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. f_equal.
  destruct (Z.eqb_spec v 0) as [-> | Hn]; [reflexivity|].
  apply Z.eqb_neq. destruct (Z_lt_le_dec v 0).
  - rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) by lia. lia.
  - rewrite Z.mod_small by lia. exact Hn.
Qed.

(* the cut's pieces across a stretch whose changed bytes X miss every footprint *)
Lemma u_mem_carry : forall (X : Z -> Prop) i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 ms' md',
  u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 W3 ms3 md3 ->
  length sh = 112%nat ->
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  (forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> ~ X a) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) -> m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  getr (ms_regs ms') 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms') 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms3) 4 -> getr (ms_regs ms') 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms') 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs ms') 21 = getr (ms_regs ms3) 21 -> getr (ms_regs ms') 22 = getr (ms_regs ms3) 22 ->
  getr (ms_regs ms') 24 = getr (ms_regs ms3) 24 -> getr (ms_regs ms') 25 = getr (ms_regs ms3) 25 ->
  getr (ms_regs ms') 26 = getr (ms_regs ms3) 26 -> getr (ms_regs ms') 27 = getr (ms_regs ms3) 27 ->
  u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros X i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HU Hl KB NX GB Fd Fs
    Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q25 Q26 Q27.
  destruct HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  split; [exact Hi|]. split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
  split; [unfold u_regs in *; rewrite Q19, Q21, Q22, Q24, Q25, Q26, Q27; exact Hreg|].
  split; [exact (lf_saved_keep X cx W3 ms3 W3 ms' KB (fun a Ha => NX a ltac:(tauto)) Hsv)|].
  split; [exact (lf_header_keep X cx fp W3 ms3 W3 ms' KB (fun a Ha => NX a ltac:(tauto)) Hhd)|].
  split; [apply (lf_fshadow_keep X cx fp W3 ms3 W3 ms' sh KB); [|exact Hfs]; rewrite Hl;
    intros a Ha; exact (NX a ltac:(tauto))|].
  split; [exact (lf_slots_keep X cx md mk fp W3 ms3 W3 ms' KB (fun a Ha => NX a ltac:(tauto)) Hsl)|].
  split; [exact (lf_cur_keep X cx W3 ms3 W3 ms' P N KB (fun a Ha => NX a ltac:(tauto)) Hcur)|].
  split; [exact (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 ms' md' KB Fd Fs
    (fun a Ha => NX a ltac:(tauto)) Hjbk)|].
  split; [exact (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KB (fun a Ha => NX a ltac:(tauto)) Hblk)|].
  split; [exact (lf_data_keep X _ _ cx md mk kbs mbs gbs KB (wcarry_on_grows _ _ _ GB) (fun a Ha => NX a ltac:(tauto))
    Hdat)|].
  exact Hop.
Qed.

(* the bcmp wrapper's 15 bytes: the alias buffer equals .str.11 ("reac-pw:served" and its NUL) exactly when the
   alias is S_SERVED *)
Lemma u_cmp15 : forall (W : world SEGS) mem x y al,
  acstr_at SEGS (rdW W mem) x al -> (forall i, 0 <= i < 15 -> aview SEGS (w_H W) mem (x + i) <> None) ->
  acstr_at SEGS (rdW W mem) y S_SERVED ->
  ((forall i, 0 <= i < 15 -> aview SEGS (w_H W) mem (x + i) = aview SEGS (w_H W) mem (y + i)) <-> al = S_SERVED).
Proof.
  intros W mem x y al ((Ax0 & Ax1 & Axb) & Anz) Hp ((Ay0 & Ay1 & Ayb) & _).
  set (m := rdW W mem) in *.
  set (rest := map (fun k => match mbyte SEGS m (x + Z.of_nat (length al) + 1 + Z.of_nat k) with
                             | Some b => b | None => Z_to_bv 8 0 end) (seq 0 15)).
  assert (Lr : length rest = 15%nat) by (unfold rest; rewrite length_map, length_seq; reflexivity).
  assert (BX : forall i, (i < 15)%nat -> mbyte SEGS m (x + Z.of_nat i) = nth_error (al ++ Z_to_bv 8 0 :: rest) i).
  { intros i Hi. destruct (Nat.le_gt_cases i (length al)) as [Hle | Hgt].
    - rewrite (Axb i ltac:(rewrite length_app; cbn [length]; lia)).
      destruct (Nat.lt_ge_cases i (length al)) as [Hl | Hl].
      + rewrite !nth_error_app1 by lia. reflexivity.
      + assert (i = length al) by lia. subst i. rewrite !nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - rewrite nth_error_app2 by lia. replace (i - length al)%nat with (S (i - length al - 1)) by lia. cbn [nth_error].
      unfold rest. rewrite (lw_nth_error_map_seq _ 15 0 (i - length al - 1) ltac:(lia)).
      replace (x + Z.of_nat (length al) + 1 + Z.of_nat (0 + (i - length al - 1))) with (x + Z.of_nat i) by lia.
      destruct (mbyte SEGS m (x + Z.of_nat i)) as [b|] eqn:Eb; [reflexivity|].
      exfalso. apply (Hp (Z.of_nat i) ltac:(lia)). unfold aview. fold m. rewrite Eb. reflexivity. }
  assert (BY : forall i, (i < 15)%nat -> mbyte SEGS m (y + Z.of_nat i) = nth_error (S_SERVED ++ [Z_to_bv 8 0]) i).
  { intros i Hi. apply Ayb. rewrite length_app, u_served_len. cbn [length]. lia. }
  rewrite <- (u_bcmp15 al rest Anz ltac:(lia)).
  split.
  - intros H i Hi.
    pose proof (H (Z.of_nat i) ltac:(lia)) as Hv. unfold aview in Hv. fold m in Hv.
    rewrite (BX i Hi), (BY i Hi) in Hv.
    assert (Hs1 : exists b, nth_error (al ++ Z_to_bv 8 0 :: rest) i = Some b).
    { destruct (nth_error (al ++ Z_to_bv 8 0 :: rest) i) as [b|] eqn:E; [exists b; reflexivity|].
      apply nth_error_None in E. rewrite length_app in E. cbn [length] in E. lia. }
    assert (Hs2 : exists b, nth_error (S_SERVED ++ [Z_to_bv 8 0]) i = Some b).
    { destruct (nth_error (S_SERVED ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [exists b; reflexivity|].
      apply nth_error_None in E. rewrite length_app, u_served_len in E. cbn [length] in E. lia. }
    destruct Hs1 as (b1 & E1). destruct Hs2 as (b2 & E2). rewrite E1, E2 in Hv. cbn [option_map] in Hv.
    injection Hv as Hv. rewrite E1, E2. f_equal. apply bv_eq. exact Hv.
  - intros H i Hi. unfold aview. fold m.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (BX (Z.to_nat i) ltac:(lia)), (BY (Z.to_nat i) ltac:(lia)), (H (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.

(* a C string's bytes are readable *)
Lemma u_cstr_some : forall H (mem : word -> option byte) p s a, acstr_at SEGS (mrestrict H mem) p s ->
  p <= a <= p + Z.of_nat (length s) -> aview SEGS H mem a <> None.
Proof.
  intros H mem p s a ((_ & _ & Hb) & _) Ha. unfold aview. cbv beta.
  replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
  rewrite (Hb (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)).
  destruct (nth_error (s ++ [zb 0]) (Z.to_nat (a - p))) eqn:En; [intros Hc; simpl in Hc; discriminate Hc|].
  apply nth_error_None in En. rewrite length_app in En. cbn [length] in En. lia.
Qed.

Lemma u_mid : forall POST i j,
  FROM POST (u_j_inv i j) -> FROM POST (u_b_inv i j) -> FROM POST (u_r_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i j HJN HBI cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HR.
  destruct HR as (md & mk & P & N & kbs & mbs & gbs & T3 & nm & reqs0 & K0 & Hsh & R23 & R20 & R18 & HU & Hj & Hns
    & Hnm & Hnmc & Hnml & HUW & Hrq & Hks & R10 & Hal & Hab & Kso & Kse & Ken).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  set (R := read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) in *.
  assert (RR : - 2 ^ 32 < norm_rc (r_rc R) < 2 ^ 32)
    by (apply u_norm_rc_range; unfold R; apply u_read_rc_range; assumption).
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E10 : ew E 10 = Z_to_bv 64 (norm_rc (r_rc R))) by (rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E u_r_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_mr)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold u_r_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LU_mr ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_mr)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x808 taken: model_read failed, the mark is skipped *)
    rewrite (u_bne0 E 10 _ E10 ltac:(lia)) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hr0 : r_rc R <> 0) by (intros H0; apply Hc; apply u_norm_rc_zero; exact H0).
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LU_join; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E) by exact (lf_env_agree0 (ms_regs ms3)).
    assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
    apply (HJN cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R23|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R18|].
    split.
    { apply (u_mem_carry (fun _ => False) i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 ms3 md3 msB md5 HU
        SH_Z_len KB (fun a _ H => H) HGB Fd5 Fs5); rewrite KR by (vm_compute; reflexivity); reflexivity. }
    split; [exact Hj|]. split; [exact Hns|].
    rewrite Hrq, Hks. unfold R.
    exact (u_step_skip lf_tab (mk_names gbs) j nm reqs0 K0 _ ltac:(lia) Hnm HUW (or_introl Hr0)).
  - (* +0x808 not taken: model_read answered 0; the bcmp wrapper on the alias *)
    rewrite (u_bne0 E 10 _ E10 ltac:(lia)) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hr0 : r_rc R = 0) by (apply u_norm_rc_zero; exact Hc).
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
    pmkst HS.
    assert (Hpc : ss_pc ssA = pa_sigma LS___interceptor_trampoline_bcmp) by reflexivity.
    rewrite Hpc.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    try rewrite (img_env_codeptr E HEI) in Q1.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q10.
    rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21.
    rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (E251 : ew E 251 = Z_to_bv 64 0x21100).
    { unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 251%nat with (A_OBJ 10).
      rewrite (lv_obj LV 10 ltac:(unfold link_nobj; lia)). reflexivity. }
    rewrite E251 in Q11.
    assert (HUA : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 msA md4)
      by exact (u_mem_carry (fun _ => False) i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 ms3 md3 msA md4 HU
        SH_Z_len KA (fun a _ H => H) HGA Fd Fs Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q25 Q26 Q27).
    pose proof HUA as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatA & _).
    pose proof HjbkA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROA & _).
    destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly3 S3 W3 (ms_mem msA) md4 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
    destruct (u_buf_shadow cx fp W3 msA HfsA F32 F4 Fc) as (BRA & BHV).
    destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
      (ms_mem msA) md4 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
    { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
    pose proof (acstr_keep SEGS (fun _ => False) _ _ _ _ KA (fun _ _ H => H) Hal) as HalA.
    (* .str.11, "reac-pw:served", texts[1] *)
    pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with Hh : forallb _ (seq 0 11) = true |- _ => rename Hh into KTx end.
    pose proof (kp_forallb_seq _ _ KTx 1 ltac:(lia)) as KT1. cbv beta zeta in KT1.
    apply andb_prop in KT1 as [_ KS1].
    change (fst (nth 1 KP_TEXTS (0, []))) with 0x21100 in KS1.
    destruct (kp_kstr_acstr B (w_H W3) (ms_mem msA) _ _ HROA KS1) as (HSV & _ & _).
    change (map (Z_to_bv 8) (snd (nth 1 KP_TEXTS (0, [])))) with S_SERVED in HSV.
    unfold kp_kstr_b in KS1.
    repeat match type of KS1 with (_ && _)%bool = true => apply andb_prop in KS1 as [KS1 ?] end.
    match goal with Hh : kp_hull_b _ _ = true |- _ => rename Hh into KH1 end.
    match goal with Hh : kp_ra_b _ _ = true |- _ => rename Hh into KR1 end.
    pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _). pose proof HARA as (MA & _).
    assert (SVra : range_addressable (aview SEGS (w_H W3) (ms_mem msA)) SHADOW_OFF 0x21100 15)
      by exact (kp_ra B TB ly3 S3 _ _ _ MA KR1).
    assert (SVhv : shadow_hull_vis (aview SEGS (w_H W3) (ms_mem msA)) 0x21100 15)
      by exact (kp_hull B TB ly3 S3 _ _ _ MA KH1).
    set (F := lf_F cx fp) in *.
    assert (BUFP : forall a, F + LO_WA <= a < F + LO_WA + 15 -> aview SEGS (w_H W3) (ms_mem msA) a <> None)
      by (intros a Ha; apply aview_some_of_apresent; exact (proj1 (Fpres a ltac:(unfold LO_WA in *; clia)))).
    assert (SVP : forall a, 0x21100 <= a < 0x21100 + 15 -> aview SEGS (w_H W3) (ms_mem msA) a <> None)
      by (intros a Ha; apply (u_cstr_some _ _ _ _ a HSV); rewrite u_served_len; clia).
    assert (BUFP' : forall i0, 0 <= i0 < 15 -> aview SEGS (w_H W3) (ms_mem msA) (F + LO_WA + i0) <> None)
      by (intros i0 Hi0; apply BUFP; clia).
    change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_bcmp)) (ms_mem msA)
      (seg_rom SEGS)) md4) with (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_bcmp))
      (ms_mem msA) (seg_rom SEGS)) md4).
    eapply SRr_bind.
    { eapply (@aj_gx_bcmp_at fy rc SK SEGS B LAWS pa_segs_low _ (ABCMP fy)) with (x := F + LO_WA) (y := 0x21100) (n := 15).
      - exact HGX.
      - exact HJ.
      - rewrite Rsp. exact H16.
      - rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
      - rewrite Rsp. unfold LLVMF_STK in *. clia.
      - rewrite Q3, R3. exact (proj1 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
      - rewrite Q4, R4. exact (proj2 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
      - reflexivity.
      - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite Q10, R26. reflexivity.
      - rewrite Q11. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - unfold LO_WA. clia.
      - unfold LO_WA. clia.
      - lia.
      - lia.
      - intros a Ha. split; [exact (BUFP a Ha)|]. rewrite Rsp. unfold ESTACK, LO_WA, LLVMF_STK in *. clia.
      - intros a Ha. split; [exact (SVP a Ha)|]. rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
      - intros a Ha. rewrite Rsp. unfold ESTACK, LO_WA, LLVMF_STK in *. clia.
      - intros a Ha. rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
      - unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, LO_WA in *. clia.
      - unfold amem_range. left. unfold kLowMemEnd. lia.
      - rewrite <- ard_aview. apply (md_ra_sub _ (F + LO_WA) 256); [exact BRA | lia | lia].
      - intros _. rewrite <- ard_aview. apply (md_hull_sub _ (F + LO_WA) 256); [exact BHV | lia | lia | lia].
      - exact SVra.
      - intros _. exact SVhv. }
    cbv beta. intros W2 c2 HWle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HRES & HKP2 & HPR2 & HSM2).
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, HKP2, HPR2.
    assert (Fd2 : m_fds md2 = m_fds md4) by (unfold same_but_materialized in HSM2; rewrite HSM2; reflexivity).
    assert (Fs2 : m_fs md2 = m_fs md4) by (unfold same_but_materialized in HSM2; rewrite HSM2; reflexivity).
    set (X2 := fun a => ~ (0 <= a < 2 ^ 64) \/ (lf_sp1 cx - 2 * ESTACK <= a < lf_sp1 cx)).
    assert (KB2 : kagree SEGS X2 (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem ms2))).
    { apply kagree_of_aview. intros a Ha. unfold X2 in Ha. apply HKP2; [tauto|]. rewrite Rsp. tauto. }
    assert (GB2 : mem_grows (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem ms2))) by exact (ar_grows _ _ _ HPR2).
    assert (NX2 : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
       lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> ~ X2 a).
    { intros a Hf HXa. destruct (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 msA md4 a HB HJ Hfr HjbkA HblkA Hf) as (R0 & R1).
      unfold X2 in HXa. unfold ESTACK, LLVMF_STK in *. clia. }
    pose proof (ar_pres _ _ HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    apply (HBI cx fy fp k2 ly3 S3 W3 ms2 md2 HB Hfx HJ2 Hfr).
    exists md, mk, P, N, kbs, mbs, gbs, T3, nm, reqs0, K0.
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1. unfold LU_bc, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    cbn [ms_regs ms2 mkst].
    split; [rewrite P23, Q23; exact R23|]. split; [rewrite P20, Q20; exact R20|]. split; [rewrite P18, Q18; exact R18|].
    split.
    { apply (u_mem_carry X2 i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 msA md4 ms2 md2 HUA SH_Z_len KB2 NX2 GB2
        ltac:(rewrite Fd2; exact eq_refl) ltac:(rewrite Fs2; exact eq_refl)); cbn [ms_regs ms2 mkst]; assumption. }
    split; [exact Hj|]. split; [exact Hns|]. split; [exact Hnm|].
    split.
    { apply (acstr_keep SEGS X2 _ _ _ _ KB2); [|exact (acstr_keep SEGS (fun _ => False) _ _ _ _ KA (fun _ _ H => H) Hnmc)].
      intros k0 Hk0 HXk. apply (NX2 (md + MD_MARK + MARK_LEN * j + k0)); [|exact HXk].
      pose proof HdatA as (_ & _ & _ & _ & _ & _ & _ & DmwfA & _). pose proof DmwfA as (_ & _ & _ & _ & _ & (WnmA & _)).
      unfold MARKS_MAX in WnmA.
      right; right; right; right; right; right; right. right; right; right; left. unfold MD_MARK, MARK_LEN, MD_SIZE. clia. }
    split; [exact Hnml|]. split; [exact HUW|]. split; [exact Hrq|]. split; [exact Hks|]. split; [exact Hr0|].
    rewrite HRES. unfold R in HalA. rewrite <- (u_cmp15 W3 (ms_mem msA) (F + LO_WA) 0x21100 _ HalA BUFP' HSV).
    reflexivity.
Qed.

End a.
