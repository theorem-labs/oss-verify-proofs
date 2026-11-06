(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 259 of its 305 lines of code are new or changed and 221 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_e.v, with its numbers changed; 225 of its 286 lines of code are new or changed and 244 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_lha.v; 261 of its 300 lines of code are new or changed and 247 lines of the source are left out. *)
(* G4.ExTok.TokLH: tk_seg_LH (FMW_ex_tok_base.v): expected's ex_token loop body (fuzz_manifest.c:103-108) at
   TK_LH 0x81574 .. 0x815dc of fm.asan (expected.dis lines 274-299). One symbolic walk from tl_entry (kit:
   FMW_ex_tok_lha.v): run to bcmp (text + j, text + name, nl) at 0x81584 (tl_bcmp, reseat by jafter_call_keep);
   a0 <> 0: TK_N; else the ASan check and text[j + nl]: <> ':': TK_N; else bcmp (text + j + nl + 1, local, ll) at
   0x815bc; a0 <> 0: TK_N; else s10 = 0: TK_E, s10 > 0: TK_B. Each cut's tk_mem / tk_regs come from tl_exit. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_tok_base FMW_ex_tok_lha.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* back to the entry environment through the walk's havoc and token layers (E1o: the first call's havoc) *)
Ltac tl_o H := repeat first [rewrite H by lia | rewrite ew_havoc_old by lia | progress cbn [ew ewset Nat.eqb]].
(* at a cut: tk_mem and tk_regs of the walk's final state (tl_exit) *)
Ltac tl_hmr B cx p ly3 S3 W3 regs3 mem3 md3 HS HJ HM HR AVw EE E32 E1o :=
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
    let HMR := fresh "HMR" in
    assert (HMR : tk_mem B cx p ly3 S3 W3 (ms_regs msx) (ms_mem msx) mdx /\ tk_regs cx p (ms_regs msx))
      by (apply (tl_exit B cx p ly3 S3 W3 regs3 mem3 md3 _ _ _ HM HR HJ AVw);
          tl_g HS; tl_o E1o; first [apply EE; reflexivity | rewrite E32; reflexivity]);
    destruct HMR as (HM' & HR') end end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis BCMP : abcmp_realizes tfibsegs B PC_bcmp.

Theorem tk_seg_LH_holds : tk_seg_LH B.
Proof.
  intros cx p j KN KE KB ly3 S3 W3 regs3 mem3 md3 HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof (tl_entry B cx p j ly3 S3 W3 regs3 mem3 md3 HA) as HS.
  pose proof HA as (HM & HR & R23 & R26 & Hb & HNO).
  pose proof HM as (HX & HC & HSL & V8 & V28 & V10 & V0).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HR as (R8 & R18 & R22 & R20 & R21 & R24 & R27 & R19 & R9).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  pose proof HCt as (_ & Ht4096 & Htc & Ht32 & Htam & HtRA & _).
  pose proof HCu as (_ & Hu4096 & Huc & Hu32 & _).
  unfold tk_bound in Hb.
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  assert (ESTACK = 4096) as Hes by reflexivity.
  assert (HFlo : alloc_ceiling <= cx_F cx - 2 * ESTACK) by (unfold cx_F, cx_sp; lia).
  assert (HFhi : cx_F cx + 208 <= 2 ^ 47) by (unfold cx_F, cx_sp; lia).
  unfold tl_E in HS.
  set (q := tl_q cx p j) in *. set (lv := tl_l cx p) in *. set (c := tl_c cx p j) in *.
  assert (Hq : q = cx_t cx + Z.of_nat (tk_nl p) + Z.of_nat j) by reflexivity.
  assert (Hlv : lv = cx_u cx + Z.of_nat (tk_nl2 p)) by reflexivity.
  assert (Hcd : c = nth (j + tk_nl p) (cx_tb cx) 0) by reflexivity.
  clearbody q lv c.
  pose proof HCt as ((HGt & _) & _).
  destruct (HGt (j + tk_nl p)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [_ Rc].
  rewrite app_nth1 in Rc by lia. rewrite <- Hcd in Rc.
  remember (Ereg regs3 (tl_extra q lv c)) as E eqn:HE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
    by (intros n r Hr; rewrite HE; apply ew_Ereg_nat; exact Hr).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 q) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 lv) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 3)).
  clear HE.
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx)
    by (rewrite (EE 2%nat 2%bv eq_refl), Rsp; apply unsigned_lit_small; unfold cx_F, cx_sp; lia).
  assert (U23 : bv_unsigned (ew E 23) = cx_t cx)
    by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = Z.of_nat j)
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = q) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_LH) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AVw : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 2 * ESTACK <= a < cx_F cx) ->
    aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_LH) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 TK_LH) with (Z_to_bv 64 TK_LH).
  (* ---- TK_LH .. the first bcmp ---- *)
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
  assert (KL1 : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (intros a Ha; apply AVw; lia).
  pose proof (fw_cstr_low tfibsegs W3 mem3 (ms_mem ms) _ _ KL1 HCt) as HCt1.
  assert (A10 : getr (ms_regs ms) 10 = w64 (cx_t cx + Z.of_nat j)).
  { tl_reg HS (10%bv : bv 5). unfold w64. apply fw_sv_U.
    rewrite U_add_off_atom by (rewrite ?U23, ?U26; unfold M64; lia). rewrite ?U23, ?U26. lia. }
  assert (A11 : getr (ms_regs ms) 11 = w64 (cx_t cx + Z.of_nat (tk_name p))).
  { tl_g HS. rewrite (EE 20%nat 20%bv eq_refl). exact R20. }
  assert (A12 : getr (ms_regs ms) 12 = w64 (Z.of_nat (tk_nl p))).
  { tl_g HS. rewrite (EE 21%nat 21%bv eq_refl). exact R21. }
  assert (A2 : spZ (ms_regs ms) = cx_sp cx - 208).
  { unfold spZ. tl_reg HS (2%bv : bv 5). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Usp. reflexivity. }
  assert (A3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
  { tl_g HS. rewrite (EE 3%nat 3%bv eq_refl), Rgp. exact Hgp. }
  assert (A4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
  { tl_g HS. rewrite (EE 4%nat 4%bv eq_refl), Rtp. exact Htp. }
  assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x81588) by (tl_g HS; reflexivity).
  tl_mk HS.
  eapply SRr_bind.
  { apply (tl_bcmp B BCMP W3 (ms_regs ms) (ms_mem ms) (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) ly3 S3 _
      (cx_sp cx) (cx_t cx) (cx_tb cx) j (cx_t cx) (cx_tb cx) (tk_name p) (tk_nl p) (Z_to_bv 64 0x81588) HJ HCt1 HCt1
      ltac:(lia) ltac:(lia) A10 A11 A12 A2 ltac:(unfold cx_F in HFlo; lia) A3 A4 A1 ltac:(vm_compute; reflexivity)). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v1 & -> & HJ4 & HP4 & Hv1 & Hcmp1 & Hfr4 & Hpres4).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let K := eval vm_compute in (run_K 0 EX_Bx [] ss) in
    jafter_call_keep HS K regs4 (mrestrict (w_H W3) mem4) HP4 [0; 1]%nat HS2 end.
  match type of HS2 with ?tt -> _ => assert (HK : tt) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (fw_region_kept tfibsegs E (w_H W3) (ms_mem ms) mem4 2 (cx_F cx)); [exact Usp | | exact Hpres4].
      intros a Ha. apply Hfr4; [lia | unfold cx_F in *; lia].
    - eapply (fw_region_kept tfibsegs E (w_H W3) (ms_mem ms) mem4 33 q); [exact U33 | | exact Hpres4].
      intros a Ha. apply Hfr4; [lia | unfold cx_F in *; lia]. }
  specialize (HS2 HK). clear HK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  set (E1 := havoc E 36 (map (getr regs4) CLOB)) in *.
  assert (E1o : forall k, (k < 36)%nat -> ew E1 k = ew E k) by (intros k Hk; apply ew_havoc_old; exact Hk).
  assert (EA40 : ew E1 40 = v1).
  { change 40%nat with (36 + 4)%nat. unfold E1. rewrite (ew_havoc_new E 36 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
    transitivity (getr regs4 10); [reflexivity | exact Hv1]. }
  assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 2 * ESTACK <= a < cx_F cx) ->
    aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn'. rewrite (Hfr4 a Ha ltac:(unfold cx_F in Hn'; lia)). exact (AVw a Ha Hn'). }
  clear AVw Hfr4. rename AV4 into AVw.
  assert (KL4 : fw_low tfibsegs (w_H W3) mem3 mem4) by (intros a Ha; apply AVw; lia).
  pose proof (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL4 HCt) as HCt4.
  pose proof (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL4 HCu) as HCu4.
  pose proof HCt4 as (_ & _ & _ & _ & _ & HtRA4 & _).
  clear SHOK.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (SHOK : sh_ok tfibsegs EX_Bx TL_SH E1 (mrestrict (w_H W3) (ms_mem msx))) end.
  { constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem4 E1 EX_Bx 33 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1) q 0 1).
    - exact HtRA4.
    - unfold EX_Bx. rewrite (U_atom E1 32 FW_SB) by (first [rewrite E1o by lia; exact E32 | unfold FW_SB; lia]).
      reflexivity.
    - rewrite (U_atom E1 33 q) by (first [rewrite E1o by lia; exact E33 | lia]). reflexivity.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Htam. unfold SHADOW_OFF. lia. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => change mem4 with (ms_mem msx) in HJ4 end.
  clear HJ. rename HJ4 into HJ.
  (* ---- the first bcmp's answer ---- *)
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* a0 <> 0: text[j, j + nl) differs from the name: no token at j; TK_N *)
    rewrite branch_ne_U, (tl_U_atom_w E1 40 v1 EA40), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hne : firstn (tk_nl p) (skipn j (cx_tb cx)) <> tk_pre cx p).
    { intros Heq. apply Hc. assert (Hv0 : v1 = w64 0) by (apply Hcmp1; exact Heq).
      rewrite Hv0. first [reflexivity | vm_compute; reflexivity]. }
    pose proof (tk_none_S cx p j HNO (tk_at_pre B cx p j HX Hne)) as HN1. clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_N; [awr_ok_tac|].
    tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
    tl_mk HS.
    tl_hmr B cx p ly3 S3 W3 regs3 mem3 md3 HS HJ HM HR AVw EE E32 E1o.
    apply (KN ly3 S3 W3 _ _ _).
    split; [exact HM'|]. split; [exact HR'|].
    split; [tl_g HS; tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
    split; [unfold tk_bound; lia | exact HN1]. }
  rewrite branch_ne_U, (tl_U_atom_w E1 40 v1 EA40), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (M1 : v1 = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
  apply Hcmp1 in M1. clear Hc.
  (* ---- the ASan check and the load of text[j + nl] ---- *)
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* text[j + nl] <> ':': no token at j; TK_N *)
    rewrite branch_ne_U, (U_atom _ 35 c), U_SLit in Hc by (first [tl_o E1o; exact E35 | lia]).
    rewrite zcanon_id in Hc by (unfold M64; lia).
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hcol : ManifestModel.byte_at (cx_tb cx) (j + tk_nl p) <> 58)
      by (unfold ManifestModel.byte_at; rewrite <- Hcd; exact Hc).
    pose proof (tk_none_S cx p j HNO (tk_at_colon B cx p j HX Hcol)) as HN1. clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_N; [awr_ok_tac|].
    tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
    tl_mk HS.
    tl_hmr B cx p ly3 S3 W3 regs3 mem3 md3 HS HJ HM HR AVw EE E32 E1o.
    apply (KN ly3 S3 W3 _ _ _).
    split; [exact HM'|]. split; [exact HR'|].
    split; [tl_g HS; tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
    split; [unfold tk_bound; lia | exact HN1]. }
  rewrite branch_ne_U, (U_atom _ 35 c), U_SLit in Hc by (first [tl_o E1o; exact E35 | lia]).
  rewrite zcanon_id in Hc by (unfold M64; lia).
  apply Bool.negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hc58.
  (* ---- TK_LH + 0x48: the second bcmp ---- *)
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms5 end.
  assert (KL5 : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms5)) by (intros a Ha; apply AVw; lia).
  pose proof (fw_cstr_low tfibsegs W3 mem3 (ms_mem ms5) _ _ KL5 HCt) as HCt5.
  pose proof (fw_cstr_low tfibsegs W3 mem3 (ms_mem ms5) _ _ KL5 HCu) as HCu5.
  assert (B10 : getr (ms_regs ms5) 10 = w64 (cx_t cx + Z.of_nat (j + tk_nl p + 1))).
  { tl_reg HS (10%bv : bv 5). unfold w64. apply fw_sv_U.
    rewrite (U_atom_off _ 33 q 1) by (first [tl_o E1o; exact E33 | lia]). lia. }
  assert (B11 : getr (ms_regs ms5) 11 = w64 (cx_u cx + Z.of_nat (tk_nl2 p))).
  { tl_g HS. tl_o E1o. rewrite E34, Hlv. reflexivity. }
  assert (B12 : getr (ms_regs ms5) 12 = w64 (Z.of_nat (tk_ll cx p))).
  { tl_g HS. tl_o E1o. rewrite (EE 19%nat 19%bv eq_refl). exact R19. }
  assert (B2 : spZ (ms_regs ms5) = cx_sp cx - 208).
  { unfold spZ. tl_reg HS (2%bv : bv 5). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. tl_o E1o.
    rewrite Usp. reflexivity. }
  assert (B3 : getr (ms_regs ms5) 3 = w64 (as_gp B)).
  { tl_g HS. tl_o E1o. rewrite (EE 3%nat 3%bv eq_refl), Rgp. exact Hgp. }
  assert (B4 : getr (ms_regs ms5) 4 = w64 (as_tp B)).
  { tl_g HS. tl_o E1o. rewrite (EE 4%nat 4%bv eq_refl), Rtp. exact Htp. }
  assert (B1 : getr (ms_regs ms5) 1 = Z_to_bv 64 0x815c0) by (tl_g HS; reflexivity).
  tl_mk HS.
  eapply SRr_bind.
  { apply (tl_bcmp B BCMP W3 (ms_regs ms5) (ms_mem ms5) (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) ly3 S3 _
      (cx_sp cx) (cx_t cx) (cx_tb cx) (j + tk_nl p + 1) (cx_u cx) (cx_ub cx) (tk_nl2 p) (tk_ll cx p)
      (Z_to_bv 64 0x815c0) HJ HCt5 HCu5 ltac:(lia) ltac:(unfold tk_ll; lia) B10 B11 B12 B2
      ltac:(unfold cx_F in HFlo; lia) B3 B4 B1 ltac:(vm_compute; reflexivity)). }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & v2 & -> & HJ5 & HP5 & Hv2 & Hcmp2 & Hfr5 & Hpres5).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let K := eval vm_compute in (run_K 0 EX_Bx [] ss) in
    jafter_call_keep HS K regs5 (mrestrict (w_H W3) mem5) HP5 (@nil nat) HS2 end.
  match type of HS2 with ?tt -> _ => assert (HK : tt) end.
  { constructor. }
  specialize (HS2 HK). clear HK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok _ (havoc ?E4 ?K2 ?ws) _ _ =>
    let k4 := eval vm_compute in (K2 + 4)%nat in
    assert (EA2 : ew (havoc E4 K2 ws) k4 = v2)
      by (change k4 with (K2 + 4)%nat; rewrite (ew_havoc_new E4 K2 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
          transitivity (getr regs5 10); [reflexivity | exact Hv2]) end.
  assert (AV5 : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - 2 * ESTACK <= a < cx_F cx) ->
    aview tfibsegs (w_H W3) mem5 a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha Hn'. rewrite (Hfr5 a Ha ltac:(unfold cx_F in Hn'; lia)). exact (AVw a Ha Hn'). }
  clear AVw Hfr5. rename AV5 into AVw.
  clear SHOK.
  lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) =>
    assert (SHOK : sh_ok tfibsegs EX_Bx [] Ex (mrestrict (w_H W3) (ms_mem msx))) by constructor end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => change mem5 with (ms_mem msx) in HJ5 end.
  clear HJ. rename HJ5 into HJ.
  (* ---- the second bcmp's answer ---- *)
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  - (* a0 = 0: the three matches hold *)
    rewrite branch_eq_U, (tl_U_atom_w _ _ v2 EA2), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_eq in Hc.
    assert (M3 : v2 = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
    apply Hcmp2 in M3. clear Hc.
    assert (Hmid : tk_mid cx p j).
    { split; [exact M1|]. split; [unfold ManifestModel.byte_at; rewrite <- Hcd; exact Hc58|].
      rewrite M3. unfold tk_loc, tk_ll. rewrite <- length_skipn. apply firstn_all. }
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
    { awr_ok_tac. }
    tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    + (* j = 0: TK_E *)
      rewrite branch_eq_U, (U_atom _ 26 (Z.of_nat j)), U_SLit in Hc
        by (first [tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia]).
      change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. assert (Hj0 : j = 0%nat) by lia. clear Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_E; [awr_ok_tac|].
      tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
      tl_mk HS.
      tl_hmr B cx p ly3 S3 W3 regs3 mem3 md3 HS HJ HM HR AVw EE E32 E1o.
      apply (KE ly3 S3 W3 _ _ _).
      split; [exact HM'|]. split; [exact HR'|].
      split; [tl_g HS; tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
      split; [unfold tk_bound; lia|]. split; [exact HNO|]. split; [exact Hmid|].
      subst j. reflexivity.
    + (* j > 0: TK_B *)
      rewrite branch_eq_U, (U_atom _ 26 (Z.of_nat j)), U_SLit in Hc
        by (first [tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia]).
      change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. assert (Hj0 : (0 < j)%nat) by lia. clear Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_B; [awr_ok_tac|].
      tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
      tl_mk HS.
      tl_hmr B cx p ly3 S3 W3 regs3 mem3 md3 HS HJ HM HR AVw EE E32 E1o.
      apply (KB ly3 S3 W3 _ _ _).
      split; [exact HM'|]. split; [exact HR'|].
      split.
      { tl_reg HS (23%bv : bv 5). unfold w64. apply fw_sv_U.
        rewrite U_add_off_atom by (tl_o E1o; rewrite ?U23, ?U26; unfold M64; lia).
        tl_o E1o. rewrite ?U23, ?U26. lia. }
      split; [tl_g HS; tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
      split; [exact Hj0|]. split; [unfold tk_bound; lia|]. split; [exact HNO | exact Hmid].
  - (* a0 <> 0: text[j + nl + 1, + ll) differs from local: no token at j; TK_N *)
    rewrite branch_eq_U, (tl_U_atom_w _ _ v2 EA2), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_neq in Hc.
    assert (Hne : firstn (tk_ll cx p) (skipn (j + tk_nl p + 1) (cx_tb cx)) <> tk_loc cx p).
    { intros Heq. apply Hc. assert (Hv0 : v2 = w64 0).
      { apply Hcmp2. rewrite Heq. unfold tk_loc, tk_ll. rewrite <- length_skipn. symmetry. apply firstn_all. }
      rewrite Hv0. first [reflexivity | vm_compute; reflexivity]. }
    pose proof (tk_none_S cx p j HNO (tk_at_loc B cx p j HX Hne)) as HN1. clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_N; [awr_ok_tac|].
    tl_av W3 (cx_F cx - 2 * ESTACK) (cx_F cx).
    tl_mk HS.
    tl_hmr B cx p ly3 S3 W3 regs3 mem3 md3 HS HJ HM HR AVw EE E32 E1o.
    apply (KN ly3 S3 W3 _ _ _).
    split; [exact HM'|]. split; [exact HR'|].
    split; [tl_g HS; tl_o E1o; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
    split; [unfold tk_bound; lia | exact HN1].
Qed.
End W.

Print Assumptions tk_seg_LH_holds.
