(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 259 of its 305 lines of code are new or changed and 221 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_e.v, with its numbers changed; 225 of its 286 lines of code are new or changed and 244 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_tok_lha.v; 151 of its 203 lines of code are new or changed and 234 lines of the source are left out. *)
(* G4.ExTok.TokN: tk_seg_N (FMW_ex_tok_base.v): TK_N 0x815c4 .. j + 1 and the loop test of fuzz_manifest.c:103
   (expected.dis lines 294-298): back to TK_LH at j + 1, or out through the shared exit 0x814c8 .. 0x814e0 to EX_L at
   close + 1 (the token is absent). No byte of text is read, no call. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_tok_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the symbolic state at TK_N: registers are their own atoms; the frame (based at sp = F) holds the three slots the
   segment loads: F+0x58 text (atom 32), F+0x28 close = text + c (atom 32 plus atom 33 = c, so that the exit's
   `sub s3, a1, s7` normalizes to atom 33), F+0x60 the mask (atom 34) *)
Definition tkn_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 208 0 0
    [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x28 (CVal 8 (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)));
     YP09.mkChunk 0x60 (CVal 8 (SOff 34 0))].
Definition ss_TN : sstate := mkSS TK_N sr_atoms [tkn_frame] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).

(* FMW_plain.v's fw_reg / pl_mk / pl_g, renamed *)
Ltac tkn_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac tkn_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac tkn_g HS :=
  lazymatch goal with |- getr _ ?r = _ => tkn_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Definition tkn_extra (cx : ecx) (p : tkp) : list word :=
  [Z_to_bv 64 (cx_t cx); Z_to_bv 64 (Z.of_nat (tk_close p)); Z_to_bv 64 EX_MASK1].

Lemma tkn_entry : forall cx p ly3 S3 W3 regs3 mem3 md3,
  tk_mem B cx p ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (tkn_extra cx p)) ss_TN
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 TK_N) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx p ly3 S3 W3 regs3 mem3 md3 (HX & HC & HSL & V8 & V28 & V10 & V0).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _ & _ & _ & HCt & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  destruct HSL as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  pose proof HCt as (_ & Ht4096 & Htc & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (tkn_extra cx p)).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { subst E. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp. apply unsigned_lit_small.
    unfold cx_F, cx_sp. lia. }
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (tk_close p))) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 EX_MASK1) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (U32 : bv_unsigned (ew E 32) = cx_t cx) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = Z.of_nat (tk_close p)) by (rewrite E33; apply unsigned_lit_small; lia).
  unfold ss_TN. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (tkn_extra cx p)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tkn_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    unfold cx_F, cx_sp in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val tfibsegs E _ (spZ (cx_regs cx) - 208) 0x58 8 (SOff 32 0) (cx_t cx));
        [cbn [sv_denot]; rewrite Z.add_0_r, U32; reflexivity | cbn; lia | cbn; lia | exact S8].
    + apply (chunk_ok_val tfibsegs E _ (spZ (cx_regs cx) - 208) 0x28 8 (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))
        (cx_t cx + Z.of_nat (tk_close p))); [| cbn; lia | cbn; lia | exact V28].
      rewrite denot_lit_U, U_add_off_atom by (rewrite ?U32, ?U33; unfold M64; lia).
      rewrite U32, U33. f_equal; lia.
    + apply (chunk_ok_val tfibsegs E _ (spZ (cx_regs cx) - 208) 0x60 8 (SOff 34 0) EX_MASK1);
        [cbn [sv_denot]; rewrite Z.add_0_r, E34, unsigned_lit_small by (unfold EX_MASK1; lia); reflexivity
        | unfold EX_MASK1; cbn; lia | cbn; lia | exact S9].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [|exact I].
    unfold cx_F, cx_sp in *. split; [lia|].
    replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia. rewrite Z_mod_plus_full.
    split; [exact Hal16 | lia].
Qed.

Theorem tk_seg_N_holds : tk_seg_N B.
Proof.
  intros cx p j HLF KLH ly3 S3 W3 regs3 mem3 md3 (HM & HR & R26 & Hb & Hn).
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof (tkn_entry cx p ly3 S3 W3 regs3 mem3 md3 HM) as HS.
  pose proof HM as (HX & HC & HSL & V8 & V28 & V10 & V0).
  pose proof HX as (HB & _).
  pose proof HB as ((HPRE & _) & _ & _ & _ & HCt & _ & _ & _ & _ & HMAX).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  pose proof HR as (R8 & R18 & R22 & R20 & R21 & R24 & R27 & R19 & R9).
  pose proof (tk_decl_facts B cx p HX) as (D1 & D2 & D3 & D4 & D5).
  unfold tk_bound in Hb. unfold MANIFEST_MAX in HMAX.
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  remember (Ereg regs3 (tkn_extra cx p)) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hq; rewrite HE; apply ew_Ereg_nat; exact Hq).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (tk_close p))) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 EX_MASK1) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 2)).
  clear HE.
  assert (G24 : ew E 24 = Z_to_bv 64 (Z.of_nat (tk_ll cx p) + 1 + Z.of_nat (tk_nl p)))
    by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
  assert (G26 : ew E 26 = Z_to_bv 64 (Z.of_nat j)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (G27 : ew E 27 = Z_to_bv 64 (Z.of_nat (length (cx_tb cx))))
    by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (U24 : bv_unsigned (ew E 24) = Z.of_nat (tk_ll cx p) + 1 + Z.of_nat (tk_nl p))
    by (rewrite G24; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = Z.of_nat j) by (rewrite G26; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = Z.of_nat (tk_close p)) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U27 : U E (SOff 27 0) = Z.of_nat (length (cx_tb cx))) by (apply (U_atom E 27); [exact G27 | lia]).
  assert (UA : U E (SAlu ALU_ADD (SOff 24 1) (SOff 26 0)) =
    Z.of_nat (tk_ll cx p) + 1 + Z.of_nat (tk_nl p) + 1 + Z.of_nat j).
  { rewrite U_add_off_atom by (rewrite ?U24, ?U26; unfold M64; lia). rewrite U24, U26. lia. }
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 TK_N) mem3 (seg_rom tfibsegs))))) by constructor.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 TK_N) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 TK_N) with (Z_to_bv 64 TK_N).
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  - (* len >= ll + 1 + nl + j + 1: TK_LH at j + 1 *)
    rewrite branch_geu_U, U27, UA in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan TK_LH; [awr_ok_tac|].
    repeat rewrite wvb_collapse in HJ.
    assert (AV : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms0) a = aview tfibsegs (w_H W3) mem3 a).
    { intros a Ha. rewrite (fw_nowin tfibsegs _ _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) a Ha).
      exact (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a Ha). }
    tkn_mk HS.
    eassert (HM' : tk_mem B cx p ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _).
    { apply (tk_mem_move B cx p ly3 S3 W3 regs3 mem3 md3 _ _ _ (cx_F cx) HM HJ).
      - unfold cx_F, cx_sp. lia.
      - intros a Ha _. exact (AV a Ha).
      - tkn_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
      - tkn_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
      - tkn_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
      - tkn_g HS. rewrite (EE 25%nat 25%bv eq_refl). exact R25. }
    apply (KLH ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _).
    split; [exact HM'|]. split.
    { unfold tk_regs.
      split; [tkn_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
      split; [tkn_g HS; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      split; [tkn_g HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [tkn_g HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [tkn_g HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
      split; [tkn_g HS; exact G24|].
      split; [tkn_g HS; exact G27|].
      split; [tkn_g HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
      tkn_g HS; rewrite (EE 9%nat 9%bv eq_refl); exact R9. }
    split; [tkn_g HS; exact E32|].
    split; [tkn_g HS; rewrite U26; unfold w64; f_equal; lia|].
    split; [unfold tk_bound; lia | exact Hn].
  - (* len < ll + 1 + nl + j + 1: no token; EX_L at close + 1 *)
    rewrite branch_geu_U, U27, UA in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L; [awr_ok_tac|].
    repeat rewrite wvb_collapse in HJ.
    assert (AV : forall a, 0 <= a < 2 ^ 64 ->
      aview tfibsegs (w_H W3) (ms_mem ms0) a = aview tfibsegs (w_H W3) mem3 a).
    { intros a Ha. rewrite (fw_nowin tfibsegs _ _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) a Ha).
      exact (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a Ha). }
    tkn_mk HS.
    eassert (HM' : tk_mem B cx p ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _).
    { apply (tk_mem_move B cx p ly3 S3 W3 regs3 mem3 md3 _ _ _ (cx_F cx) HM HJ).
      - unfold cx_F, cx_sp. lia.
      - intros a Ha _. exact (AV a Ha).
      - tkn_g HS. rewrite (EE 2%nat 2%bv eq_refl). exact Rsp.
      - tkn_g HS. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
      - tkn_g HS. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
      - tkn_g HS. rewrite (EE 25%nat 25%bv eq_refl). exact R25. }
    assert (Htok : ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = false)
      by (apply (tk_none_false B cx p (S j) HX Hn); lia).
    destruct (tk_scan_next B cx p HX Htok) as (Hlt & Hsc).
    destruct HM' as (_ & HC' & HSL' & _).
    apply (HLF (S (tk_close p)) (S (tk_d p)) (pred (tk_f p)) ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ Hlt).
    unfold ex_at_L.
    split; [exact HB|]. split; [exact HC'|]. split; [exact HSL'|].
    split.
    { unfold ex_sregs.
      split; [tkn_g HS; exact E32|].
      split; [tkn_g HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [tkn_g HS; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      tkn_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8. }
    split; [exact Hsc|].
    split; [tkn_g HS; rewrite U33; unfold w64; f_equal; lia|].
    split; [tkn_g HS; reflexivity|].
    split; [tkn_g HS; reflexivity|].
    tkn_g HS. exact E34.
Qed.
End W.

Print Assumptions tk_seg_N_holds.
