(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:49-57;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:337-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:193-195, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg1.v, with its module paths, module names and numbers changed; 459 of its 550 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/SbDecSeg1.v, with its module paths, module names and numbers changed; 1841 of its 1900 lines of code are new or changed and 491 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_rd_pl.v, with its module paths and module names changed; 919 of its 1019 lines of code are new or changed and 1800 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_rd_lp.v; 181 of its 221 lines of code are new or changed and 979 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp_w3.v (a working branch e2e59892bef),
   re-walked on B's code (B-readings.lst 0x8215c .. 0x821a8 and CONT 0x81ffc .. 0x82010). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP, piece W3: the third inner loop at L3 0x8215c
   (lv2_locate.c:126, the spaces after the name's ':'), pp_seg_W3 of lib/B/FMW_rd_pp_cuts.v. One iteration checks
   and loads the byte c at s8 + 1 = text + S p2 + j (0x8215c .. 0x82170) and tests it (0x82178 bgeu (c - 9, s3 = 5),
   0x82190 bne (c, s2 = 32), 0x821a8 bne (c, '<')): a space (0x8217c: s9, s10 -= 1, s8 += 1, the back edge
   0x82188) goes back to the head at j + 1; '<' falls into ST 0x821ac (pp_seg_ST) with p3 = S p2 + j; any other byte
   makes the declaration DNone (readings_scan.db_nlt) and CONT (0x81ffc .. 0x8200c) goes on to L at i + 1 (pp_to_L).
   The loop closes by strong induction on |text| - (S p2 + j).
   UBSan guards (trap 0x823b4): the back edge 0x82188 (bne a0,s0) with its fall-through 0x8218c (j trap) is decided
   by the token engine from the entry fact 4096 <= s8 <= 2^47 - 16 (class K1n); CONT's 0x8200c (bne a0,s0, a0 = at)
   surfaces as a branch whose not-taken arm, the fall-through 0x82010 (j trap), pp_guard refutes (K1n,
   fmt_ne_taken: at = text + i is not -1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the walk's tactics ---- *)
(* a read-only run: its memory is the cut's (FMW_rd_lp.v lp_mem) *)
Ltac w3_mem m0 :=
  lazymatch goal with H : frame_of ?Ex ?rs ?mp (ms_mem ?m1) |- _ =>
    let Hm := fresh "Hmem" in
    assert (Hm : ms_mem m1 = m0) by
      (rewrite (frame_of_read_only Ex rs mp (ms_mem m1) ltac:(vm_compute; reflexivity) H);
       first [reflexivity | assumption]) end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the machine state of the goal, as mkst at a literal pc, over the cut's memory (FMW_rd_lp.v lp_mk) *)
Ltac w3_mk HS :=
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end;
  repeat match goal with Hm : ms_mem ?x = _ |- _ => rewrite Hm in * end.
(* a register after a run: a literal the state pins, or the engine's value over the entry facts (pp_g) *)
Ltac w3_g HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms') =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      lazymatch e with
      | SLit _ =>
          rewrite (st_ok_restrict_reg segs H Ev ss ms' r HS); change (sr_get (ss_regs ss) r) with e;
          cbn [sv_denot]; reflexivity
      | _ => pp_g HS
      end end end.
(* a register the run keeps as its entry atom: the cut's register (EE : ew E n = getr regs q) *)
Ltac w3_qq HS EE :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms') =>
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      rewrite (st_ok_restrict_reg segs H Ev ss ms' r HS); change (sr_get (ss_regs ss) r) with e;
      cbn [sv_denot ew ewset extK havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
      rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact (EE n r eq_refl) end end.
Ltac w3_kept HS EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [PP_KEPT In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [w3_qq HS EE |]); destruct Hr.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

Lemma w3_loop : forall f, rd_seg_L B CTX f -> pp_seg_ST B CTX f ->
  forall r cx i d s11 p1 p2 j ly3 S3 W3 regs mem md,
  r = (length (cx_tb cx) - (S p2 + j))%nat -> rd_base B CTX cx ->
  pp_at_L3 B cx i d (S f) s11 p1 p2 j ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L3 regs mem md) (rd_post B cx).
Proof.
intros f HL HST r. induction r as [r IH] using lt_wf_ind.
intros cx i d s11 p1 p2 j ly3 S3 W3 regs mem md Hr HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HP as ((HI & HA & Hi & Hh & Hs11 & Hsp0 & R21) & Ep1 & Ep2 & H58 & Hjc & HS48 & R22 & R24 & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
pose proof HFR as (V58 & Hu2 & HFc & HF2 & HF16).
assert (Hp2 : (p2 < length (cx_tb cx))%nat) by (apply pp_lt_of_nz; rewrite H58; lia).
assert (Hle : (S p2 + j <= length (cx_tb cx))%nat)
  by (pose proof (pp_cw_le is_space (cx_tb cx) (S p2)); lia).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (S p2 + j) Ct Hle) as [Vc Hcr].
set (c := byte_at (cx_tb cx) (S p2 + j)) in *.
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (cx_t cx + Z.of_nat p2 + Z.of_nat j + 1) 1 c)
  by (replace (cx_t cx + Z.of_nat p2 + Z.of_nat j + 1) with (cx_t cx + Z.of_nat (S p2 + j)) by lia; exact Vc).
pose proof (pp_entry_L3 W3 regs mem (cx_F cx) (cx_t cx + Z.of_nat p2 + Z.of_nat j) c R2 R27 HPN HFc HF2 HF16 R24
  ltac:(lia) ltac:(lia) Hcr Vc') as HS.
remember (Ereg regs (pp_extra 0 c 0)) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = w64 c) by (rewrite HE; exact (ew_Ereg_extra regs _ 1)).
clear HE.
assert (E9 : ew E 9 = w64 (Z.of_nat d)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = w64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (cx_t cx + Z.of_nat p1)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (cx_t cx + Z.of_nat p2 + Z.of_nat j)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - pp_s10_L3 i s11 p2 j))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - pp_s10_L3 i s11 p2 j))
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
unfold pp_s10_L3 in E25, E26.
assert (HBx : U E PP_Bx = SHADOW_OFF) by exact (pp_U_Bx E E27).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L3) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L3) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_L3) with (Z_to_bv 64 PP_L3).
(* 0x8215c .. 0x82178: a0 = s8 + 1, its shadow, the byte c at a0, bgeu (c - 9, 5) *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ apply (pp_obl1 W3 _ E (SOff 24 1) (cx_t cx) (cx_tb cx) Ct HBx);
    rewrite (pp_U_off E 24%nat _ 1 E24); unfold zcanon, M64; rewrite Z.mod_small by lia; lia. }
{ awr_ok_tac. }
w3_mem mem.
srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
- (* c - 9 >=u 5: 0x82190 bne (c, 32) *)
  pp_decb HS E33 c Hc.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  w3_mem mem.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* c <> 32: not a space; 0x821a4 a2 = '<', 0x821a8 bne (c, '<') *)
    pp_decb HS E33 c Hc0.
    assert (Hns : is_space c = false) by exact (pp_sp_no c Hcr Hc Hc0).
    assert (Hcw : count_while is_space (skipn (S p2) (cx_tb cx)) = j)
      by exact (pp_cw_exact is_space (cx_tb cx) (S p2) j Hjc Hns).
    aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
    { awr_ok_tac. }
    w3_mem mem.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * (* c <> '<': the declaration is DNone; CONT 0x81ffc .. 0x8200c *)
      pp_decb HS E33 c Hc1.
      assert (Hn60 : c <> 60) by exact (pp_lt_no c Hcr Hc1).
      assert (Hdecl : decl (cx_tb cx) i = DNone).
      { rewrite (readings_scan.decl_some (cx_tb cx) i (i + s11)%nat Hh).
        apply (readings_scan.db_nlt (cx_tb cx) (i + s11)%nat p1 p2 (S p2 + j)%nat Hsp0 Ep1 Ep2 H58);
          [rewrite Hcw; reflexivity | exact Hn60]. }
      aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
      { awr_ok_tac. }
      w3_mem mem.
      srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
      -- (* 0x8200c bne (at, -1) taken: the scan goes on at i + 1 *)
         aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan RD_L.
         { awr_ok_tac. }
         w3_mem mem. w3_mk HS.
         apply (pp_to_L B CTX f cx i d ly3 S3 W3 _ mem _ HL HB).
         ++ apply (pp_loop_keep B cx d ly3 S3 W3 regs mem md _ _ HI HJ); [w3_kept HS EE | w3_g HS ..].
         ++ exact HA.
         ++ exact Hi.
         ++ exact Hdecl.
         ++ w3_g HS.
      -- (* the fall-through 0x82010 (j 0x823b4): at = text + i is not -1 *)
         pp_guard Hc2.
    * (* c = '<': ST 0x821ac with p3 = S p2 + j *)
      pp_decb HS E33 c Hc1.
      assert (H60 : c = 60) by exact (pp_lt_yes c Hcr Hc1).
      assert (Hp3 : (S p2 + j < length (cx_tb cx))%nat) by (apply pp_lt_of_nz; fold c; lia).
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_ST.
      { awr_ok_tac. }
      w3_mem mem. w3_mk HS.
      apply (HST cx i d s11 p1 p2 (S p2 + j)%nat ly3 S3 W3 _ mem _ HB).
      unfold pp_at_ST, pp_head.
      split; [split|].
      -- apply (pp_loop_keep B cx d ly3 S3 W3 regs mem md _ _ HI HJ); [w3_kept HS EE | w3_g HS ..].
      -- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|].
         split; [exact Hsp0|]. w3_g HS.
      -- split.
         { unfold rd_decl. cbv zeta.
           split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
           split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|].
           split; [rewrite Hcw; reflexivity|]. split; [exact H60 | lia]. }
         split; [exact HS48|].
         split; [w3_g HS|]. split; [w3_g HS|]. split; [w3_g HS|].
         unfold pp_cd, rd_s10. split; w3_g HS.
  + (* c = 32: a space; 0x82194 -> 0x8217c .. 0x82188, back to the head at j + 1 *)
    pp_decb HS E33 c Hc0.
    assert (Hsp : is_space c = true) by exact (pp_sp_32 c Hcr Hc Hc0).
    assert (Hlt : (S p2 + j < length (cx_tb cx))%nat)
      by (apply pp_lt_of_nz; fold c; exact (pp_sp_nz c Hsp)).
    assert (Hjc' : (S j <= count_while is_space (skipn (S p2) (cx_tb cx)))%nat)
      by exact (pp_cw_next is_space (cx_tb cx) (S p2) j Hjc Hsp Hlt).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3.
    { awr_ok_tac. }
    w3_mem mem. w3_mk HS.
    apply (IH (length (cx_tb cx) - (S p2 + S j))%nat ltac:(lia) cx i d s11 p1 p2 (S j) ly3 S3 W3 _ mem _
      eq_refl HB).
    unfold pp_at_L3, pp_head.
    split; [split|].
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs mem md _ _ HI HJ); [w3_kept HS EE | w3_g HS ..].
    * split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|].
      split; [exact Hsp0|]. w3_g HS.
    * split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|]. split; [exact Hjc'|].
      split; [exact HS48|].
      split; [w3_g HS|]. split; [w3_g HS|].
      unfold pp_cd, pp_s10_L3. split; w3_g HS.
- (* c - 9 <u 5: c is \t .. \r, a space; 0x8217c .. 0x82188, back to the head at j + 1 *)
  pp_decb HS E33 c Hc.
  assert (Hsp : is_space c = true) by exact (pp_sp_in c Hcr Hc).
  assert (Hlt : (S p2 + j < length (cx_tb cx))%nat)
    by (apply pp_lt_of_nz; fold c; exact (pp_sp_nz c Hsp)).
  assert (Hjc' : (S j <= count_while is_space (skipn (S p2) (cx_tb cx)))%nat)
    by exact (pp_cw_next is_space (cx_tb cx) (S p2) j Hjc Hsp Hlt).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3.
  { awr_ok_tac. }
  w3_mem mem. w3_mk HS.
  apply (IH (length (cx_tb cx) - (S p2 + S j))%nat ltac:(lia) cx i d s11 p1 p2 (S j) ly3 S3 W3 _ mem _
    eq_refl HB).
  unfold pp_at_L3, pp_head.
  split; [split|].
  + apply (pp_loop_keep B cx d ly3 S3 W3 regs mem md _ _ HI HJ); [w3_kept HS EE | w3_g HS ..].
  + split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|].
    split; [exact Hsp0|]. w3_g HS.
  + split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|]. split; [exact Hjc'|].
    split; [exact HS48|].
    split; [w3_g HS|]. split; [w3_g HS|].
    unfold pp_cd, pp_s10_L3. split; w3_g HS.
Qed.

Theorem pp_w3_holds : forall f, rd_seg_L B CTX f -> pp_seg_ST B CTX f -> pp_seg_W3 B CTX f.
Proof.
intros f HL HST cx i d s11 p1 p2 j ly3 S3 W3 regs mem md HB HP.
exact (w3_loop f HL HST _ cx i d s11 p1 p2 j ly3 S3 W3 regs mem md eq_refl HB HP).
Qed.
End c.
