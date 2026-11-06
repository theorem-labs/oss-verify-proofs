(* G4.ExDecl part d3c: dseg_D3c (FMW_ex_decl_base.v:377). From D3c (0x81490, the '<' at p3 found):
   0x81490 a1 = '>', 0x81494 a0 = s7 = text + S p3 = ns, 0x81498 jal strchr (PC_strchr 0x412e0, ra 0x8149c)
   [expected.dis 217-219]. strchr (ns, '>') on l = skipn (S p3) text (dd_cstr_suffix) decides the model's declaration
   (dm_decl_gt): no '>' (r = 0) is DCut (dm_find_none), a first '>' at o (r = ns + o) is
   DFound p1 (p2 - p1) (S p3) o (S p3 + o) (dm_find_some). dat_D4 at the return EX_D4 (0x8149c): the callee-saved
   registers kept (aregs_preserved), the memory kept outside strchr's window [F - STK_RT_STR, F) (dd_com_kept,
   dd_slots_kept); then SD4. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* D3c's symbolic state: the registers as atoms; the three instructions touch no memory *)
Definition ss_D3c : sstate := mkSS EX_D3c sr_atoms [] None (mkFacts [] [] []).

(* a register of a symbolic state as its sv's value (FMW_plain.v fw_reg) *)
Ltac d3c_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma d3c_entry : forall (W3 : world tfibsegs) regs3 mem3,
  st_ok tfibsegs (Ereg regs3 []) ss_D3c
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D3c) mem3 (seg_rom tfibsegs))).
Proof.
  intros W3 regs3 mem3. rewrite restrict_mkst_fx. unfold ss_D3c.
  apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I].
Qed.

Hypothesis SD4 : dseg_D4 B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.

Theorem decl_D3c_holds : dseg_D3c B.
Proof.
  intros cx i d f a1 p1 p2 p3 ly3 S3 W3 regs3 mem3 md3 HLf HD.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  destruct HD as (HDC & HP3 & R20 & R21 & R24 & R19 & R9 & R23 & R27 & R26).
  pose proof HDC as (HB & HC & HSL & R22 & R18 & R8 & Hscan & Hilt).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & _).
  assert (HSTK : STK_expected = 8432) by reflexivity.
  assert (HRS : STK_RT_STR = 8192) by reflexivity.
  assert (HFe : cx_F cx = cx_sp cx - 208) by reflexivity.
  (* the model: the '<' at p3 is inside the text *)
  pose proof HP3 as ((((Hh & Ha1 & Hs) & Q1) & Q2 & Hc) & Q3 & Hl).
  assert (Hp3 : (p3 < length (cx_tb cx))%nat)
    by (apply expected_m.byte_at_nz_lt; rewrite Hl; discriminate).
  assert (Hle : (S p3 <= length (cx_tb cx))%nat) by lia.
  pose proof (dd_cstr_suffix W3 mem3 (cx_t cx) (cx_tb cx) (S p3) Ct Hle) as Cs.
  (* the run 0x81490 .. 0x81498 to strchr *)
  pose proof (d3c_entry W3 regs3 mem3) as HS.
  set (E := Ereg regs3 []) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; subst E; apply ew_Ereg_nat; exact Hn).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { rewrite (EE 2%nat 2%bv eq_refl), R2. apply unsigned_lit_small. lia. }
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D3c) mem3 (seg_rom tfibsegs))))) by constructor.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D3c) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D3c) with (Z_to_bv 64 EX_D3c).
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha. apply (fw_nowin tfibsegs _ _ _ _ _ HFr); [vm_compute; reflexivity | exact Ha]. }
  assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (intros a Ha; apply AV; lia).
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
  rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  (* strchr (text + S p3, '>') *)
  eapply SRr_bind.
  { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strchr STK_RT_STR
      (fun v => (v = 0 /\ ~ In 62 (skipn (S p3) (cx_tb cx))) \/
                (exists j, first_at (skipn (S p3) (cx_tb cx)) 62 j /\ v = cx_t cx + Z.of_nat (S p3) + Z.of_nat j))
      W3 (ms_regs ms) (ms_mem ms) STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) []
      ly3 S3 _ 0 (-208) (Z_to_bv 64 0x8149c) HJ).
    - unfold spZ at 1. rewrite Rsp, Usp. rewrite HFe. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - exact Rra.
    - vm_compute. reflexivity.
    - intros HPK.
      apply (STRCHR ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_t cx + Z.of_nat (S p3)) 62 (skipn (S p3) (cx_tb cx)) HPK).
      + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL HRO))).
      + exact (proj1 (proj2 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL HRO)))).
      + rewrite Ra0, (EE 23%nat 23%bv eq_refl). exact R23.
      + rewrite Ra1. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
      + lia.
      + exact (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL Cs). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & HR & Hfr2 & Hpres2).
  change (SRr tfibsegs W3 (cfg_at tfibsegs EX_D4 regs2 mem2 md2) (ex_post B cx)).
  (* the callee-saved registers: strchr keeps them, the run left them as at D3c *)
  assert (PR : forall q, acallee_saved q -> getr regs2 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q)).
  { intros q Hq. rewrite (HP2 q Hq). unfold acallee_saved in Hq.
    assert (Hq' : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
      q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
    repeat (destruct Hq' as [->|Hq']); try subst q;
      lazymatch goal with |- getr _ ?r = _ => d3c_reg HS r end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity. }
  (* the memory: kept outside strchr's window *)
  assert (HK : dd_kept cx W3 mem3 mem2).
  { intros a Ha H1 H2 H3. rewrite Hfr2 by lia. exact (AV a Ha). }
  assert (HC2 : ex_com B cx ly3 S3 W3 regs2 mem2 md2).
  { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 regs2 mem2 md2 HB HC HJ2 HK).
    - exact (PR 2 ltac:(unfold acallee_saved; lia)).
    - exact (PR 3 ltac:(unfold acallee_saved; lia)).
    - exact (PR 4 ltac:(unfold acallee_saved; lia)).
    - exact (PR 25 ltac:(unfold acallee_saved; lia)). }
  assert (HSL2 : ex_slots cx W3 mem2 d).
  { apply (dd_slots_kept B cx W3 mem3 mem2 d HB HSL). intros a Ha. rewrite Hfr2 by lia. apply AV. lia. }
  assert (HDC2 : dd_com B cx i d f ly3 S3 W3 regs2 mem2 md2).
  { split; [exact HB|]. split; [exact HC2|]. split; [exact HSL2|].
    split; [exact (eq_trans (PR 22 ltac:(unfold acallee_saved; lia)) R22)|].
    split; [exact (eq_trans (PR 18 ltac:(unfold acallee_saved; lia)) R18)|].
    split; [exact (eq_trans (PR 8 ltac:(unfold acallee_saved; lia)) R8)|].
    split; [exact Hscan | exact Hilt]. }
  assert (T20 := eq_trans (PR 20 ltac:(unfold acallee_saved; lia)) R20).
  assert (T21 := eq_trans (PR 21 ltac:(unfold acallee_saved; lia)) R21).
  assert (T24 := eq_trans (PR 24 ltac:(unfold acallee_saved; lia)) R24).
  assert (T19 := eq_trans (PR 19 ltac:(unfold acallee_saved; lia)) R19).
  assert (T9 := eq_trans (PR 9 ltac:(unfold acallee_saved; lia)) R9).
  assert (T23 := eq_trans (PR 23 ltac:(unfold acallee_saved; lia)) R23).
  assert (T27 := eq_trans (PR 27 ltac:(unfold acallee_saved; lia)) R27).
  assert (T26 := eq_trans (PR 26 ltac:(unfold acallee_saved; lia)) R26).
  (* the model's declaration from strchr's answer *)
  pose proof (dm_decl_gt (cx_tb cx) i (i + a1) p1 p2 p3 Hh Hs Q1 Q2 Q3 Hc Hl) as Hdecl.
  destruct HR as [(Hv0 & Hni) | (j & Hj & Hvj)].
  - (* no '>': DCut, r = 0 *)
    rewrite (dm_find_none _ Hni) in Hdecl.
    apply (SD4 cx i d f p1 (p2 - p1)%nat (S p3) 0%nat 0%nat 0 ly3 S3 W3 regs2 mem2 md2 HLf).
    split; [exact HDC2|].
    split; [left; split; [exact Hdecl | reflexivity]|].
    split; [rewrite Hv, Hv0; reflexivity|].
    split; [exact T20|]. split; [exact T21|]. split; [exact T24|]. split; [exact T19|]. split; [exact T9|].
    split; [exact T23|]. split; [exact T27 | exact T26].
  - (* the first '>' at j: DFound, r = text + S p3 + j *)
    rewrite (dm_find_some _ _ Hj) in Hdecl.
    apply (SD4 cx i d f p1 (p2 - p1)%nat (S p3) j (S p3 + j)%nat v ly3 S3 W3 regs2 mem2 md2 HLf).
    split; [exact HDC2|].
    split; [right; split; [exact Hdecl | rewrite Hvj; lia]|].
    split; [exact Hv|].
    split; [exact T20|]. split; [exact T21|]. split; [exact T24|]. split; [exact T19|]. split; [exact T9|].
    split; [exact T23|]. split; [exact T27 | exact T26].
Qed.
End W.

Check decl_D3c_holds.
Print Assumptions decl_D3c_holds.
