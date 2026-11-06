(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths, module names and numbers changed; 325 of its 448 lines of code are new or changed and 306 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/check_provenance_lem.v, with its module paths and module names changed; 181 of its 211 lines of code are new or changed and 418 lines of the source are left out. *)
(* nl_error on image A: the two phases of the head (nl_error_defs.v), after frame_alloc_1 (nl_error.v walks the
   entry up to it).
   JE -> J0: +0x7c..+0x11c (s4 := s9 := F, s3 := w + 4096, `bnez s4` taken since F >= 4096, F + 0, 8, 16 := the
   frame's description, s8 := F's shadow address, its bytes 0..11 := f1 f1 f1 f1 f8 f8 f8 f3 f3 f3 f3 f3, s11 := the
   shadow address of w + 4096), a plain run (it writes F's shadow).
   J0 -> J1: +0x120..+0x1ac (check C1, F into the spill slot sp1 + 48, s6 := n, nl_put32(w, 0)), as nl_error_puts.v's
   put32 phases.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide PcapRelro nl_error_c nl_error_defs nl_error_kit nl_error_puts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* a plain run from a seated state up to `stop`: leaves the write obligation and the continuation *)
Ltac ne_run_to_plain RUNP HS HJ stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
  lazymatch type of RUNP with
  | context [sym_run_toN_pi ?tpi _ _ _] =>
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNP W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ); clear Hrun
    end end end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma ne_sv51 : forall cx pos regs3 n f, sv_denot (ne_E cx pos regs3 n f) (SOff 51 0) = getr (n_regs cx) 22.
Proof.
  intros cx pos regs3 n f. change (SOff 51 0) with (SOff (44 + 7) 0). cbn [sv_denot].
  rewrite (ne_Esave cx pos regs3 n f 7 ltac:(lia)), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ne_updE_ok : forall cx pos regs3 n f,
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rvE cx pos) ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_updE.
Proof.
  intros cx pos regs3 n f HR. unfold ne_rvE in HR.
  inversion HR as [|? ? R10 HR1]; subst; inversion HR1 as [|? ? R18 HR2]; subst;
  inversion HR2 as [|? ? R19 HR3]; subst; inversion HR3 as [|? ? R23 HR4]; subst;
  inversion HR4 as [|? ? R22 _]; subst. cbn [fst snd] in *.
  unfold ne_updE. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R10. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R18. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R19. reflexivity.
  - rewrite R23. symmetry. apply ne_sv42.
  - rewrite R22. symmetry. apply ne_sv51.
Qed.

Lemma ne_upd0_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rv0 cx pos) ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_upd0.
Proof.
  intros cx pos regs3 n f HB HR. unfold ne_rv0 in HR.
  inversion HR as [|? ? R18 HR1]; subst; inversion HR1 as [|? ? R20 HR2]; subst;
  inversion HR2 as [|? ? R23 HR3]; subst; inversion HR3 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_upd0. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R18. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R23. symmetry. apply ne_sv42.
  - rewrite R22. symmetry. apply ne_sv51.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

(* PHASE JE -> J0 *)
Lemma ne_ph_JE : forall POST, ne_from SK B POST NE_J0 (ne_J0i SK B) -> ne_from SK B POST NE_JE (ne_JEi SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (HJ & HRV).
  set (n := ne_n0 cx) in *. set (f := nw_full (n_bs cx)) in *.
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & HF64 & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_updE_ok cx pos regs3 n f HRV).
  assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
  destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_JE ne_updE true [] [] HB HFc HJ HU HX I)
    as (HEI & HS & _).
  pose proof HS as HS0.
  pose (RUNP := paj_run_to_plain_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  ne_run_to_plain RUNP HS HJX (AF_nl_error + NE_J0).
  - exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ true [] HB HFc HJ HX).
  - intros ms mat HS' HJX' HF HFr HG. cbn [ms_mem restrict mkst] in HFr, HG. clear HS. rename HS' into HS.
    pmkst HS. apply (HN cx pos S3 memA); [exact HB | exact HFc |].
    split.
    + assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; apply ne_E33).
      assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
      assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
      ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_JE ne_updE true (@nil YP09.region) (@nil acond)
        HB HFc HJ HX HS0 HS HJX' HFr HG n f (SOff 33 0) (SOff 34 0) Hen Hef Hn' Hfr.
      * intros Hc; discriminate Hc.
      * intros _. eapply ne_sh_after; [exact HS | vm_compute; reflexivity |].
        rewrite ne_E38. apply unsigned_lit_small. unfold ne_Fsh, shadow_addr, SHADOW_OFF.
        assert (0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        lia.
    + unfold ne_rv0. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      [ ne_reg HS (18%bv : bv 5); apply sv_off0; apply ne_E35
      | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E36
      | ne_reg HS (23%bv : bv 5); apply ne_sv42
      | ne_reg HS (22%bv : bv 5); apply ne_sv51
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].
Qed.

(* PHASE J0 -> J1: C1, F's spill, s6 := n, nl_put32(w, 0) *)
Lemma ne_ph_J0 : forall POST, ne_from SK B POST NE_J1 (ne_JA SK B) -> ne_from SK B POST NE_J0 (ne_J0i SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (HJ & HRV).
  set (n := ne_n0 cx) in *. set (f := nw_full (n_bs cx)) in *.
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_upd0_ok cx pos regs3 n f HB HRV).
  assert (E33 : ew (ne_E cx pos regs3 n f) 33 = Z_to_bv 64 n) by apply ne_E33.
  destruct (Z_le_gt_dec n 4092) as [Hroom|Hfull].
  - (* room: 4 zero bytes at w + n, n := n + 4 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J0 ne_upd0 false [ne_put_region 4] ne_room32
      HB HFc HJ HU ltac:(right; right; left; split; [reflexivity | lia])
      ltac:(split; [apply (ne_acond_ltu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J1).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [ne_put_region 4] HB HFc HJ
        ltac:(right; right; left; split; [reflexivity | lia])).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists (n + 4), f. split.
      * assert (HX : ne_xr_ok cx n [ne_put_region 4]) by (right; right; left; split; [reflexivity | lia]).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 4) = w64 (n + 4))
          by (rewrite (sv_offc _ 33 n 4 E33) by lia; reflexivity).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
        assert (Hn' : n <= n + 4 <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J0 ne_upd0 false [ne_put_region 4] ne_room32
          HB HFc HJ HX HS0 HS HJX HFr HG (n + 4) f (SOff 33 4) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * unfold ne_rvA. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        [ ne_reg HS (11%bv : bv 5); reflexivity
        | ne_reg HS (18%bv : bv 5); apply sv_off0; apply ne_E35
        | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E36
        | ne_reg HS (23%bv : bv 5); apply ne_sv42
        | ne_reg HS (22%bv : bv 5); apply sv_off0; exact E33
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].
  - (* no room: full := 1 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J0 ne_upd0 false [] ne_full32
      HB HFc HJ HU ltac:(left; reflexivity)
      ltac:(split; [apply (ne_acond_geu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J1).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ ltac:(left; reflexivity)).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, 1. split.
      * assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SLit 1) = w64 1) by reflexivity.
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        assert (Hf' : 0 <= 1 <= 1) by lia.
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J0 ne_upd0 false (@nil YP09.region) ne_full32
          HB HFc HJ HX HS0 HS HJX HFr HG n 1 (SOff 33 0) (SLit 1) Hen Hef Hn' Hf'.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * unfold ne_rvA. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        [ ne_reg HS (11%bv : bv 5); reflexivity
        | ne_reg HS (18%bv : bv 5); apply sv_off0; apply ne_E35
        | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E36
        | ne_reg HS (23%bv : bv 5); apply ne_sv42
        | ne_reg HS (22%bv : bv 5); apply sv_off0; exact E33
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].
Qed.

End b.
End a.
