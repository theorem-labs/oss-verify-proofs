(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths, module names and numbers changed; 313 of its 439 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_provenance_lem.v, with its module paths and module names changed; 292 of its 325 lines of code are new or changed and 406 lines of the source are left out. *)
(* nl_error on image A: the four put phases of the walk (nl_error_defs.v): from each join J1 .. J4 to the next.
   nl_put16(w, 2) +0x1b0..+0x234 (J1 -> J2), nl_put16(w, 0) +0x238..+0x2b8 (J2 -> J3), nl_put32(w, 1)
   +0x2bc..+0x344 (J3 -> J4), nl_put32(w, 0) +0x348..+0x3dc (J4 -> J5).

   Each phase splits on the room test before it runs (n + k <= 4096 or not) and seats the symbolic state with the
   decided test as an engine condition (ne_seat's xc), so the engine takes the one arm by itself: on the room arm
   with the put's region at w + n (ne_put_region k), checks C1, C3 / C4 passing by the shadow entries of ne_SH,
   the k bytes stored and n := n + k; on the no-room arm check C2 and full := 1. No path is walked twice; both
   arms end at the next join, which ne_after reads back from the run's end state.

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
link_aaddr link_amem LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide PcapRelro nl_error_c nl_error_defs nl_error_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the room tests: put16 compares 2 ^ 64 - 4098 <u n - 4095 (room iff n <= 4094), put32 2 ^ 64 - 4098 <u n - 4093
   (room iff n <= 4092) *)
Definition NE_C16 : Z := 18446744073709547518.
Definition ne_room16 : list acond := [mkAC BC_LTU (SLit NE_C16) (SOff 33 (-4095))].
Definition ne_full16 : list acond := [mkAC BC_GEU (SLit NE_C16) (SOff 33 (-4095))].
Definition ne_room32 : list acond := [mkAC BC_LTU (SLit NE_C16) (SOff 33 (-4093))].
Definition ne_full32 : list acond := [mkAC BC_GEU (SLit NE_C16) (SOff 33 (-4093))].

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

(* the code (a1 at entry) through its atom 42 *)
Lemma ne_sv42 : forall cx pos regs3 n f, sv_denot (ne_E cx pos regs3 n f) (SOff 42 0) = getr (n_regs cx) 11.
Proof.
  intros cx pos regs3 n f. cbn [sv_denot]. rewrite ne_E42, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* the J1 .. J4 registers, as the seat's Forall premise *)
Lemma ne_updA_ok : forall cx pos regs3 n f, ne_base SK B cx ->
  Forall (fun rw : bv 5 * word => getr regs3 (fst rw) = snd rw) (ne_rvA cx pos) ->
  0 <= ne_w cx < 2 ^ 64 -> 0 <= ne_F cx pos < 2 ^ 64 ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) ne_updA.
Proof.
  intros cx pos regs3 n f HB HR Hw HF. unfold ne_rvA in HR.
  inversion HR as [|? ? R11 HR1]; subst; inversion HR1 as [|? ? R18 HR2]; subst;
  inversion HR2 as [|? ? R20 HR3]; subst; inversion HR3 as [|? ? R23 HR4]; subst;
  inversion HR4 as [|? ? R22 HRx]; subst;
  inversion HRx as [|? ? Q19 HRy]; subst; inversion HRy as [|? ? Q24 HRz]; subst;
  inversion HRz as [|? ? Q25 HRw]; subst; inversion HRw as [|? ? Q27 _]; subst. cbn [fst snd] in *.
  unfold ne_updA. repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
  - rewrite R11. reflexivity.
  - rewrite R18. symmetry. apply sv_off0. apply ne_E35.
  - rewrite R20. symmetry. apply sv_off0. apply ne_E36.
  - rewrite R23. symmetry. apply ne_sv42.
  - rewrite R22. symmetry. apply sv_off0. apply ne_E41.
  - rewrite Q19. symmetry. apply ne_den19.
  - rewrite Q24. symmetry. apply sv_off0. apply ne_E38.
  - rewrite Q25. symmetry. apply sv_off0. apply ne_E36.
  - rewrite Q27. symmetry. exact (ne_den27 SK B cx pos regs3 n f HB).
Qed.

(* the J1 .. J4 registers at the end of a put run *)
Ltac ne_rvA_after HS :=
  unfold ne_rvA; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  [ ne_reg HS (11%bv : bv 5); reflexivity
  | ne_reg HS (18%bv : bv 5); apply sv_off0; apply ne_E35
  | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (23%bv : bv 5); apply ne_sv42
  | ne_reg HS (22%bv : bv 5); apply sv_off0; apply ne_E41
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].

(* the J5 registers at the end of the last put run *)
Ltac ne_rv5_after HS :=
  unfold ne_rv5; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  [ ne_reg HS (18%bv : bv 5); apply ne_sv42
  | ne_reg HS (20%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (21%bv : bv 5); apply sv_off0; apply ne_E35
  | ne_reg HS (23%bv : bv 5); apply ne_sv42
  | ne_reg HS (22%bv : bv 5); apply sv_off0; apply ne_E41
  | ne_reg HS (19%bv : bv 5); apply ne_den19
  | ne_reg HS (24%bv : bv 5); apply sv_off0; apply ne_E38
  | ne_reg HS (25%bv : bv 5); apply sv_off0; apply ne_E36
  | ne_reg HS (27%bv : bv 5); eapply ne_den27; eassumption ].

(* PHASE J1 -> J2: nl_put16(w, 2). *)
Lemma ne_ph_J1 : forall POST, ne_from SK B POST NE_J2 (ne_JA SK B) -> ne_from SK B POST NE_J1 (ne_JA SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_updA_ok cx pos regs3 n f HB HRV ltac:(unfold NW_SIZE in *; lia) ltac:(lia)).
  assert (E33 : ew (ne_E cx pos regs3 n f) 33 = Z_to_bv 64 n) by apply ne_E33.
  destruct (Z_le_gt_dec n 4094) as [Hroom|Hfull].
  - (* room: 2 bytes at w + n, n := n + 2 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J1 ne_updA false [ne_put_region 2] ne_room16
      HB HFc HJ HU ltac:(right; left; split; [reflexivity | lia])
      ltac:(split; [apply (ne_acond_ltu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J2).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [ne_put_region 2] HB HFc HJ
        ltac:(right; left; split; [reflexivity | lia])).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists (n + 2), f. split.
      * assert (HX : ne_xr_ok cx n [ne_put_region 2]) by (right; left; split; [reflexivity | lia]).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 2) = w64 (n + 2))
          by (rewrite (sv_offc _ 33 n 2 E33) by lia; reflexivity).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
        assert (Hn' : n <= n + 2 <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J1 ne_updA false [ne_put_region 2] ne_room16
          HB HFc HJ HX HS0 HS HJX HFr HG (n + 2) f (SOff 33 2) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rvA_after HS.
  - (* no room: full := 1 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J1 ne_updA false [] ne_full16
      HB HFc HJ HU ltac:(left; reflexivity)
      ltac:(split; [apply (ne_acond_geu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J2).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ ltac:(left; reflexivity)).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, 1. split.
      * assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SLit 1) = w64 1) by reflexivity.
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        assert (Hf' : 0 <= 1 <= 1) by lia.
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J1 ne_updA false (@nil YP09.region) ne_full16
          HB HFc HJ HX HS0 HS HJX HFr HG n 1 (SOff 33 0) (SLit 1) Hen Hef Hn' Hf'.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rvA_after HS.
Qed.

(* PHASE J2 -> J3: nl_put16(w, 0). *)
Lemma ne_ph_J2 : forall POST, ne_from SK B POST NE_J3 (ne_JA SK B) -> ne_from SK B POST NE_J2 (ne_JA SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_updA_ok cx pos regs3 n f HB HRV ltac:(unfold NW_SIZE in *; lia) ltac:(lia)).
  assert (E33 : ew (ne_E cx pos regs3 n f) 33 = Z_to_bv 64 n) by apply ne_E33.
  destruct (Z_le_gt_dec n 4094) as [Hroom|Hfull].
  - (* room: 2 bytes at w + n, n := n + 2 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J2 ne_updA false [ne_put_region 2] ne_room16
      HB HFc HJ HU ltac:(right; left; split; [reflexivity | lia])
      ltac:(split; [apply (ne_acond_ltu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J3).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [ne_put_region 2] HB HFc HJ
        ltac:(right; left; split; [reflexivity | lia])).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists (n + 2), f. split.
      * assert (HX : ne_xr_ok cx n [ne_put_region 2]) by (right; left; split; [reflexivity | lia]).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 2) = w64 (n + 2))
          by (rewrite (sv_offc _ 33 n 2 E33) by lia; reflexivity).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SOff 34 0) = w64 f) by (apply sv_off0; apply ne_E34).
        assert (Hn' : n <= n + 2 <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J2 ne_updA false [ne_put_region 2] ne_room16
          HB HFc HJ HX HS0 HS HJX HFr HG (n + 2) f (SOff 33 2) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rvA_after HS.
  - (* no room: full := 1 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J2 ne_updA false [] ne_full16
      HB HFc HJ HU ltac:(left; reflexivity)
      ltac:(split; [apply (ne_acond_geu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J3).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ ltac:(left; reflexivity)).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, 1. split.
      * assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SLit 1) = w64 1) by reflexivity.
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        assert (Hf' : 0 <= 1 <= 1) by lia.
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J2 ne_updA false (@nil YP09.region) ne_full16
          HB HFc HJ HX HS0 HS HJX HFr HG n 1 (SOff 33 0) (SLit 1) Hen Hef Hn' Hf'.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rvA_after HS.
Qed.

(* PHASE J3 -> J4: nl_put32(w, 1). *)
Lemma ne_ph_J3 : forall POST, ne_from SK B POST NE_J4 (ne_JA SK B) -> ne_from SK B POST NE_J3 (ne_JA SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_updA_ok cx pos regs3 n f HB HRV ltac:(unfold NW_SIZE in *; lia) ltac:(lia)).
  assert (E33 : ew (ne_E cx pos regs3 n f) 33 = Z_to_bv 64 n) by apply ne_E33.
  destruct (Z_le_gt_dec n 4092) as [Hroom|Hfull].
  - (* room: 4 bytes at w + n, n := n + 4 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J3 ne_updA false [ne_put_region 4] ne_room32
      HB HFc HJ HU ltac:(right; right; left; split; [reflexivity | lia])
      ltac:(split; [apply (ne_acond_ltu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J4).
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
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J3 ne_updA false [ne_put_region 4] ne_room32
          HB HFc HJ HX HS0 HS HJX HFr HG (n + 4) f (SOff 33 4) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rvA_after HS.
  - (* no room: full := 1 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J3 ne_updA false [] ne_full32
      HB HFc HJ HU ltac:(left; reflexivity)
      ltac:(split; [apply (ne_acond_geu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J4).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ ltac:(left; reflexivity)).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, 1. split.
      * assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SLit 1) = w64 1) by reflexivity.
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        assert (Hf' : 0 <= 1 <= 1) by lia.
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J3 ne_updA false (@nil YP09.region) ne_full32
          HB HFc HJ HX HS0 HS HJX HFr HG n 1 (SOff 33 0) (SLit 1) Hen Hef Hn' Hf'.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rvA_after HS.
Qed.

(* PHASE J4 -> J5: nl_put32(w, 0); s5 := w, s2 := code. *)
Lemma ne_ph_J4 : forall POST, ne_from SK B POST NE_J5 (ne_J5i SK B) -> ne_from SK B POST NE_J4 (ne_JA SK B).
Proof.
  intros POST HN cx pos S3 memA regs3 mem3 md3 HB HFc (n & f & HJ & HRV).
  pose proof (ne_base_facts SK B cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HFc as (_ & _ & _ & HF4096 & _ & HFceil & _ & _ & _ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as ((HJ0 & HGok & _) & _).
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & Hn0n & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HU := ne_updA_ok cx pos regs3 n f HB HRV ltac:(unfold NW_SIZE in *; lia) ltac:(lia)).
  assert (E33 : ew (ne_E cx pos regs3 n f) 33 = Z_to_bv 64 n) by apply ne_E33.
  destruct (Z_le_gt_dec n 4092) as [Hroom|Hfull].
  - (* room: 4 bytes at w + n, n := n + 4 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J4 ne_updA false [ne_put_region 4] ne_room32
      HB HFc HJ HU ltac:(right; right; left; split; [reflexivity | lia])
      ltac:(split; [apply (ne_acond_ltu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J5).
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
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J4 ne_updA false [ne_put_region 4] ne_room32
          HB HFc HJ HX HS0 HS HJX HFr HG (n + 4) f (SOff 33 4) (SOff 34 0) Hen Hef Hn' Hfr.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rv5_after HS.
  - (* no room: full := 1 *)
    destruct (ne_seat SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ NE_J4 ne_updA false [] ne_full32
      HB HFc HJ HU ltac:(left; reflexivity)
      ltac:(split; [apply (ne_acond_geu _ 33 n); [exact E33 | lia | unfold NE_C16; lia | unfold NE_C16; lia] | exact I]))
      as (HEI & HS & SHOK).
    pose proof HS as HS0.
    pose (RUN := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
    paj_run_to_tok RUN HS HJX SHOK ne_span (AF_nl_error + NE_J5).
    + exact (ne_awr SK B LAWS cx pos S3 memA regs3 mem3 md3 n f _ false [] HB HFc HJ ltac:(left; reflexivity)).
    + pmkst HS.
      apply (HN cx pos S3 memA); [exact HB | exact HFc |].
      exists n, 1. split.
      * assert (HX : ne_xr_ok cx n (@nil YP09.region)) by (left; reflexivity).
        assert (Hen : sv_denot (ne_E cx pos regs3 n f) (SOff 33 0) = w64 n) by (apply sv_off0; exact E33).
        assert (Hef : sv_denot (ne_E cx pos regs3 n f) (SLit 1) = w64 1) by reflexivity.
        assert (Hn' : n <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
        assert (Hf' : 0 <= 1 <= 1) by lia.
        ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f NE_J4 ne_updA false (@nil YP09.region) ne_full32
          HB HFc HJ HX HS0 HS HJX HFr HG n 1 (SOff 33 0) (SLit 1) Hen Hef Hn' Hf'.
        -- intros _; reflexivity.
        -- intros Hc; discriminate Hc.
      * ne_rv5_after HS.
Qed.


End b.
End a.
