(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgParse1.v of this library, for image B
   (fuzz_pin.asan-ubsan, reac_box_pin_parse at 0x80ba4). What differs: the image modules are image B's lib/AU twins,
   the cut states are image B's (lib/AU/PPgParseCx.v) and the addresses are image B's (the refusal exit 0x80e98,
   the live exit 0x80cd0); the registers of the tests are image B's (s2 = sa, s5 = lb, s9 = mo); the proof text is
   the A file's. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-pw/fuzz_pin/lib/AU/PPgParse1.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgParse1.v of this library, for image B
   (fuzz_pin.asan-ubsan, reac_box_pin_parse at 0x80ba4). What differs: the image modules are image B's lib/AU twins,
   the cut states are image B's (lib/AU/PPgParseCx.v) and the addresses are image B's (the refusal exit 0x80e98,
   the live exit 0x80cd0); the registers of the tests are image B's (s2 = sa, s5 = lb, s9 = mo); the proof text is
   the A file's. *)
(* reac_box_pin_parse of reac-pw/fuzz_pin, image B (fuzz_pin.asan-ubsan): segment 1 of the walk, 0x80cac -> 0x80cd0
   or 0x80e98. The code tests sa = 0 (`beqz s2`, to 0x80e98 with a3 = -1); then it makes the instrumented check of
   the 1-byte load at sa: the shadow byte of sa is loaded, and when it is not 0 the slow path 0x80f40-0x80f44
   compares sa mod 8 with it and returns to 0x80cc0. The spec string lies in a heap block of the caller (the
   contract's block premise), so its s + 1 bytes are marked usable at every memory the allocator relation holds of,
   and the error path 0x80f48-0x80f4c is not reached. Then lb = 0 (`beqz s5`) and mo = 0 (`beqz s9`) go to 0x80e98
   with a3 = -1, and so does an empty spec (its first byte is the NUL: pin_row [] = None); a live call with a
   non-empty spec reaches 0x80cd0. No trap branch is in this segment. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgParseLib PPgParseCx PPgParse4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The hand-off to ss_P4 with a3 = -1 (a refused call): the frame region writable again (HFp, the frame bytes at
   the current memory), the result word as atom PN_rc, the dead registers the window PW_P4, and INV_P4 by
   Hnone : pin_parse_res .. = None. *)
Ltac p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F :=
pp_fr_rw HS E75 F HFp;
let E104 := fresh "E104" in
add_atom_win HS 104%nat (Z_to_bv 64 (-1)) E104;
let R13 := fresh "R13" in rreg HS (13%bv : bv 5) R13;
ws_pin HS (13%bv : bv 5) (SOff 104 0) R13
  ltac:(rewrite E104, Z.add_0_r, Z_to_bv_bv_unsigned; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity);
ra_join_win HS ss_P4 PW_P4 pp_deads_P4_bv ltac:(idtac);
pp_hand2 RC4 HS AG E70 E75 E87 E88;
split; [ unfold PN_rc, PW_P4; ewpeel; rewrite E104, Hnone; reflexivity
       | let x := fresh "x" in let y := fresh "y" in let Hx := fresh "Hx" in intros x y Hx; rewrite Hnone in Hx; discriminate ].
(* the frame bytes at the memory of the journal HJx *)
Ltac p1_frame_now HJx Hfin EFA F HFp :=
let LAWS := rnLAWS in
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 _ (proj1 HJx) Hfin) as (_ & _ & HFp & _);
change (fs_frame_bytes 0) with 64 in HFp; rewrite !EFA in HFp; fold F in HFp.
(* the instrumented check's obligation at sa, from the heap block (b, m) the spec string lies in *)
Ltac p1_obl HARN HbmN E10n E32n :=
let LAWS := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 10 0)) ?len =>
lazymatch type of HbmN with In (?b, ?m) _ =>
lazymatch type of E10n with _ = Z_to_bv 64 ?sa =>
rewrite (U_atom Ex 10 sa ltac:(ewpeel; exact E10n) ltac:(lia));
eapply (obl_of_block tfibsegs _ LAWS _ _ _ _ _ Ex PPBx sa len b m HARN HbmN);
[ unfold PPBx; rewrite (U_atom Ex 32 SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; lia)); reflexivity | lia | lia ] end end end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.  Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.                Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Variables RLO RHI cat : Z.  Variables TP DP : nat -> Z.

Lemma pp_seg1 : PP_seg1 B MT RLO RHI cat TP DP.
Proof.
unfold PP_seg1. intros RC2 RC4.
pp_prelude.
clear HINV.
pose proof (proj1 HJ0) as HARc.
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrsc & _).
assert (ELF : ly_F lyN = ly_F lyc) by (eapply pp_lyF; [exact HJ0 | exact HJ]).
assert (HOCF : pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl).
{ intros Hl. destruct (Hlive Hl) as (_ & _ & _ & Hm & _ & _ & Hm1 & Hm2 & Hl' & _ & _ & Hl1 & Hl2 & _).
  rewrite Hfrsc. split; [apply in_or_app; left; exact Hm|]. split; [exact Hm1|]. split; [exact Hm2|].
  split; [apply in_or_app; left; exact Hl'|]. split; [exact Hl1 | exact Hl2]. }
ppLOW HS AG E10 E10n. ppLOW HS AG E11 E11n. ppLOW HS AG E12 E12n. ppLOW HS AG E32 E32n.
assert (SHOK : sh_ok tfibsegs PPBx [] E (mrestrict (w_H WN) (ms_mem msN))) by constructor.
pp_fr_ro HS.
(* 0x80cac beqz s2 *)
srr_branch_tok tfibtbl_lib_ok HS SHOK PPBspan.
{ (* sa = 0: to 0x80e98 *)
  hc_bool Hc ltac:(fun H => hc_atom H 10%nat sa E10n ltac:(lia)); hc_prop Hc.
  aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80e98.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
  pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
  assert (Hnone : pin_parse_res cat DP sa mo lb s = None) by (rewrite Hc; apply pp_res_sa0).
  p1_frame_now HJ Hfin EFA F HFp.
  p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F. }
(* sa <> 0: the spec string s ++ NUL is in the heap block (b, m) *)
hc_bool Hc ltac:(fun H => hc_atom H 10%nat sa E10n ltac:(lia)); hc_prop Hc.
destruct (Hstr Hc) as (HSTR & b & m & Hbm & Hb1 & Hb2).
pose proof HSTR as (Hnul & Hsa0 & Hsa63 & Hlen32 & HG8 & _ & _ & _ & _ & HOFF).
assert (HbmN : In (b, m) (ablocks B lyN SN)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hbm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARN HbmN) as (_ & Hb4096 & Hbce & Hbapp & _).
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ b m 0 fpos HARN HbmN Hfin) as HbF.
unfold zdisjoint in HbF. cbn [fst snd] in HbF. change (fs_frame_bytes 0) with 64 in HbF. rewrite EFA in HbF. fold F in HbF.
assert (HOFF0 : ~ (spZ regs - 8400 <= sa < spZ regs)) by (pose proof (HOFF sa ltac:(lia)) as X; change T_parse_STK with 8400 in X; exact X).
(* the first byte of the spec at the current memory: the block's bytes are kept, and sa is no out-cell byte *)
assert (HV0 : val_mem tfibsegs (mrestrict (w_H WN) (ms_mem msN)) sa 1 (nth 0 (pin_zbytes s ++ [0]) 0)).
{ destruct (HG8 0%nat ltac:(rewrite length_app; cbn; lia)) as (V & _). rewrite Z.add_0_r in V.
  apply (val_mem_kept tfibsegs (w_H W) (w_H WN) memc (ms_mem msN)); [|exact V].
  intros j Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. replace (sa + j) with (b + (sa - b)) by lia.
  pose proof HKE as (_ & K2 & _). apply (K2 b m (sa - b) Hbm); [lia|].
  intros (Hl & Ho). destruct (Hlive Hl) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS).
  apply (HOS (b + (sa - b)) Ho). lia. }
pose proof (proj2 (HG8 0%nat ltac:(rewrite length_app; cbn; lia))) as HV0r.
(* the region of the first byte; its chunk is the literal 0 when s = [], else an atom PP_N0 in [1, 255] *)
destruct s as [|c0 s'].
{ (* s = [] *)
  cbn [pin_zbytes map app nth] in HV0, HV0r.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E10n, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val tfibsegs Ev _ sa 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HV0])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp;
    repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
  (* 0x80cb0-0x80cbc the instrumented check of the byte at sa (slow path 0x80f40-0x80f44): passes, the block's
     bytes are marked usable; stops at 0x80cc0 `beqz s5` *)
  aj_run_tok tfibtbl_lib_ok HS HJ SHOK PPBspan.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
  all: try (p1_obl HARN HbmN E10n E32n).
  pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
  srr_branch_tok tfibtbl_lib_ok HS SHOK PPBspan.
  { (* lb = 0 *)
    hc_bool Hc0 ltac:(fun H => hc_atom H 12%nat lb E12n ltac:(lia)); hc_prop Hc0.
    aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80e98.
    all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
    pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
    assert (Hnone : pin_parse_res cat DP sa mo lb [] = None) by (rewrite Hc0; apply pp_res_lb0).
    p1_frame_now HJ Hfin EFA F HFp.
    p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F. }
  hc_bool Hc0 ltac:(fun H => hc_atom H 12%nat lb E12n ltac:(lia)); hc_prop Hc0.
  aj_run_tok tfibtbl_lib_ok HS HJ SHOK PPBspan.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
  pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
  srr_branch_tok tfibtbl_lib_ok HS SHOK PPBspan.
  { (* mo = 0 *)
    hc_bool Hc1 ltac:(fun H => hc_atom H 11%nat mo E11n ltac:(lia)); hc_prop Hc1.
    aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80e98.
    all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
    pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
    assert (Hnone : pin_parse_res cat DP sa mo lb [] = None) by (rewrite Hc1; apply pp_res_mo0).
    p1_frame_now HJ Hfin EFA F HFp.
    p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F. }
  (* mo <> 0: the first byte is the NUL, `beqz a0` at 0x80ccc is taken *)
  aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80e98.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
  pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
  assert (Hnone : pin_parse_res cat DP sa mo lb [] = None) by (apply pp_res_nil).
  p1_frame_now HJ Hfin EFA F HFp.
  p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F. }
(* s = c0 :: s': the first byte is an atom in [1, 255] *)
cbn [pin_zbytes map app nth] in HV0, HV0r.
assert (Hc0nz : bv_unsigned c0 <> 0) by (intros X; apply Hnul; left; apply bv_eq; rewrite X; reflexivity).
add_atom_win HS 400%nat (Z_to_bv 64 (bv_unsigned c0)) E400.
AWalkFw2.add_fact HS 400%nat 1 255 E400 ltac:(lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 400 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  ewpeel; rewrite E10n, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
  apply Forall_cons; [|apply Forall_nil];
  apply (chunk_ok_val tfibsegs Ev _ sa 0 1 (SOff 400 0) (bv_unsigned c0));
  [cbn [sv_denot]; rewrite E400, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HV0])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; ewpeel; evalE AG;
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp;
  repeat split; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
clear SHOK. assert (SHOK : sh_ok tfibsegs PPBx [] (havoc E 400 [Z_to_bv 64 (bv_unsigned c0)]) (mrestrict (w_H WN) (ms_mem msN))) by constructor.
aj_run_tok tfibtbl_lib_ok HS HJ SHOK PPBspan.
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
all: try (p1_obl HARN HbmN E10n E32n).
pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
srr_branch_tok tfibtbl_lib_ok HS SHOK PPBspan.
{ (* lb = 0 *)
  hc_bool Hc0 ltac:(fun H => hc_atom H 12%nat lb E12n ltac:(lia)); hc_prop Hc0.
  aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80e98.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
  pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
  assert (Hnone : pin_parse_res cat DP sa mo lb (c0 :: s') = None) by (rewrite Hc0; apply pp_res_lb0).
  p1_frame_now HJ Hfin EFA F HFp.
  p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F. }
hc_bool Hc0 ltac:(fun H => hc_atom H 12%nat lb E12n ltac:(lia)); hc_prop Hc0.
aj_run_tok tfibtbl_lib_ok HS HJ SHOK PPBspan.
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
srr_branch_tok tfibtbl_lib_ok HS SHOK PPBspan.
{ (* mo = 0 *)
  hc_bool Hc1 ltac:(fun H => hc_atom H 11%nat mo E11n ltac:(lia)); hc_prop Hc1.
  aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80e98.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
  pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
  assert (Hnone : pin_parse_res cat DP sa mo lb (c0 :: s') = None) by (rewrite Hc1; apply pp_res_mo0).
  p1_frame_now HJ Hfin EFA F HFp.
  p1_to_P4 RC4 HS Hnone HFp AG E70 E75 E87 E88 F. }
hc_bool Hc1 ltac:(fun H => hc_atom H 11%nat mo E11n ltac:(lia)); hc_prop Hc1.
(* the call is live and the first byte is not the NUL: `beqz a0` at 0x80ccc is not taken, to 0x80cd0 *)
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80cd0.
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(fail).
assert (Hl : pin_parse_live sa mo lb = true) by (apply pp_live_iff; tauto).
destruct (HOCF Hl) as (Hm & Hm1 & Hm2 & Hl' & Hl1 & Hl2).
destruct (Hlive Hl) as (Hmo8 & Hlb8 & _).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cidm posm HARc Hm) as (M4096 & Mce & _).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cidl posl HARc Hl') as (L4096 & Lce & _).
p1_frame_now HJ Hfin EFA F HFp.
pp_fr_rw HS E75 F HFp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E10c : ew Ev 10 = Z_to_bv 64 sa) by (ewpeel; exact E10n) end.
AWalkFw2.add_fact HS 10%nat 4096 140737479966720 E10c ltac:(lia).
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 11%nat (mkAF 4096 140737479966720 3) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E11n, unsigned_lit_small by lia;
        change (2 ^ 3) with 8; repeat split; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 12%nat (mkAF 4096 140737479966720 3) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E12n, unsigned_lit_small by lia;
        change (2 ^ 3) with 8; repeat split; lia)) as HS3; clear HS; rename HS3 into HS end.
ra_join_win HS ss_P2 PW_P2 pp_deads_P2_bv ltac:(idtac).
pp_hand2 RC2 HS AG E70 E75 E87 E88.
split; [exact Hl | discriminate].
Qed.
End c.

Print Assumptions pp_seg1.
