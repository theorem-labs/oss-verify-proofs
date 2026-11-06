(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 521 of its 608 lines of code are new or changed and 4966 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B8b_s.v, with its module paths and module names changed; 1037 of its 1132 lines of code are new or changed and 513 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the SECOND HALF of segment A3 of reac_segconf_parse_file's walk,
   `a3_ret1_ok : A3_RET1_stmt B` (statement and cut a3_ret1 in lib/A/Prog/pf_a3_d.v). Segment A3's proof,
   2026-10-30.
   proves function reac_segconf_parse_file (segment A3; reuse search and CONFIRM:
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md, the rule-24 check
   2026-10-30T15:42:08Z; reuse verdict none).

   From 0x87cec (the snprintf's return, BASE + PF_RET1) to HEAD 0x87ddc or DONE 0x88bb8 (the unit's internal
   record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s):
     0x87cec .. 0x87cfc  check #1 (load4 of c->gen; its slow block 0x88c68 .. 0x88c78)
     0x87d00 .. 0x87d14  c->gen++ (lw / addi / sw at s10 = &c->gen); s2 = 0x3000; a0 = c + RC_N
     0x87d18             s3 = slot 0x98 = SH + 8
     0x87d1c             beqz s9: dead, the text pointer is not NULL
     0x87d20 .. 0x87d48  slots 0x38 0x80 0x58 0x40 0x68 0x50; cur_name's two shadow cells SH + 4, SH + 5 = 0
     0x87d4c             jal __asan_memset(cur_name, 0, 16)
     0x87d50 .. 0x87d5c  check #2 (load1 of text[0]; slow block 0x88c80 .. 0x88c88)
     0x87d60 .. 0x87d70  a0 = text[0]; slot 0x60 = (c + RC_N) / 8; beqz a0 -> DONE
     0x87d74 .. 0x87dd8  s4 = cur = NULL, s10 = ln = 0, s2 = '#', the remaining 11 slots; HEAD
   THE ENGINE (the plan validated by probe in segment A3's proof): one environment a3wE (atoms 0..31 the registers,
   32 = c->gen's old value, 33 = the text's first byte), re-seeded at five points:
     R1  token run, no region, 0x87cec -> 0x87d00 (check #1: the obligation is c->gen's 8 bytes addressable);
     R2  plain run, regions slots / c->gen / cur_name's two shadow cells, 0x87d00 -> the memset call;
     the memset by pf_a3_k.a3_mset_site;
     R3  token run, no region, 0x87d50 -> 0x87d60 (check #2: the obligation is text[0] addressable);
     R4  plain run, regions slots / text[0] (read only), s2 pinned to 0x3000, 0x87d60 -> HEAD or DONE.
   The memory kept across the four steps is A3's write set a3w_Wr; the keep lemmas below are pf_a2_g.v's pa2_k_*
   (segment A2's proof) restated over that write set: it holds c->gen, a heap word, so a text byte is kept by
   reader_pre's sa_disj and a c byte other than gen by its offset.
   Section hypotheses: MSET (the checked memset, pf_pieces.v's list for A3; the call at 0x87d4c) and OBJ (the
   listing's object addresses, SegObj.seg_val_objs; slots 0xa0 / 0xa8 hold the literals F_long and " \t\r" that
   the auipc pairs at 0x87db4 / 0x87db8 form). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a2_g pf_a2 pf_a5_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a3_d pf_a3_f pf_a3_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the regions and facts of the seeds ======================= *)
(* R2 (0x87d00): the 19 spill slots s1 + 0x20 .. s1 + 0xc0 with the two the cut states, c->gen (atom 32 its old
   value), cur_name's two shadow cells *)
Definition a3w_RSL : YP09.region := YP09.mkRegion (Some 9%nat) 0x20 0xc0 0x20 0xc0
  [YP09.mkChunk 0x88 (CVal 8 (SOff 23 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 27 8))].
Definition a3w_RGEN : YP09.region := YP09.mkRegion (Some 26%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition a3w_RFSH : YP09.region := YP09.mkRegion (Some 27%nat) 4 6 4 6 [].
Definition a3w_G2 : facts := mkFacts [(25%nat, mkAF 1 (2 ^ 47) 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
(* R1 and R3: the shadow base s6 and the pointers the checks test *)
Definition a3w_G1 : facts := mkFacts [(22%nat, mkAF SB SB 0); (25%nat, PTR 0); (26%nat, PTR 0)] [] [].
Definition a3w_G3 : facts := mkFacts [(22%nat, mkAF SB SB 0); (25%nat, PTR 0)] [] [].
(* R4 (0x87d60): the eight slots known there (0x38 is the shadow address of &c->gen, s6 + (s10 >> 3)), and the
   text's first byte, read only: atom 33 on the HEAD path, the literal 0 on the DONE path *)
Definition a3w_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 26 0) (SLit 3)) (SOff 22 0).
Definition a3w_RSL4 : YP09.region := YP09.mkRegion (Some 9%nat) 0x20 0xc0 0x20 0xc0
  [YP09.mkChunk 0x38 (CVal 8 a3w_shx); YP09.mkChunk 0x40 (CVal 8 (SOff 26 0));
   YP09.mkChunk 0x50 (CVal 8 (SOff 23 32)); YP09.mkChunk 0x58 (CVal 8 (SOff 21 0));
   YP09.mkChunk 0x68 (CVal 8 (SOff 23 0)); YP09.mkChunk 0x80 (CVal 8 (SOff 24 11392));
   YP09.mkChunk 0x88 (CVal 8 (SOff 23 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 27 8))].
Definition a3w_RTXT (z : sv) : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 z)].
Definition a3w_G4h : facts := mkFacts [(33%nat, mkAF 1 255 0)] [] [].

(* ======================= small arithmetic and denotation facts ======================= *)
Lemma a3w_gen1 : forall g, 0 <= g -> g + 1 < 2 ^ 32 ->
  zcanon (zcanon (bv_swrap 32 (g mod 2 ^ 32)) + zcanon 1) mod 2 ^ 32 = g + 1.
Proof.
intros g H0 H1. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
Lemma a3w_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma a3w_den_sh : forall E m x, ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 60 -> ew E 22 = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m 0) (SLit 3)) (SOff 22 0)) = Z_to_bv 64 (shadow_addr x).
Proof.
intros E m x Hm Hx H22. rewrite <- (a3w_den_lit E (shadow_addr x)). apply U_inj.
rewrite U_SAlu, U_srl3, (U_atom E m x Hm) by lia. rewrite (U_atom E 22 SHADOW_OFF H22) by (unfold SHADOW_OFF; lia).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
rewrite U_lit by (unfold shadow_addr, SHADOW_OFF; lia). cbn [zalu_raw]. unfold shadow_addr.
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.
Lemma a3w_den_srl : forall E n x d, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + d < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff n d) (SLit 3)) = Z_to_bv 64 ((x + d) / 8).
Proof.
intros E n x d Hn H0 Hd. rewrite <- (a3w_den_lit E ((x + d) / 8)). apply U_inj.
rewrite U_srl3, (U_atom_off E n x d Hn) by lia.
pose proof (Z.div_mod (x + d) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + d) 8 ltac:(lia)).
rewrite U_lit by lia. reflexivity.
Qed.
Lemma a3w_den_gen1 : forall E g, ew E 32 = Z_to_bv 64 g -> 0 <= g -> g + 1 < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = g + 1.
Proof.
intros E g H32 H0 H1. change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1))))
  with (U E (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1))).
rewrite U_SAlu, U_SExt, (U_atom E 32 g H32) by lia. rewrite U_SLit. cbn [zalu_raw].
change (8 * Z.of_N 4) with 32. change (2 ^ Z.of_N 32) with (2 ^ 32). exact (a3w_gen1 g H0 H1).
Qed.
Lemma a3w_shb_out : forall i, ~ (4 <= i < 6) -> pf_shb PF_SC_HEAD i = pf_shb PF_SC0 i.
Proof.
intros i Hi. unfold pf_shb, PF_SC_HEAD, PF_SC0. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4) eqn:E1; [reflexivity|]. destruct (i <? 6) eqn:E2; [|reflexivity].
apply Z.ltb_ge in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma a3w_shb_in : forall i, 4 <= i < 6 -> pf_shb PF_SC_HEAD i = 0.
Proof.
intros i Hi. unfold pf_shb, PF_SC_HEAD. cbn [sc_cn].
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma a3w_rg_cons : forall rX r z L, getr rX (Z_to_bv 5 r) = w64 z -> pf_rg rX L -> pf_rg rX ((r, z) :: L).
Proof. intros rX r z L H1 H2. apply Forall_cons; [exact H1 | exact H2]. Qed.
Ltac a3w_inc := cbn [In]; repeat first [left; reflexivity | right].
(* a register of the state a run left, as the denotation of the run's symbolic value (SegPaLib.prreg without its
   normalisation) *)
Ltac a3w_rr HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.
Ltac a3w_arith := unfold seg_spec.RC_GEN, seg_spec.RC_N, seg_spec.RC_READING, seg_spec.RC_OVERFLOW,
  seg_spec.RS_SEEN_GEN, PF_O_CN, PF_O_BUF, PF_O_LOW, PF_O_L146, PF_O_KNOWN, PF_O_NTOK, seg_spec.SEG_C_SIZE,
  shadow_addr, SHADOW_OFF; lia.
(* the value of a chunk a run left: an atom plus an offset, the shadow address of &c->gen, or (c + RC_N) >> 3 *)
Ltac a3w_den :=
  lazymatch goal with
  | |- sv_denot ?E (SOff ?n ?d) = Z_to_bv 64 ?val =>
      lazymatch goal with Hn : ew E n = Z_to_bv 64 ?x |- _ =>
        rewrite (pa2_den_off E n x d Hn) by a3w_arith; f_equal; a3w_arith end
  | |- sv_denot ?E (SAlu ALU_SRL (SOff ?n ?d) (SLit 3)) = Z_to_bv 64 ?val =>
      lazymatch goal with Hn : ew E n = Z_to_bv 64 ?x |- _ =>
        rewrite (a3w_den_srl E n x d Hn) by a3w_arith; f_equal; a3w_arith end
  | |- sv_denot ?E a3w_shx = Z_to_bv 64 ?val =>
      lazymatch goal with H26 : ew E 26 = Z_to_bv 64 ?x |- _ =>
      lazymatch goal with H22 : ew E 22 = Z_to_bv 64 SHADOW_OFF |- _ =>
        unfold a3w_shx; rewrite (a3w_den_sh E 26 x H26 ltac:(a3w_arith) H22); reflexivity end end
  | |- sv_denot ?E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 26 0) (SLit 3)) (SOff 22 0)) = Z_to_bv 64 ?val =>
      lazymatch goal with H26 : ew E 26 = Z_to_bv 64 ?x |- _ =>
      lazymatch goal with H22 : ew E 22 = Z_to_bv 64 SHADOW_OFF |- _ =>
        rewrite (a3w_den_sh E 26 x H26 ltac:(a3w_arith) H22); reflexivity end end
  end.
(* one slot of pf_sl from the chunk of the slot region (pf_a2.v's pa2_word_of_region) *)
Ltac a3w_slot HR Ub :=
  lazymatch goal with |- rdword _ (?b + ?od) = Some ?val =>
    eapply (pa2_word_of_region _ _ _ _ b _ _ _ _ _ od _ val HR Ub); [a3w_inc | a3w_den | a3w_arith] end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the checked memset at every FP state (pf_pieces.v's list for A3; the call 0x87d4c) *)
Hypothesis MSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
(* the listing's object addresses (SegObj.v): the literals F_long and " \t\r" of slots 0xa0 / 0xa8 *)
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ======================= the environment of every seed ======================= *)
Definition a3wE (v : pfv) (rX : bvmap 5 word) : env :=
  Eimg (Ereg rX [w64 (rc_gen (p_rcs v)); w64 (hd0 (p_s v))]).
Lemma a3wE_img : forall v rX, img_env VAL A_LIM (a3wE v rX).
Proof. intros. unfold a3wE. apply Eimg_env. Qed.
Lemma a3wE_low : forall v rX (n : nat), (n < 32)%nat -> ew (a3wE v rX) n = getr rX (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros v rX n Hn. unfold a3wE. apply ew_Eimg_Ereg_nat.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
Qed.
Lemma a3wE_low_ext : forall v rX (K : nat) ws (n : nat), (32 <= K)%nat -> (n < 32)%nat ->
  ew (extK (a3wE v rX) K ws) n = getr rX (Z_to_bv 5 (Z.of_nat n)).
Proof. intros v rX K ws n HK Hn. rewrite (proj1 (env_agree_extK (a3wE v rX) K ws) n) by lia. apply a3wE_low. exact Hn. Qed.
Lemma a3wE_x32 : forall v rX, ew (a3wE v rX) 32%nat = w64 (rc_gen (p_rcs v)).
Proof. intros. unfold a3wE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 0%nat). Qed.
Lemma a3wE_x33 : forall v rX, ew (a3wE v rX) 33%nat = w64 (hd0 (p_s v)).
Proof. intros. unfold a3wE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX _ 1%nat). Qed.
Lemma a3w_obj : forall E (i : nat), img_env VAL A_LIM E -> (i < 78)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (nth i seg_objs 0).
Proof.
intros E i HE Hi. rewrite (img_env_atomP E (A_OBJ i) HE) by (unfold A_OBJ, A_TEXT, A_LIM in *; lia).
rewrite (OBJ i ltac:(unfold seg_objs; cbn [length]; lia)). reflexivity.
Qed.
Lemma a3w_lit_blanks : nth 36 seg_objs 0 = seg_litA_rc [SP; TAB; CR].
Proof. vm_compute. reflexivity. Qed.
Lemma a3w_lit_flong : nth 37 seg_objs 0 = seg_litA_rc F_long.
Proof. vm_compute. reflexivity. Qed.

Section rk. Context {fx : YK11.FPState}.
(* the registers a run left: atom k of the seed holds what rX held *)
Lemma a3w_rg_keep : forall E ss (H : word -> bool) ms (rX : bvmap 5 word) L,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n : nat, (n < 32)%nat -> ew E n = getr rX (Z_to_bv 5 (Z.of_nat n))) ->
  forallb (fun rv => (0 <=? fst rv) && (fst rv <? 32) &&
     sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (fst rv))) (SOff (Z.to_nat (fst rv)) 0)) L = true ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss H ms rX L HS HE Hb HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r z] Hin.
rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn [fst snd] in *.
apply andb_prop in Hb as [Hb Heq]. apply andb_prop in Hb as [H0 H32].
apply Z.leb_le in H0. apply Z.ltb_lt in H32. apply sv_eqb_eq in Heq.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Heq, pa2_crt_den_atom0, HE by lia.
rewrite Z2Nat.id by lia. exact (HR _ Hin).
Qed.
Lemma a3w_rg_keepC : forall E ss (H : word -> bool) ms (rX : bvmap 5 word) L,
  st_ok SEGS E ss (restrict H ms) ->
  (forall n : nat, (n < 32)%nat -> ew E n = getr rX (Z_to_bv 5 (Z.of_nat n))) ->
  forallb (fun rv => (0 <=? fst rv) && (fst rv <? 32) &&
     sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (fst rv))) (SOff (Z.to_nat (fst rv)) 0)) L = true ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss H ms rX L HS HE Hb HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r z] Hin.
rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn [fst snd] in *.
apply andb_prop in Hb as [Hb Heq]. apply andb_prop in Hb as [H0 H32].
apply Z.leb_le in H0. apply Z.ltb_lt in H32. apply sv_eqb_eq in Heq.
rewrite (st_ok_restrict_reg SEGS H E ss ms _ HS), Heq, pa2_crt_den_atom0, HE by lia.
rewrite Z2Nat.id by lia. exact (HR _ Hin).
Qed.
End rk.

(* sa_val (the reader's bytes of a value) and val_mem (the memory's) are the same statement *)
Lemma a3w_vm_of_sv : forall H mem a n v, sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma a3w_sv_of_vm : forall H mem a n v, val_mem SEGS (mrestrict H mem) a n v -> sa_val (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact (pa2_le_byte_range v n k).
Qed.
Lemma a3w_sl_keep : forall (rd rd' : reader) b L,
  (forall ov, In ov L -> forall k, 0 <= k < 8 -> rd' (b + fst ov + k) = rd (b + fst ov + k)) ->
  pf_sl rd b L -> pf_sl rd' b L.
Proof.
intros rd rd' b L HK H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hin.
rewrite (rdword_ext rd rd'); [exact (H ov Hin)|]. exact (HK ov Hin).
Qed.
Lemma a3w_sl_in : forall (rd : reader) b L o z, pf_sl rd b L -> In (o, z) L -> rdword rd (b + o) = Some z.
Proof. intros rd b L o z H Hin. unfold pf_sl in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
Lemma a3w_le1 : forall x, 0 <= x < 256 -> YG0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia. rewrite Z.shiftr_0_r. apply Z.mod_small. lia.
Qed.
(* a seed's chunk from the reader: an 8-byte slot, a 1-byte read-only cell *)
Lemma a3w_ck : forall E H mem base off e val, sv_denot E e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  rdword (aview SEGS H mem) (base + off) = Some val ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E H mem base off e val He Hv Hr. apply (chunk_ok_val SEGS E _ base off 8 e val);
  [exact He | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | apply val_mem_of_rdword; exact Hr].
Qed.
Lemma a3w_ck1 : forall E H mem a e x, sv_denot E e = Z_to_bv 64 x -> 0 <= x < 256 -> aview SEGS H mem a = Some x ->
  YP09.chunk_ok SEGS E (mrestrict H mem) a (YP09.mkChunk 0 (CVal 1 e)).
Proof.
intros E H mem a e x He Hx Hr. apply (chunk_ok_val SEGS E _ a 0 1 e x);
  [exact He | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
rewrite Z.add_0_r. apply a3w_vm_of_sv. intros k Hk. assert (k = 0%nat) as -> by (cbn in Hk; lia).
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hr. f_equal. symmetry. apply a3w_le1. exact Hx.
Qed.

(* ======================= A3's write set and what keeps outside it ======================= *)
(* the callees' windows below s1 and the 19 slots, c->gen, cur_name, cur_name's two shadow cells *)
Definition a3w_Wr (v : pfv) (pos a : Z) : Prop :=
  (pf_sp0 v - 12800 <= a < pf_s1 v + 0xc0) \/
  (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4) \/
  (pf_F v pos + 32 <= a < pf_F v pos + 48) \/ (pf_SH v pos + 4 <= a < pf_SH v pos + 6).
Definition a3w_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ a3w_Wr v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Lemma a3w_kept_trans : forall v pos rd1 rd2 rd3, a3w_kept v pos rd1 rd2 -> a3w_kept v pos rd2 rd3 ->
  a3w_kept v pos rd1 rd3.
Proof.
intros v pos rd1 rd2 rd3 [K1 M1] [K2 M2]. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (M2 a Ha (M1 a Ha H)).
Qed.
Lemma a3w_kept_step : forall v pos (rd rd' : reader) (Ws : Z -> Prop),
  (forall a, Ws a -> a3w_Wr v pos a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Ws a -> rd' a = rd a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None) -> a3w_kept v pos rd rd'.
Proof.
intros v pos rd rd' Ws Hs K V. split; [|exact V].
intros a Ha Hn. apply K; [exact Ha|]. intros Hw. exact (Hn (Hs a Hw)).
Qed.

Section k.
Variables (v : pfv) (pos : Z).
Hypothesis G : pa2_geoP v pos.
(* c->gen's four bytes are bytes of the heap block c: below alloc_ceiling, application bytes, outside the frame,
   and outside the image *)
Hypothesis HCG : forall y, p_c v + seg_spec.RC_GEN <= y < p_c v + seg_spec.RC_GEN + 4 -> pa2_out v pos y.
Hypothesis HCI : forall y, p_c v + seg_spec.RC_GEN <= y < p_c v + seg_spec.RC_GEN + 4 -> ~ (0x10000 <= y < kImgEnd).
(* a byte A3 never writes: pf_a2_g's pa2_out (an application byte below alloc_ceiling outside the frame) that is
   not one of c->gen's *)
Definition a3w_out (x : Z) : Prop :=
  pa2_out v pos x /\ ~ (p_c v + seg_spec.RC_GEN <= x < p_c v + seg_spec.RC_GEN + 4).
Lemma a3w_F8 : pf_F v pos mod 8 = 0.
Proof.
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma a3w_out_nw : forall x, a3w_out x -> 0 <= x < 2 ^ 64 /\ ~ a3w_Wr v pos x.
Proof.
intros x ((Hx1 & Hx2 & Hx3) & Hx4).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
unfold a3w_Wr, pf_SH, shadow_addr, SHADOW_OFF. split; [lia|]. lia.
Qed.
Lemma a3w_shadow_nw : forall x, pa2_out v pos x ->
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ a3w_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx2 & Hx3).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (pa2_granule (pf_F v pos) x a3w_F8 Hx3 ltac:(lia)) as Gr.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
assert (HY : ~ (p_c v + seg_spec.RC_GEN <= SHADOW_OFF + x / 8 < p_c v + seg_spec.RC_GEN + 4)).
{ intros Hy. destruct (HCG _ Hy) as (_ & Hy2 & _). unfold SHADOW_OFF in *. lia. }
unfold a3w_Wr, pf_SH, shadow_addr. unfold SHADOW_OFF in *. split; [lia|]. lia.
Qed.
Lemma a3w_out_img : forall x, 0x10000 <= x < kImgEnd -> a3w_out x.
Proof. intros x Hx. split; [exact (pa2_out_img v pos G x Hx) | intros H; exact (HCI x H Hx)]. Qed.
Lemma a3w_out_inimg : forall x, in_img SEGS x -> a3w_out x.
Proof. intros x Hx. apply a3w_out_img. exact (pa_img_range x Hx). Qed.
(* the stack slots of the prologue's saved registers, the frame's flag word, the frame's other shadow cells *)
Lemma a3w_saved_nw : forall a, pf_sp0 v - 104 <= a < pf_sp0 v -> 0 <= a < 2 ^ 64 /\ ~ a3w_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
assert (HY : ~ (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4))
  by (intros Hy; destruct (HCG _ Hy) as ((_ & Hy1) & _); lia).
unfold a3w_Wr, pf_SH, shadow_addr, SHADOW_OFF. split; [lia|]. lia.
Qed.
Lemma a3w_flag_nw : forall a, pf_F v pos + 2040 <= a < pf_F v pos + 2048 -> 0 <= a < 2 ^ 64 /\ ~ a3w_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
assert (HY : ~ (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4))
  by (intros Hy; destruct (HCG _ Hy) as (_ & _ & Hy3); apply Hy3; lia).
unfold a3w_Wr, pf_SH, shadow_addr, SHADOW_OFF. split; [lia|]. lia.
Qed.
Lemma a3w_cell_nw : forall i, 0 <= i < 144 -> ~ (4 <= i < 6) ->
  0 <= pf_SH v pos + i < 2 ^ 64 /\ ~ a3w_Wr v pos (pf_SH v pos + i).
Proof.
intros i Hi Hi'. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
assert (HY : ~ (p_c v + seg_spec.RC_GEN <= pf_SH v pos + i < p_c v + seg_spec.RC_GEN + 4)).
{ intros Hy. destruct (HCG _ Hy) as (_ & Hy2 & _). unfold pf_SH, shadow_addr, SHADOW_OFF in *. lia. }
unfold a3w_Wr. unfold pf_SH, shadow_addr, SHADOW_OFF in *. split; [lia|]. lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : a3w_kept v pos rd rd'.
Lemma a3w_k_byte : forall x, a3w_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (a3w_out_nw x Hx) as (H0 & H1). exact (proj1 K x H0 H1). Qed.
Lemma a3w_k_shadow : forall x, pa2_out v pos x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (a3w_shadow_nw x Hx) as (H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma a3w_k_zs : forall p l, (forall i, (i < length l)%nat -> a3w_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (a3w_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma a3w_k_bytes : forall p l, (forall i, (i < length l)%nat -> a3w_out (p + Z.of_nat i)) ->
  sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (a3w_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma a3w_k_rdword : forall a, (forall k, 0 <= k < 8 -> a3w_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (a3w_k_byte _ (Ho k Hk)). Qed.
Lemma a3w_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma a3w_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma a3w_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> a3w_out x) ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as ((He & _) & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (a3w_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (a3w_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma a3w_k_addr : forall q n, (forall x, q <= x < q + n -> pa2_out v pos x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (a3w_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (a3w_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma a3w_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (a3w_k_str a s); [|exact Hs]. intros x Hx. apply a3w_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma a3w_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (a3w_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (a3w_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply a3w_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma a3w_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (a3w_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply a3w_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply a3w_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma a3w_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> a3w_out (a + k))
  by (intros a Ha k Hk; apply a3w_out_img; lia).
split; [rewrite (a3w_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (a3w_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.

(* the cut's objects, the record c after c->gen++, the saved registers, the flag word, the frame's shadow *)
Lemma a3w_keep_obj : forall lyc Sc rd rd',
  (forall x, p_t v <= x < p_t v + pf_len v -> a3w_out x) ->
  (forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> pa2_out v pos x) ->
  a3w_kept v pos rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros lyc Sc rd rd' Ht Hc K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [apply (a3w_k_str rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (a3w_k_addr rd rd' K _ _ (fun x Hx => proj1 (Ht x Hx)) H2)|]. split; [exact H3|].
split; [exact (a3w_k_addr rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (a3w_k_cat rd rd' K _ H6)|].
split; [intros x Hx; exact (a3w_k_lit rd rd' K _ _ (H7 x Hx))|].
split; [exact (a3w_k_rod rd rd' K H8) | exact (a3w_k_ssp rd rd' K H9)].
Qed.
Lemma a3w_keep_rconf : forall rd rd' cf,
  (forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> pa2_out v pos x) ->
  a3w_kept v pos rd rd' -> sa_rconf rd (p_c v) cf -> rc_gen cf + 1 < 2 ^ 32 ->
  sa_val rd' (p_c v + seg_spec.RC_GEN) 4 (rc_gen cf + 1) ->
  sa_rconf rd' (p_c v)
    (RConf (rc_seg cf) (rc_refusal cf) (rc_refused cf) (rc_overflow cf) (rc_reading cf) (rc_gen cf + 1)).
Proof.
intros rd rd' cf Hc K Hr Hg Hv. apply (a3f_rconf_gen rd rd' (p_c v) cf Hr Hg Hv).
intros a Ha Hn. apply (a3w_k_byte rd rd' K). split; [exact (Hc a Ha) | exact Hn].
Qed.
Lemma a3w_keep_saved : forall rd rd' regs, a3w_kept v pos rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros rd rd' regs K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
intros k Hk. destruct (a3w_saved_nw (pf_sp0 v - 8 - 8 * Z.of_nat j + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma a3w_keep_flag : forall rd rd', a3w_kept v pos rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros rd rd' K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (a3w_flag_nw (pf_F v pos + 2048 - 8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma a3w_keep_fsh : forall rd rd', a3w_kept v pos rd rd' ->
  (forall i, 0 <= i < 2 -> rd' (pf_SH v pos + 4 + i) = Some 0) ->
  pf_fsh rd (pf_SH v pos) PF_SC0 -> pf_fsh rd' (pf_SH v pos) PF_SC_HEAD.
Proof.
intros rd rd' K H45 H i Hi.
destruct (Z_lt_le_dec i 4) as [Hi4 | Hi4]; [|destruct (Z_lt_le_dec i 6) as [Hi6 | Hi6]].
- destruct (a3w_cell_nw i Hi ltac:(lia)) as (H0 & H1). rewrite (proj1 K _ H0 H1), (H i Hi).
  rewrite a3w_shb_out by lia. reflexivity.
- replace (pf_SH v pos + i) with (pf_SH v pos + 4 + (i - 4)) by lia. rewrite (H45 (i - 4) ltac:(lia)).
  rewrite a3w_shb_in by lia. reflexivity.
- destruct (a3w_cell_nw i Hi ltac:(lia)) as (H0 & H1). rewrite (proj1 K _ H0 H1), (H i Hi).
  rewrite a3w_shb_out by lia. reflexivity.
Qed.
End k.

(* the facts of the cut every step uses: the frame part (pf_fi), the geometry (pf_a2_g's pa2_geo), and where c, its
   gen field and the text lie *)
Section x. Context {fx : YK11.FPState}.
Let RUNTO := paj_run_to B LAWS.
Let PRUN := SRr_run_pi_AJ B LAWS.
Let PRUNC := SRr_run_pi_AJ_call B LAWS.
Let PRUNTO := SRr_run_to_pi_AJ B LAWS.

(* the registers of the cut (pf_a3_d.v's a3_ret1) and the list the state after the slot stores holds *)
Definition a3w_RL0 (v : pfv) (pos : Z) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF);
   (23, pf_F v pos); (24, p_c v); (25, p_t v); (26, p_c v + seg_spec.RC_GEN); (27, pf_SH v pos);
   (21, p_c v + seg_spec.RC_READING)].
Definition a3w_RL1 (v : pfv) (pos : Z) : list (Z * Z) := a3w_RL0 v pos ++ [(18, 12288); (19, pf_SH v pos + 8)].
(* the slots after the stores of 0x87d20 .. 0x87d44 *)
Definition a3w_SL2 (v : pfv) (pos : Z) : list (Z * Z) :=
  [(0x38, shadow_addr (p_c v + seg_spec.RC_GEN)); (0x40, p_c v + seg_spec.RC_GEN); (0x50, pf_F v pos + 32);
   (0x58, p_c v + seg_spec.RC_READING); (0x68, pf_F v pos); (0x80, p_c v + seg_spec.RC_N); (0x88, pf_F v pos);
   (0x98, pf_SH v pos + 8)].

Lemma a3w_fi : forall v pos Sc Wc rX memc mdc, a3_ret1 B v pos Sc Wc rX memc mdc ->
  pf_fi B v pos (p_ly v) Sc Wc rX memc mdc.
Proof.
intros v pos Sc Wc rX memc mdc (_ & HJ & HSc & HPm & HSV & HFL & HFRM & HRG & _).
split; [exact HJ|]. split; [reflexivity|]. split; [exact HSc|]. split; [exact HPm|].
split; [exact HSV|]. split; [exact HFL|]. split; [exact HFRM|].
eapply a5_rg_incl; [|exact HRG]. intros x Hx. cbn [In] in Hx |- *. tauto.
Qed.

Definition a3w_ctx (v : pfv) (pos : Z) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) : Prop :=
  pa2_geoP v pos /\ AR SEGS B (p_ly v) Sc Wc memc mdc /\ In (5, pos) (frames Sc) /\
  frame_addr (p_ly v) 5 pos = pf_F v pos /\
  (forall y, p_c v + seg_spec.RC_GEN <= y < p_c v + seg_spec.RC_GEN + 4 -> pa2_out v pos y) /\
  (forall y, p_c v + seg_spec.RC_GEN <= y < p_c v + seg_spec.RC_GEN + 4 -> ~ (0x10000 <= y < kImgEnd)) /\
  (forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> pa2_out v pos x) /\
  (forall x, p_t v <= x < p_t v + pf_len v -> a3w_out v pos x).
Lemma a3w_ctx_of : forall v pos Sc Wc rX memc mdc, a3_ret1 B v pos Sc Wc rX memc mdc ->
  a3w_ctx v pos Sc Wc memc mdc.
Proof.
intros v pos Sc Wc rX memc mdc HR.
pose proof (a3w_fi _ _ _ _ _ _ _ HR) as HFI.
pose proof HR as (HCX & _ & _ & _ & _ & _ & _ & _ & HOBJ & _).
destruct (pa2_geo B v pos (p_ly v) Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HOBJ as (_ & _ & Hht & _ & Hhc & _).
assert (HC : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> pa2_out v pos x)
  by (intros x Hx; exact (pa2_out_sa_heap B v pos (p_ly v) Sc Wc memc mdc _ _ x HG HAR Hin EF Hhc Hx)).
assert (HT : forall x, p_t v <= x < p_t v + pf_len v -> pa2_out v pos x)
  by (intros x Hx; exact (pa2_out_sa_heap B v pos (p_ly v) Sc Wc memc mdc _ _ x HG HAR Hin EF Hht Hx)).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HRP) & _).
destruct HRP as (HRD & _).
destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdisj & _).
unfold sa_disj, seg_spec.cstr_span in Hdisj.
pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)) as Hsp.
destruct Hhc as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof (blk_off_imgP B (p_ly v) Sc Wc memc mdc b m HAR Hb) as Hoff. unfold off_img in Hoff.
split; [exact HG|]. split; [exact HAR|]. split; [exact Hin|]. split; [exact EF|].
split; [intros y Hy; apply HC; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia|].
split; [intros y Hy Hi; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, kImgEnd in *; lia|].
split; [exact HC|].
intros x Hx. split; [exact (HT x Hx)|]. unfold pf_len, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. lia.
Qed.

(* the seed: every region hangs off a register atom, so the symbolic registers are the atoms *)
Lemma a3w_seed : forall v rX (Wc : world SEGS) memc pc rs G,
  regions_wf rs = true -> Forall (region_ok SEGS (a3wE v rX) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (a3wE v rX) rs -> facts_ok (a3wE v rX) G ->
  st_ok_pi SEGS VAL (a3wE v rX) (mkSS pc sr_atoms rs None G)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; try assumption. apply regs_ok_Eimg_Ereg.
Qed.

(* ======================= phase 1: R1, R2 and the memset (0x87cec -> 0x87d50) ======================= *)
(* what R2 writes: the 19 slots, c->gen, cur_name's two shadow cells *)
Definition a3w_W2 (v : pfv) (pos a : Z) : Prop :=
  (pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0) \/ (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4) \/
  (pf_SH v pos + 4 <= a < pf_SH v pos + 6).
Definition a3w_M2 (v : pfv) (pos : Z) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (rX2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc mem2 md2 0 /\
  a3w_kept v pos (rdW Wc memc) (rdW Wc mem2) /\
  sa_val (rdW Wc mem2) (p_c v + seg_spec.RC_GEN) 4 (rc_gen (p_rcs v) + 1) /\
  (forall i, 0 <= i < 2 -> rdW Wc mem2 (pf_SH v pos + 4 + i) = Some 0) /\
  (forall i, 0 <= i < 16 -> rdW Wc mem2 (pf_F v pos + 32 + i) = Some 0) /\
  pf_sl (rdW Wc mem2) (pf_s1 v) (a3w_SL2 v pos) /\
  pf_rg rX2 (a3w_RL1 v pos).

Lemma a3w_ph1 : forall v pos Sc Wc rX memc mdc (Q : world SEGS -> config -> Prop),
  a3_ret1 B v pos Sc Wc rX memc mdc ->
  (forall rX2 mem2 md2, a3w_M2 v pos Sc Wc memc rX2 mem2 md2 ->
     SRr SEGS Wc (mkCfg (mkst rX2 (Z_to_bv 64 (BASE + PF_RET2)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_RET1)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros v pos Sc Wc rX memc mdc Q HR Kc.
pose proof (a3w_ctx_of _ _ _ _ _ _ _ HR) as (HGEO & HAR & Hin & EF & HCG & HCI & HC & HT).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & FI).
pose proof HR as (HCX & HJ & HSc & HPm & HSV & HFL & HFRM & HRG & HOBJ & HRC & HSL & HFSH).
pose proof HOBJ as (Hst & Hat & Hht & Hac & Hhc & HCAT & HLITS & HROD & HSSP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & ESTK & _).
destruct (HC (p_c v) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc1 & Hc2 & Hc3).
destruct (HC (p_c v + 16615) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hc5 & Hc6).
destruct (HT (p_t v) ltac:(unfold pf_len; lia)) as ((Ht1 & Ht2 & Ht3) & _).
destruct (a3f_rconf_gen_val _ _ _ HRC) as (Hg0 & HgV).
assert (Hg1 : rc_gen (p_rcs v) + 1 < 2 ^ 32).
{ pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HRP) & _).
  destruct HRP as ((_ & _ & _ & _ & _ & Hg & _) & _). exact Hg. }
pose proof (a5_rg_get rX _ 2 _ HRG ltac:(pa2_in)) as R2.
pose proof (a5_rg_get rX _ 9 _ HRG ltac:(pa2_in)) as R9.
pose proof (a5_rg_get rX _ 22 _ HRG ltac:(pa2_in)) as R22.
pose proof (a5_rg_get rX _ 23 _ HRG ltac:(pa2_in)) as R23.
pose proof (a5_rg_get rX _ 24 _ HRG ltac:(pa2_in)) as R24.
pose proof (a5_rg_get rX _ 25 _ HRG ltac:(pa2_in)) as R25.
pose proof (a5_rg_get rX _ 26 _ HRG ltac:(pa2_in)) as R26.
pose proof (a5_rg_get rX _ 27 _ HRG ltac:(pa2_in)) as R27.
assert (HSH : pf_SH v pos = 2147450880 + pf_F v pos / 8) by reflexivity.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
pose proof (Z.div_mod (p_c v + 16608) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p_c v + 16608) 8 ltac:(lia)).
pose proof (Z.div_mod (p_c v + 11392) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p_c v + 11392) 8 ltac:(lia)).
pose proof Hhc as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrqc].
pose proof (Forall_inv HSL) as W88. pose proof (Forall_inv (Forall_inv_tail HSL)) as W98. cbn [fst snd] in W88, W98.
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HAR Hin) as (_ & Happ0 & _ & _).
unfold a3_rd1 in Hg0, HgV. cbn [rc_gen] in Hg0, HgV.
(* ---- R1: the seed at 0x87cec, no region; check #1, the token run to 0x87d00 ---- *)
assert (HEI : img_env VAL A_LIM (a3wE v rX)) by apply a3wE_img.
assert (E22 : ew (a3wE v rX) 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (a3wE_low v rX 22) by lia; exact R22).
assert (E25 : ew (a3wE v rX) 25 = Z_to_bv 64 (p_t v)) by (rewrite (a3wE_low v rX 25) by lia; exact R25).
assert (E26 : ew (a3wE v rX) 26 = Z_to_bv 64 (p_c v + seg_spec.RC_GEN))
  by (rewrite (a3wE_low v rX 26) by lia; exact R26).
pose proof (a3w_seed v rX Wc memc PF_RET1 [] a3w_G1 eq_refl (Forall_nil _) I) as HS.
assert (HS1 : st_ok_pi SEGS VAL (a3wE v rX) (mkSS PF_RET1 sr_atoms [] None a3w_G1)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_RET1)) memc (seg_rom SEGS)))).
{ apply HS. split; [|split; exact I]. unfold a3w_G1, PTR. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E22, E25, E26, !unsigned_lit_small by (unfold seg_spec.RC_GEN, SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF, seg_spec.RC_GEN. repeat split; lia. }
clear HS.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] (a3wE v rX) (mrestrict (w_H Wc) memc)) by constructor.
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan (PF_FRAME + 0x3c).
{ cbn [ms_mem]. rewrite (U_atom _ 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 26 _ E26) by (unfold seg_spec.RC_GEN; lia).
  pose proof Hac as (_ & _ & _ & HRA & _).
  exact (range_addressable_sub _ _ (p_c v) seg_spec.SEG_C_SIZE (p_c v + seg_spec.RC_GEN) 8 HRA
    ltac:(unfold seg_spec.RC_GEN; lia) ltac:(unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE; lia)). }
{ apply awr_ok_nil. }
(* ---- after R1: the memory is memc; the registers are rX's but a0 and a3 = the shadow address of &c->gen ---- *)
pa2_clear_md.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) (a3wE v rX) _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b0 wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (RA1 : pf_rg (ms_regs ms) (a3w_RL0 v pos)).
{ apply (a3w_rg_keep _ _ _ _ rX _ HS1); [|vm_compute; reflexivity | exact HRG].
  intros n Hn. rewrite ?ew_ewset_other by lia. apply a3wE_low. exact Hn. }
a3w_rr HS1 (Z_to_bv 5 13) R13'.
assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (shadow_addr (p_c v + seg_spec.RC_GEN))).
{ rewrite R13'. apply a3w_den_sh.
  - rewrite ?ew_ewset_other by lia. rewrite (a3wE_low v rX 26) by lia. exact R26.
  - unfold seg_spec.RC_GEN. lia.
  - rewrite ?ew_ewset_other by lia. rewrite (a3wE_low v rX 22) by lia. exact R22. }
clear R13'.
pmkst HS1. clear HS1 SHOK HF HFr HG E22 E25 E26.
rename ms into ms1.
(* ---- R2: the seed at 0x87d00 with the slots, c->gen and cur_name's shadow cells; the plain run to the memset ---- *)
assert (HEI1 : img_env VAL A_LIM (a3wE v (ms_regs ms1))) by apply a3wE_img.
pose proof (proj1 HJ) as HAR1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
rewrite ESTK in Hpres1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR1 Hbc) as (_ & _ & _ & _ & Hbp1 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HAR1 Hin) as (_ & _ & _ & Hsh1).
rewrite EF in Hsh1. change (fs_frame_bytes 5 / 8) with 256 in Hsh1.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh1.
assert (E1 : forall (n : nat) z, (n < 32)%nat -> In (Z.of_nat n, z) (a3w_RL0 v pos) ->
    ew (a3wE v (ms_regs ms1)) n = Z_to_bv 64 z).
{ intros n z Hn Hz. rewrite (a3wE_low v (ms_regs ms1) n Hn). exact (a5_rg_get _ _ _ _ RA1 Hz). }
assert (E9 := E1 9%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
assert (E13 : ew (a3wE v (ms_regs ms1)) 13 = Z_to_bv 64 (shadow_addr (p_c v + seg_spec.RC_GEN)))
  by (rewrite (a3wE_low v (ms_regs ms1) 13) by lia; exact R13).
assert (E21 := E1 21%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
assert (E23 := E1 23%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
assert (E24 := E1 24%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
assert (E25 := E1 25%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
assert (E26 := E1 26%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
assert (E27 := E1 27%nat _ ltac:(lia) ltac:(unfold a3w_RL0; pa2_in)).
clear E1.
assert (U9 : bv_unsigned (ew (a3wE v (ms_regs ms1)) 9) = pf_s1 v) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (a3wE v (ms_regs ms1)) 25) = p_t v) by (rewrite E25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (a3wE v (ms_regs ms1)) 26) = p_c v + seg_spec.RC_GEN)
  by (rewrite E26; apply unsigned_lit_small; unfold seg_spec.RC_GEN; lia).
assert (U27 : bv_unsigned (ew (a3wE v (ms_regs ms1)) 27) = pf_SH v pos)
  by (rewrite E27; apply unsigned_lit_small; lia).
assert (HS2 : st_ok_pi SEGS VAL (a3wE v (ms_regs ms1)) (mkSS 12236 sr_atoms [a3w_RSL; a3w_RGEN; a3w_RFSH] None a3w_G2)
    (restrict (w_H Wc) (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + 12236)) (ms_mem ms1) (seg_rom SEGS)))).
{ apply a3w_seed.
  - vm_compute. reflexivity.
  - unfold a3w_RSL, a3w_RGEN, a3w_RFSH. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply Hpres1. lia.
      * constructor; [|constructor; [|constructor]].
        -- apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0x88 8 (SOff 23 0) (pf_F v pos));
             [rewrite pa2_crt_den_atom0; exact E23 | lia | lia |].
           apply val_mem_of_rdword. rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms1)));
             [exact W88 | intros k Hk; apply KM1; lia].
        -- apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0x98 8 (SOff 27 8) (pf_SH v pos + 8));
             [exact (pa2_den_off _ 27 (pf_SH v pos) 8 E27 ltac:(lia)) | lia | lia |].
           apply val_mem_of_rdword. rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms1)));
             [exact W98 | intros k Hk; apply KM1; lia].
    + rewrite U26. split; [unfold seg_spec.RC_GEN; lia|]. split; [unfold seg_spec.RC_GEN; lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). refine (proj1 (Hbp1 _ _)).
        unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS _ _ (p_c v + seg_spec.RC_GEN) 0 4 (SOff 32 0) (rc_gen (p_rcs v)));
          [rewrite pa2_crt_den_atom0, a3wE_x32; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
        rewrite Z.add_0_r. apply a3w_vm_of_sv. intros k Hk. rewrite KM1; [exact (HgV k Hk)|].
        unfold seg_spec.RC_GEN. lia.
    + rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hsh1 o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, a3w_RSL, a3w_RGEN, a3w_RFSH.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U26, U27. unfold seg_spec.RC_GEN.
    repeat split; lia.
  - split; [|split; exact I]. unfold a3w_G2. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U25, (a3wE_x32 v (ms_regs ms1)). unfold w64. rewrite unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
paj_run_shc PRUN PRUNC HS2 HJ.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr. unfold a3w_RSL, a3w_RGEN, a3w_RFSH in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite U9 in Ha. rewrite ESTK. lia.
  - right; left. rewrite U26 in Ha. split.
    + exists (p_c v + seg_spec.RC_READING, p_c v + seg_spec.RC_GEN + 4). split.
      * unfold seg_spec.RC_PARSE_W. right; right; left; reflexivity.
      * cbn [fst snd]. unfold seg_spec.RC_READING, seg_spec.RC_GEN in *. lia.
    + exists bc, mc. split; [exact Hbc | unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia].
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    rewrite U27 in Ha. lia. }
(* ---- after R2, at the memset call: what the run kept and wrote, the registers ---- *)
pa2_clear_md.
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ a3w_W2 v pos a -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem ms1) a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) (a3wE v (ms_regs ms1)) _ (w_H Wc) (ms_mem ms1) (ms_mem ms)
    (a3w_W2 v pos) HFr); [|exact Ha | exact Hn].
  intros b0 wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
    rewrite ?U9, ?U26, ?U27 in Hrr; unfold a3w_W2; lia |]).
  destruct Hin'. }
lazymatch type of HS2 with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) a3w_RFSH) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS2 ltac:(vm_compute; reflexivity)) as HQ0;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) a3w_RFSH) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS2 ltac:(vm_compute; reflexivity)) as HQ1;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) a3w_RFSH) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 2 r2 HS2 ltac:(vm_compute; reflexivity)) as HQ2 end.
cbn [ms_mem restrict] in HQ0, HQ1, HQ2.
assert (SL2a : pf_sl (rdW Wc (ms_mem ms)) (pf_s1 v) (a3w_SL2 v pos)).
{ unfold pf_sl, a3w_SL2. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a3w_slot HQ0 U9. }
pose proof (field_of_region_any (segs := SEGS) (a3wE v (ms_regs ms1)) _ 26 (p_c v + seg_spec.RC_GEN) _ 0 4 0 4 0 4%N
  (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) HQ1 U26 ltac:(a3w_inc) ltac:(lia)) as VG.
rewrite (a3w_den_gen1 _ (rc_gen (p_rcs v)) (a3wE_x32 v (ms_regs ms1)) ltac:(lia) Hg1), Z.add_0_r in VG.
pose proof (a3w_sv_of_vm (w_H Wc) (ms_mem ms) _ _ _ VG) as VGs. clear VG.
pose proof (pa2_cell_of_region _ (w_H Wc) (ms_mem ms) 27 (pf_SH v pos) _ _ _ _ _ 4 0 HQ2 U27
  ltac:(vm_compute; reflexivity)) as CL4.
pose proof (pa2_cell_of_region _ (w_H Wc) (ms_mem ms) 27 (pf_SH v pos) _ _ _ _ _ 5 0 HQ2 U27
  ltac:(vm_compute; reflexivity)) as CL5.
assert (RB2 : pf_rg (ms_regs ms) (a3w_RL0 v pos)).
{ apply (a3w_rg_keepC _ _ _ _ (ms_regs ms1) _ HS2); [intros n Hn; apply a3wE_low; exact Hn | vm_compute; reflexivity | exact RA1]. }
a3w_rr HS2 (Z_to_bv 5 18) Q18. rewrite a3w_den_lit in Q18.
a3w_rr HS2 (Z_to_bv 5 19) Q19. rewrite (pa2_den_off _ 27 (pf_SH v pos) 8 E27) in Q19 by lia.
a3w_rr HS2 (Z_to_bv 5 1) Q1.
a3w_rr HS2 (Z_to_bv 5 10) Q10. rewrite (pa2_den_off _ 23 (pf_F v pos) 32 E23) in Q10 by lia.
a3w_rr HS2 (Z_to_bv 5 11) Q11. rewrite a3w_den_lit in Q11.
a3w_rr HS2 (Z_to_bv 5 12) Q12. rewrite a3w_den_lit in Q12.
pmkst HS2.
(* ---- 0x87d4c: __asan_memset(cur_name, 0, 16) (pf_a3_k.a3_mset_site) ---- *)
eapply SRr_bind.
{ apply (a3_mset_site B MSET Wc (ms_regs ms) (ms_mem ms) (pf_sp0 v) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v)
    (p_ly v) Sc _ 0 (p_c v) pos (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_RET2)) (SIGMA SS___asan_memset) HJ Hin).
  - apply (pa2_bvr _ _ 10); [reflexivity|]. rewrite Q10, EF. reflexivity.
  - apply (pa2_bvr _ _ 11); [reflexivity | exact Q11].
  - apply (pa2_bvr _ _ 12); [reflexivity | exact Q12].
  - apply (pa2_bvr _ _ 3); [reflexivity | exact (a5_rg_get _ _ 3 _ RB2 ltac:(unfold a3w_RL0; pa2_in))].
  - apply (pa2_bvr _ _ 4); [reflexivity | exact (a5_rg_get _ _ 4 _ RB2 ltac:(unfold a3w_RL0; pa2_in))].
  - apply (pa2_bvr _ _ 1); [reflexivity|]. rewrite Q1. exact (codeptr_val _ 12316 HEI1).
  - apply ret_ok_codeptr_v; [unfold PF_RET2, PF_FRAME, AF_reac_segconf_parse_file; lia | reflexivity].
  - unfold spZ. match goal with |- context [getr (ms_regs ms) ?r] =>
      rewrite (pa2_bvr (ms_regs ms) r 2 _ eq_refl (a5_rg_get _ _ 2 _ RB2 ltac:(unfold a3w_RL0; pa2_in))) end.
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (pa2_m16 _ _ S6 S3).
  - lia.
  - rewrite ESTK. unfold ESTACK. lia.
  - unfold ESTACK. lia.
  - rewrite EF. lia.
  - rewrite EF. change (fs_frame_bytes 5) with 2048. lia.
  - exact Happ0.
  - intros a Ha Hf. apply a5_rcw_in in Hf. destruct (HC a Hf) as (_ & _ & Hx). apply Hx.
    rewrite EF in Ha. change (fs_frame_bytes 5) with 2048 in Ha. lia.
  - intros i Hi. rewrite EF. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    assert (i = 0 \/ i = 1) as [-> | ->] by lia; [rewrite Z.add_0_r; exact CL4 | rewrite <- Z.add_assoc; exact CL5].
  - reflexivity. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Heff & Hkeep & Hpres2 & Hsame).
apply Kc.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk2 & _). rewrite ESTK in Hstk2.
split; [exact HJ2|].
split.
{ apply (a3w_kept_trans v pos _ (rdW Wc (ms_mem ms1))).
  { apply (a3w_kept_step v pos _ _ (fun _ => False));
      [tauto | intros a Ha _; exact (KM1 a Ha) | intros a Ha Hv; rewrite (KM1 a Ha); exact Hv]. }
  apply (a3w_kept_trans v pos _ (rdW Wc (ms_mem ms))).
  { apply (a3w_kept_step v pos _ _ (a3w_W2 v pos)).
    - intros a Hw. unfold a3w_W2, a3w_Wr in *. lia.
    - exact KM2.
    - intros a Ha Hv. exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms) a HG Hv). }
  apply (a3w_kept_step v pos _ _ (fun a => pf_F v pos + 32 <= a < pf_F v pos + 48 \/ pf_s1 v - 4096 <= a < pf_s1 v)).
  - intros a Hw. unfold a3w_Wr. lia.
  - intros a Ha Hn. apply Hkeep; [exact Ha | rewrite EF; lia | unfold ESTACK; lia].
  - intros a Ha Hv.
    assert (Hd : (pf_F v pos + 32 <= a < pf_F v pos + 48) \/ (pf_s1 v - 4096 <= a < pf_s1 v) \/
       ~ (pf_F v pos + 32 <= a < pf_F v pos + 48 \/ pf_s1 v - 4096 <= a < pf_s1 v)) by lia.
    destruct Hd as [Hd | [Hd | Hd]].
    + replace a with (frame_addr (p_ly v) 5 pos + 32 + (a - pf_F v pos - 32)) by (rewrite EF; lia).
      rewrite Heff by lia. discriminate.
    + apply (aview_some_of_apresent SEGS). apply Hstk2. lia.
    + rewrite Hkeep; [exact Hv | exact Ha | rewrite EF; lia | unfold ESTACK; lia]. }
split.
{ intros k Hk. destruct (HCG (p_c v + seg_spec.RC_GEN + Z.of_nat k) ltac:(lia)) as ((Hx1 & Hx2) & _ & Hx3).
  rewrite Hkeep; [exact (VGs k Hk) | lia | rewrite EF; lia | unfold ESTACK; lia]. }
split.
{ intros i Hi. rewrite Hkeep; [| lia | rewrite EF; lia | unfold ESTACK; lia].
  assert (i = 0 \/ i = 1) as [-> | ->] by lia; [rewrite Z.add_0_r; exact CL4 | rewrite <- Z.add_assoc; exact CL5]. }
split.
{ intros i Hi. rewrite <- EF. exact (Heff i Hi). }
split.
{ apply (a3w_sl_keep (rdW Wc (ms_mem ms))); [|exact SL2a].
  intros ov Hov k Hk. unfold a3w_SL2 in Hov. cbn [In] in Hov.
  assert (Hoff : 0x38 <= fst ov <= 0x98) by (repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia |]); destruct Hov).
  apply Hkeep; [lia | rewrite EF; lia | unfold ESTACK; lia]. }
unfold a3w_RL1. apply (proj2 (a5_rg_app _ _ _)). split.
- apply (a5_rg_pres (ms_regs ms) regs2 _ HP2); [|exact RB2].
  unfold a3w_RL0. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
- apply (a5_rg_pres (ms_regs ms) regs2 _ HP2).
  + repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
  + apply a3w_rg_cons; [exact Q18 |]. apply a3w_rg_cons; [exact Q19 |]. apply Forall_nil.
Qed.

(* ======================= phase 2: R3, check #2 (0x87d50 -> 0x87d60) ======================= *)
Lemma a3w_ph2 : forall v pos Sc Wc rX memc mdc rX2 mem2 md2 (Q : world SEGS -> config -> Prop),
  a3_ret1 B v pos Sc Wc rX memc mdc -> a3w_M2 v pos Sc Wc memc rX2 mem2 md2 ->
  (forall rX4 mem4 md4, a3w_M2 v pos Sc Wc memc rX4 mem4 md4 ->
     SRr SEGS Wc (mkCfg (mkst rX4 (Z_to_bv 64 (BASE + (PF_FRAME + 0x9c))) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS Wc (mkCfg (mkst rX2 (Z_to_bv 64 (BASE + PF_RET2)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros v pos Sc Wc rX memc mdc rX2 mem2 md2 Q HR HM Kc.
pose proof (a3w_ctx_of _ _ _ _ _ _ _ HR) as (HGEO & HAR & Hin & EF & HCG & HCI & HC & HT).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & FI).
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & HOBJ & _).
pose proof HOBJ as (_ & Hat & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (HC (p_c v) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc1 & Hc2 & Hc3).
destruct (HC (p_c v + 16615) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hc5 & Hc6).
destruct (HT (p_t v) ltac:(unfold pf_len; lia)) as ((Ht1 & Ht2 & Ht3) & _).
assert (HSH : pf_SH v pos = 2147450880 + pf_F v pos / 8) by reflexivity.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
pose proof HM as (HJ & HK & HVG & HCL & HZ & HSL & HRG).
pose proof (a5_rg_get rX2 _ 22 _ HRG ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)) as R22.
pose proof (a5_rg_get rX2 _ 25 _ HRG ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)) as R25.
assert (HEI : img_env VAL A_LIM (a3wE v rX2)) by apply a3wE_img.
assert (E22 : ew (a3wE v rX2) 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (a3wE_low v rX2 22) by lia; exact R22).
assert (E25 : ew (a3wE v rX2) 25 = Z_to_bv 64 (p_t v)) by (rewrite (a3wE_low v rX2 25) by lia; exact R25).
assert (HS : st_ok_pi SEGS VAL (a3wE v rX2) (mkSS PF_RET2 sr_atoms [] None a3w_G3)
    (restrict (w_H Wc) (mkst rX2 (Z_to_bv 64 (BASE + PF_RET2)) mem2 (seg_rom SEGS)))).
{ apply a3w_seed; [reflexivity | apply Forall_nil | exact I |].
  split; [|split; exact I]. unfold a3w_G3, PTR. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E22, E25, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff 22 0) [] (a3wE v rX2) (mrestrict (w_H Wc) mem2)) by constructor.
assert (Haddr : sa_addr (rdW Wc mem2) (p_t v) (pf_len v)).
{ eapply (a3w_k_addr v pos); try eassumption. intros x Hx. exact (proj1 (HT x Hx)). }
paj_run_to_tok RUNTO HS HJ SHOK Bspan (PF_FRAME + 0x9c).
{ cbn [ms_mem]. rewrite (U_atom _ 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 25 _ E25) by lia.
  pose proof Haddr as (_ & _ & _ & HRA & _).
  exact (range_addressable_sub _ _ (p_t v) (pf_len v) (p_t v) 1 HRA ltac:(lia) ltac:(unfold pf_len; lia)). }
{ apply awr_ok_nil. }
pa2_clear_md.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) (a3wE v rX2) _ (w_H Wc) mem2 (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b0 wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
assert (RA : pf_rg (ms_regs ms) (a3w_RL1 v pos)).
{ apply (a3w_rg_keep _ _ _ _ rX2 _ HS); [|vm_compute; reflexivity | exact HRG].
  intros n Hn. rewrite ?ew_ewset_other by lia. apply a3wE_low. exact Hn. }
pmkst HS.
change (Z_to_bv 64 (BASE + 12332)) with (Z_to_bv 64 (BASE + (PF_FRAME + 0x9c))).
apply Kc.
split; [exact HJ|].
split.
{ apply (a3w_kept_trans v pos _ (rdW Wc mem2)); [exact HK|].
  apply (a3w_kept_step v pos _ _ (fun _ => False));
    [tauto | intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
split; [intros k Hk; rewrite KM by (unfold seg_spec.RC_GEN; lia); exact (HVG k Hk)|].
split; [intros i Hi; rewrite KM by lia; exact (HCL i Hi)|].
split; [intros i Hi; rewrite KM by lia; exact (HZ i Hi)|].
split; [|exact RA].
apply (a3w_sl_keep (rdW Wc mem2)); [|exact HSL].
intros ov Hov k Hk. unfold a3w_SL2 in Hov. cbn [In] in Hov.
assert (Hoff : 0x38 <= fst ov <= 0x98) by (repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia |]); destruct Hov).
apply KM. lia.
Qed.

(* ======================= phase 3: R4 (0x87d60 -> HEAD or DONE) and the exit cut ======================= *)
Lemma a3w_post_eq : forall v, PF_POST B v = PF_POSTr B v (fst (r_parse_file (p_rcs v) (p_s v) (p_lab v))).
Proof. intros v. unfold PF_POST, PF_POSTr. rewrite a3f_parse_snd. reflexivity. Qed.
Local Ltac a3w_ck8 HSL := (eapply a3w_ck; [ | | eapply a3w_sl_in; [exact HSL | unfold a3w_SL2; a3w_inc]]);
  [a3w_den | a3w_arith].

(* what every exit needs at the state R4 left: the facts of the cut carried to it *)
Definition a3w_FIN (v : pfv) (pos : Z) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (rX5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc mem5 md5 0 /\
  a3w_kept v pos (rdW Wc memc) (rdW Wc mem5) /\
  sa_val (rdW Wc mem5) (p_c v + seg_spec.RC_GEN) 4 (rc_gen (p_rcs v) + 1) /\
  (forall i, 0 <= i < 2 -> rdW Wc mem5 (pf_SH v pos + 4 + i) = Some 0) /\
  (forall i, 0 <= i < 16 -> rdW Wc mem5 (pf_F v pos + 32 + i) = Some 0) /\
  pf_rg rX5 [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF);
             (19, pf_SH v pos + 8); (24, p_c v); (25, p_t v); (27, pf_SH v pos)].
(* the cut's frame part, objects, record and shadow at that state *)
Lemma a3w_fin_parts : forall v pos Sc Wc rX memc mdc rX5 mem5 md5,
  a3_ret1 B v pos Sc Wc rX memc mdc -> a3w_FIN v pos Sc Wc memc rX5 mem5 md5 ->
  pf_fi B v pos (p_ly v) Sc Wc rX5 mem5 md5 /\ pf_obj B v (p_ly v) Sc (rdW Wc mem5) /\
  sa_rconf (rdW Wc mem5) (p_c v) (pf_start (p_rcs v) (p_lab v)) /\
  pf_fsh (rdW Wc mem5) (pf_SH v pos) PF_SC_HEAD /\
  pf_nm (rdW Wc mem5) (pf_F v pos + PF_O_CN) [].
Proof.
intros v pos Sc Wc rX memc mdc rX5 mem5 md5 HR (HJ & HK & HVG & HCL & HZ & HRG).
pose proof (a3w_ctx_of _ _ _ _ _ _ _ HR) as (HGEO & HAR & Hin & EF & HCG & HCI & HC & HT).
pose proof HR as (HCX & _ & HSc & HPm & HSV & HFL & HFRM & _ & HOBJ & HRC & _ & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & HLITS & _).
destruct (a3f_rconf_gen_val _ _ _ HRC) as (Hg0 & _).
assert (Hg1 : rc_gen (p_rcs v) + 1 < 2 ^ 32).
{ pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HRP) & _).
  destruct HRP as ((_ & _ & _ & _ & _ & Hg & _) & _). exact Hg. }
assert (HNL : ~ In 0 (a3_LT v)).
{ unfold a3_LT. pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (_ & HOS & _)) & _).
  revert HOS. destruct (p_lab v) as [l|]; intros HOS.
  - destruct HOS as (_ & (_ & Hn) & _). exact Hn.
  - destruct (HLITS S_base ltac:(unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; tauto))
      as (_ & ((_ & Hn) & _) & _). exact Hn. }
split.
{ split; [exact HJ|]. split; [reflexivity|]. split; [exact HSc|]. split; [exact HPm|].
  split; [eapply (a3w_keep_saved v pos); eassumption|].
  split; [eapply (a3w_keep_flag v pos); eassumption|].
  split; [exact HFRM|].
  eapply a5_rg_incl; [|exact HRG]. intros x Hx. cbn [In] in Hx |- *. tauto. }
split; [eapply (a3w_keep_obj v pos); eassumption|].
split.
{ rewrite (a3f_pf_start_eq (p_rcs v) (p_lab v) (a3_LT v) eq_refl HNL).
  eapply (a3w_keep_rconf v pos) with (cf := a3_rd1 v); eassumption. }
split; [eapply (a3w_keep_fsh v pos); eassumption|].
apply a3f_nm_nil. exact HZ.
Qed.

Lemma a3w_head : forall v pos Sc Wc rX memc mdc rX4 mem4 md4,
  (forall n, HA_HEAD B n) -> a3_ret1 B v pos Sc Wc rX memc mdc ->
  a3w_M2 v pos Sc Wc memc rX4 mem4 md4 -> hd0 (p_s v) <> 0 ->
  SRr SEGS Wc (mkCfg (mkst rX4 (Z_to_bv 64 (BASE + (PF_FRAME + 0x9c))) mem4 (seg_rom SEGS)) md4) (PF_POST B v).
Proof.
intros v pos Sc Wc rX memc mdc rX4 mem4 md4 HEADS HR HM Hh0.
pose proof (a3w_ctx_of _ _ _ _ _ _ _ HR) as (HGEO & HAR & Hin & EF & HCG & HCI & HC & HT).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & FI).
pose proof HR as (HCX & _ & _ & _ & _ & _ & _ & _ & HOBJ & _).
pose proof HOBJ as (Hst & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & ESTK & _).
destruct (HC (p_c v) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc1 & Hc2 & Hc3).
destruct (HC (p_c v + 16615) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hc5 & Hc6).
destruct (HT (p_t v) ltac:(unfold pf_len; lia)) as ((Ht1 & Ht2 & Ht3) & _).
assert (HSH : pf_SH v pos = 2147450880 + pf_F v pos / 8) by reflexivity.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
pose proof (Z.div_mod (p_c v + 16608) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p_c v + 16608) 8 ltac:(lia)).
pose proof (Z.div_mod (p_c v + 11392) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p_c v + 11392) 8 ltac:(lia)).
pose proof HM as (HJ & HK & HVG & HCL & HZ & HSL & HRG).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). rewrite ESTK in Hstk.
(* the text's first byte at mem4 *)
assert (Hs4 : sa_str (rdW Wc mem4) (p_t v) (p_s v)).
{ eapply (a3w_k_str v pos); try eassumption; intros x Hx; apply HT; unfold pf_len; lia. }
assert (HT0 : rdW Wc mem4 (p_t v) = Some (hd0 (p_s v))).
{ destruct Hs4 as ((Hz & _) & _). pose proof (Hz 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hz0.
  change (Z.of_nat 0) with 0 in Hz0. rewrite Z.add_0_r in Hz0. rewrite Hz0. destruct (p_s v); reflexivity. }
destruct (aview_byte SEGS _ _ _ _ HT0) as (_ & _ & _ & Hh8).
assert (Hlen0 : (0 < length (p_s v))%nat)
  by (clear - Hh0; revert Hh0; destruct (p_s v) as [|b l]; cbn; intros H; [exfalso; apply H; reflexivity | lia]).
(* ---- R4: the seed at 0x87d60 with the eight slots and text[0] = atom 33, s2 pinned to 0x3000 ---- *)
assert (HEI : img_env VAL A_LIM (a3wE v rX4)) by apply a3wE_img.
assert (E1 : forall (n : nat) z, (n < 32)%nat -> In (Z.of_nat n, z) (a3w_RL1 v pos) ->
    ew (a3wE v rX4) n = Z_to_bv 64 z)
  by (intros n z Hn Hz; rewrite (a3wE_low v rX4 n Hn); exact (a5_rg_get _ _ _ _ HRG Hz)).
assert (E9 := E1 9%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E21 := E1 21%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E22 := E1 22%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E23 := E1 23%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E24 := E1 24%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E25 := E1 25%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E26 := E1 26%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E27 := E1 27%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
clear E1.
pose proof (a5_rg_get _ _ 18 _ HRG ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)) as R18.
assert (U9 : bv_unsigned (ew (a3wE v rX4) 9) = pf_s1 v) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (a3wE v rX4) 25) = p_t v) by (rewrite E25; apply unsigned_lit_small; lia).
assert (E277 : ew (a3wE v rX4) 277 = Z_to_bv 64 0x21380).
{ change 277%nat with (A_OBJ 36). rewrite (a3w_obj _ 36 HEI) by lia. rewrite a3w_lit_blanks. reflexivity. }
assert (E278 : ew (a3wE v rX4) 278 = Z_to_bv 64 0x213a0).
{ change 278%nat with (A_OBJ 37). rewrite (a3w_obj _ 37 HEI) by lia. rewrite a3w_lit_flong. reflexivity. }
assert (HLB : seg_litA_rc [SP; TAB; CR] = 0x21380) by (vm_compute; reflexivity).
assert (HLF : seg_litA_rc F_long = 0x213a0) by (vm_compute; reflexivity).
assert (HS0 : st_ok_pi SEGS VAL (a3wE v rX4) (mkSS 12332 sr_atoms [a3w_RSL4; a3w_RTXT (SOff 33 0)] None a3w_G4h)
    (restrict (w_H Wc) (mkst rX4 (Z_to_bv 64 (BASE + 12332)) mem4 (seg_rom SEGS)))).
{ apply a3w_seed.
  - vm_compute. reflexivity.
  - unfold a3w_RSL4, a3w_RTXT. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply Hstk. lia.
      * repeat (apply Forall_cons; [a3w_ck8 HSL|]). apply Forall_nil.
    + rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (a3w_ck1 _ _ _ _ _ (hd0 (p_s v))); [rewrite pa2_crt_den_atom0, a3wE_x33; reflexivity | lia | exact HT0].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, a3w_RSL4, a3w_RTXT.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25. repeat split; lia.
  - split; [|split; exact I]. unfold a3w_G4h. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (a3wE_x33 v rX4). unfold w64. rewrite unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 18) 12288 HS0 R18 eq_refl) as HS. clear HS0.
paj_run_to_sh PRUNTO HS HJ PF_HEAD.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr. unfold a3w_RSL4, a3w_RTXT in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite U9 in Ha. rewrite ESTK. lia.
  - lia. }
pa2_clear_md.
assert (KM5 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0) -> rdW Wc (ms_mem ms) a = rdW Wc mem4 a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) (a3wE v rX4) _ (w_H Wc) mem4 (ms_mem ms)
    (fun a => pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0) HFr); [|exact Ha | exact Hn].
  intros b0 wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
    rewrite ?U9, ?U25 in Hrr; lia |]).
  destruct Hin'. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) a3w_RFSH) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HQ0 end.
cbn [ms_mem restrict] in HQ0.
assert (RF : pf_rg (ms_regs ms) [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (22, SHADOW_OFF); (19, pf_SH v pos + 8); (24, p_c v); (25, p_t v); (27, pf_SH v pos)]).
{ apply (a3w_rg_keep _ _ _ _ rX4 _ HS); [intros n Hn; apply a3wE_low; exact Hn | vm_compute; reflexivity |].
  eapply a5_rg_incl; [|exact HRG]. intros x Hx. unfold a3w_RL1, a3w_RL0. cbn [In app] in Hx |- *. tauto. }
a3w_rr HS (Z_to_bv 5 18) Q18. rewrite a3w_den_lit in Q18.
a3w_rr HS (Z_to_bv 5 20) Q20. rewrite a3w_den_lit in Q20.
a3w_rr HS (Z_to_bv 5 26) Q26. rewrite a3w_den_lit in Q26.
assert (HFIN : a3w_FIN v pos Sc Wc memc (ms_regs ms) (ms_mem ms) mdv).
{ split; [exact HJ|].
  split.
  { apply (a3w_kept_trans v pos _ (rdW Wc mem4)); [exact HK|].
    apply (a3w_kept_step v pos _ _ (fun a => pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0)).
    - intros a Hw. unfold a3w_Wr. lia.
    - exact KM5.
    - intros a Ha Hv. exact (aview_keeps_vis SEGS (w_H Wc) mem4 (ms_mem ms) a HG Hv). }
  split; [intros k Hk; rewrite KM5 by (unfold seg_spec.RC_GEN; lia); exact (HVG k Hk)|].
  split; [intros i Hi; rewrite KM5 by lia; exact (HCL i Hi)|].
  split; [intros i Hi; rewrite KM5 by lia; exact (HZ i Hi) | exact RF]. }
destruct (a3w_fin_parts v pos Sc Wc rX memc mdc _ _ _ HR HFIN) as (HFI5 & HOBJ5 & HRC5 & HFSH5 & HNM5).
pmkst HS.
rewrite a3w_post_eq, a3f_parse_fst.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
  change (mkCfg (mkst r (Z_to_bv 64 (BASE + 12456)) m (seg_rom SEGS)) d) with (cfg_at SEGS (BASE + PF_HEAD) r m d) end.
apply (HEADS (length (p_s v)) fx v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv
  (pf_start (p_rcs v) (p_lab v)) None [] 0%nat 0 []).
split.
{ split; [exact HCX|]. split; [exact HFI5|]. split; [exact HOBJ5|]. split; [|exact HFSH5].
  unfold pf_sl, PF_SL. rewrite HLF, HLB. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    a3w_slot HQ0 U9. }
split; [exact (pf_lctx_start (p_s v))|].
split; [exact Hlen0|].
split; [apply Nat.le_refl|].
split.
{ split; [exact HRC5|]. split; [exact I|]. split; [exact HNM5|].
  pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HRP) & _).
  destruct HRP as ((_ & _ & _ & _ & _ & _ & Hrf & Hov & _ & _ & Hl & _) & _).
  exact (a3f_cnt_start (p_rcs v) (p_lab v) (p_s v) Hrf Hov Hl). }
unfold PF_RL. cbn [app pf_cur_ptr]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
apply a3w_rg_cons; [exact Q18|]. apply a3w_rg_cons; [exact (a5_rg_get _ _ 19 _ RF ltac:(pa2_in))|].
apply a3w_rg_cons; [exact (a5_rg_get _ _ 24 _ RF ltac:(pa2_in))|].
apply a3w_rg_cons; [exact (a5_rg_get _ _ 27 _ RF ltac:(pa2_in))|].
apply a3w_rg_cons; [exact (a5_rg_get _ _ 25 _ RF ltac:(pa2_in))|].
apply a3w_rg_cons; [exact Q26|]. apply a3w_rg_cons; [exact Q20|]. apply Forall_nil.
Qed.

Lemma a3w_done : forall v pos Sc Wc rX memc mdc rX4 mem4 md4,
  HA_DONE B -> a3_ret1 B v pos Sc Wc rX memc mdc ->
  a3w_M2 v pos Sc Wc memc rX4 mem4 md4 -> hd0 (p_s v) = 0 ->
  SRr SEGS Wc (mkCfg (mkst rX4 (Z_to_bv 64 (BASE + (PF_FRAME + 0x9c))) mem4 (seg_rom SEGS)) md4) (PF_POST B v).
Proof.
intros v pos Sc Wc rX memc mdc rX4 mem4 md4 HDONE HR HM Hh0.
pose proof (a3w_ctx_of _ _ _ _ _ _ _ HR) as (HGEO & HAR & Hin & EF & HCG & HCI & HC & HT).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & FI).
pose proof HR as (HCX & _ & _ & _ & _ & _ & _ & _ & HOBJ & _).
pose proof HOBJ as (Hst & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & ESTK & _).
destruct (HC (p_c v) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc1 & Hc2 & Hc3).
destruct (HC (p_c v + 16615) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hc5 & Hc6).
destruct (HT (p_t v) ltac:(unfold pf_len; lia)) as ((Ht1 & Ht2 & Ht3) & _).
assert (HSH : pf_SH v pos = 2147450880 + pf_F v pos / 8) by reflexivity.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
pose proof (Z.div_mod (p_c v + 16608) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p_c v + 16608) 8 ltac:(lia)).
pose proof (Z.div_mod (p_c v + 11392) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p_c v + 11392) 8 ltac:(lia)).
pose proof HM as (HJ & HK & HVG & HCL & HZ & HSL & HRG).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). rewrite ESTK in Hstk.
(* the empty text: text[0] is its NUL *)
assert (Hs0 : p_s v = []) by (apply a3f_s_nil; [exact (proj2 (proj1 Hst)) | exact Hh0]).
assert (Hs4 : sa_str (rdW Wc mem4) (p_t v) (p_s v)).
{ eapply (a3w_k_str v pos); try eassumption; intros x Hx; apply HT; unfold pf_len; lia. }
assert (HT0 : rdW Wc mem4 (p_t v) = Some 0).
{ destruct Hs4 as ((Hz & _) & _). rewrite Hs0 in Hz. pose proof (Hz 0%nat ltac:(cbn; lia)) as Hz0.
  change (Z.of_nat 0) with 0 in Hz0. rewrite Z.add_0_r in Hz0. exact Hz0. }
(* ---- R4: the seed at 0x87d60 with the eight slots and text[0] = 0, s2 pinned to 0x3000 ---- *)
assert (HEI : img_env VAL A_LIM (a3wE v rX4)) by apply a3wE_img.
assert (E1 : forall (n : nat) z, (n < 32)%nat -> In (Z.of_nat n, z) (a3w_RL1 v pos) ->
    ew (a3wE v rX4) n = Z_to_bv 64 z)
  by (intros n z Hn Hz; rewrite (a3wE_low v rX4 n Hn); exact (a5_rg_get _ _ _ _ HRG Hz)).
assert (E9 := E1 9%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E21 := E1 21%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E22 := E1 22%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E23 := E1 23%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E24 := E1 24%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E25 := E1 25%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E26 := E1 26%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
assert (E27 := E1 27%nat _ ltac:(lia) ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)).
clear E1.
pose proof (a5_rg_get _ _ 18 _ HRG ltac:(unfold a3w_RL1, a3w_RL0; pa2_in)) as R18.
assert (U9 : bv_unsigned (ew (a3wE v rX4) 9) = pf_s1 v) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (a3wE v rX4) 25) = p_t v) by (rewrite E25; apply unsigned_lit_small; lia).
assert (HS0 : st_ok_pi SEGS VAL (a3wE v rX4) (mkSS 12332 sr_atoms [a3w_RSL4; a3w_RTXT (SLit 0)] None
    (mkFacts [] [] [])) (restrict (w_H Wc) (mkst rX4 (Z_to_bv 64 (BASE + 12332)) mem4 (seg_rom SEGS)))).
{ apply a3w_seed.
  - vm_compute. reflexivity.
  - unfold a3w_RSL4, a3w_RTXT. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply Hstk. lia.
      * repeat (apply Forall_cons; [a3w_ck8 HSL|]). apply Forall_nil.
    + rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (a3w_ck1 _ _ _ _ _ 0); [apply a3w_den_lit | lia | exact HT0].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, a3w_RSL4, a3w_RTXT.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25. repeat split; lia.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 18) 12288 HS0 R18 eq_refl) as HS. clear HS0.
paj_run_to_sh PRUNTO HS HJ PF_DONE.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr. unfold a3w_RSL4, a3w_RTXT in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite U9 in Ha. rewrite ESTK. lia.
  - lia. }
pa2_clear_md.
assert (KM5 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0) -> rdW Wc (ms_mem ms) a = rdW Wc mem4 a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) (a3wE v rX4) _ (w_H Wc) mem4 (ms_mem ms)
    (fun a => pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0) HFr); [|exact Ha | exact Hn].
  intros b0 wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
    rewrite ?U9, ?U25 in Hrr; lia |]).
  destruct Hin'. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) a3w_RFSH) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HQ0 end.
cbn [ms_mem restrict] in HQ0.
assert (RF : pf_rg (ms_regs ms) [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (22, SHADOW_OFF); (19, pf_SH v pos + 8); (24, p_c v); (25, p_t v); (27, pf_SH v pos)]).
{ apply (a3w_rg_keep _ _ _ _ rX4 _ HS); [intros n Hn; apply a3wE_low; exact Hn | vm_compute; reflexivity |].
  eapply a5_rg_incl; [|exact HRG]. intros x Hx. unfold a3w_RL1, a3w_RL0. cbn [In app] in Hx |- *. tauto. }
assert (HFIN : a3w_FIN v pos Sc Wc memc (ms_regs ms) (ms_mem ms) mdv).
{ split; [exact HJ|].
  split.
  { apply (a3w_kept_trans v pos _ (rdW Wc mem4)); [exact HK|].
    apply (a3w_kept_step v pos _ _ (fun a => pf_s1 v + 0x20 <= a < pf_s1 v + 0xc0)).
    - intros a Hw. unfold a3w_Wr. lia.
    - exact KM5.
    - intros a Ha Hv. exact (aview_keeps_vis SEGS (w_H Wc) mem4 (ms_mem ms) a HG Hv). }
  split; [intros k Hk; rewrite KM5 by (unfold seg_spec.RC_GEN; lia); exact (HVG k Hk)|].
  split; [intros i Hi; rewrite KM5 by lia; exact (HCL i Hi)|].
  split; [intros i Hi; rewrite KM5 by lia; exact (HZ i Hi) | exact RF]. }
destruct (a3w_fin_parts v pos Sc Wc rX memc mdc _ _ _ HR HFIN) as (HFI5 & HOBJ5 & HRC5 & HFSH5 & _).
pmkst HS.
rewrite a3w_post_eq, (a3f_parse_done _ _ _ Hs0).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
  change (mkCfg (mkst r (Z_to_bv 64 (BASE + 16004)) m (seg_rom SEGS)) d) with (cfg_at SEGS (BASE + PF_DONE) r m d) end.
apply (HDONE fx v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv (pf_start (p_rcs v) (p_lab v))).
split; [exact HCX|]. split; [exact HFI5|]. split; [exact HOBJ5|]. split; [exact HRC5|].
split.
{ unfold pf_sl. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a3w_slot HQ0 U9. }
split; [exact HFSH5|].
apply a3w_rg_cons; [exact (a5_rg_get _ _ 27 _ RF ltac:(pa2_in))|]. apply Forall_nil.
Qed.

(* ======================= the second half of segment A3 ======================= *)
Theorem a3_ret1_ok : A3_RET1_stmt B.
Proof.
intros HEADS HDONE v pos Sc Wc rX memc mdc HR.
apply (a3w_ph1 v pos Sc Wc rX memc mdc _ HR). intros rX2 mem2 md2 HM2.
apply (a3w_ph2 v pos Sc Wc rX memc mdc rX2 mem2 md2 _ HR HM2). intros rX4 mem4 md4 HM4.
destruct (Z.eq_dec (hd0 (p_s v)) 0) as [H0 | H0].
- exact (a3w_done v pos Sc Wc rX memc mdc rX4 mem4 md4 HDONE HR HM4 H0).
- exact (a3w_head v pos Sc Wc rX memc mdc rX4 mem4 md4 HEADS HR HM4 H0).
Qed.
End x.
End d.
