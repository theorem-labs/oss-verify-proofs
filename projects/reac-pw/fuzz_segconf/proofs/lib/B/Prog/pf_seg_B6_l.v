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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 792 of its 874 lines of code are new or changed and 4971 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B6 of
   reac_segconf_parse_file's walk (0x87e38), its LONG half: b6_long_ok : forall f0 n, HA_REF3 B n -> H_LONG (fx := f0) B n,
   the first conjunct of S_B6 (lib/B/Prog/pf_pieces.v:925) with HA_REF3 for HA_TAIL (the REF3 half, H_REF3 from HA_TAIL,
   is the lane's other file). The B6 segment lane of the image-B G3 walk owner, prover a B6 sub-lane, 2026-10-30.
   proves no function (kind: segment piece of reac_segconf_parse_file's image-B walk; the function's rule-24 record is
   the rule-24 lookup record: no released proof, ADAPTED from the image-A and UBSan walks).
   ADAPTED from the unit owner's UBSan piece lib/U/Prog/pf_p3.v (the same long-line step on the UBSan build: p3_in_set /
   p3_spn are copied here as b6l_in_set / b6l_spn over the image-B carrier's spn_len; its trap `bltu a1,a0` is the
   C-level check of T06 below), re-derived on image B's code in the form of the proved image-B sibling pieces of this
   stream (each copied under the prefix b6l_, none Required): pf_seg_B9_s1.v (a working branch: a seed, a token run
   to an interceptor call, PaArt.aj_art_at with the entry's _realizes, the next state rebuilt), pf_seg_B5_hd.v
   (a working branch: the text's rest as the interceptor's string), pf_seg_B5_r2.v (a working branch: a branch
   by psrr_branch_pi and a UBSan trap refuted with branch_geu_U / U_not / U_atom), pf_seg_B10b_j.v
   (a working branch: a piece that ends by applying the next cut's hypothesis), pf_seg_B9_c.v (the literal's
   premises), pf_seg_B4.v (a token run over seeded slot regions) and lib/B/Prog/trim_l.v (a 1-byte inline check on a
   string byte and the byte's load from a seeded region). Kit: this lane's pf_seg_B6_k.v (geometry, B6's write set,
   the keep lemmas, b6_text, b6_rom, b6_word_of_region) and pf_seg_B6_a.v.

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), LONG 0x88258 .. the refuse call 0x882b4:
     0x88258 mv a0,s11              at = t + o (INV_LONG's s11)
     0x8825c ld a1,184(s1)          slot 0xb8 = seg_litA_rc [SP; TAB; CR] = 0x21380 (PF_SL)
     0x88260 jal strspn             the listing's pa_sigma SS___interceptor_trampoline_strspn (RtString.astrspn_realizes,
                                    window 2 * ESTACK at s1); returns 0x88264 with a0 = lead = strspn_blank (skipn o s)
     0x88264 bgeu a0,s7,0x882a4     lead >= len: cur kept (b6l_cur_ge), straight to refuse's arguments
     0x88268 not a1,s11
     0x8826c bgeu a1,a0,0x88274     UBSan trap T06: not taken only when 2 ^ 64 - 1 - at < lead; refuted (b6l_t06):
     0x88270 j 0x891c8              at + lead <= t + length s < 2 ^ 63 (b6_text's sa_addr t (length s + 1)), never run
     0x88274 add a0,s11,a0          a0 = at + lead (re-seed at 0x88278, b6l_p5)
     0x88278 srli a1,a0,3; 0x8827c add a1,a1,s4; 0x88280 lb a1,0(a1); 0x88284 bnez a1,0x88f78
                                    check B#3 of the load1 at at[lead]; slow arm 0x88f78 andi a2,a0,7; 0x88f7c blt
                                    a2,a1,0x88288; 0x88f80 j 0x89260 (errpath_load1, its stub 0x89260): the token
                                    executor's obligation range_addressable SHADOW_OFF (at + lead) 1, discharged from
                                    sa_addr t (length s + 1) by range_addressable_sub
     0x88288 lbu a0,0(a0)           at[lead] = nth lead (skipn o s) 0
     0x8828c addi a0,a0,-91; 0x88290 seqz a0,a0; 0x88294 addi a0,a0,-1
     0x88298 ld a1,192(s1); 0x8829c and a1,a0,a1; 0x882a0 sd a1,192(s1)
                                    slot 0xc0 = 0 when at[lead] = '[', else cur (b6l_mask_U): pf_cur_ptr c (b6l_cur s o cur)
     0x882a4 li a3,511; 0x882a8 ld a0,200(s1) (c); 0x882ac mv a1,s6 (ln + 1); 0x882b0 ld a2,168(s1) (seg_litA_rc F_long)
     0x882b4 jal refuse             = BASE + PF_REF3: INV_REF3 with pf_ref3's F_long arm, then HA_REF3
   24 hot instructions in 0x88258 .. 0x882b4: the 23 before the cut are walked here (the trap's jump 0x88270 proved
   not reached), the jal at 0x882b4 is the cut REF3, handed on; 4 cold (0x88f78, 0x88f7c, 0x88f80 and the stub 0x89260,
   the slow arm and error edge of check B#3, which the token executor's obligation covers). Trap site T06 discharged,
   check B#3 discharged.
   THE PROOF, three runs and one call: b6l_long (LONG: seed b6l_ss1, a token run to the call, aj_art_at with STRSPN,
   INV_LONG rebuilt at strspn's return by b6l_long_same, its answer by b6l_spn), b6l_after (0x88264: seed b6l_ss2, the
   two branches by psrr_branch_pi, the taken arm run to REF3, the trap refuted, the no-wrap arm run to 0x88278), b6l_p5
   (0x88278: seed b6l_ss3, the token run through check B#3 and the cur store to REF3, slot 0xc0 read back from the
   region). The step is r_line's long branch: pfA_facts.r_line_long_rest (b6l_rline) turns H_LONG's post into REF3's
   post with cur' = b6l_cur s o cur.
   WHERE EACH PREMISE COMES FROM: the text, its NUL, its tail and its heap block from INV_LONG's pf_obj (b6_text); the
   set's literal from pf_obj's sa_lit over PARSE_FILE_LITS; the stack-protector cells (aguard_ok) from pf_obj's sa_ssp;
   the read-only view from pf_obj's arodata_okP (b6_rom); slots 0xa8 / 0xb8 from PF_SL, 0xc8 (c) from pf_fi, 0xc0 (cur)
   from pf_st; s1, s4 (SHADOW_OFF), gp, tp, s0 from pf_fi's registers; s11 = at, s7 = len, s6 = ln + 1 from INV_LONG's
   registers; the window and the call's stack from pf_cx's afn_pre (b6_geo); lead <= len from pfA_facts.O2_strspn_rest.
   SECTION HYPOTHESES: STRSPN (RtString.astrspn_realizes at the listing's strspn trampoline, gotwA, guardA, at every FP
   state, pf_pieces.v:849), SIGP (SegObj.seg_sig_prog) and VRO (SegObj.seg_val_relro), both as the lane's brief names
   them and neither used by this half's proof, and TL (SegPaLib.PALib B: aj_art_at's errno cell, pal_env; agreed with
   the B6 segment lane, 2026-10-30, as the B5 and B9 siblings take it). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
(* the strspn carrier: RtString.astrspn_realizes (its answer is lib/Prog/strspn_c.v spn_len, RtString.PSpn) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
  PaCall PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B6_k pf_seg_B6_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= pure facts ======================= *)
(* strspn's answer on the bytes of a NUL-free string is the spine's strspn_blank (the unit owner's UBSan piece
   lib/U/Prog/pf_p3.v p3_in_set / p3_spn, over the carrier's spn_len) *)
Lemma b6l_in_set : forall x : byte,
  RtString.PSpn.in_set (seg_spec.zb [SP; TAB; CR]) x = blank (bv_unsigned x).
Proof.
intros x.
assert (A : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z).
{ intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hz. }
unfold RtString.PSpn.in_set. cbn [seg_spec.zb map existsb]. rewrite !A by lia. unfold blank.
rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), (Z.eqb_sym 13), orb_false_r, orb_assoc. reflexivity.
Qed.
Lemma b6l_spn : forall bs : list byte, ~ In 0 (seg_spec.zs bs) ->
  RtString.PSpn.spn_len (seg_spec.zb [SP; TAB; CR]) bs = strspn_blank (seg_spec.zs bs).
Proof.
intros bs H. unfold strspn_blank. rewrite cut_nul_id by exact H. clear H. unfold seg_spec.zs.
induction bs as [|b bs IH]; [reflexivity|].
cbn [RtString.PSpn.spn_len map takewhile]. rewrite b6l_in_set.
destruct (blank (bv_unsigned b)); cbn [length]; [rewrite IH; reflexivity | reflexivity].
Qed.
Lemma b6l_map_skipn : forall {A C : Type} (f : A -> C) n l, map f (skipn n l) = skipn n (map f l).
Proof. intros A C f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
Lemma b6l_zs_skipn : forall (l : list Z) o, seg_spec.zs (seg_spec.zb l) = l ->
  seg_spec.zs (skipn o (seg_spec.zb l)) = skipn o l.
Proof. intros l o H. unfold seg_spec.zs in *. rewrite b6l_map_skipn. f_equal. exact H. Qed.
(* the lead strspn counts is at most the line's length (the blanks stop at the line's '\n') *)
Lemma b6l_lead_le : forall rest, ~ In 0 rest -> (strspn_blank rest <= length (fst (break_nl rest)))%nat.
Proof.
intros rest Hn. destruct (O2_strspn_rest_holds rest Hn) as [_ Hsp]. rewrite Hsp. unfold strspn_blank.
pose proof (cut_nul_len (fst (break_nl rest))) as A.
pose proof (pfa_takewhile_len blank (cut_nul (fst (break_nl rest)))) as B. lia.
Qed.
(* the long branch's cur' (pfA_facts.r_line_long_rest), read as the binary reads it *)
Definition b6l_cur (s : list Z) (o : nat) (cur : option nat) : option nat :=
  if nth (strspn_blank (skipn o s)) (skipn o s) 0 =? LBR then None else cur.
Lemma b6l_rline : forall rc cur nm ln s o, ~ In 0 s -> (512 <= length (pf_line s o))%nat ->
  r_line rc cur nm ln (pf_line s o) = (refuse rc ln F_long [AI 511], b6l_cur s o cur, nm).
Proof. intros rc cur nm ln s o Hn Hl. exact (r_line_long_rest rc cur nm ln s o Hn Hl). Qed.
(* lead >= len (0x88264 `bgeu a0,s7` taken): cur is kept *)
Lemma b6l_cur_ge : forall s o cur, ~ In 0 s ->
  (length (pf_line s o) <= strspn_blank (skipn o s))%nat -> b6l_cur s o cur = cur.
Proof.
intros s o cur Hn Hge. unfold b6l_cur.
pose proof (nulfree_skipn o s Hn) as Hr.
rewrite <- (pfa_long_pick (skipn o s) cur Hr).
destruct (O2_strspn_rest_holds (skipn o s) Hr) as [_ Hsp].
unfold pf_line in Hge. rewrite <- Hsp.
replace ((strspn_blank (skipn o s) <? length (fst (break_nl (skipn o s))))%nat) with false
  by (symmetry; apply Nat.ltb_ge; exact Hge).
reflexivity.
Qed.
Lemma b6l_cur_ptr : forall c s o cur,
  pf_cur_ptr c (b6l_cur s o cur) =
  if nth (strspn_blank (skipn o s)) (skipn o s) 0 =? 91 then 0 else pf_cur_ptr c cur.
Proof. intros c s o cur. unfold b6l_cur. destruct (_ =? 91); reflexivity. Qed.
Lemma b6l_cur_ok : forall rc s o cur, pf_cur_ok rc cur -> pf_cur_ok rc (b6l_cur s o cur).
Proof. intros rc s o cur H. unfold b6l_cur. destruct (_ =? 91); [exact I | exact H]. Qed.
(* the trap T06 (0x8826c `bgeu a1,a0` not taken, a1 = not s11): 2 ^ 64 - 1 - at < lead is false when
   at + lead < 2 ^ 63 *)
Lemma b6l_t06 : forall E a b p len, U E a = 2 ^ 64 - 1 - p -> 0 <= p -> 0 <= len -> p + len < 2 ^ 63 ->
  U E b = len -> branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = false -> False.
Proof.
intros E a b p len Ha Hp Hl Hpl Hb Hc. rewrite branch_geu_U, Ha, Hb in Hc.
apply Bool.negb_false_iff, Z.ltb_lt in Hc. lia.
Qed.
(* the word 0x8828c-0x8829c stores in slot 0xc0: ((at[lead] - 91 == 0) - 1) & cur, i.e. 0 when at[lead] == '['
   and cur otherwise (the executor's term at 0x882a0) *)
Lemma b6l_mask_Z : forall b p, 0 <= b < 256 -> 0 <= p < 2 ^ 64 ->
  Z.land (((if (b + -91) mod 2 ^ 64 <? 1 then 1 else 0) mod 2 ^ 64 + (2 ^ 64 - 1)) mod 2 ^ 64) p mod 2 ^ 64 =
  (if b =? 91 then 0 else p).
Proof.
intros b p Hb Hp.
destruct (Z.eqb_spec b 91) as [->|Hne].
- assert (H0 : ((if (91 + -91) mod 2 ^ 64 <? 1 then 1 else 0) mod 2 ^ 64 + (2 ^ 64 - 1)) mod 2 ^ 64 = 0)
    by reflexivity.
  rewrite H0, Z.land_0_l. reflexivity.
- assert (Hm : (b + -91) mod 2 ^ 64 <> 0).
  { intros H0. pose proof (Z.div_mod (b + -91) (2 ^ 64) ltac:(lia)) as D. rewrite H0 in D. lia. }
  pose proof (Z.mod_pos_bound (b + -91) (2 ^ 64) ltac:(lia)) as M.
  assert (H1 : ((if (b + -91) mod 2 ^ 64 <? 1 then 1 else 0) mod 2 ^ 64 + (2 ^ 64 - 1)) mod 2 ^ 64 = Z.ones 64).
  { replace ((b + -91) mod 2 ^ 64 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  rewrite H1, Z.land_comm, Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma b6l_mask_U : forall E b p, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> ew E 33 = Z_to_bv 64 p ->
  0 <= p < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-91)) (SLit 1)) (SLit (-1))) (SOff 33 0)) =
  (if b =? 91 then 0 else p).
Proof.
intros E b p E32 Hb E33 Hp.
rewrite !U_SAlu. rewrite (U_atom E 33 p E33 Hp). rewrite U_SOff, !U_SLit. cbn [zalu_raw].
rewrite E32, unsigned_lit_small by lia.
unfold zcanon, M64. change (1 mod 2 ^ 64) with 1. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
apply b6l_mask_Z; assumption.
Qed.
(* a register named by a bv literal and by Z_to_bv 5 k, both ways *)
Lemma b6l_bvr2 : forall (rr : bvmap 5 word) (r : bv 5) k x, bv_unsigned r = k -> getr rr r = x -> getr rr (Z_to_bv 5 k) = x.
Proof. intros rr r k x Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
(* a word read through a reader of bytes is below 2 ^ 64 *)
Lemma b6l_rdword_rng : forall (rd : reader) a v,
  (forall x w, rd x = Some w -> 0 <= w < 256) -> rdword rd a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros rd a v Hb Hw. unfold rdword in Hw.
destruct (rd a) as [b0|] eqn:E0; [|discriminate].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (Hb _ _ E0). pose proof (Hb _ _ E1). pose proof (Hb _ _ E2). pose proof (Hb _ _ E3).
pose proof (Hb _ _ E4). pose proof (Hb _ _ E5). pose proof (Hb _ _ E6). pose proof (Hb _ _ E7). lia.
Qed.
Ltac b6l_in := unfold PF_RL, PF_RM; cbn [In app]; repeat first [left; reflexivity | right].
Ltac b6l_awr := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* the listing offsets of the two re-seeds: 0x88264 (strspn's return) and 0x88278 (after `add a0,s11,a0`) *)
Definition B6L_RET : Z := AF_reac_segconf_parse_file + 0x42c.
Definition B6L_P5 : Z := AF_reac_segconf_parse_file + 0x440.
(* the token executor's shadow base: s4 = x20 (pf_fi's SHADOW_OFF) *)
Definition b6l_Bx : sv := SOff 20 0.
(* LONG (0x88258): every register its own atom; slot 0xb8 (seg_litA_rc [SP; TAB; CR] = 0x21380) read-only on s1 *)
Definition b6l_ss1 : sstate := mkSS PF_LONG sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xb8 0xc0 0xb8 0xb8 [YP09.mkChunk 0xb8 (CVal 8 (SLit 0x21380))]] None (mkFacts [] [] []).
(* strspn's return (0x88264): every register its own atom; slots 0xa8 (seg_litA_rc F_long = 0x213a0) and 0xc8
   (c, atom 32) read-only on s1 *)
Definition b6l_ss2 : sstate := mkSS B6L_RET sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xa8 0xd0 0 0
     [YP09.mkChunk 0xa8 (CVal 8 (SLit 0x213a0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []).
(* 0x88278: a0 = at + lead (atom 10, the check's address and the load's base); slots 0xa8, 0xc0 (cur, atom 33,
   writable) and 0xc8 (c, atom 34) on s1; the byte at[lead] (atom 32) on a0 *)
Definition b6l_ss3 : sstate := mkSS B6L_P5 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xa8 0xd0 0xc0 0xc8
     [YP09.mkChunk 0xa8 (CVal 8 (SLit 0x213a0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0));
      YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 255 0)] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the strspn entry at the listing's trampoline (pf_pieces.v:849), at every FP state *)
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strspn) gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the listing's runtime record (SegPaLib.v PALib): aj_art_at needs its errno cell, pal_env *)
Hypothesis TL : PALib B.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------- the seeds ---------- *)
Lemma b6l_seed1 : forall v (Wc : world SEGS) (rX : bvmap 5 word) memc,
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) -> 0 <= pf_s1 v -> pf_s1 v + 0xd0 <= 2 ^ 64 ->
  rdword (rdW Wc memc) (pf_s1 v + 0xb8) = Some 0x21380 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b6l_ss1
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_LONG)) memc (seg_rom SEGS))).
Proof.
intros v Wc rX memc R9 S0 S1 HW.
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b6l_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xb8 8 (SLit 0x21380) 0x21380).
  + cbn [sv_denot]. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + change (Z.of_N 8) with 8. lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HW).
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.
Lemma b6l_seed2 : forall v (Wc : world SEGS) (rX : bvmap 5 word) memc,
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) -> 0 <= pf_s1 v -> pf_s1 v + 0xd0 <= 2 ^ 64 -> 0 <= p_c v < 2 ^ 64 ->
  rdword (rdW Wc memc) (pf_s1 v + 0xa8) = Some 0x213a0 ->
  rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (p_c v)])) b6l_ss2
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B6L_RET)) memc (seg_rom SEGS))).
Proof.
intros v Wc rX memc R9 S0 S1 HC Wa8 Wc8.
set (E := Eimg (Ereg rX [w64 (p_c v)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (p_c v))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
rewrite restrict_mkst_fx. unfold b6l_ss2. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xa8 8 (SLit 0x213a0) 0x213a0).
    * cbn [sv_denot]. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * change (Z.of_N 8) with 8. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Wa8).
  + apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xc8 8 (SOff 32 0) (p_c v)).
    * rewrite b6_den_atom0. exact E32.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * change (Z.of_N 8) with 8. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Wc8).
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.
Lemma b6l_seed3 : forall v (Wc : world SEGS) (rX : bvmap 5 word) memc x bb pv,
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) -> getr rX (Z_to_bv 5 10) = w64 x ->
  getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF ->
  2 ^ 46 <= pf_s1 v <= 2 ^ 47 -> pf_s1 v mod 32 = 0 -> 4096 <= x <= 2 ^ 47 - 1 -> x + 1 <= pf_s1 v ->
  0 <= bb < 256 -> 0 <= pv < 2 ^ 64 -> 0 <= p_c v < 2 ^ 64 ->
  rdW Wc memc x = Some bb ->
  rdword (rdW Wc memc) (pf_s1 v + 0xa8) = Some 0x213a0 ->
  rdword (rdW Wc memc) (pf_s1 v + 0xc0) = Some pv ->
  rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v) ->
  (forall q, 0xc0 <= q < 0xc8 -> apresent (w_H Wc) memc (pf_s1 v + q)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 bb; w64 pv; w64 (p_c v)])) b6l_ss3
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B6L_P5)) memc (seg_rom SEGS))).
Proof.
intros v Wc rX memc x bb pv R9 R10 R20 S0 S5 Hx Hxs Hb Hp HC HrdB Wa8 Wc0 Wc8 Hpres.
set (E := Eimg (Ereg rX [w64 bb; w64 pv; w64 (p_c v)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = x)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 bb)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 pv)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 (p_c v))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (U32 : bv_unsigned (ew E 32) = bb) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b6l_ss3. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|].
    split; [intros q Hq; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xa8 8 (SLit 0x213a0) 0x213a0).
      -- cbn [sv_denot]. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- change (Z.of_N 8) with 8. lia.
      -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Wa8).
    * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xc0 8 (SOff 33 0) pv).
      -- rewrite b6_den_atom0. exact E33.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- change (Z.of_N 8) with 8. lia.
      -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Wc0).
    * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xc8 8 (SOff 34 0) (p_c v)).
      -- rewrite b6_den_atom0. exact E34.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- change (Z.of_N 8) with 8. lia.
      -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Wc8).
  + rewrite U10. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    apply Forall_cons; [|apply Forall_nil].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi.
    assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H Wc) memc x bb HrdB) as (b & Hbb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32. unfold w64.
      rewrite !Z.add_0_r, (unsigned_lit_small bb), (unsigned_lit_small bb) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. rewrite Hv. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hbb.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U10. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U10, U20, U32. change (2 ^ 5) with 32.
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

(* ---------- pf_fi's register list, the cut after a step ---------- *)
Definition b6l_FI (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
(* pf_base after a step that kept every byte off b6_Wr (B6's write set) and every visible byte visible, with the
   journal it returned at the same layout and frame state *)
Lemma b6l_move : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  b6_kept v (rdW Wc memc) (rdW Wc memc') ->
  pf_rg rX' (b6l_FI v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' HB HJ' K HRG.
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR & Hly0).
destruct HFI as (_ & Hly & HSc & HP0 & HSV & HFL & HFRM & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HP0|].
  split; [exact (b6_keep_saved v pos _ _ _ HG K HSV)|].
  split; [exact (b6_keep_flag v pos _ _ HG K HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split.
  { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
    exact (b6_keep_slot v pos _ _ 0xc8 _ HG K ltac:(lia) ltac:(lia) ltac:(right; lia) HC8). }
  exact HRG. }
split; [exact (b6_keep_obj B v pos lyc Sc Wc memc mdc _ _ HG HAR K HOBJ)|].
split; [exact (b6_keep_sl v pos _ _ HG K HSL) | exact (b6_keep_fsh v pos _ _ _ HG K HFSH)].
Qed.
(* pf_st after such a step, with the cur slot's new word *)
Lemma b6l_st : forall v pos lyc Sc Wc memc mdc rd' cf cur cur' nm k,
  b6_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> b6_kept v (rdW Wc memc) rd' ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_cur_ok cf cur' ->
  rdword rd' (pf_s1 v + 0xc0) = Some (pf_cur_ptr (p_c v) cur') ->
  pf_st v pos rd' cf cur' nm k.
Proof.
intros v pos lyc Sc Wc memc mdc rd' cf cur cur' nm k HG HAR K HC (HRC & _ & HNM & HCNT & _) HOK HSL.
split; [exact (b6_keep_rconf B v pos lyc Sc Wc memc mdc _ _ cf HG HAR K HC HRC)|].
split; [exact HOK|]. split; [exact (b6_keep_nm v pos _ _ nm HG K HNM)|]. split; [exact HCNT | exact HSL].
Qed.
(* INV_LONG after a step that wrote nothing at or above s1 (a run, or strspn's window below s1) and kept the
   registers INV_LONG names *)
Lemma b6l_long_same : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc',
  INV_LONG B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_sp0 v - 12832 <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 27; 23] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  INV_LONG B n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM KV KR.
destruct HI as (HB & HMID & HST & HLEN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR & Hly).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HFI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
assert (K : b6_kept v (rdW Wc memc) (rdW Wc memc')).
{ split; [intros a Ha Hn; apply KM; [exact Ha|]; intros Hw; apply Hn; left; exact Hw | exact KV]. }
destruct (b6_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & _ & _ & HC & _).
pose proof asan_consts as (C1 & _).
split; [|split; [exact HMID|split; [|split; [exact HLEN|]]]].
- apply (b6l_move v pos lyc Sc Wc rX memc mdc rX' memc' mdc' HB HJ' K).
  unfold pf_rg, b6l_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite KR; [apply (b6_rg rX _ _ _ HRG0); b6_in | b6_in]).
- pose proof HST as (_ & HOK & _ & _ & H5).
  apply (b6l_st v pos lyc Sc Wc memc mdc _ cf cur cur nm _ G HAR K HC HST HOK).
  rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact H5|].
  intros q Hq. apply KM; lia.
- unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hrv.
  rewrite (KR (fst rv)); [exact (HRG rv Hrv)|].
  unfold PF_RL, PF_RM in Hrv. cbn [app In] in Hrv.
  repeat (destruct Hrv as [<- | Hrv]; [cbn [fst]; b6_in |]). destruct Hrv.
Qed.

(* ---------- strspn's premises at the call 0x88260 ---------- *)
(* the C string l at q, from sa_str (lib/B/Prog/pf_seg_B9_c.v b9_astr_of_sa) *)
Lemma b6l_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ astr_atR (rdW W mem) q (seg_spec.zb l) /\
  astr_len (seg_spec.zb l) = Z.of_nat (length l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  atail_vis SEGS W mem (q + astr_len (seg_spec.zb l)).
Proof.
  intros W mem q l [Hz Ht].
  destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & Hzs).
  assert (HR : astr_atR (rdW W mem) q (seg_spec.zb l)) by (split; [exact Hb | exact Hn]).
  assert (HL : astr_len (seg_spec.zb l) = Z.of_nat (length l))
    by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  split; [apply astr_atR_view; exact HR|].
  split; [exact HR|]. split; [exact HL|]. split; [exact Hzs|].
  rewrite HL. exact Ht.
Qed.
(* the string strspn reads: the rest of the text from the line's start, at at = t + o (pf_seg_B5_hd.v
   b5hd_str_pre over this lane's kit) *)
Lemma b6l_str_pre : forall v pos lyc Sc Wc rX memc mdc regsc o stk,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> (o < length (p_s v))%nat ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 2 * ESTACK ->
  0 < p_t v + Z.of_nat o /\
  astr_at SEGS Wc memc (p_t v + Z.of_nat o) (skipn o (seg_spec.zb (p_s v))) /\
  aread_ok SEGS stk Wc regsc memc (p_t v + Z.of_nat o) (astr_len (skipn o (seg_spec.zb (p_s v))) + 1) /\
  amem_range (p_t v + Z.of_nat o) (astr_len (skipn o (seg_spec.zb (p_s v))) + 8) /\
  atail_vis SEGS Wc memc (p_t v + Z.of_nat o + astr_len (skipn o (seg_spec.zb (p_s v)))) /\
  rt_rom_view SEGS B Wc memc /\
  astr_len (skipn o (seg_spec.zb (p_s v))) = Z.of_nat (length (p_s v)) - Z.of_nat o /\
  seg_spec.zs (skipn o (seg_spec.zb (p_s v))) = skipn o (p_s v).
Proof.
intros v pos lyc Sc Wc rX memc mdc regsc o stk HB Ho Hsp Hstk.
pose proof HB as (HCX & HFI & _).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR & Hly).
pose proof (b6_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NZ & HL65 & HSTR & HADDR & HHT & HHC & _).
pose proof (b6_rom B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HROM.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct HHT as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (Hp16 & Hp4096 & Hpceil & Happ & Hpres & _ & Hk).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
unfold pf_len in Hb2.
pose proof HSTR as (HSZ & HTAIL).
destruct (sa_strz_bytes SEGS (w_H Wc) memc (p_t v) (p_s v) HSZ) as (HBY & HNZ & HZS).
assert (HLS : astr_len (skipn o (seg_spec.zb (p_s v))) = Z.of_nat (length (p_s v)) - Z.of_nat o).
{ unfold astr_len, seg_spec.zb. rewrite length_skipn, length_map. lia. }
split; [lia|].
split.
{ apply astr_atR_view.
  assert (HA : astr_atR (rdW Wc memc) (p_t v) (seg_spec.zb (p_s v))) by exact (conj HBY HNZ).
  apply (astr_atR_skipn _ _ _ o HA). unfold seg_spec.zb. rewrite length_map. lia. }
split.
{ rewrite HLS.
  apply (aread_ok_of_block SEGS B LAWS stk lyc Sc Wc regsc memc mdc b m (p_t v + Z.of_nat o)
    (Z.of_nat (length (p_s v)) - Z.of_nat o + 1) HAR Hb); [lia | lia | lia | rewrite Hsp; lia]. }
split.
{ rewrite HLS. unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
split.
{ rewrite HLS.
  replace (p_t v + Z.of_nat o + (Z.of_nat (length (p_s v)) - Z.of_nat o)) with (p_t v + Z.of_nat (length (p_s v)))
    by lia.
  exact HTAIL. }
split; [exact HROM|]. split; [exact HLS|].
apply b6l_zs_skipn. exact HZS.
Qed.
(* the set strspn reads: the literal " \t\r" of PARSE_FILE_LITS (pf_seg_B9_c.v b9_lit_read) *)
Lemma b6l_lit_pre : forall v pos lyc Sc Wc rX memc mdc regsc stk s,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> In s PARSE_FILE_LITS ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 2 * ESTACK ->
  0 < seg_litA_rc s /\
  astr_at SEGS Wc memc (seg_litA_rc s) (seg_spec.zb s) /\
  aread_ok SEGS stk Wc regsc memc (seg_litA_rc s) (astr_len (seg_spec.zb s) + 1) /\
  amem_range (seg_litA_rc s) (astr_len (seg_spec.zb s) + 8) /\
  atail_vis SEGS Wc memc (seg_litA_rc s + astr_len (seg_spec.zb s)).
Proof.
intros v pos lyc Sc Wc rX memc mdc regsc stk s HB Hin Hsp Hs.
pose proof HB as (HCX & HFI & HOBJ & _).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & _ & _ & _ & HAR & _).
pose proof G as (G1 & G2 & G3 & G4 & _).
destruct HOBJ as (_ & _ & _ & _ & _ & _ & HL & _).
destruct (HL s Hin) as (Ha & Hstr & Hp & _ & Hi).
destruct (b6l_astr_of_sa Wc memc _ s Hstr) as (HA & _ & HLn & _ & HT).
pose proof (Hp lyc Sc Wc memc mdc HAR) as HP.
pose proof (proj1 (Hi (seg_litA_rc s + Z.of_nat (length s)) ltac:(lia))) as Himg.
pose proof (pa_img_range _ Himg) as Hrg.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
try unfold kImgEnd in Hrg.
assert (HES : ESTACK = 4096) by reflexivity.
rewrite HLn in *.
split; [exact Ha|]. split; [exact HA|].
split; [|split].
- destruct HP as (A0 & A1 & A2 & A3 & A4).
  split; [exact A0|]. split; [exact A1|]. split; [lia|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha'. split.
  + destruct Hstr as ((Hz & _) & _).
    pose proof (Hz (Z.to_nat (a - seg_litA_rc s)) ltac:(rewrite length_app; cbn [length]; lia)) as Hx.
    replace (seg_litA_rc s + Z.of_nat (Z.to_nat (a - seg_litA_rc s))) with a in Hx by lia. rewrite Hx. discriminate.
  + unfold ascratch_stk. rewrite Hsp. lia.
- unfold amem_range. left. rewrite C5. lia.
- exact HT.
Qed.
Lemma b6l_lits_in : In [SP; TAB; CR] PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. right; right; left; reflexivity. Qed.
Lemma b6l_aview_rng : forall H m x w, aview SEGS H m x = Some w -> 0 <= w < 256.
Proof. intros H m x w Hw. destruct (aview_byte SEGS H m x w Hw) as (_ & _ & _ & R). exact R. Qed.

Let errno_low := pal_env B TL.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* a register a run left as an atom of the seed: its value is the seed register's (the run's env may carry the
   token atoms the token executor added above A_LIM) *)
(* a register of the symbolic state, read through st_ok_pi or st_ok (the state a run to a call leaves) *)
Ltac b6l_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | ?t => fail 0 "b6l_rreg: HS is" t
 end end.
Ltac b6l_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = getr _ (Z_to_bv 5 ?k) =>
    b6l_rreg HS; rewrite b6_den_atom0; rewrite ?ew_ewset_other by lia;
    let kn := eval vm_compute in (Z.to_nat k) in
    exact (EE kn (Z_to_bv 5 k) eq_refl) end.
(* the same against the value the cut's register list R gives *)
Ltac b6l_kr HS EE rX R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    transitivity (getr rX (Z_to_bv 5 k)); [b6l_kept HS EE | apply (b6_rg rX _ k _ R); b6_in] end.

(* ======================= 0x88278 .. REF3 0x882b4 ======================= *)
(* check B#3 (0x88278-0x88284, its slow arm 0x88f78-0x88f7c, error call 0x88f80 to errpath_load1 0x89260): the
   token executor's obligation that at + lead is addressable, from pf_obj's sa_addr t (length s + 1); the byte
   at[lead] (0x88288), the mask (0x8828c-0x88294), cur masked into slot 0xc0 (0x88298-0x882a0), refuse's
   arguments (0x882a4-0x882b0); then REF3 with cur' = b6l_cur. *)
Lemma b6l_p5 : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  HA_REF3 B n ->
  INV_LONG B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  getr rX (Z_to_bv 5 10) = w64 (p_t v + Z.of_nat o + Z.of_nat (strspn_blank (skipn o (p_s v)))) ->
  (strspn_blank (skipn o (p_s v)) < length (pf_line (p_s v) o))%nat ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B6L_P5) rX memc mdc)
    (pf_postm B v (refuse cf (ln + 1) F_long [AI 511], b6l_cur (p_s v) o cur, nm) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HREF3 HI H10 Hlt.
pose proof HI as (HB & HMID & HST & HLEN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR & Hly).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & HC8 & HRG0).
destruct (b6_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & HL65 & HSTR & HADDR & HHT & HHC & _).
pose proof HMID as (Ho & Hk & HCTX).
pose proof HST as (HRC & HOK & HNM & HCNT & HW0).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & _ & ELONG & _).
pose proof HCX as (_ & _ & _ & HCR & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct HHT as (bk & mk & Hbk & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bk mk HAR Hbk) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hkk).
pose proof (req_size_pos mk ltac:(lia)) as [_ Hreq].
unfold pf_len in Hb2.
pose proof HADDR as (_ & Ht63 & _ & HRA & _).
pose proof (pf_line_len_le (p_s v) o) as HLL. rewrite length_skipn in HLL.
set (k := strspn_blank (skipn o (p_s v))) in *.
set (len := length (pf_line (p_s v) o)) in *.
assert (Hok : (o + k < length (p_s v))%nat) by lia.
(* the byte at[lead] *)
assert (HBY : rdW Wc memc (p_t v + Z.of_nat o + Z.of_nat k) = Some (nth k (skipn o (p_s v)) 0)).
{ destruct HSTR as ((HZ & _) & _).
  pose proof (HZ (o + k)%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hx.
  rewrite Nat2Z.inj_add, Z.add_assoc in Hx. rewrite Hx. f_equal.
  rewrite app_nth1 by lia. rewrite nth_skipn. reflexivity. }
set (bval := nth k (skipn o (p_s v)) 0) in *.
pose proof (b6l_aview_rng _ _ _ _ HBY) as Hbr.
set (pv := pf_cur_ptr (p_c v) cur) in *.
pose proof (b6l_rdword_rng _ _ _ (b6l_aview_rng (w_H Wc) memc) HW0) as Hpv.
(* the slots and the registers of the cut *)
assert (Wa8 : rdword (rdW Wc memc) (pf_s1 v + 0xa8) = Some 0x213a0).
{ rewrite <- ELONG. unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xa8, seg_litA_rc F_long) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
assert (Wc8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)).
{ unfold pf_sl in HC8. apply Forall_inv in HC8. exact HC8. }
unfold PF_RL, PF_RM in HRG.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b6_rg rX _ 9 _ HRG0); b6_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b6_rg rX _ 20 _ HRG0); b6_in).
(* the seed *)
pose proof (b6l_seed3 v Wc rX memc (p_t v + Z.of_nat o + Z.of_nat k) bval pv R9 H10 R20 ltac:(lia) G5
  ltac:(lia) ltac:(lia) Hbr Hpv HCR HBY Wa8 HW0 Wc8 (fun q Hq => Hpres (pf_s1 v + q) ltac:(rewrite SPF; lia)))
  as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX [w64 bval; w64 pv; w64 (p_c v)]))) by apply Eimg_env.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r ->
    ew (Eimg (Ereg rX [w64 bval; w64 pv; w64 (p_c v)])) k0 = getr rX r)
  by (intros k0 r Hk0; apply ew_Eimg_Ereg_nat; exact Hk0).
assert (E32 : ew (Eimg (Ereg rX [w64 bval; w64 pv; w64 (p_c v)])) 32 = w64 bval)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (Eimg (Ereg rX [w64 bval; w64 pv; w64 (p_c v)])) 33 = w64 pv)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew (Eimg (Ereg rX [w64 bval; w64 pv; w64 (p_c v)])) 34 = w64 (p_c v))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
revert HS HEI EE E32 E33 E34. generalize (Eimg (Ereg rX [w64 bval; w64 pv; w64 (p_c v)])) as E.
intros E HS HEI EE E32 E33 E34.
assert (E10 : ew E 10 = Z_to_bv 64 (p_t v + Z.of_nat o + Z.of_nat k))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS b6l_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B6L_P5)) with (Z_to_bv 64 (BASE + B6L_P5)).
(* 0x88278 .. 0x882b0, the check by the token executor, up to the refuse call *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_REF3.
{ cbn [ms_mem]. unfold b6l_Bx. rewrite (U_atom E 20 SHADOW_OFF E20), (U_atom E 10 _ E10) by (unfold SHADOW_OFF; lia).
  exact (range_addressable_sub _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) (p_t v + Z.of_nat o + Z.of_nat k) 1 HRA
    ltac:(lia) ltac:(lia)). }
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (pf_s1 v - pf_sp0 v));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo YP09.r_whi]; try rewrite SPF; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
b6_clear_md.
(* what the run kept and what it wrote *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0xc0 <= a < pf_s1 v + 0xc8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun a => pf_s1 v + 0xc0 <= a < pf_s1 v + 0xc8) HFr);
    [|exact Ha | exact Hn] end.
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
    rewrite ?ew_ewset_other in Hrr by lia; rewrite ?U9 in Hrr; cbv beta; lia |]).
  destruct Hin'. }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
assert (K : b6_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split; [intros a Ha Hn; apply KM; [exact Ha|]; intros Hw; apply Hn; right; exact Hw | exact KV]. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (WC0 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0xc0) = Some (pf_cur_ptr (p_c v) (b6l_cur (p_s v) o cur))).
{ rewrite b6l_cur_ptr. fold k. fold bval. fold pv.
  lazymatch type of HR0 with
  | region_ok _ ?Ex _ (YP09.mkRegion (Some 9%nat) ?lo ?hi ?wlo ?whi (YP09.mkChunk 0xc0 (CVal 8 ?e) :: ?cs)) =>
    apply (b6_word_of_region Ex (w_H Wc) (ms_mem ms) 9 (pf_s1 v) lo hi wlo whi _ 0xc0 e _ HR0);
    [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity | | destruct (bval =? 91); lia ]
  end.
  rewrite denot_lit_U. f_equal.
  apply b6l_mask_U; [rewrite ?ew_ewset_other by lia; exact E32 | lia | rewrite ?ew_ewset_other by lia; exact E33 | lia]. }
(* REF3 with cur' = b6l_cur and the F_long arguments *)
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_REF3) rg mm mdx) end.
apply (HREF3 fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf (b6l_cur (p_s v) o cur) nm o ln d F_long
  (seg_litA_rc F_long) [AI 511] 511).
split; [|split; [exact HMID|split; [|split]]].
- apply (b6l_move v pos lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HB HJ K).
  unfold pf_rg, b6l_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; b6l_kr HS EE rX HRG0.
- exact (b6l_st v pos lyc Sc Wc memc mdc _ cf cur _ nm _ G HAR K HHC HST (b6l_cur_ok cf (p_s v) o cur HOK) WC0).
- left. split; [reflexivity | split; [reflexivity | split; reflexivity]].
- unfold pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: first
    [ solve [b6l_kr HS EE rX HRG]
    | solve [b6_rreg HS; rewrite b6_den_atom0; rewrite ?ew_ewset_other by lia; exact E34]
    | solve [b6_rreg HS; rewrite b6_den_atom0; rewrite ?ew_ewset_other by lia;
             rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); apply (b6_rg rX _ 22 _ HRG); b6_in]
    | solve [b6_rreg HS; cbn [sv_denot]; rewrite ELONG; reflexivity]
    | solve [b6_rreg HS; reflexivity] ].
Qed.

(* ======================= 0x88264 (strspn's return) .. REF3 or 0x88278 ======================= *)
(* 0x88264 `bgeu a0,s7` (lead >= len): taken, 0x882a4-0x882b0 refuse's arguments, REF3 with cur kept; not taken:
   0x88268 `not a1,s11`, 0x8826c `bgeu a1,a0` (trap T06 when not taken: refuted, at + lead < 2 ^ 63), 0x88274
   `add a0,s11,a0`, then 0x88278 (b6l_p5) *)
Lemma b6l_after : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  HA_REF3 B n ->
  INV_LONG B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  getr rX (Z_to_bv 5 10) = w64 (Z.of_nat (strspn_blank (skipn o (p_s v)))) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B6L_RET) rX memc mdc)
    (pf_postm B v (refuse cf (ln + 1) F_long [AI 511], b6l_cur (p_s v) o cur, nm) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HREF3 HI H10.
pose proof HI as (HB & HMID & HST & HLEN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR & Hly).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & HC8 & HRG0).
destruct (b6_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & HL65 & HSTR & HADDR & HHT & HHC & _).
pose proof HMID as (Ho & Hk & HCTX).
pose proof HST as (HRC & HOK & HNM & HCNT & HW0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & _ & ELONG & _).
pose proof HCX as (_ & _ & _ & HCR & _ & HTR & _).
pose proof HADDR as (Ht0 & Ht63 & _).
unfold pf_len in Ht63.
pose proof (pf_line_len_le (p_s v) o) as HLL. rewrite length_skipn in HLL.
pose proof (b6l_lead_le (skipn o (p_s v)) (nulfree_skipn o (p_s v) NUL)) as HKL.
change (fst (break_nl (skipn o (p_s v)))) with (pf_line (p_s v) o) in HKL.
set (k := strspn_blank (skipn o (p_s v))) in *.
set (len := length (pf_line (p_s v) o)) in *.
assert (Wa8 : rdword (rdW Wc memc) (pf_s1 v + 0xa8) = Some 0x213a0).
{ rewrite <- ELONG. unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xa8, seg_litA_rc F_long) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
assert (Wc8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)).
{ unfold pf_sl in HC8. apply Forall_inv in HC8. exact HC8. }
unfold PF_RL, PF_RM in HRG.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b6_rg rX _ 9 _ HRG0); b6_in).
(* the seed *)
pose proof (b6l_seed2 v Wc rX memc R9 ltac:(lia) ltac:(lia) HCR Wa8 Wc8) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX [w64 (p_c v)]))) by apply Eimg_env.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew (Eimg (Ereg rX [w64 (p_c v)])) k0 = getr rX r)
  by (intros k0 r Hk0; apply ew_Eimg_Ereg_nat; exact Hk0).
assert (E32 : ew (Eimg (Ereg rX [w64 (p_c v)])) 32 = w64 (p_c v))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI EE E32. generalize (Eimg (Ereg rX [w64 (p_c v)])) as E. intros E HS HEI EE E32.
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat k)) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat len))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); apply (b6_rg rX _ 23 _ HRG); b6_in).
assert (E27 : ew E 27 = Z_to_bv 64 (p_t v + Z.of_nat o))
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); apply (b6_rg rX _ 27 _ HRG); b6_in).
unfold cfg_at. change (w64 (BASE + B6L_RET)) with (Z_to_bv 64 (BASE + B6L_RET)).
psrr_branch_pi RUNP BR HS.
- (* lead >= len: cur kept; 0x882a4 .. 0x882b0, refuse's arguments *)
  rewrite branch_geu_U, (U_atom E 10 _ E10), (U_atom E 23 _ E23) in Hc by lia.
  apply Bool.negb_true_iff, Z.ltb_ge in Hc.
  rewrite (b6l_cur_ge (p_s v) o cur NUL ltac:(lia)).
  paj_run_to_sh RUNTOP HS HJ PF_REF3.
  { b6l_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b6_clear_md.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (K : b6_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_REF3) rg mm mdx) end.
  apply (HREF3 fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf cur nm o ln d F_long
    (seg_litA_rc F_long) [AI 511] 511).
  split; [|split; [exact HMID|split; [|split]]].
  + apply (b6l_move v pos lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HB HJ K).
    unfold pf_rg, b6l_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; b6l_kr HS EE rX HRG0.
  + apply (b6l_st v pos lyc Sc Wc memc mdc _ cf cur cur nm _ G HAR K HHC HST HOK).
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [exact HW0|]. intros q Hq. apply KM; lia.
  + left. split; [reflexivity | split; [reflexivity | split; reflexivity]].
  + unfold pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first
      [ solve [b6l_kr HS EE rX HRG]
      | solve [b6_rreg HS; rewrite b6_den_atom0; exact E32]
      | solve [b6_rreg HS; rewrite b6_den_atom0;
               rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); apply (b6_rg rX _ 22 _ HRG); b6_in]
      | solve [b6_rreg HS; cbn [sv_denot]; rewrite ELONG; reflexivity]
      | solve [b6_rreg HS; reflexivity] ].
- (* lead < len *)
  rewrite branch_geu_U, (U_atom E 10 _ E10), (U_atom E 23 _ E23) in Hc by lia.
  apply Bool.negb_false_iff, Z.ltb_lt in Hc.
  assert (Hkl : (k < len)%nat) by lia.
  clear Hc.
  (* 0x88264 (decided), 0x88268 `not a1,s11`, up to the trap test 0x8826c *)
  paj_run_sh RUNP HS HJ.
  { b6l_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b6_clear_md.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (V1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
  clear HFr HG HF.
  psrr_branch_pi RUNP BR HS.
  + (* no wrap: 0x88274 `add a0,s11,a0`, up to 0x88278 *)
    clear Hc.
    paj_run_to_sh RUNTOP HS HJ B6L_P5.
    { b6l_awr. }
    cbn [ms_mem mkst] in HFr, HG, HF.
    b6_clear_md.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
    { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
        apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
        [|exact Ha | tauto] end.
      intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
      repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
    assert (Q10 : getr (ms_regs ms0) (Z_to_bv 5 10) = w64 (p_t v + Z.of_nat o + Z.of_nat k)).
    { b6_rreg HS. rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 27 _ E27), (U_atom E 10 _ E10) by lia.
      unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + B6L_P5) rg mm mdx) end.
    apply (b6l_p5 n v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf cur nm o ln d HREF3); [|exact Q10 | exact Hkl].
    apply (b6l_long_same n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (ms_regs ms0) (ms_mem ms0) mdv0 HI HJ).
    * intros a Ha _. rewrite (K2 a Ha). exact (K1 a Ha).
    * intros a _ Hv. exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (V1 a Hv)).
    * intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [b6l_kept HS EE |]). destruct Hr.
  + (* the trap T06: 2 ^ 64 - 1 - at < lead, refuted *)
    exfalso.
    lazymatch type of Hc with branch_taken BC_GEU (sv_denot _ ?a) (sv_denot _ ?b) = false =>
      refine (b6l_t06 E a b (p_t v + Z.of_nat o) (Z.of_nat k) _ ltac:(lia) ltac:(lia) _ _ Hc) end.
    * apply (U_not E 27 _ E27). lia.
    * lia.
    * apply (U_atom E 10 _ E10). lia.
Qed.
(* ======================= LONG 0x88258: strspn(at, " \t\r"), then 0x88264 ======================= *)
Lemma b6l_long : forall n, HA_REF3 B n -> H_LONG (fx := fx) B n.
Proof.
intros n HREF3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HMID & HST & HLEN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR & Hly).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
destruct (b6_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & _).
pose proof HMID as (Ho & _ & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESPN & _).
(* the step is r_line's long branch *)
rewrite (b6l_rline cf cur nm (ln + 1) (p_s v) o NUL HLEN).
(* slot 0xb8 holds the set's literal *)
assert (Wb8 : rdword (rdW Wc memc) (pf_s1 v + 0xb8) = Some 0x21380).
{ rewrite <- ESPN. unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xb8, seg_litA_rc [SP; TAB; CR]) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
unfold PF_RL, PF_RM in HRG.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b6_rg rX _ 9 _ HRG0); b6_in).
assert (Hal16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by exact (b6_m16 _ _ G6 G3).
(* the seed *)
pose proof (b6l_seed1 v Wc rX memc R9 ltac:(lia) ltac:(lia) Wb8) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew (Eimg (Ereg rX [])) k0 = getr rX r)
  by (intros k0 r Hk0; apply ew_Eimg_Ereg_nat; exact Hk0).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (E2 : ew E 2 = Z_to_bv 64 (pf_s1 v)) by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl); apply (b6_rg rX _ 2 _ HRG0); b6_in).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl); apply (b6_rg rX _ 3 _ HRG0); b6_in).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl); apply (b6_rg rX _ 4 _ HRG0); b6_in).
assert (E27 : ew E 27 = Z_to_bv 64 (p_t v + Z.of_nat o))
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); apply (b6_rg rX _ 27 _ HRG); b6_in).
assert (SHOK : sh_ok SEGS b6l_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_LONG)) with (Z_to_bv 64 (BASE + PF_LONG)).
(* 0x88258 mv a0,s11; 0x8825c ld a1,184(s1); 0x88260 jal the strspn trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b6l_awr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E27 in Q10.
assert (R1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + B6L_RET)) by (rewrite R1; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1'; apply ret_ok_codeptr_v; [unfold B6L_RET, AF_reac_segconf_parse_file; lia | reflexivity]).
assert (Hsp1 : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite Q2; rewrite unsigned_lit_small by lia; lia).
assert (Hsp1' : spZ (ms_regs ms) = pf_s1 v) by lia.
(* the cut at the call: the run wrote nothing and kept INV_LONG's registers *)
assert (HI1 : INV_LONG B n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf cur nm o ln d).
{ apply (b6l_long_same n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (ms_regs ms) (ms_mem ms) mdv HI HJ).
  - intros a Ha _. exact (KM1 a Ha).
  - intros a _ Hv. exact (KV1 a Hv).
  - intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [|]). all: try destruct Hr. all: b6l_kept HS EE. }
pose proof HI1 as (HB1 & _).
pose proof HB1 as (_ & _ & HOBJ1 & _).
pose proof HOBJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & HSSP1).
destruct (b6l_str_pre v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (ms_regs ms) o (2 * ESTACK) HB1 Ho Hsp1'
  ltac:(rewrite HES; lia)) as (Hx0 & HSTR1 & HRD1 & HMR1 & HTV1 & HROM1 & HLS & HZS).
destruct (b6l_lit_pre v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (ms_regs ms) (2 * ESTACK) [SP; TAB; CR] HB1
  b6l_lits_in Hsp1' ltac:(rewrite HES; lia)) as (Hy0 & HSTRy & HRDy & HMRy & HTVy).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strspn) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B6L_RET)) _ HJ Hsp1 Hal16 ltac:(lia) ltac:(rewrite HES; lia)
    ltac:(rewrite SPF, HES; lia) R1' (fun a (H : False) => False_ind _ H)).
  apply (STRSPN fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (p_t v + Z.of_nat o) (seg_litA_rc [SP; TAB; CR])
    (skipn o (seg_spec.zb (p_s v))) (seg_spec.zb [SP; TAB; CR])).
  - exact HSSP1.
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
      (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc (ms_mem ms) mdv 0 (ms_regs ms)
      (pf_s1 v - pf_sp0 v) HJ Hsp1 Hal16 ltac:(lia) ltac:(rewrite HES; lia) ltac:(rewrite SPF, HES; lia) HraT Q3 Q4).
  - rewrite Q10. reflexivity.
  - rewrite ESPN, Q11. reflexivity.
  - exact Hx0.
  - exact Hy0.
  - exact HSTR1.
  - exact HSTRy.
  - exact HRD1.
  - exact HMR1.
  - exact HRDy.
  - exact HMRy.
  - exact HTV1.
  - exact HTVy.
  - exact HROM1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B6L_RET)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B6L_RET) regs2 mem2 md2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HK2 by lia.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* the cut after the call: strspn wrote only its window below s1 *)
apply (b6l_after n v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d HREF3).
- apply (b6l_long_same n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf cur nm o ln d regs2 mem2 md2 HI1 HJ2).
  + intros a Ha Hn. apply HK2; [exact Ha | | tauto]. rewrite HES. intros Hw. apply Hn. lia.
  + intros a Ha Hv.
    destruct (Z_lt_le_dec a (pf_s1 v - 2 * ESTACK)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
    * rewrite HK2; [exact Hv | exact Ha | lia | tauto].
    * apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SPF. rewrite HES in Hlo. lia.
    * rewrite HK2; [exact Hv | exact Ha | lia | tauto].
  + intros r Hr. rewrite (HP2 r); [reflexivity|].
    cbn [In] in Hr. unfold acallee_saved. repeat (destruct Hr as [<- | Hr]; [lia |]). destruct Hr.
- (* strspn's answer: spn_len over the rest's bytes = strspn_blank of the rest *)
  apply (b6l_bvr2 _ 10%bv 10); [reflexivity|].
  rewrite Ha02. f_equal. f_equal.
  rewrite b6l_spn, HZS; [reflexivity|].
  rewrite HZS. exact (nulfree_skipn o (p_s v) NUL).
Qed.

End x.

(* the LONG half of S_B6 at every ambient FP state *)
Theorem b6_long_ok : forall (f0 : YK11.FPState) (n : nat), HA_REF3 B n -> H_LONG (fx := f0) B n.
Proof. intros f0 n H. exact (b6l_long (fx := f0) n H). Qed.
End d.
