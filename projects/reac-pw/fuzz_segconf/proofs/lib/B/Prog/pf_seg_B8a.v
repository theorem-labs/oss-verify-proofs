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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 683 of its 754 lines of code are new or changed and 4982 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B8a of
   reac_segconf_parse_file's walk, the theorem pf_seg_B8a_holds : S_B8a B of lib/B/Prog/pf_pieces.v (the image-B piece-statement lane,
   80a6c9c97a8b): SEG 0x88ca0 -> NEW 0x88e54 / FOUND 0x88eb0 / REFTL 0x887cc, the inlined seg_get search of
   reac_segconf.c:103-118 (and :106-110, :199). The B8a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8a; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; verdict: none released,
   ADAPTED from the image-A G3 walk owner's image-A segment A8a (commit 61a728170142, lib/A/Prog/pf_a8a_k.v)
   and the unit owner's UBSan piece walks (working branches, lib/U/Prog/pf_*.v), re-derived on
   image B's code).
   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 61 instructions:
     0x88ca0 .. 0x88cac  a3 = slot 0x50 + s4 = sh(&c->n); lb; bnez -> 0x8907c   inline check B#29 (load4 of c->n)
     0x88cb0 .. 0x88cb8  a2 = c->n (lw through slot 0x58); blez a2 -> NEW
     0x88cbc .. 0x88cec  slots 0x60 = sh(&c->n), 0xc0 = name, 0x68 = n, 0x70 = 356 n; s8 = 0, s7 = &seg[0].seen_gen,
                         s3 = c, s11 = 0x2c80 (slot 0x00)
     0x88cf0 (LOOP)      beqz s11 -> unimp 0x891c8                                  UBSan trap T28
     0x88cf4 .. 0x88cf8  a0 = slot 0x38 = ~c; bltu a0,s8 -> unimp 0x891c8          UBSan trap T29
     0x88cfc .. 0x88d08  strcmp(s3, slot 0xc0); beqz a0 -> FOUND
     0x88d0c .. 0x88d24  s11 -= 356, s3 += 356, s8 += 356, s7 += 356, a0 = &c->overflow, bne slot 0x70, s8 -> LOOP
     0x88d28 .. 0x88d38  s3 = 32, s7 = name, a2 = n, a3 = sh(&c->n); blt a2,s3 -> NEW
     0x88d3c .. 0x88d48  (a0 >> 3) + s4; lb; bnez -> 0x89104                         inline check B#30 (load4 of c->overflow)
     0x88d4c .. 0x88d64  c->overflow += 1 (lw / addi / sw); a2 = F_bound 0x215c0 (listing object 67); a4 = 32;
                         j REFTL
     cold: 0x8907c .. 0x8908c, 0x89104 .. 0x89110, 0x892c4 .. 0x892c8 (the two checks' slow paths and error calls)
   THE CHECKS (2): B#29 and B#30 are folded by the token executor from the seeds' shadow knowledge of c's block
   (pf_seg_B8a_s.v b8_SH: [c, c + 16616) addressable, pf_obj's sa_addr c); their 11 cold instructions are not reached.
   THE UBSAN TRAPS (2), each refuted at its branch in the loop (b8_head_part):
     T28 0x88cf0 `beqz s11`, s11 = 0x2c80 - 356 i: i < n <= 32 (sa_rconf's rconf_enc bound), so s11 >= 356.
     T29 0x88cf8 `bltu a0,s8`, a0 = ~c (slot 0x38), s8 = 356 i: c + 356 i < 2 ^ 64 (c's block below alloc_ceiling).
   THE PROOF: b8_seg_part walks SEG -> NEW (n = 0) or the loop head at i = 0; b8_head_part walks the loop head to
   strcmp's return (T28, T29, strcmp by the walk's hypothesis ASTRCMP through PaArt.aj_art_at); b8_ret_part walks
   the return to FOUND, the next pass, NEW or REFTL (on REFTL's path the c->overflow region is made writable,
   pf_seg_B8a_s.v b8_swap_ok / b8_l2w_ok); b8_loop is the loop by induction on the entries left; every exit cut is
   rebuilt by pf_seg_B8a_x.v from SEG's cut and the memory relation of pf_seg_B8a_m.v (b8_keep: the state agrees
   with SEG's off B8a's write set b8_W).
   SECTION HYPOTHESES: ASTRCMP (RtString.astrcmp_realizes at pa_sigma SS___interceptor_trampoline_strcmp, every FP
   state: pf_pieces.v's list for B8a), TL : PALib B (the listing's runtime record: errno's place for the strcmp
   step), OBJ : seg_val_objs (the listing's objects: F_bound's literal, object 67 = 0x215c0). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaSB PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B8a_k pf_seg_B8a_m
  pf_seg_B8a_x pf_seg_B8a_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** Small tools *)
Lemma pf_stk : STK_reac_segconf_parse_file = 12832.
Proof. reflexivity. Qed.
Lemma b8_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b8_U_off : forall E k x d, ew E k = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + d < 2 ^ 64 -> U E (SOff k d) = x + d.
Proof.
intros E k x d H H1 H2. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_small. lia.
Qed.
Lemma b8_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* `blez a2` (bge zero,a2) on a value below 2 ^ 63 *)
Lemma b8_bge0 : forall E k x, ew E k = w64 x -> 0 <= x < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (x <=? 0).
Proof.
intros E k x Hk Hx. cbn [branch_taken sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !b8_swrap_small by lia.
destruct (Z.ltb_spec 0 x); destruct (Z.leb_spec x 0); try reflexivity; lia.
Qed.
(* `blt a2,s3` (s3 = 32) on a value below 2 ^ 63 *)
Lemma b8_blt32 : forall E k x, ew E k = w64 x -> 0 <= x < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff k 0)) (sv_denot E (SLit 32)) = (x <? 32).
Proof.
intros E k x Hk Hx. cbn [branch_taken sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !b8_swrap_small by lia. reflexivity.
Qed.
(* a word the run left in a region, read back *)
Lemma b8_word_of_region : forall {segs : list Segment} E H m n b lo hi wlo whi cs od e x,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> U E e = x -> rdword (aview segs H m) (b + od) = Some x.
Proof.
intros segs E H m n b lo hi wlo whi cs od e x HR Hb Hin Hx.
pose proof (field_of_region_any E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin ltac:(cbn; lia)) as HV.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV. change (N.to_nat 8) with 8%nat in HV.
fold (U E e) in HV. rewrite Hx in HV. pose proof (U_range E e) as Hr. rewrite Hx in Hr. unfold M64 in Hr.
rewrite Z.mod_small in HV by lia. apply rdword_of_val_mem; [exact HV | lia].
Qed.
Lemma b8_val4_of_region : forall {segs : list Segment} E H m n b lo hi wlo whi cs od e x,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 4 e)) cs -> U E e mod 2 ^ 32 = x -> sa_val (aview segs H m) (b + od) 4 x.
Proof.
intros segs E H m n b lo hi wlo whi cs od e x HR Hb Hin Hx.
pose proof (field_of_region_any E (mrestrict H m) n b cs lo hi wlo whi od 4 e HR Hb Hin ltac:(cbn; lia)) as HV.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in HV. change (N.to_nat 4) with 4%nat in HV.
fold (U E e) in HV. rewrite Hx in HV.
intros k Hk. specialize (HV k Hk). unfold aview. rewrite HV. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
Lemma b8_ag : forall E0 E1 (k n : nat) x, env_agree k E0 E1 -> (n < k)%nat -> ew E0 n = x -> ew E1 n = x.
Proof. intros E0 E1 k n x H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma b8_rgx : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
Ltac b8_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b8_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

Lemma b8_U_reg : forall E k, U E (SOff k 0) = bv_unsigned (ew E k).
Proof.
intros E k. rewrite U_SOff, Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range _ (ew E k)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. unfold M64. lia.
Qed.
Lemma b8_w64_0 : forall w : bv 64, bv_unsigned w = 0 -> w = w64 0.
Proof. intros w H. apply bv_eq. rewrite H. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. Qed.
Lemma b8_bu : forall E k x, ew E k = w64 x -> 0 <= x < 2 ^ 64 -> bv_unsigned (ew E k) = x.
Proof. intros E k x H Hx. rewrite H. unfold w64. apply unsigned_lit_small. lia. Qed.
Lemma b8_reg_off : forall E k x d y, ew E k = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + d < 2 ^ 64 -> y = x + d ->
  sv_denot E (SOff k d) = w64 y.
Proof.
intros E k x d y H H1 H2 ->. unfold w64. apply b8_den_of_U; [|lia]. apply U_atom_off; [exact H | lia | lia].
Qed.
Lemma b8_reg_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof. intros E z Hz. unfold w64. apply b8_den_of_U; [apply U_lit; lia | lia]. Qed.
(* c->overflow + 1 as the run stores it: `lw a1,0(a0); addi a1,a1,1; sw a1,0(a0)` (0x88d4c .. 0x88d54) *)
Lemma b8_ovf_U : forall E ov, ew E 35 = w64 ov -> 0 <= ov -> ov + 1 < 2 ^ 32 ->
  U E (SAlu ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)) mod 2 ^ 32 = ov + 1.
Proof.
intros E ov H H0 H1.
rewrite U_SAlu, U_SExt, (U_atom E 35 ov H ltac:(lia)), U_lit by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small ov) by lia.
assert (Hs : bv_swrap 32 ov = ov \/ bv_swrap 32 ov = ov - 2 ^ 32).
{ unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31).
  destruct (Z_lt_le_dec ov (2 ^ 31)).
  - left. rewrite Z.mod_small by lia. lia.
  - right. replace (ov + 2 ^ 31) with ((ov - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
unfold zcanon, M64. cbn [zalu_raw].
destruct Hs as [-> | ->].
- rewrite (Z.mod_small ov) by lia. rewrite (Z.mod_small (ov + 1)) by lia. apply Z.mod_small. lia.
- replace (ov - 2 ^ 32) with ((ov - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. rewrite (Z.mod_small (ov - 2 ^ 32 + 2 ^ 64) (2 ^ 64)) by lia.
  rewrite (Z.mod_small (ov - 2 ^ 32 + 2 ^ 64 + 1) (2 ^ 64)) by lia.
  replace (ov - 2 ^ 32 + 2 ^ 64 + 1) with ((ov + 1) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Ltac b8_inr := unfold b8_FI, PF_RL, PF_RM; cbn [app In]; tauto.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* pf_pieces.v's hypothesis for B8a: the strcmp wrapper at the listing's trampoline, at every FP state *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
(* the listing's record and objects *)
Hypothesis TL : PALib B.
Hypothesis OBJ : seg_val_objs (PI := PI).

(* F_bound's literal: listing object 67 is .str (0x215c0) *)
Lemma b8_lit_bound : forall E, img_env VAL A_LIM E -> ew E 308%nat = w64 (seg_litA_rc F_bound).
Proof.
intros E HE. rewrite (img_env_atomP E 308%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 308%nat with (A_OBJ 67). rewrite (OBJ 67%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
vm_compute. reflexivity.
Qed.

Lemma b8_slx_hi : forall v cf np (rd rd' : reader), 0 <= pf_s1 v <= 2 ^ 47 ->
  (forall a, pf_s1 v <= a < pf_s1 v + 0x100 -> rd' a = rd a) ->
  pf_sl rd (pf_s1 v) (b8_SLx v cf np) -> pf_sl rd' (pf_s1 v) (b8_SLx v cf np).
Proof.
intros v cf np rd rd' Hs HK H. unfold pf_sl, b8_SLx in *.
rewrite Forall_forall in *. intros [off x] Hin. specialize (H _ Hin). cbn [fst snd] in *.
assert (Ho : 0 <= off <= 0xc0)
  by (cbn [In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia |]); destruct Hin).
rewrite (rdword_ext rd rd'); [exact H|]. intros k Hk. apply HK. lia.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Section s.
Variables (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
  (np : Z) (name : list Z).
Hypothesis HSEG : INV_SEG B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name.
Hypothesis HNEW : H_NEW (fx := fx) B n.
Hypothesis HFOUND : H_FOUND (fx := fx) B n.
Hypothesis HREFTL : H_REFTL (fx := fx) B n.
#[local] Notation Q := (pf_postm B v (pf_seg_step cf nm (ln + 1) name) o ln).
#[local] Notation NN := (Z.of_nat (length (rc_seg cf))).

(* the loop head after i entries *)
Definition b8_lp (i : nat) (rY : bvmap 5 word) (memY : word -> option byte) (mdY : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memY mdY 0 /\
  b8_keep v false (rdW Wc memc) (rdW Wc memY) /\
  (i < length (rc_seg cf))%nat /\ b8_find_inv (rc_seg cf) name i /\
  pf_sl (rdW Wc memY) (pf_s1 v) (b8_SLx v cf np) /\
  pf_rg rY (b8_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++
            [(19, p_c v + 356 * Z.of_nat i); (23, p_c v + 0x160 + 356 * Z.of_nat i); (24, 356 * Z.of_nat i);
             (27, 0x2c80 - 356 * Z.of_nat i)]).

Ltac b8_awr U9 HAE :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat first
    [ apply awr_ok_nil
    | (apply awr_ok_cons_ro; [cbn; lia|])
    | (eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (pf_s1 v - pf_sp0 v));
       [reflexivity | first [rewrite U9 | rewrite (proj1 HAE 9%nat ltac:(lia)), U9]; lia
       | cbn [YP09.r_wlo YP09.r_whi]; rewrite pf_stk; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]) ].

(* after a run: the model named, the environment agreeing with the seed's below 48, the memory relation to SEG's
   carried through the run's write windows (all inside b8_W v ov) *)
Ltac b8_after U9 K HAE :=
  b8_clear_md;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows _ _ |- _ =>
    lazymatch type of HAE with env_agree ?k ?E0 _ =>
    lazymatch type of K with b8_keep ?vv ?ov ?r0 _ =>
    let HAEn := fresh "HAEn" in let Kn := fresh "Kn" in let Kr := fresh "Kr" in
    assert (Kr : b8_keep vv ov (rdW Wc m0) (rdW Wc (ms_mem msn)));
    [ intros a Ha Hn; apply (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (b8_W vv ov) HFr); [ | exact Ha | exact Hn];
      let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
      let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
      intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr;
         rewrite ?(proj1 HAE 9%nat ltac:(lia)), ?(proj1 HAE 32%nat ltac:(lia)) in Hrr; rewrite ?U9 in Hrr;
         unfold b8_W; first [lia | (right; right; right; split; [reflexivity | unfold seg_spec.RC_OVERFLOW; lia])] |]);
      destruct Hin
    | ];
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    pose proof (b8_keep_trans vv ov _ _ _ K Kr) as Kn;
    clear HFr HG HAE K Kr; rename HAEn into HAE; rename Kn into K;
    try (match m0 with ms_mem ?mo => repeat (match goal with H : context [mo] |- _ => clear H end); clear mo end);
    try (lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms end)
    end end
  end.

Lemma b8_seg_part :
  (forall rY memY mdY, b8_lp 0 rY memY mdY ->
     SRr SEGS Wc (mkCfg (mkst rY (Z_to_bv 64 (BASE + PF_LOOP)) memY (seg_rom SEGS)) mdY) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_SEG) rX memc mdc) Q.
Proof using HSEG HNEW.
intros LOOPK.
pose proof HSEG as (HB & HM & (HRC & HNM & HCNT) & HSTR & HI & HL & HR).
destruct (b8_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof HB as (_ & HFI & _ & _ & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof (b8_rconf_n _ _ _ HRC) as (VN & L32).
destruct (b8_c_blk B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (bc & mc & Hbc & Hc1 & Hc2 & Hc4 & Hc3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). rewrite pf_stk in G1.
destruct HI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
unfold seg_spec.SEG_C_SIZE in *.
destruct (b8_seed_seg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE cf HB HRC) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (b8_Eseg rX v cf)) by (unfold b8_Eseg; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (b8_Eseg rX v cf) k = getr rX r)
  by (intros k r Hk; unfold b8_Eseg; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall k, (k < A_TEXT)%nat -> ew (b8_Eseg rX v cf) k =
  ew (Ereg rX [w64 (p_c v); w64 (pf_nt (p_c v)); w64 NN; w64 (rc_overflow cf)]) k)
  by (intros k Hk; unfold b8_Eseg; apply Eimg_low; exact Hk).
assert (E32 : ew (b8_Eseg rX v cf) 32 = w64 (p_c v)) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E34 : ew (b8_Eseg rX v cf) 34 = w64 NN) by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
clear EX.
remember (b8_Eseg rX v cf) as E eqn:HE. clear HE.
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (b8_rgx rX _ 9 _ HRG0 ltac:(cbn; tauto)); unfold w64; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = w64 SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact (b8_rgx rX _ 20 _ HRG0 ltac:(cbn; tauto))).
assert (E23 : ew E 23 = w64 np)
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); apply (b8_rgx rX _ 23 _ HR); unfold PF_RL, PF_RM; cbn; tauto).
pose proof (env_agree_refl 48 E) as HAE.
pose proof (b8_keep_refl v false (rdW Wc memc)) as K.
unfold cfg_at. change (w64 (BASE + PF_SEG)) with (Z_to_bv 64 (BASE + PF_SEG)).
(* 0x88ca0 .. 0x88cb4: check B#29 folded, a2 = c->n; stops at `blez a2` 0x88cb8 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b8_awr U9 HAE. }
b8_after U9 K HAE.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <= 0: to NEW *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?En _) _ = _ =>
    assert (E34n : ew En 34 = w64 NN) by exact (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34) end.
  rewrite (b8_bge0 _ 34 NN E34n ltac:(lia)) in Hc. apply Z.leb_le in Hc. clear E34n.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_NEW.
  { b8_awr U9 HAE. }
  b8_after U9 K HAE.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (HAEw : forall k, (k < 48)%nat -> ew En k = ew E k) by exact (proj1 HAE) end.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19; 23] ->
      getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    do 13 (destruct Hr as [<- | Hr]; [b8_rreg HS; rewrite b8_den_atom0; apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity] |]). destruct Hr. }
  assert (N12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 NN) by (b8_rreg HS; rewrite b8_den_atom0; exact (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34)).
  assert (N13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (shadow_addr (p_c v + seg_spec.RC_N))).
  { b8_rreg HS. unfold w64. apply b8_den_of_U.
    - apply b8_U_sh; [exact (b8_ag _ _ 48 32 _ HAE ltac:(lia) E32) | exact (b8_ag _ _ 48 20 _ HAE ltac:(lia) E20) | lia | unfold seg_spec.RC_N; lia].
    - unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N. pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)). lia. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_NEW) rg mm mdx) end.
  pose proof HNEW as HNEW'. unfold H_NEW in HNEW'. apply (HNEW' v pos lyc Sc Wc _ _ _ cf nm o ln d np name).
  apply (b8_new_ok B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG _ _ _ HJ K).
  + unfold pf_rg, b8_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ exact N12 | exact N13
            | rewrite QK by (cbn; tauto);
              first [apply (b8_rgx rX _ _ _ HRG0); cbn; tauto | apply (b8_rgx rX _ _ _ HR); unfold PF_RL, PF_RM; cbn; tauto] ].
  + destruct (rc_seg cf); [reflexivity | cbn [length] in Hc; lia].
  + lia.
- (* n > 0: to the loop head at i = 0 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?En _) _ = _ =>
    assert (E34n : ew En 34 = w64 NN) by exact (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34) end.
  rewrite (b8_bge0 _ 34 NN E34n ltac:(lia)) in Hc. apply Z.leb_gt in Hc. clear E34n.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_LOOP.
  { b8_awr U9 HAE. }
  b8_after U9 K HAE.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (HAEw : forall k, (k < 48)%nat -> ew En k = ew E k) by exact (proj1 HAE) end.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
      getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    do 11 (destruct Hr as [<- | Hr]; [b8_rreg HS; rewrite b8_den_atom0; apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity] |]). destruct Hr. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) b8_R0) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) b8_R0) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
  cbn [ms_mem restrict] in HR0, HR1.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (U9n : bv_unsigned (ew En 9) = pf_s1 v) by (transitivity (bv_unsigned (ew E 9)); [first [reflexivity | f_equal; exact (b8_ag _ _ 48 9 _ HAE ltac:(lia) eq_refl)] | exact U9]) end.
  assert (Hsh : 0 <= shadow_addr (p_c v + seg_spec.RC_N) < 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N. pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)). lia. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (mkCfg (mkst rg (Z_to_bv 64 (BASE + PF_LOOP)) mm rom) mdx) end.
  apply LOOPK.
  split; [exact HJ|]. split; [exact K|]. split; [lia|]. split; [apply b8_find_inv0|].
  split.
  { unfold pf_sl, b8_SLx. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - eapply (b8_word_of_region _ _ _ _ _ _ _ _ _ _ 0x60 _ _ HR0 U9n); [cbn [In]; repeat first [left; reflexivity | right] |].
      apply b8_U_sh; [exact (b8_ag _ _ 48 32 _ HAE ltac:(lia) E32) | exact (b8_ag _ _ 48 20 _ HAE ltac:(lia) E20) | lia | unfold seg_spec.RC_N; lia].
    - eapply (b8_word_of_region _ _ _ _ _ _ _ _ _ _ 0x68 _ _ HR0 U9n); [cbn [In]; repeat first [left; reflexivity | right] |].
      rewrite (b8_U_off _ 34 NN 0) by first [exact (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34) | lia]. lia.
    - eapply (b8_word_of_region _ _ _ _ _ _ _ _ _ _ 0x70 _ _ HR0 U9n); [cbn [In]; repeat first [left; reflexivity | right] |].
      apply b8_U_n356; [rewrite (b8_U_off _ 34 NN 0) by first [exact (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34) | lia]; lia | lia].
    - eapply (b8_word_of_region _ _ _ _ _ _ _ _ _ _ 0xc0 _ _ HR1 U9n); [cbn [In]; repeat first [left; reflexivity | right] |].
      rewrite (b8_U_off _ 23 np 0) by first [exact (b8_ag _ _ 48 23 _ HAE ltac:(lia) E23) | lia]. lia. }
  unfold pf_rg, b8_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [ rewrite QK by (cbn; tauto);
            first [apply (b8_rgx rX _ _ _ HRG0); cbn; tauto | apply (b8_rgx rX _ _ _ HR); unfold PF_RL, PF_RM; cbn; tauto]
          | b8_rreg HS; unfold w64; apply b8_den_of_U;
            [ first [ rewrite (b8_U_off _ 32 (p_c v) _) by first [exact (b8_ag _ _ 48 32 _ HAE ltac:(lia) E32) | lia]; lia
                    | rewrite U_lit by lia; lia ]
            | lia ] ].
Qed.


(* the return state of strcmp (0x88d08): the loop head's facts and strcmp's answer on the i-th name *)
Definition b8_rp (i : nat) (rY : bvmap 5 word) (memY : word -> option byte) (mdY : Model) : Prop :=
  b8_lp i rY memY mdY /\
  (getr rY (Z_to_bv 5 10) = w64 0 <-> strcmp (rs_name (nth i (rc_seg cf) rseg_d)) name = 0).

(* after a run that writes nothing: the environment chain, SEG's memory relation and the slots carried *)
Ltac b8_after0 Hs1r HAE K HSX :=
  b8_clear_md;
  lazymatch goal with
  | HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)), HG : mem_grows _ _ |- _ =>
    let En := lazymatch goal with
              | HS : st_ok_pi _ _ ?En _ (restrict _ msn) |- _ => En
              | HS : st_ok _ ?En _ (restrict _ msn) |- _ => En end in
    lazymatch type of HAE with env_agree ?k ?E0 _ =>
    let HAEn := fresh "HAEn" in let KE := fresh "KE" in let Kn := fresh "Kn" in let HSXn := fresh "HSXn" in
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msn) a = rdW Wc m0 a)
      by (intros a Ha; apply (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ | exact Ha | tauto];
          let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
          let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
          intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
          destruct Hin);
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (Kn : b8_keep v false (rdW Wc memc) (rdW Wc (ms_mem msn)))
      by (intros a Ha Hn; rewrite (KE a Ha); exact (K a Ha Hn));
    pose proof (b8_slx_hi v cf np _ _ Hs1r (fun a Ha => KE a ltac:(lia)) HSX) as HSXn;
    clear HFr HG HAE K HSX KE; rename HAEn into HAE; rename Kn into K; rename HSXn into HSX;
    repeat (match goal with H : frame_of _ _ _ (mrestrict _ (ms_mem msn)) |- _ => clear H end);
    try (match m0 with ms_mem ?mo => repeat (match goal with H : context [mo] |- _ => clear H end); clear mo end);
    try (rename msn into ms)
    end
  end.

(* the eleven registers every run of the loop leaves as its own atoms *)
Ltac b8_QK HS HAE EE rY QK :=
  let m := lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => m | st_ok _ _ _ (restrict _ ?m) => m end in
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
      getr (ms_regs m) (Z_to_bv 5 r) = getr rY (Z_to_bv 5 r));
  [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
    do 11 (destruct Hr as [<- | Hr]; [b8_rreg HS; rewrite b8_den_atom0; apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity] |]);
    destruct Hr
  | ].

(* the loop head (0x88cf0) to strcmp's return (0x88d08): T28, T29, the call *)
Lemma b8_head_part : forall i rY memY mdY, b8_lp i rY memY mdY ->
  (forall r2 m2 md2, b8_rp i r2 m2 md2 ->
     SRr SEGS Wc (mkCfg (mkst r2 (Z_to_bv 64 (BASE + PF_RET)) m2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst rY (Z_to_bv 64 (BASE + PF_LOOP)) memY (seg_rom SEGS)) mdY) Q.
Proof.
intros i rY memY mdY HLP RETK.
pose proof HLP as (HJ & K & Hi & HFV & HSX & HRY).
pose proof HSEG as (HB & HM & (HRC & HNM & HCNT) & HSTR & HI & HL & HR).
destruct (b8_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof (b8_rconf_n _ _ _ HRC) as (VN & L32).
destruct (b8_c_blk B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (bc & mc & Hbc & Hc1 & Hc2 & Hc4 & Hc3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). rewrite pf_stk in G1.
pose proof HI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
unfold seg_spec.SEG_C_SIZE in *.
assert (Hs1r : 0 <= pf_s1 v <= 2 ^ 47) by lia.
assert (HBY : pf_base B v pos lyc Sc Wc rY memY mdY PF_SC_LINE).
{ apply (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false rY memY mdY HB HJ K).
  apply (b8_rg_incl _ _ _ HRY). b8_incl. }
assert (HRCY : sa_rconf (rdW Wc memY) (p_c v) cf)
  by exact (b8_keep_rconf B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB K cf eq_refl HRC).
assert (Hnp : 0 <= np < 2 ^ 64) by lia.
destruct (b8_seed_loop B PF_LOOP v pos lyc Sc Wc rY memY mdY PF_SC_LINE cf np HBY HRCY ltac:(lia) HSX Hnp)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (b8_Eloop rY v cf np)) by (unfold b8_Eloop; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (b8_Eloop rY v cf np) k = getr rY r)
  by (intros k r Hk; unfold b8_Eloop; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall k, (k < A_TEXT)%nat -> ew (b8_Eloop rY v cf np) k = ew (Ereg rY [w64 (p_c v); w64 (pf_nt (p_c v));
  w64 NN; w64 (rc_overflow cf); w64 (shadow_addr (p_c v + seg_spec.RC_N)); w64 (356 * NN); w64 np]) k)
  by (intros k Hk; unfold b8_Eloop; apply Eimg_low; exact Hk).
assert (E33 : ew (b8_Eloop rY v cf np) 33 = w64 (pf_nt (p_c v)))
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 1)).
assert (E38 : ew (b8_Eloop rY v cf np) 38 = w64 np)
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 6)).
clear EX.
remember (b8_Eloop rY v cf np) as E eqn:HE. clear HE.
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (b8_rgx rY _ 9 _ HRY ltac:(b8_inr)); unfold w64;
      apply unsigned_lit_small; lia).
assert (E19 : ew E 19 = w64 (p_c v + 356 * Z.of_nat i))
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); apply (b8_rgx rY _ 19 _ HRY); b8_inr).
assert (E24 : ew E 24 = w64 (356 * Z.of_nat i))
  by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl); apply (b8_rgx rY _ 24 _ HRY); b8_inr).
assert (E27 : ew E 27 = w64 (0x2c80 - 356 * Z.of_nat i))
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); apply (b8_rgx rY _ 27 _ HRY); b8_inr).
pose proof (env_agree_refl 48 E) as HAE.
(* 0x88cf0 `beqz s11` (UBSan trap T28): s11 = 0x2c80 - 356 i >= 356 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U in Hc.
  rewrite (U_atom E 27 (0x2c80 - 356 * Z.of_nat i) E27) in Hc by lia. rewrite U_lit in Hc by lia.
  apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x88cf4 `ld a0,56(s1)` (~c); 0x88cf8 `bltu a0,s8` (UBSan trap T29): s8 = 356 i <= ~c *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b8_awr U9 HAE. }
b8_after0 Hs1r HAE K HSX.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (U_atom _ 33 (pf_nt (p_c v)) (b8_ag _ _ 48 33 _ HAE ltac:(lia) E33)) in Hc by (unfold pf_nt; lia).
  rewrite (U_atom _ 24 (356 * Z.of_nat i) (b8_ag _ _ 48 24 _ HAE ltac:(lia) E24)) in Hc by lia.
  apply Z.ltb_lt in Hc. unfold pf_nt in Hc. lia. }
clear Hc.
(* 0x88cfc `mv a0,s3`; 0x88d00 `ld a1,192(s1)`; 0x88d04 `jal strcmp` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b8_awr U9 HAE. }
b8_after0 Hs1r HAE K HSX.
b8_QK HS HAE EE rY QK.
assert (Q10 : getr (ms_regs ms) 10 = w64 (p_c v + 356 * Z.of_nat i)).
{ b8_rreg HS. rewrite b8_den_atom0. exact (b8_ag _ _ 48 19 _ HAE ltac:(lia) E19). }
assert (Q11 : getr (ms_regs ms) 11 = w64 np).
{ b8_rreg HS. rewrite b8_den_atom0. exact (b8_ag _ _ 48 38 _ HAE ltac:(lia) E38). }
assert (Q19 : getr (ms_regs ms) (Z_to_bv 5 19) = getr rY (Z_to_bv 5 19)).
{ b8_rreg HS. rewrite b8_den_atom0. apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity]. }
assert (Q23 : getr (ms_regs ms) (Z_to_bv 5 23) = getr rY (Z_to_bv 5 23)).
{ b8_rreg HS. rewrite b8_den_atom0. apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity]. }
assert (Q24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr rY (Z_to_bv 5 24)).
{ b8_rreg HS. rewrite b8_den_atom0. apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity]. }
assert (Q27 : getr (ms_regs ms) (Z_to_bv 5 27) = getr rY (Z_to_bv 5 27)).
{ b8_rreg HS. rewrite b8_den_atom0. apply (b8_ag _ _ 48 _ _ HAE); [lia | apply EE; reflexivity]. }
pmkst HS.
prreg HS (1%bv : bv 5) R1.
assert (R1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_RET)) by (rewrite R1; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1'; apply ret_ok_codeptr_v; [unfold PF_RET, AF_reac_segconf_parse_file; lia | reflexivity]).
assert (RFI : pf_rg (ms_regs ms) (b8_FI B v)).
{ unfold pf_rg, b8_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    rewrite QK by (cbn; tauto); apply (b8_rgx rY _ _ _ HRY); b8_inr. }
assert (HB1 : pf_base B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ PF_SC_LINE)
  by exact (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false (ms_regs ms) (ms_mem ms) _ HB HJ K RFI).
assert (HRC1 : sa_rconf (rdW Wc (ms_mem ms)) (p_c v) cf)
  by exact (b8_keep_rconf B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false (ms_mem ms) HB K cf eq_refl HRC).
assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) np name)
  by exact (b8_keep_buf_str B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false (ms_mem ms) HB K np name HI HSTR).
assert (Hsp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. change (getr (ms_regs ms) 2) with (getr (ms_regs ms) (Z_to_bv 5 2)).
  rewrite QK by (cbn; tauto). rewrite (b8_rgx rY _ 2 _ HRY) by b8_inr. unfold w64. apply unsigned_lit_small. lia. }
assert (Hgp : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ change (getr (ms_regs ms) 3) with (getr (ms_regs ms) (Z_to_bv 5 3)).
  rewrite QK by (cbn; tauto). apply (b8_rgx rY _ 3 _ HRY). b8_inr. }
assert (Htp : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ change (getr (ms_regs ms) 4) with (getr (ms_regs ms) (Z_to_bv 5 4)).
  rewrite QK by (cbn; tauto). apply (b8_rgx rY _ 4 _ HRY). b8_inr. }
destruct (b8_strcmp_pre B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ (ms_regs ms) cf np name i HB1 HRC1 Hi HSTR1 HI
  Hsp HraT Hgp Htp) as (sx & Zx & Nx & HPRE & Hx0 & Hy0 & HSXs & HSYs & HRDX & HRDY & HTX & HTY & HROM).
assert (Hal16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)). pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)).
  replace (pf_s1 v - pf_sp0 v) with ((2 * (pf_s1 v / 32) - pf_sp0 v / 16) * 16) by lia. apply Z_mod_mult. }
assert (Hsp1 : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by (rewrite Hsp; lia).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcmp) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_RET)) _ HJ Hsp1 Hal16 ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(rewrite pf_stk; unfold ESTACK; lia) R1' (fun a (H : False) => False_ind _ H)).
  apply (ASTRCMP fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ (p_c v + 356 * Z.of_nat i) np sx (seg_spec.zb name)).
  - exact HPRE.
  - exact Q10.
  - exact Q11.
  - exact Hx0.
  - exact Hy0.
  - exact HSXs.
  - exact HSYs.
  - exact HRDX.
  - exact HRDY.
  - exact HTX.
  - exact HTY.
  - exact HROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
apply RETK.
split; [split; [exact HJ2|]|].
- split.
  { apply (b8_keep_step v false _ _ _ (fun a => pf_s1 v - 2 * ESTACK <= a < pf_s1 v) K).
    - intros a Ha Hn. apply HK2; [exact Ha | unfold ESTACK in *; lia | tauto].
    - intros a Hw. left. unfold ESTACK in Hw. lia. }
  split; [exact Hi|]. split; [exact HFV|].
  split.
  { refine (b8_slx_hi v cf np _ _ Hs1r _ HSX).
    intros a Ha. apply HK2; [lia | unfold ESTACK; lia | tauto]. }
  unfold pf_rg in HRY |- *. rewrite Forall_forall in HRY |- *. intros [r x] Hrx.
  rewrite <- (HRY _ Hrx). cbn [fst snd].
  assert (Hr : In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] \/ r = 19 \/ r = 23 \/ r = 24 \/ r = 27).
  { unfold b8_FI, PF_RL, PF_RM in Hrx. cbn [app In] in Hrx.
    repeat (destruct Hrx as [Hq | Hrx]; [injection Hq as <- _; cbn [In]; tauto |]). destruct Hrx. }
  assert (Hcs : acallee_saved r) by (unfold acallee_saved; cbn [In] in Hr; lia).
  rewrite (HP2 r Hcs).
  destruct Hr as [Hr | [-> | [-> | [-> | ->]]]]; [exact (QK r Hr) | exact Q19 | exact Q23 | exact Q24 | exact Q27].
- cbv beta in Ha02.
  destruct (sa_strz_bytes SEGS (w_H Wc) memc np name (proj1 HSTR)) as (_ & Nb & Zn).
  rewrite <- Zx. rewrite <- Zn.
  rewrite (check_segments.CsPure.bridge_strcmp sx (seg_spec.zb name) Nx Nb). exact Ha02.
Qed.


(* the return state (0x88d08) to FOUND, the next loop pass, NEW or REFTL *)
Lemma b8_ret_part : forall i rY memY mdY, b8_rp i rY memY mdY ->
  (forall r m md, b8_lp (S i) r m md ->
     SRr SEGS Wc (mkCfg (mkst r (Z_to_bv 64 (BASE + PF_LOOP)) m (seg_rom SEGS)) md) Q) ->
  SRr SEGS Wc (mkCfg (mkst rY (Z_to_bv 64 (BASE + PF_RET)) memY (seg_rom SEGS)) mdY) Q.
Proof.
intros i rY memY mdY (HLP & HA0) LOOPK.
pose proof HLP as (HJ & K & Hi & HFV & HSX & HRY).
pose proof HSEG as (HB & HM & (HRC & HNM & HCNT) & HSTR & HI & HL & HR).
destruct (b8_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof (b8_rconf_n _ _ _ HRC) as (VN & L32).
pose proof (b8_rconf_ov _ _ _ HRC) as (VO & RO).
destruct (b8_c_blk B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (bc & mc & Hbc & Hc1 & Hc2 & Hc4 & Hc3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). rewrite pf_stk in G1.
pose proof HI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
unfold seg_spec.SEG_C_SIZE in *.
assert (Hs1r : 0 <= pf_s1 v <= 2 ^ 47) by lia.
assert (Hsh : 0 <= shadow_addr (p_c v + seg_spec.RC_N) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N. pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)). lia. }
assert (HBY : pf_base B v pos lyc Sc Wc rY memY mdY PF_SC_LINE).
{ apply (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false rY memY mdY HB HJ K).
  apply (b8_rg_incl _ _ _ HRY). b8_incl. }
assert (HRCY : sa_rconf (rdW Wc memY) (p_c v) cf)
  by exact (b8_keep_rconf B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB K cf eq_refl HRC).
assert (Hnp : 0 <= np < 2 ^ 64) by lia.
destruct (b8_seed_loop B PF_RET v pos lyc Sc Wc rY memY mdY PF_SC_LINE cf np HBY HRCY ltac:(lia) HSX Hnp)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (b8_Eloop rY v cf np)) by (unfold b8_Eloop; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (b8_Eloop rY v cf np) k = getr rY r)
  by (intros k r Hk; unfold b8_Eloop; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall k, (k < A_TEXT)%nat -> ew (b8_Eloop rY v cf np) k = ew (Ereg rY [w64 (p_c v); w64 (pf_nt (p_c v));
  w64 NN; w64 (rc_overflow cf); w64 (shadow_addr (p_c v + seg_spec.RC_N)); w64 (356 * NN); w64 np]) k)
  by (intros k Hk; unfold b8_Eloop; apply Eimg_low; exact Hk).
assert (E32 : ew (b8_Eloop rY v cf np) 32 = w64 (p_c v))
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 0)).
assert (E34 : ew (b8_Eloop rY v cf np) 34 = w64 NN)
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 2)).
assert (E35 : ew (b8_Eloop rY v cf np) 35 = w64 (rc_overflow cf))
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 3)).
assert (E36 : ew (b8_Eloop rY v cf np) 36 = w64 (shadow_addr (p_c v + seg_spec.RC_N)))
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 4)).
assert (E37 : ew (b8_Eloop rY v cf np) 37 = w64 (356 * NN))
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 5)).
assert (E38 : ew (b8_Eloop rY v cf np) 38 = w64 np)
  by (rewrite EX by (unfold A_TEXT; lia); exact (ew_Ereg_extra rY _ 6)).
clear EX.
remember (b8_Eloop rY v cf np) as E eqn:HE. clear HE.
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (b8_rgx rY _ 9 _ HRY ltac:(b8_inr)); unfold w64;
      apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (apply (b8_bu E 32 (p_c v) E32); lia).
assert (E19 : ew E 19 = w64 (p_c v + 356 * Z.of_nat i))
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); apply (b8_rgx rY _ 19 _ HRY); b8_inr).
assert (E23 : ew E 23 = w64 (p_c v + 0x160 + 356 * Z.of_nat i))
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); apply (b8_rgx rY _ 23 _ HRY); b8_inr).
assert (E24 : ew E 24 = w64 (356 * Z.of_nat i))
  by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl); apply (b8_rgx rY _ 24 _ HRY); b8_inr).
assert (E27 : ew E 27 = w64 (0x2c80 - 356 * Z.of_nat i))
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); apply (b8_rgx rY _ 27 _ HRY); b8_inr).
pose proof (env_agree_refl 48 E) as HAE.
(* 0x88d08 `beqz a0` *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* strcmp = 0: FOUND 0x88eb0, entry i holds the name *)
  rewrite branch_eq_U, b8_U_reg in Hc. rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (H0 : strcmp (rs_name (nth i (rc_seg cf) rseg_d)) name = 0).
  { apply HA0. rewrite <- (EE 10%nat (Z_to_bv 5 10) eq_refl). apply b8_w64_0. exact Hc. }
  pose proof (b8_find_hit _ _ _ HFV Hi H0) as HF. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_FOUND.
  { b8_awr U9 HAE. }
  b8_after0 Hs1r HAE K HSX.
  b8_QK HS HAE EE rY QK.
  assert (Q19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (seg_spec.rseg_addr (p_c v) i)).
  { b8_rreg HS. rewrite b8_den_atom0. rewrite (b8_ag _ _ 48 19 _ HAE ltac:(lia) E19).
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. f_equal; lia. }
  assert (Q23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN)).
  { b8_rreg HS. rewrite b8_den_atom0. rewrite (b8_ag _ _ 48 23 _ HAE ltac:(lia) E23).
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN. f_equal; lia. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_FOUND) rg mm mdx) end.
  pose proof HFOUND as HFD. unfold H_FOUND in HFD. apply (HFD v pos lyc Sc Wc _ _ _ cf nm o ln d np name i).
  apply (b8_found_ok B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG _ _ _ HJ i K).
  + unfold pf_sl. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    exact (b8_sl_get _ _ _ 0xc0 np HSX ltac:(unfold b8_SLx; cbn [In]; tauto)).
  + unfold pf_rg, b8_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ exact Q19 | exact Q23 | rewrite QK by (cbn; tauto); apply (b8_rgx rY _ _ _ HRY); b8_inr ].
  + exact HF.
- (* strcmp <> 0 *)
  rewrite branch_eq_U, b8_U_reg in Hc. rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (H1 : strcmp (rs_name (nth i (rc_seg cf) rseg_d)) name <> 0).
  { intros H0. apply Hc. apply HA0 in H0. rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), H0.
    unfold w64. apply unsigned_lit_small. lia. }
  pose proof (b8_find_next _ _ _ HFV Hi H1) as HFV'. clear Hc.
  (* 0x88d0c .. 0x88d24: s11 -= 356, s3 += 356, s8 += 356, s7 += 356, a0 = &c->overflow; `bne` slot 0x70, s8 *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { b8_awr U9 HAE. }
  b8_after0 Hs1r HAE K HSX.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* taken: i + 1 < n, back to the loop head *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 37 (356 * NN) (b8_ag _ _ 48 37 _ HAE ltac:(lia) E37)) in Hc by lia.
    rewrite (U_atom_off _ 24 (356 * Z.of_nat i) 356 (b8_ag _ _ 48 24 _ HAE ltac:(lia) E24)) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Hi1 : (S i < length (rc_seg cf))%nat) by lia. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_LOOP.
    { b8_awr U9 HAE. }
    b8_after0 Hs1r HAE K HSX.
    b8_QK HS HAE EE rY QK.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
        with (mkCfg (mkst rg (Z_to_bv 64 (BASE + PF_LOOP)) mm rom) mdx) end.
    apply LOOPK.
    split; [exact HJ|]. split; [exact K|]. split; [exact Hi1|]. split; [exact HFV'|]. split; [exact HSX|].
    unfold pf_rg, b8_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ rewrite QK by (cbn; tauto); apply (b8_rgx rY _ _ _ HRY); b8_inr
            | b8_rreg HS;
              first [ apply (b8_reg_off _ 19 (p_c v + 356 * Z.of_nat i)); [exact (b8_ag _ _ 48 19 _ HAE ltac:(lia) E19) | lia | lia | lia]
                    | apply (b8_reg_off _ 23 (p_c v + 0x160 + 356 * Z.of_nat i)); [exact (b8_ag _ _ 48 23 _ HAE ltac:(lia) E23) | lia | lia | lia]
                    | apply (b8_reg_off _ 24 (356 * Z.of_nat i)); [exact (b8_ag _ _ 48 24 _ HAE ltac:(lia) E24) | lia | lia | lia]
                    | apply (b8_reg_off _ 27 (0x2c80 - 356 * Z.of_nat i)); [exact (b8_ag _ _ 48 27 _ HAE ltac:(lia) E27) | lia | lia | lia] ] ].
  + (* not taken: i + 1 = n, no entry holds the name *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 37 (356 * NN) (b8_ag _ _ 48 37 _ HAE ltac:(lia) E37)) in Hc by lia.
    rewrite (U_atom_off _ 24 (356 * Z.of_nat i) 356 (b8_ag _ _ 48 24 _ HAE ltac:(lia) E24)) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (HSn : S i = length (rc_seg cf)) by lia. clear Hc.
    assert (HNONE : r_find_go (rc_seg cf) name 0 = None) by (apply b8_find_miss; rewrite <- HSn; exact HFV').
    (* 0x88d28 .. 0x88d38: s3 = 32, s7 = name, a2 = n, a3 = sh(&c->n); `blt a2,s3` *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { b8_awr U9 HAE. }
    b8_after0 Hs1r HAE K HSX.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* n < 32: NEW *)
      rewrite (b8_blt32 _ 34 NN (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_NEW.
      { b8_awr U9 HAE. }
      b8_after0 Hs1r HAE K HSX.
      b8_QK HS HAE EE rY QK.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
        change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_NEW) rg mm mdx) end.
      pose proof HNEW as HNEW'. unfold H_NEW in HNEW'. apply (HNEW' v pos lyc Sc Wc _ _ _ cf nm o ln d np name).
      apply (b8_new_ok B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG _ _ _ HJ K).
      -- unfold pf_rg, b8_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
           first [ rewrite QK by (cbn; tauto); apply (b8_rgx rY _ _ _ HRY); b8_inr
                 | b8_rreg HS;
                   first [ rewrite b8_den_atom0; exact (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34)
                         | rewrite b8_den_atom0; exact (b8_ag _ _ 48 36 _ HAE ltac:(lia) E36)
                         | rewrite b8_den_atom0; exact (b8_ag _ _ 48 38 _ HAE ltac:(lia) E38)
                         | apply b8_reg_lit; lia ] ].
      -- exact HNONE.
      -- lia.
    * (* n = 32: the bound refusal; c->overflow + 1 (B#30 folded), a2 = F_bound, a4 = 32, `j` REFTL *)
      rewrite (b8_blt32 _ 34 NN (b8_ag _ _ 48 34 _ HAE ltac:(lia) E34) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
      assert (HN32 : (32 <= length (rc_seg cf))%nat) by lia. clear Hc.
      destruct (b8_reftl_cnt (p_s v) o cf (proj1 HM) HCNT) as (_ & _ & COV).
      b8_QK HS HAE EE rY QK.
      assert (RFI : pf_rg (ms_regs ms) (b8_FI B v)).
      { unfold pf_rg, b8_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rewrite QK by (cbn; tauto); apply (b8_rgx rY _ _ _ HRY); b8_inr. }
      assert (HB2 : pf_base B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ PF_SC_LINE)
        by exact (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false (ms_regs ms) (ms_mem ms) _ HB HJ K RFI).
      assert (HRC2 : sa_rconf (rdW Wc (ms_mem ms)) (p_c v) cf)
        by exact (b8_keep_rconf B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false (ms_mem ms) HB K cf eq_refl HRC).
      lazymatch type of HS with st_ok_pi _ _ ?En ?ssx (restrict _ ?msx) =>
        assert (HRW : region_ok SEGS En (ms_mem (restrict (w_H Wc) msx)) b8_L2w)
          by exact (b8_l2w_ok B v pos lyc Sc Wc _ _ _ PF_SC_LINE cf En HB2 HRC2
                      (b8_ag _ _ 48 32 _ HAE ltac:(lia) E32) (b8_ag _ _ 48 35 _ HAE ltac:(lia) E35));
        pose proof (b8_swap_ok En ssx (restrict (w_H Wc) msx) b8_L2w HS ltac:(vm_compute; reflexivity) HRW) as HS2;
        clear HS HRW; rename HS2 into HS end.
      pose proof (b8_keep_mono v _ _ K) as Kt. clear K. rename Kt into K.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_REFTL.
      { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
          let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
        eapply awr_ok_cons_gen with (n := 32%nat);
          [reflexivity | first [exact U32 | (rewrite (b8_ag _ _ 48 32 _ HAE ltac:(lia) eq_refl); exact U32)] | | apply awr_ok_nil].
        intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
        - exists (p_c v + seg_spec.RC_REFUSAL, p_c v + seg_spec.RC_OVERFLOW + 4). split; [right; left; reflexivity|].
          cbn [fst snd]. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW. lia.
        - exists bc, mc. split; [exact Hbc | lia]. }
      b8_after U9 K HAE.
      b8_QK HS HAE EE rY QK.
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) b8_L2w) in
        pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
        assert (U32f : bv_unsigned (ew Ex 32) = p_c v)
          by (apply (b8_bu Ex 32 (p_c v) (b8_ag _ _ 48 32 _ HAE ltac:(lia) E32)); lia) end.
      cbn [ms_mem restrict] in HR0.
      assert (VOV : sa_val (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_OVERFLOW) 4 (rc_overflow cf + 1)).
      { unfold seg_spec.RC_OVERFLOW.
        eapply (b8_val4_of_region _ _ _ _ _ _ _ _ _ _ 0x34d0 _ _ HR0 U32f); [cbn [In]; left; reflexivity |].
        apply b8_ovf_U; [exact (b8_ag _ _ 48 35 _ HAE ltac:(lia) E35) | lia | lia]. }
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
        change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_REFTL) rg mm mdx) end.
      rewrite (b8_step_full cf nm (ln + 1) name HNONE ltac:(lia)).
      pose proof HREFTL as HRT. unfold H_REFTL in HRT.
      apply (HRT v pos lyc Sc Wc _ _ _ (b8_ovf cf) nm o ln d F_bound (seg_litA_rc F_bound) 32 np name).
      apply (b8_reftl_ok B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG _ _ _ HJ K VOV).
      unfold pf_rg, b8_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [ rewrite QK by (cbn; tauto); apply (b8_rgx rY _ _ _ HRY); b8_inr
              | b8_rreg HS;
                first [ rewrite b8_den_atom0; exact (b8_ag _ _ 48 38 _ HAE ltac:(lia) E38)
                      | apply b8_reg_lit; lia
                      | rewrite b8_den_atom0;
                        lazymatch goal with |- ew ?Ex _ = _ =>
                          lazymatch goal with HEIx : img_env _ _ Ex |- _ => exact (b8_lit_bound Ex HEIx) end end ] ].
Qed.


(* the loop, by induction on the entries left *)
Lemma b8_loop : forall k i rY memY mdY, (length (rc_seg cf) - i = k)%nat -> b8_lp i rY memY mdY ->
  SRr SEGS Wc (mkCfg (mkst rY (Z_to_bv 64 (BASE + PF_LOOP)) memY (seg_rom SEGS)) mdY) Q.
Proof.
induction k as [|k IH]; intros i rY memY mdY Hk HLP.
{ exfalso. destruct HLP as (_ & _ & Hi & _). lia. }
apply (b8_head_part i rY memY mdY HLP).
intros r2 m2 md2 HRP. apply (b8_ret_part i r2 m2 md2 HRP).
intros r m md HLP'. apply (IH (S i) r m md); [lia | exact HLP'].
Qed.

End s.
End x.

(** ** The segment *)
Theorem pf_seg_B8a_holds : S_B8a B.
Proof.
intros f0 n HAN HAF HAR v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG.
apply (b8_seg_part (fx := f0) n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG (HAN f0)).
intros rY memY mdY HLP.
exact (b8_loop (fx := f0) n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HSEG (HAN f0) (HAF f0) (HAR f0)
  (length (rc_seg cf) - 0) 0 rY memY mdY eq_refl HLP).
Qed.
End d.
