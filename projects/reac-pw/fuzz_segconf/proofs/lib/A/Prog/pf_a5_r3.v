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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 618 of its 695 lines of code are new or changed and 4976 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: segment A5 of reac_segconf_parse_file, the pieces Q3 / R3 / R4 of
   lib/A/Prog/pf_a5_d.v (segment A5's proof, 2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk; the function's rule-24 record
   is the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md).
   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s):
     Q3 0x87e14 addiw s10,s10,1; addi a1,zero,0x40; mv a0,s3 (s3 = SH + 8); 0x87e20 jal meta_fill_00
        (__asan_set_shadow_00 on buf's 64 shadow cells; return 0x87e24 = R3).
     R3 0x87e24 addi a0,zero,0x200; bltu s7,a0,0x87e7c. LEN >= 512 falls to LONG 0x87e2c. LEN < 512:
        0x87e7c sd s4,0xb0(s1); ld s4,0xb8(s1) (buf, PF_SL); mv a0,s4; mv a1,s9; mv a2,s7; 0x87e90 jal
        checked_memcpy (__asan_memcpy; return 0x87e94 = R4).
     R4 0x87e94 mv a3,zero; add s7,s4,s7; sb zero,0(s7) (no inline check); mv a1,s4; mv a0,s4; addi s4,zero,0x20;
        addi a6,zero,9; addi a7,zero,0x3b; then 0x87eb4 = L 0.
   Each piece: a fresh seed at its pc (every register its own atom), a run of the plain symbolic executor
   (PaLibF / PaCallRun, as segment A2's lib/A/Prog/pf_a2.v), the call step (pf_a2_k.v aj_set_shadow_atS,
   PaCall.v aj_intrin_atS), and the next point's INV rebuilt with pf_a5_k.v's a5_move0. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YK1g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a2_k pf_a2_g pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small facts ---------- *)
Lemma r3_m16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. rewrite Hk.
replace (k * 32) with ((2 * k) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma r3_m8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. rewrite Hk.
replace (k * 32) with ((4 * k) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma r3_addiw : forall x, 0 <= x -> x + 1 < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (x + 1).
Proof.
intros x H0 H1. rewrite YK1g.aluw_addi_lit. apply bv_eq.
rewrite (v_addiw_small (Z_to_bv 64 x) 1); rewrite ?unsigned_lit_small; lia.
Qed.
Lemma r3_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma r3_dec : forall x lo hi, (lo <= x < hi) \/ ~ (lo <= x < hi).
Proof.
intros x lo hi. destruct (Z_lt_le_dec x lo) as [H1 | H1]; [right; lia|].
destruct (Z_lt_le_dec x hi) as [H2 | H2]; [left; lia | right; lia].
Qed.
(* a5_text's 65535%nat is an abstract numeral (Nat.of_num_uint) that zify cannot read: its Z form *)
Lemma r3_le65535 : forall k : nat, (k <= 65535)%nat -> Z.of_nat k <= 65535.
Proof. intros k H. apply Nat2Z.inj_le in H. exact H. Qed.
Ltac r3_in := solve [unfold PF_RL, PF_RM, a5_FI; cbn [In app]; repeat first [left; reflexivity | right]].
Ltac r3_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac r3_atom HS EE R :=
  lazymatch type of R with pf_rg ?rx _ =>
    r3_rreg HS; rewrite pa2_crt_den_atom0;
    lazymatch goal with |- ew _ ?nn = _ =>
      let k := eval vm_compute in (Z.of_nat nn) in
      transitivity (getr rx (Z_to_bv 5 k)); [apply EE; reflexivity | apply (a5_rg_get _ _ k _ R); r3_in] end end.
Ltac r3_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* the seed at Q3: every register its own atom, no region (the run reads and writes no memory) *)
Definition r3_ssQ : sstate := mkSS (AF_reac_segconf_parse_file + 0x39c) sr_atoms [] None (mkFacts [] [] []).
(* the seed at R3: slot 0xb0 written, slot 0xb8 read (its chunk = buf, the extra atom 32), both on atom 9 = s1 *)
Definition r3_ssR : sstate := mkSS (AF_reac_segconf_parse_file + 0x3ac) sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xb0 0xc0 0xb0 0xb8 [YP09.mkChunk 0xb8 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []).
(* the seed at R4: the extra atom 32 = buf + LEN, the alias s4 + s7 = atom 32 (0x87e98), the one byte written at it *)
Definition r3_ss4 : sstate := mkSS (AF_reac_segconf_parse_file + 0x41c) sr_atoms
  [YP09.mkRegion (Some 32%nat) 0 1 0 1 []] None
  (mkFacts [] [] [(SAlu ALU_ADD (SOff 20 0) (SOff 23 0), SOff 32 0)]).
(* cur's address is a number (c's table holds at most 32 entries) *)
Lemma r3_cur_rng : forall c cf cur, (length (rc_seg cf) <= 32)%nat -> pf_cur_ok cf cur -> 0 <= c ->
  c + seg_spec.SEG_C_SIZE <= 2 ^ 63 -> 0 <= pf_cur_ptr c cur < 2 ^ 64.
Proof.
intros c cf cur Hl Hok H0 H1. unfold pf_cur_ptr. destruct cur as [i|]; [|lia].
unfold pf_cur_ok in Hok. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. unfold seg_spec.SEG_C_SIZE in H1. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma r3_aview_mod : forall H m a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma r3_vis_mod : forall H m m', (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m a <> None -> aview SEGS H m' a <> None) ->
  forall a, aview SEGS H m a <> None -> aview SEGS H m' a <> None.
Proof.
intros H m m' K a Hv. rewrite r3_aview_mod in *. apply K; [apply Z.mod_pos_bound; lia | exact Hv].
Qed.
(* the registers a run left as their own atoms keep the values they had *)
Lemma r3_rg_keep : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok SEGS E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_restrict_reg SEGS H E ss ms _ HS), Hs, pa2_crt_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma r3_rg_keep_pi : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hs, pa2_crt_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Ltac r3_atoms := repeat (apply Forall_cons; [split; [cbn [fst]; lia | cbn [fst]; vm_compute; reflexivity] |]); apply Forall_nil.
(* reading back what a run wrote into a region (segment A2's pa2_word_of_region, lib/A/Prog/pf_a2.v; trim_t.v's
   tr_wbyte for one byte) *)
Lemma r3_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.
Lemma r3_byte_of_region : forall E H m n b lo hi wlo whi cs od e,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> aview SEGS H m (b + od) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E H m n b lo hi wlo whi cs od e HR Hb Hin.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 1 e HR Hb Hin
  ltac:(cbn; lia)) as V.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. change (N.to_nat 1) with 1%nat in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.
(* buf at a reader that holds buf's 64 shadow cells 0 (scope PF_SC_LINE) and the frame's 256 cells: what the checked
   memcpy asks of its destination *)
Lemma r3_buf_addr : forall v pos (rd : reader) len, a5_G v pos -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  (forall i, 0 <= i < 256 -> rd (pf_SH v pos + i) <> None) -> 0 <= len <= 512 ->
  amem_range (a5_buf v pos) len /\ range_addressable rd SHADOW_OFF (a5_buf v pos) len /\
  (0 < len -> shadow_hull_vis rd (a5_buf v pos) len).
Proof.
intros v pos rd len G HF HP Hl.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (r3_m8 _ G8) as F8.
assert (DF : pf_F v pos = 8 * (pf_F v pos / 8)) by (pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)); lia).
assert (Eb : a5_buf v pos / 8 = pf_F v pos / 8 + 8).
{ unfold a5_buf, PF_O_BUF. replace (pf_F v pos + 64) with (pf_F v pos + 8 * 8) by lia. apply Z.div_add. lia. }
assert (Mb : a5_buf v pos mod 8 = 0) by (unfold a5_buf, PF_O_BUF; rewrite Zplus_mod, F8; reflexivity).
split; [|split].
- unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold a5_buf, PF_O_BUF, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
- apply (range_addressable_sub _ _ (a5_buf v pos) 512); [| lia | lia].
  apply zero_shadow_range; [exact Mb | reflexivity |].
  intros i Hi. change (512 / 8) with 64 in Hi. unfold shadow_of_addr. rewrite Eb.
  replace (SHADOW_OFF + (pf_F v pos / 8 + 8) + i) with (pf_SH v pos + (8 + i)) by lia.
  rewrite (HF (8 + i) ltac:(lia)), (a5_shb_in PF_SC_LINE (8 + i) ltac:(lia)). reflexivity.
- intros Hl0 s Hs. unfold shadow_addr in Hs.
  assert (Hub : (a5_buf v pos + len - 1) / 8 < pf_F v pos / 8 + 72).
  { apply Z.div_lt_upper_bound; [lia|]. unfold a5_buf, PF_O_BUF. lia. }
  pose proof (Z.div_mod (SHADOW_OFF + a5_buf v pos / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + a5_buf v pos / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.mul_div_le (SHADOW_OFF + (a5_buf v pos + len - 1) / 8) 8 ltac:(lia)) as D2.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia. apply HP. lia.
Qed.
Definition r3_slot (v : pfv) (a : Z) : Prop := pf_s1 v + 0xb0 <= a < pf_s1 v + 0xb8.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callees of the three pieces (pf_pieces.v's list for A5): meta_fill_00 = __asan_set_shadow_00 (segment A2's
   hypothesis form) and checked_memcpy = __asan_memcpy *)
Hypothesis ASH00 : forall fx0 : YK11.FPState,
  @aset_shadow_realizes fx0 rc SEGS B (pa_sigma SS___asan_set_shadow_00) 0.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (pa_sigma SS___asan_memcpy).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* a byte of a live heap object of the cut (the text, the block c) is not an A5 write *)
Lemma r3_heap_out : forall v pos Sc Wc memc mdc q len a, a5_G v pos -> AR SEGS B (p_ly v) Sc Wc memc mdc ->
  In (5, pos) (frames Sc) -> sa_heap B (p_ly v) Sc q len -> q <= a < q + len -> ~ a5_Wrx v pos true true a.
Proof.
intros v pos Sc Wc memc mdc q len a G HAR Hin (b & m & Hb & H1 & H2) Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
apply (a5_heap_out B v pos (p_ly v) Sc Wc memc mdc b m a G HAR Hin eq_refl Hb). lia.
Qed.

(* ======================= Q3 (0x87e14): lineno++, buf into scope ======================= *)
Lemma a5_q3_ok : forall n, H_R3 B n -> H_Q3 B n.
Proof.
intros n HR3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & HLS & _ & _ & _ & HC).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _ & _ & HFSH).
pose proof HLN as ((Ho1 & Hlines & Hln & Hlno) & Ho & Hk & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ES : ESTACK = 4096) by reflexivity.
assert (Hln0 : 0 <= ln) by lia.
assert (Hln31 : ln + 1 < 2 ^ 31).
{ assert (Ho2 : (o < 65535)%nat) by (eapply Nat.lt_le_trans; [exact Ho | exact HLS]).
  apply Nat2Z.inj_lt in Ho2. change (2 ^ 31) with 2147483648. change (Z.of_nat 65535) with 65535 in Ho2. lia. }
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HS : st_ok_pi SEGS VAL E r3_ssQ
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x39c))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold r3_ssQ. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + A5_Q3)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x39c))).
paj_run_shc RUNP RUNC HS HJ.
{ unfold r3_ssQ. apply awr_ok_nil. }
r3_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem r3_ssQ) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
(* the registers at the call *)
assert (QFI : pf_rg (ms_regs ms) (a5_FI B v)).
{ apply (r3_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold a5_FI; r3_atoms | exact HFI]. }
assert (Q2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (a5_rg_get _ _ 2 _ QFI); r3_in).
assert (Q3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (a5_rg_get _ _ 3 _ QFI); r3_in).
assert (Q4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (a5_rg_get _ _ 4 _ QFI); r3_in).
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + A5_R3)).
{ r3_rreg HS. rewrite (codeptr_val _ _ HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_SH v pos + 8)) by r3_atom HS EE HRG.
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 64) by (r3_rreg HS; reflexivity).
assert (R26 : getr rX (Z_to_bv 5 26) = w64 ln) by (apply (a5_rg_get _ _ 26 _ HRG); r3_in).
assert (E26 : ew E 26 = Z_to_bv 64 ln) by (rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl); exact R26).
assert (Q26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 (ln + 1)).
{ r3_rreg HS. transitivity (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 ln)) (low32 (Z_to_bv 64 1)))).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E26. reflexivity.
  - exact (r3_addiw ln Hln0 Hln31). }
assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln ++
    [(20, pf_cur_ptr (p_c v) cur); (25, p_t v + Z.of_nat o); (23, Z.of_nat (a5_len v o))])).
{ unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [exact Q26 | r3_atom HS EE HRG]. }
pmkst HS.
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (pa_sigma SS___asan_set_shadow_00) 0 (ASH00 fx) Wc
    (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc _ 0 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A5_R3)) 5 pos
    (pf_SH v pos + 8) 64 HJ).
  - left. reflexivity.
  - unfold spZ. match goal with |- context [getr (ms_regs ms) ?r] => rewrite (r3_bvr (ms_regs ms) r 2 _ eq_refl Q2) end.
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - apply pa2_m16; [apply r3_m16; exact G5 | exact G3].
  - lia.
  - rewrite ESTK, ES. lia.
  - apply (r3_bvr _ _ 3); [reflexivity | exact Q3].
  - apply (r3_bvr _ _ 4); [reflexivity | exact Q4].
  - apply (r3_bvr _ _ 1); [reflexivity | exact Q1].
  - apply ret_ok_codeptr_v; [unfold A5_R3, AF_reac_segconf_parse_file; lia | reflexivity].
  - apply (r3_bvr _ _ 10); [reflexivity | exact Q10].
  - apply (r3_bvr _ _ 11); [reflexivity | exact Q11].
  - lia.
  - change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). lia.
  - change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). change (fs_frame_bytes 5 / 8) with 256. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hval & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A5_R3)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + A5_R3) regs2 mem2 md2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HK2 by lia.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite ESTK in Hpres2.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. rewrite HK2; [exact (K1 a Ha) | exact Ha | |]; intros Hq; apply Hn; unfold a5_Wrx.
  - right; right; right. split; [reflexivity | lia].
  - left. rewrite ES in Hq. rewrite ESTK. lia. }
assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ apply r3_vis_mod. intros a Ha Hv.
  destruct (r3_dec a (pf_s1 v - ESTACK) (pf_s1 v)) as [Dw | Dw].
  { apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ES in Dw. lia. }
  destruct (r3_dec a (pf_SH v pos + 8) (pf_SH v pos + 8 + 64)) as [Ds | Ds].
  { replace a with (pf_SH v pos + 8 + (a - (pf_SH v pos + 8))) by lia. rewrite Hval by lia. discriminate. }
  rewrite (HK2 a Ha Ds Dw), (K1 a Ha). exact Hv. }
assert (HF8 : forall i, 8 <= i < 72 -> rdW Wc mem2 (pf_SH v pos + i) = Some (pf_io true)).
{ intros i Hi. replace (pf_SH v pos + i) with (pf_SH v pos + 8 + (i - 8)) by lia. rewrite Hval by lia. reflexivity. }
apply (HR3 v pos (p_ly v) Sc Wc regs2 mem2 md2 cf cur nm o ln d).
split; [|split].
- apply (a5_move0 B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_HEAD Sc Wc regs2 mem2 md2 PF_SC_LINE HB HJ2).
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact KW.
  + exact HV.
  + exact (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_FI_cs B v) QFI).
  + exact (a5_fill_fsh v pos (rdW Wc memc) (rdW Wc mem2) true PF_SC_HEAD true G KW HF8 HFSH).
- eapply (a5_keep_ln B v pos (p_ly v) Sc Wc memc mdc Wc mem2);
    first [exact G | exact HAR | exact Hin | reflexivity | exact KW | exact HV | exact HC | exact HLN].
- apply (a5_rg_pres (ms_regs ms) regs2 _ HP2); [|exact QL].
  unfold PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.

(* ======================= R3 (0x87e24): the length test, memcpy ======================= *)
Lemma a5_r3_ok : forall n, H_LONG B n -> H_R4 B n -> H_R3 B n.
Proof.
intros n HLONG HR4 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & HLS & HSTR & HADDR & HHT & HC).
pose proof (r3_le65535 _ HLS) as HLSZ.
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & (_ & _ & _ & HCA & _) & HSL & HFSH).
pose proof HLN as (_ & Ho & _ & HST).
pose proof HST as ((bsc & _ & HENC) & HCOK & _).
pose proof HENC as (_ & HSEGL & _).
pose proof HCA as (HCA0 & HCA1 & _).
pose proof HADDR as (HT0 & HT63 & HTam & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
rewrite ESTK in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ES : ESTACK = 4096) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite ESTK in Hpres.
pose proof (pf_line_len_le (p_s v) o) as HLL. rewrite pfa_len_skipn in HLL.
assert (HCUR : 0 <= pf_cur_ptr (p_c v) cur < 2 ^ 64) by exact (r3_cur_rng (p_c v) cf cur HSEGL HCOK HCA0 HCA1).
assert (HB8 : rdword (rdW Wc memc) (pf_s1 v + 0xb8) = Some (a5_buf v pos)).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xb8, pf_F v pos + PF_O_BUF) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
(* the text: its bytes, its block, the block apart from the frame *)
pose proof HSTR as ((HZS & _) & _).
pose proof HHT as (bt & mt & Hbt & Ht1 & Ht2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & _ & _ & _ & _ & _ & Hmt).
pose proof (req_size_pos mt (proj1 Hmt)) as [_ Hmtr].
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc bt mt 5 pos HAR Hbt Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
assert (TXT : forall a, p_t v <= a < p_t v + pf_len v -> ~ a5_Wrx v pos true true a)
  by (intros a Ha; exact (r3_heap_out v pos Sc Wc memc mdc _ _ a G HAR Hin HHT Ha)).
assert (TXV0 : forall j, (j < a5_len v o)%nat ->
    rdW Wc memc (p_t v + Z.of_nat o + Z.of_nat j) = Some (nth j (pf_line (p_s v) o) 0)).
{ intros j Hj. unfold a5_len in Hj.
  replace (p_t v + Z.of_nat o + Z.of_nat j) with (p_t v + Z.of_nat (o + j)) by lia.
  rewrite (HZS (o + j)%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia.
  destruct (L_line_bytes_holds (p_s v) o NZ) as (LB1 & _ & _).
  rewrite LB1. rewrite nth_firstn. destruct (Nat.ltb_spec j (length (pf_line (p_s v) o))) as [_ | Hc0]; [|lia].
  rewrite PaArt.nth_skipn_add. reflexivity. }
(* the seed *)
set (E := Eimg (Ereg rX [w64 (a5_buf v pos)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (a5_buf v pos))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get _ _ 9 _ HFI); r3_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (Z.of_nat (a5_len v o))) by (apply (a5_rg_get _ _ 23 _ HRG); r3_in).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat (a5_len v o))) by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (HS : st_ok_pi SEGS VAL E r3_ssR
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x3ac))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold r3_ssR. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split.
    + intros o0 Ho0. apply (apresent_writable SEGS). apply Hpres. lia.
    + apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xb8 8 (SOff 32 0) (a5_buf v pos)).
      * rewrite pa2_crt_den_atom0. exact E32.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold a5_buf, PF_O_BUF. lia.
      * change (Z.of_N 8) with 8. lia.
      * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HB8).
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + A5_R3)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x3ac))).
(* 0x87e24 addi a0,zero,0x200: the run stops at the length test *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr & Ha). unfold r3_ssR in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
  left. rewrite ESTK. lia. }
r3_clear_md.
rename ms into ms1, HF into HF1, HFr into HFr1, HG into HG1, mat into mat1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ r3_slot v a -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms1) (r3_slot v) HFr1);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. unfold r3_slot. lia. }
(* 0x87e28 bltu s7,a0 *)
psrr_branch_pi RUNP BR HS.
- (* LEN < 512: 0x87e7c .. the memcpy call 0x87e90 *)
  assert (HL512 : (a5_len v o < 512)%nat).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom E 23 (Z.of_nat (a5_len v o)) E23) in Hc by (unfold a5_len; lia).
    rewrite U_lit in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  paj_run_shc RUNP RUNC HS HJ.
  { intros a (r & Hr & Ha). vm_compute in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. rewrite ESTK. lia. }
  r3_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ r3_slot v a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite <- (K1 a Ha Hn).
    apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms1) (ms_mem ms) (r3_slot v) HFr); [|exact Ha | exact Hn].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. unfold r3_slot. lia. }
  assert (V2 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None).
  { intros a Hv. apply (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms) a HG).
    exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms1) a HG1 Hv). }
  pose proof HJ as (HART & _).
  (* the registers at the call *)
  assert (QFI : pf_rg (ms_regs ms) (a5_FI B v)).
  { apply (r3_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold a5_FI; r3_atoms | exact HFI]. }
  assert (Q2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (a5_rg_get _ _ 2 _ QFI); r3_in).
  assert (Q3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (a5_rg_get _ _ 3 _ QFI); r3_in).
  assert (Q4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (a5_rg_get _ _ 4 _ QFI); r3_in).
  assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + A5_R4)).
  { r3_rreg HS. rewrite (codeptr_val _ _ HEI). reflexivity. }
  assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (a5_buf v pos)) by (r3_rreg HS; rewrite pa2_crt_den_atom0; exact E32).
  assert (Q20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (a5_buf v pos)) by (r3_rreg HS; rewrite pa2_crt_den_atom0; exact E32).
  assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (p_t v + Z.of_nat o)) by r3_atom HS EE HRG.
  assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (a5_len v o))) by r3_atom HS EE HRG.
  assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln ++
      [(20, a5_buf v pos); (25, p_t v + Z.of_nat o); (23, Z.of_nat (a5_len v o))])).
  { unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      first [exact Q20 | r3_atom HS EE HRG]. }
  assert (Qsp : spZ (ms_regs ms) = pf_s1 v).
  { unfold spZ. rewrite (r3_bvr (ms_regs ms) 2%bv 2 _ eq_refl Q2). unfold w64. rewrite unsigned_lit_small by lia.
    reflexivity. }
  (* slot 0xb0 = cur (0x87e7c) *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
  cbn [ms_mem restrict] in HR0.
  assert (W0 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0xb0) = Some (pf_cur_ptr (p_c v) cur)).
  { eapply (r3_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0xb0 (SOff 20 0) _ HR0 U9).
    - cbn [In]. repeat first [left; reflexivity | right].
    - rewrite pa2_crt_den_atom0, (EE 20%nat (Z_to_bv 5 20) eq_refl). exact (a5_rg_get _ _ 20 _ HRG ltac:(r3_in)).
    - exact HCUR. }
  (* the text's bytes at the call *)
  assert (TXV : forall j, (j < a5_len v o)%nat ->
      rdW Wc (ms_mem ms) (p_t v + Z.of_nat o + Z.of_nat j) = Some (nth j (pf_line (p_s v) o) 0)).
  { intros j Hj. rewrite K2.
    - exact (TXV0 j Hj).
    - unfold a5_len in Hj. unfold pf_len in HT63. lia.
    - intros Hq. apply (TXT (p_t v + Z.of_nat o + Z.of_nat j)); [unfold pf_len, a5_len in *; lia|].
      unfold a5_Wrx. right; left. split; [reflexivity | exact Hq]. }
  (* buf at the call: its scope cells and the frame's shadow *)
  assert (HFSHT : pf_fsh (rdW Wc (ms_mem ms)) (pf_SH v pos) PF_SC_LINE).
  { apply (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc (ms_mem ms)) true PF_SC_LINE G); [|exact HFSH].
    intros a Ha Hn. apply K2; [exact Ha|]. intros Hq. apply Hn. unfold a5_Wrx. right; left. split; [reflexivity | exact Hq]. }
  assert (HPT : forall i, 0 <= i < 256 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) <> None).
  { intros i Hi. rewrite K2.
    - exact (aview_some_of_apresent SEGS _ _ _ (HSHP i Hi)).
    - lia.
    - unfold r3_slot. lia. }
  destruct (r3_buf_addr v pos (rdW Wc (ms_mem ms)) (Z.of_nat (a5_len v o)) G HFSHT HPT ltac:(lia))
    as (BA1 & BA2 & BA3).
  pmkst HS.
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (pa_sigma SS___asan_memcpy) (AMEMCPY fx) Wc (ms_regs ms)
      (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
      (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc _ 0 (a5_buf v pos) (p_t v + Z.of_nat o) (Z.of_nat (a5_len v o))
      (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A5_R4)) HJ).
    - apply (r3_bvr _ _ 10); [reflexivity | exact Q10].
    - apply (r3_bvr _ _ 11); [reflexivity | exact Q11].
    - apply (r3_bvr _ _ 12); [reflexivity | exact Q12].
    - lia.
    - unfold a5_buf, PF_O_BUF. lia.
    - unfold a5_buf, PF_O_BUF. lia.
    - rewrite Qsp. lia.
    - apply pa2_m16; [apply r3_m16; exact G5 | exact G3].
    - lia.
    - rewrite ESTK, ES. lia.
    - apply (r3_bvr _ _ 3); [reflexivity | exact Q3].
    - apply (r3_bvr _ _ 4); [reflexivity | exact Q4].
    - apply (r3_bvr _ _ 1); [reflexivity | exact Q1].
    - apply ret_ok_codeptr_v; [unfold A5_R4, AF_reac_segconf_parse_file; lia | reflexivity].
    - intros a Ha. split.
      + right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
        change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
        unfold a5_buf, PF_O_BUF in Ha. lia.
      + unfold a5_buf, PF_O_BUF in Ha. rewrite ES. lia.
    - intros a Ha Hfp _. exfalso. apply a5_rcw_in in Hfp.
      apply (r3_heap_out v pos Sc Wc memc mdc _ _ a G HAR Hin HC Hfp).
      unfold a5_Wrx. right; right; left. lia.
    - exact BA1.
    - exact BA2.
    - exact BA3.
    - cbv iota. split; [lia|]. split; [unfold pf_len, a5_len in *; lia|]. split.
      { intros a Ha. split.
        - replace a with (p_t v + Z.of_nat o + Z.of_nat (Z.to_nat (a - (p_t v + Z.of_nat o)))) by lia.
          rewrite TXV by (unfold a5_len in *; lia). discriminate.
        - rewrite Qsp, ES. intros Hq. apply (TXT a); [unfold pf_len, a5_len in *; lia|].
          unfold a5_Wrx. left. rewrite ESTK. lia. }
      split; [unfold a5_buf, PF_O_BUF, pf_len, a5_len in *; lia|].
      split; [unfold amem_range in *; unfold pf_len, a5_len in *; lia|].
      split.
      + eapply (range_addressable_of_block SEGS B LAWS (p_ly v) Sc Wc (ms_mem ms) _ bt mt);
          [exact HART | exact Hbt | lia | unfold pf_len, a5_len in *; lia].
      + intros H0. eapply (shadow_hull_vis_of_block SEGS B LAWS (p_ly v) Sc Wc (ms_mem ms) _ bt mt);
          [exact HART | exact Hbt | lia | unfold pf_len, a5_len in *; lia | exact H0]. }
  cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HCPY & HKEEP & _ & _).
  cbv beta iota in HCPY.
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A5_R4)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + A5_R4) regs2 mem2 md2).
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HKEEP by lia.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  rewrite ESTK in Hpres2.
  assert (KX : forall shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true shw a -> rdW Wc mem2 a = rdW Wc memc a).
  { intros shw a Ha Hn. rewrite HKEEP; [| exact Ha | |].
    - apply K2; [exact Ha|]. intros Hq. apply Hn. unfold a5_Wrx. right; left. split; [reflexivity | exact Hq].
    - intros Hq. apply Hn. unfold a5_Wrx. right; right; left. unfold a5_buf, PF_O_BUF in *. lia.
    - intros Hq. apply Hn. unfold a5_Wrx. left. rewrite ES in Hq. rewrite ESTK. lia. }
  assert (HV2 : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
  { apply r3_vis_mod. intros a Ha Hv.
    destruct (r3_dec a (pf_sp0 v - 12800) (pf_sp0 v)) as [Dw | Dw].
    { apply (aview_some_of_apresent SEGS). apply Hpres2. exact Dw. }
    destruct (r3_dec a (a5_buf v pos) (a5_buf v pos + Z.of_nat (a5_len v o))) as [Db | Db].
    { replace a with (a5_buf v pos + (a - a5_buf v pos)) by lia. rewrite HCPY by lia.
      replace (p_t v + Z.of_nat o + (a - a5_buf v pos))
        with (p_t v + Z.of_nat o + Z.of_nat (Z.to_nat (a - a5_buf v pos))) by lia.
      rewrite TXV by lia. discriminate. }
    rewrite HKEEP by (rewrite ?ES; lia). exact (V2 a Hv). }
  apply (HR4 v pos (p_ly v) Sc Wc regs2 mem2 md2 cf cur nm o ln d).
  split; [|split; [|split; [|split; [|split]]]].
  + apply (a5_move0 B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE HB HJ2).
    * exists (st_fs Sc). destruct Sc; reflexivity.
    * apply Permutation_refl.
    * exact (KX true).
    * exact HV2.
    * exact (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_FI_cs B v) QFI).
    * exact (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc mem2) true PF_SC_LINE G (KX false) HFSH).
  + eapply (a5_keep_ln B v pos (p_ly v) Sc Wc memc mdc Wc mem2);
      first [exact G | exact HAR | exact Hin | reflexivity | exact (KX true) | exact HV2 | exact HC | exact HLN].
  + unfold pf_sl. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    rewrite (rdword_ext (rdW Wc (ms_mem ms)) (rdW Wc mem2)); [exact W0|].
    intros k Hk. apply HKEEP; [lia | unfold a5_buf, PF_O_BUF; lia | rewrite ES; lia].
  + exact HL512.
  + intros i Hi. rewrite HCPY by (unfold a5_len in *; lia). exact (TXV i Hi).
  + apply (a5_rg_pres (ms_regs ms) regs2 _ HP2); [|exact QL].
    unfold PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
- (* LEN >= 512: LONG 0x87e2c *)
  assert (HL512 : (512 <= a5_len v o)%nat).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom E 23 (Z.of_nat (a5_len v o)) E23) in Hc by (unfold a5_len; lia).
    rewrite U_lit in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  paj_run_to_sh RUNTO HS HJ (AF_reac_segconf_parse_file + 0x3b4).
  { intros a (r & Hr & Ha). vm_compute in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. rewrite ESTK. lia. }
  r3_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ r3_slot v a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hn. rewrite <- (K1 a Ha Hn).
    apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms1) (ms_mem ms) (r3_slot v) HFr); [|exact Ha | exact Hn].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. unfold r3_slot. lia. }
  assert (V2 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None).
  { intros a Hv. apply (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms) a HG).
    exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms1) a HG1 Hv). }
  assert (KL : forall shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true shw a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros shw a Ha Hn. apply K2; [exact Ha|]. intros Hq. apply Hn. unfold a5_Wrx. right; left.
    split; [reflexivity | exact Hq]. }
  assert (QFI : pf_rg (ms_regs ms) (a5_FI B v)).
  { apply (r3_rg_keep_pi E _ ms (w_H Wc) rX _ HS EE); [unfold a5_FI; r3_atoms | exact HFI]. }
  assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln ++
      [(20, pf_cur_ptr (p_c v) cur); (25, p_t v + Z.of_nat o); (23, Z.of_nat (a5_len v o))])).
  { apply (r3_rg_keep_pi E _ ms (w_H Wc) rX _ HS EE); [unfold PF_RL, PF_RM; cbn [app]; r3_atoms | exact HRG]. }
  assert (HLN' : a5_ln n v pos (rdW Wc (ms_mem ms)) cf cur nm o ln d).
  { eapply (a5_keep_ln B v pos (p_ly v) Sc Wc memc mdc Wc (ms_mem ms));
      first [exact G | exact HAR | exact Hin | reflexivity | exact (KL true) | exact V2 | exact HC | exact HLN]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r ?p ?m _) ?md) _ =>
    change (mkCfg (mkst r p m (seg_rom SEGS)) md) with (cfg_at SEGS (BASE + PF_LONG) r m md) end.
  rewrite (a5_post_step B v cf cur nm o ln Ho).
  apply (HLONG v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) _ cf cur nm o ln (d ++ [pf_line (p_s v) o])).
  split; [|split; [|split; [|split]]].
  + apply (a5_move0 B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _ PF_SC_LINE HB HJ).
    * exists (st_fs Sc). destruct Sc; reflexivity.
    * apply Permutation_refl.
    * exact (KL true).
    * exact V2.
    * exact QFI.
    * exact (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc (ms_mem ms)) true PF_SC_LINE G (KL false) HFSH).
  + eapply a5_mid; [exact NZ | exact HLN].
  + exact (proj2 (proj2 (proj2 HLN'))).
  + exact HL512.
  + exact QL.
Qed.

(* ======================= R4 (0x87e94): buf[LEN] = 0, the loop's constants ======================= *)
Lemma a5_r4_ok : forall n, H_L B 0 n -> H_R4 B n.
Proof.
intros n HL0 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HSL0 & HL512 & HZB & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSHP).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & HLS & _ & _ & _ & HC).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _ & _ & HFSH).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HbE : pf_F v pos + 64 <= a5_buf v pos + Z.of_nat (a5_len v o) < pf_F v pos + 64 + 512)
  by (unfold a5_buf, PF_O_BUF; lia).
set (E := Eimg (Ereg rX [w64 (a5_buf v pos + Z.of_nat (a5_len v o))])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (a5_buf v pos + Z.of_nat (a5_len v o)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 (a5_buf v pos)) by (apply (a5_rg_get _ _ 20 _ HRG); r3_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (Z.of_nat (a5_len v o))) by (apply (a5_rg_get _ _ 23 _ HRG); r3_in).
assert (E20 : ew E 20 = Z_to_bv 64 (a5_buf v pos)) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat (a5_len v o))) by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (U32 : bv_unsigned (ew E 32) = a5_buf v pos + Z.of_nat (a5_len v o))
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E r3_ss4
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x41c))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold r3_ss4. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o0 Ho0. apply (apresent_writable SEGS). apply HFP. lia.
  - cbn. tauto.
  - split; [exact I | split; [exact I |]].
    cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu.
    rewrite (U_atom E 20 (a5_buf v pos) E20) by lia. rewrite (U_atom E 23 (Z.of_nat (a5_len v o)) E23) by lia.
    rewrite (U_atom E 32 (a5_buf v pos + Z.of_nat (a5_len v o)) E32) by lia.
    cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
unfold cfg_at. change (w64 (BASE + A5_R4)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x41c))).
paj_run_to_sh RUNTO HS HJ (AF_reac_segconf_parse_file + 0x43c).
{ intros a (r & Hr & Ha). unfold r3_ss4 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048. lia. }
r3_clear_md.
(* what the run kept and the byte it wrote *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> a5_buf v pos + Z.of_nat (a5_len v o) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E (ss_mem r3_ss4) (w_H Wc) memc (ms_mem ms)
    (fun a => a = a5_buf v pos + Z.of_nat (a5_len v o)) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U32 in Hrr. cbv beta. lia. }
assert (KMg : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros sl shw a Ha Hn. apply KM; [exact Ha|]. intros ->. apply Hn. unfold a5_Wrx. right; right; left.
  unfold a5_buf, PF_O_BUF in *. lia. }
assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (HW0 : rdW Wc (ms_mem ms) (a5_buf v pos + Z.of_nat (a5_len v o)) = Some 0).
{ pose proof (r3_byte_of_region E (w_H Wc) (ms_mem ms) 32 _ _ _ _ _ _ 0 (SLit 0) HR0 U32
    ltac:(cbn [In]; left; reflexivity)) as HB0.
  rewrite Z.add_0_r in HB0. rewrite HB0. reflexivity. }
(* the registers at L 0 *)
assert (QFI : pf_rg (ms_regs ms) (a5_FI B v)).
{ apply (r3_rg_keep_pi E _ ms (w_H Wc) rX _ HS EE); [unfold a5_FI; r3_atoms | exact HFI]. }
assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln ++
    [(20, 0x20); (10, a5_buf v pos + Z.of_nat 0); (11, a5_buf v pos + Z.of_nat 0); (13, - Z.of_nat 0);
     (16, 9); (17, 0x3b)])).
{ unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [ r3_atom HS EE HRG
          | replace (a5_buf v pos + Z.of_nat 0) with (a5_buf v pos) by lia; r3_atom HS EE HRG
          | r3_rreg HS; reflexivity ]. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r ?p ?m _) ?md) _ =>
  change (mkCfg (mkst r p m (seg_rom SEGS)) md) with (cfg_at SEGS (BASE + A5_L) r m md) end.
apply (HL0 v pos (p_ly v) Sc Wc (ms_regs ms) (ms_mem ms) mdv cf cur nm o ln d).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- apply (a5_move0 B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_LINE HB HJ).
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact (KMg true true).
  + exact HV.
  + exact QFI.
  + exact (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc (ms_mem ms)) true PF_SC_LINE G (KMg true false) HFSH).
- eapply (a5_keep_ln B v pos (p_ly v) Sc Wc memc mdc Wc (ms_mem ms));
    first [exact G | exact HAR | exact Hin | reflexivity | exact (KMg true true) | exact HV | exact HC | exact HLN].
- exact (a5_keep_slot v pos (rdW Wc memc) (rdW Wc (ms_mem ms)) true _ G (KMg false true) HSL0).
- exact HL512.
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (a5_len v o)) as [Hi1 | Hi1].
  + rewrite app_nth1 by exact Hi1. rewrite KM by (unfold a5_buf, PF_O_BUF in *; lia). exact (HZB i Hi1).
  + assert (i = a5_len v o) as -> by (unfold a5_len in *; lia).
    rewrite app_nth2 by (unfold a5_len; lia).
    replace (a5_len v o - length (pf_line (p_s v) o))%nat with 0%nat by (unfold a5_len; lia).
    cbn [nth]. exact HW0.
- lia.
- intros j Hj. lia.
- exact QL.
Qed.
End e.
End f.
End d.
