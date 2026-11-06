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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths, module names and numbers changed; 536 of its 623 lines of code are new or changed and 4966 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B4 of reac_segconf_parse_file's
   walk (DONE 0x89114 -> the return 0x891c4), the theorem pf_seg_B4_holds : S_B4 B of lib/B/Prog/pf_pieces.v
   (the image-B piece statements at 80a6c9c97a8b; S_B4 := forall f0, H_DONE (fx := f0) B). The B4 segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B4; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict none).
   ADAPTED from the image-A G3 walk owner's image-A lane, on a working branch (lib/A/Prog/pf_a4_k.v, whose two journal lemmas
   lib/B/Prog/pf_seg_B4_k.v carries; its walk had not landed) in the form of the image-A G3 walk owner's segment A2
   (lib/A/Prog/pf_a2.v: seeds from the cut, the plain run to a runtime call, the call by its journal lemma) and of the
   released epilogue of plugin-hostd/fuzz_command lib/A/Prog/check_round_trip.v crt_epi (origin/ossv/recipes
   501c0d516c69: the retired magic, __asan_stack_free_5, the reload of the 13 saved registers, ret), re-derived on
   image B's code. No UBSan trap site lies in this segment (the `unimp` 0x891c8 is in B4's cover only and no walk
   reaches it).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; listing offsets from BASE = seg_text 0x84dc0,
   AF_reac_segconf_parse_file = 0x3078):
     0x89114 ld a0,80(s1); 0x89118 add s4,a0,s4; 0x8911c lb a0,0(s4); 0x89120 bnez a0,0x891f8   check B#40 of c->n
     0x89124 ld a0,88(s1); 0x89128 lw s2,0(a0)                                                  s2 = c->n
     0x8912c li a0,-8; 0x89130 sb a0,4(s5); 0x89134 sb a0,5(s5)                                 cur_name out of scope
     0x89138 ld a0,136(s1); 0x8913c ld a2,152(s1); 0x89140 j 0x8915c                             a0 = a2 = F
     0x8915c lui; 0x89160 addiw a1 = 0x45e0360e; 0x89164 sd a1,0(a2)                            the retired magic
     0x89168 beqz a0,0x89178 (not taken: F >= 4096); 0x8916c li a1,1152; 0x89170 jal frame_release_5
     0x89174 j 0x89184; 0x89184 mv a0,s2; 0x89188 addi sp,s0,-352; 0x8918c .. 0x891bc the 13 reloads;
     0x891c0 addi sp,sp,352; 0x891c4 ret.
   Not reached (57 = 36 walked + 21): 0x89144 .. 0x89158 (DONE0, check B#41: t <> 0 decides 0x88104), 0x89178 ..
   0x89180 (the real-stack release arm: slot 0x88 holds F), the `unimp` 0x891c8, B#40's slow path / stub 0x891f8 ..
   0x8920c (c's shadow is 0: the token executor's shadow entry on c) and B#41's 0x89210 .. 0x89220.

   THE PROOF, three runs and one call:
     run A (pb4_sA, 0x89114 .. 0x8912c): the token executor (lib/B/Prog/SegPaLib.v paj_run_to_tok) from a seed with
       slot 0x50 = (c + 0x2c80) >> 3, slot 0x58 = c + 0x2c80, c->n's 4 bytes = n (atom 33): the shadow entry
       [c, c + 16616) on atom 32 = c (pf_obj's sa_addr c SEG_C_SIZE) decides check B#40 (`lb` of (c + 0x2c80) >> 3 +
       s4, s4 = the shadow base) and `bnez` is not taken; s2 = n.
     run B (pb4_sB, 0x8912c .. the call 0x89170): the plain executor (PaCallRun.v paj_run_shc), which writes the two
       shadow cells SH + 4, SH + 5 and F[0 .. 8), from a fresh seed (slots 0x88 / 0x98 = F, atom 32 = F with
       4096 <= F); the call by aj_stack_free_cls_atS (pf_seg_B4_k.v) on the Section hypothesis ASF5, with the
       model's laws from the AR (YG05.model_laws_ok over am_universe).
     run C (pb4_sC, 0x89174 .. ret 0x891c4): the token executor from a seed whose stack region holds the 13 saved
       registers (pf_fi's pf_saved, kept: no write meets [sp0 - 104, sp0)); RET (SegPaLib.v paj_ret_at); the post
       PF_POSTr: a0 = n = |rc_seg cf|, c's 16616 bytes kept (sa_rconf), the journal with the frame released
       (stack_free_state 5 pos), sa_noalloc.
   The one Section hypothesis is pf_pieces.v's for B4: RtStack.astack_free_cls_realizes at
   pa_sigma SS___asan_stack_free_5 (0x3ecc4), class 5, at every FP state. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtStack.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B4_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic and register helpers ---------- *)
Lemma pb4_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma pb4_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma pb4_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pb4_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma pb4_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pb4_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma pb4_sl : forall rd b L o v, pf_sl rd b L -> In (o, v) L -> rdword rd (b + o) = Some v.
Proof. intros rd b L o v H Hin. exact (proj1 (Forall_forall _ _) H (o, v) Hin). Qed.
Lemma pb4_preg : forall r1 r2 k, aregs_preserved r1 r2 -> acallee_saved k -> getr r2 (Z_to_bv 5 k) = getr r1 (Z_to_bv 5 k).
Proof. intros r1 r2 k HP Hk. exact (HP k Hk). Qed.
Ltac pb4_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac pb4_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* a register of the symbolic state, read through st_ok / st_ok_pi (pf_a2.v pa2_rreg) *)
Ltac pb4_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.

(* ---------- the seeds ---------- *)
(* run A (0x89114): s1's slots 0x50 / 0x58 (sh(&c->n) as (c + 0x2c80) >> 3, &c->n) and c->n's 4 bytes; atom 32 = c,
   atom 33 = n; s4 = the shadow base (atom 20) is the token executor's base *)
Definition pb4_ssA : sstate := mkSS (AF_reac_segconf_parse_file + 0x12dc) sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x50 0x60 0 0
     [YP09.mkChunk 0x50 (CVal 8 (SAlu ALU_SRL (SOff 32 0x2c80) (SLit 3))); YP09.mkChunk 0x58 (CVal 8 (SOff 32 0x2c80))];
   YP09.mkRegion (Some 32%nat) 0x2c80 0x2c84 0 0 [YP09.mkChunk 0x2c80 (CVal 4 (SOff 33 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 16616) 4);
            (33%nat, mkAF 0 32 0)] [] []).
Definition pb4_BxA : sv := SOff 20 0.
(* the shadow entry: c's 16616 bytes are addressable (check B#40 at c + 0x2c80) *)
Definition pb4_SHA : list shent := [mkSHE 32 0 16616].
(* run B (0x8912c): slots 0x88 / 0x98 = F (atom 32), the two cells SH + 4 / SH + 5 (s5 = atom 21) and F[0 .. 8)
   written *)
Definition pb4_ssB : sstate := mkSS (AF_reac_segconf_parse_file + 0x12f4) sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x88 0xa0 0 0
     [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 21%nat) 4 6 4 6 [];
   YP09.mkRegion (Some 32%nat) 0 8 0 8 []] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, PTR 5)] [] []).
(* run C (0x89174): the 13 saved registers at s0 - 8 .. s0 - 104 (s0 = sp0, atom 8) as atoms 32 .. 44 *)
Definition pb4_stkC : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  (map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13)).
Definition pb4_ssC : sstate := mkSS (AF_reac_segconf_parse_file + 0x133c) sr_atoms [pb4_stkC] None
  (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASF5 : forall fx0 : YK11.FPState,
  @astack_free_cls_realizes fx0 rc SEGS B (pa_sigma SS___asan_stack_free_5) 5.

(* ---------- geometry at DONE ---------- *)
Definition pb4_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= kLowShadowBeg \/ kHighMemBeg <= pf_F v pos) /\
  4096 <= pf_FL v pos < alloc_ceiling.
(* every byte the segment may write: the frame's 256 shadow cells, the frame's first word, the flag word, and the
   stack window __asan_stack_free_5 uses below s1 *)
Definition pb4_Wr (v : pfv) (pos a : Z) : Prop :=
  (pf_SH v pos <= a < pf_SH v pos + 256) \/ (pf_F v pos <= a < pf_F v pos + 8) \/ a = pf_FL v pos \/
  (pf_s1 v - ESTACK <= a < pf_s1 v).

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Lemma pb4_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pb4_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  flag_addr lyc 5 pos = pf_FL v pos /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (ESTK : STK_reac_segconf_parse_file = 12832) by (vm_compute; reflexivity). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
destruct (al_flag _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & Hfapp & Hflt).
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
assert (EL : flag_addr lyc 5 pos = pf_FL v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc. rewrite EL in Hfapp, Hflt.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
pose proof (pb4_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply pb4_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app in Happ, Hfapp.
split; [|split; [exact Hin | split; [exact EF | split; [exact EL | exact HAR]]]].
unfold pb4_geoP, pf_s1. change 0x160 with 352.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|]. lia.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : pb4_geoP v pos.
Lemma pb4_SH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ SHADOW_OFF + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= SHADOW_OFF + 2 ^ 44 - (2 ^ 20 - 256) /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.
(* the saved registers' slots [sp0 - 104, sp0) and the flag word [F + 2040, F + 2048) lie outside pb4_Wr / the
   run-B writes *)
Lemma pb4_saved_nw : forall a, pf_sp0 v - 104 <= a < pf_sp0 v -> 0 <= a < 2 ^ 64 /\ ~ pb4_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & L1). pose proof asan_consts as (C1 & _).
pose proof pb4_SH as (E1 & E2 & E3 & _).
unfold pb4_Wr, ESTACK, SHADOW_OFF in *. lia.
Qed.
End k.

(* c's block: every byte of [c, c + 16616) is an application byte below alloc_ceiling, outside the frame, outside
   the shadow band, and not the flag word: so outside pb4_Wr *)
Lemma pb4_cblk : forall v pos lyc Sc (Wc : world SEGS) memc mdc,
  pb4_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  flag_addr lyc 5 pos = pf_FL v pos -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  4096 <= p_c v /\ p_c v + 16616 <= alloc_ceiling /\
  (forall x, p_c v <= x < p_c v + 16616 ->
     ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416) /\ 0 <= x < 2 ^ 64 /\ ~ pb4_Wr v pos x).
Proof.
intros v pos lyc Sc Wc memc mdc HG HAR Hin EF EL (b & m & Hb & H1 & H2).
unfold seg_spec.SEG_C_SIZE in H2.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & Hown & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
destruct (al_flag _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & Hfo & _ & _). rewrite EL in Hfo.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & L1). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pb4_SH v pos HG) as (E1 & E2 & E3 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowShadowBeg, kHighMemBeg in F4.
split; [lia|]. split; [lia|].
intros x Hx.
split; [unfold SHADOW_OFF; lia|]. split; [lia|].
intros [Hw | [Hw | [Hw | Hw]]].
- unfold SHADOW_OFF in *. lia.
- lia.
- subst x. exact (proj2 (Hown (pf_FL v pos) ltac:(lia)) Hfo).
- unfold ESTACK in Hw. lia.
Qed.

(* ---------- c->n's bytes ---------- *)
Lemma pb4_n_bytes : forall (len : nat), (len <= 32)%nat -> forall k, (k < 4)%nat ->
  bv_unsigned (nth k (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4 (Z_to_bv 64 (Z.of_nat len))) ZB0) =
  le_byte (Z.of_nat len) 4 k.
Proof.
intros len Hl k Hk.
do 33 (destruct len as [|len]; [destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia] |]). lia.
Qed.
Lemma pb4_n_val : forall (H : word -> bool) m c cf, sa_rconf (aview SEGS H m) c cf ->
  val_mem SEGS (mrestrict H m) (c + 0x2c80) 4 (Z.of_nat (length (rc_seg cf))) /\ (length (rc_seg cf) <= 32)%nat.
Proof.
intros H m c cf (bs & Hb & Henc).
destruct Henc as (Hlen & Hn32 & _ & (Hu1 & Hu2) & _).
unfold seg_spec.SEG_C_SIZE in Hlen.
split; [|exact Hn32].
intros k Hk.
set (o := Z.to_nat 0x2c80).
assert (Eo : Z.of_nat o = 0x2c80) by (subst o; rewrite Z2Nat.id; lia).
assert (Hlen' : length bs = Z.to_nat 16616) by lia.
assert (Hi : (o + k < length bs)%nat) by (rewrite Hlen'; lia).
pose proof (Hb (o + k)%nat Hi) as Hv.
replace (c + Z.of_nat (o + k)) with (c + 0x2c80 + Z.of_nat k) in Hv by lia.
destruct (aview_byte SEGS H m (c + 0x2c80 + Z.of_nat k) _ Hv) as (b & Hmb & Hbv & _).
rewrite Hmb. f_equal.
assert (Enth : nth (o + k) bs ZB0 = nth k (seg_spec.fldz seg_spec.RC_N 4 bs) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld, seg_spec.RC_N. fold o. change (Z.to_nat 4) with 4%nat.
  rewrite nth_firstn. destruct (Nat.ltb_spec k 4) as [_|]; [|lia].
  rewrite nth_skipn; f_equal; try lia. }
rewrite Enth, Hu2 in Hbv.
rewrite <- (Z_to_bv_bv_unsigned 8 b). f_equal. rewrite <- Hbv.
exact (pb4_n_bytes (length (rc_seg cf)) Hn32 k Hk).
Qed.

(* ---------- run A: DONE (0x89114) .. 0x8912c, check B#40 and s2 = c->n ---------- *)
Definition PB4_RA (v : pfv) (pos : Z) (n : Z) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (21, pf_SH v pos); (18, n)].
Lemma pb4_sA : forall v pos lyc Sc Wc rX memc mdc cf (Q : world SEGS -> config -> Prop),
  INV_DONE B v pos lyc Sc Wc rX memc mdc cf ->
  (forall rX1 memc1 mdc1,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc1 mdc1 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc1 a = rdW Wc memc a) ->
     pf_rg rX1 (PB4_RA v pos (Z.of_nat (length (rc_seg cf)))) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x12f4)) rX1 memc1 mdc1) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_DONE) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc rX memc mdc cf Q HI Kc.
pose proof HI as (HCX & HFI & HOBJ & HRC & HSL & _ & HRG5).
destruct (pb4_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & EL & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & L1).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & _ & HRG0).
destruct HTF as (_ & Hc16 & _).
pose proof HOBJ as (_ & _ & _ & HCA & HCH & _).
destruct (pb4_cblk v pos lyc Sc Wc memc mdc HG HAR Hin EF EL HCH) as (Cb1 & Cb2 & Cb3).
destruct (pb4_n_val (w_H Wc) memc (p_c v) cf HRC) as (HNV & Hn32).
set (n := Z.of_nat (length (rc_seg cf))) in *.
assert (Hn : 0 <= n <= 32) by (subst n; lia).
pose proof asan_consts as (C1 & _).
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (pb4_rg rX _ 2 _ HRG0); pb4_in).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (pb4_rg rX _ 3 _ HRG0); pb4_in).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (pb4_rg rX _ 4 _ HRG0); pb4_in).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 v)) by (apply (pb4_rg rX _ 8 _ HRG0); pb4_in).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb4_rg rX _ 9 _ HRG0); pb4_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (pb4_rg rX _ 20 _ HRG0); pb4_in).
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (pb4_rg rX _ 21 _ HRG5); pb4_in).
assert (W50 : rdword (rdW Wc memc) (pf_s1 v + 0x50) = Some ((p_c v + seg_spec.RC_N) / 8)) by (apply (pb4_sl _ _ _ _ _ HSL); pb4_in).
assert (W58 : rdword (rdW Wc memc) (pf_s1 v + 0x58) = Some (p_c v + seg_spec.RC_N)) by (apply (pb4_sl _ _ _ _ _ HSL); pb4_in).
unfold seg_spec.RC_N in W50, W58.
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (p_c v) 16616)
  by (destruct HCA as (_ & _ & _ & H & _); exact H).
set (E := Eimg (Ereg rX [w64 (p_c v); w64 n])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (p_c v)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pb4_ssA
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x12dc))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pb4_ssA. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x50 8 (SAlu ALU_SRL (SOff 32 0x2c80) (SLit 3)) ((p_c v + 0x2c80) / 8)).
        -- rewrite denot_lit_U. f_equal. rewrite U_srl3, (U_atom_off E 32 (p_c v) 0x2c80 E32) by lia. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W50).
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x58 8 (SOff 32 0x2c80) (p_c v + 0x2c80)).
        -- exact (pb4_den_off E 32 (p_c v) 0x2c80 E32 ltac:(lia)).
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W58).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (p_c v) 0x2c80 4 (SOff 33 0) n).
      -- rewrite pb4_den_atom0. exact E33.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      -- cbn; lia.
      -- exact HNV.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U32. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U20, U32, U33. change (2 ^ 5) with 32. change (2 ^ 4) with 16.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia. }
revert HS HEI EE E32 E33 U9 U20 U32 U33. generalize E as E0. clear E. intros E0 HS HEI EE E32 E33 U9 U20 U32 U33.
assert (UB : U E0 pb4_BxA = SHADOW_OFF).
{ unfold pb4_BxA. rewrite (U_atom E0 20 SHADOW_OFF); [reflexivity | rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20 |].
  unfold SHADOW_OFF; lia. }
assert (UC : U E0 (SOff 32 0) = p_c v) by (apply U_atom; [exact E32 | lia]).
assert (SHOK : sh_ok SEGS pb4_BxA pb4_SHA E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, pb4_SHA. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 pb4_BxA 32%nat (p_c v) 16616 (p_c v) 0 16616 HRA UB UC); [lia | lia |].
  intros x Hx. change (Z.min 0 16616) with 0 in Hx. change (Z.max 0 16616) with 16616 in Hx.
  exact (proj1 (Cb3 x ltac:(lia))). }
unfold cfg_at. change (w64 (BASE + PF_DONE)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x12dc))).
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_segconf_parse_file + 0x12f4).
{ awr_ok_tac. }
pb4_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (QA : forall r val, In (r, val) [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (21, pf_SH v pos)] -> getr (ms_regs ms) (Z_to_bv 5 r) = w64 val).
{ intros r val Hr. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr];
    [injection Hr as <- <-; pb4_rreg HS; rewrite pb4_den_atom0;
     lazymatch goal with |- ew _ ?k = _ => rewrite (EE k (Z_to_bv 5 (Z.of_nat k)) eq_refl) end;
     first [exact R2 | exact R3 | exact R4 | exact R8 | exact R9 | exact R21] |]).
  destruct Hr. }
assert (Q18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 n) by (pb4_rreg HS; rewrite pb4_den_atom0; exact E33).
pmkst HS.
change (Z_to_bv 64 (BASE + 17260)) with (w64 (BASE + (AF_reac_segconf_parse_file + 0x12f4))).
apply (Kc (ms_regs ms) (ms_mem ms) _ HJ K1).
unfold pf_rg, PB4_RA. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [exact Q18 | apply QA; pb4_in].
Qed.

(* ---------- run B: 0x8912c .. the call of frame_release_5 (0x89170), the call, back at 0x89174 ---------- *)
Definition PB4_RB (v : pfv) (n : Z) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (18, n)].
Lemma pb4_sB : forall v pos lyc Sc Wc rX1 memc1 mdc1 n (Q : world SEGS -> config -> Prop),
  pb4_geoP v pos -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos -> flag_addr lyc 5 pos = pf_FL v pos ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc1 mdc1 0 ->
  rdword (rdW Wc memc1) (pf_s1 v + 0x88) = Some (pf_F v pos) ->
  rdword (rdW Wc memc1) (pf_s1 v + 0x98) = Some (pf_F v pos) ->
  rdword (rdW Wc memc1) (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  pf_rg rX1 (PB4_RA v pos n) ->
  (forall rX2 memc2 mdc2,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [] lyc (stack_free_state 5 pos Sc) Wc memc2 mdc2 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ pb4_Wr v pos a -> rdW Wc memc2 a = rdW Wc memc1 a) ->
     pf_rg rX2 (PB4_RB v n) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x133c)) rX2 memc2 mdc2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x12f4)) rX1 memc1 mdc1) Q.
Proof.
intros v pos lyc Sc Wc rX1 memc1 mdc1 n Q HG Hin EF EL HJ W88 W98 HFL HRG Kc.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & L1).
pose proof (pb4_SH v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold kLowShadowBeg, kHighMemBeg in F4.
assert (ESTK : STK_reac_segconf_parse_file = 12832) by (vm_compute; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc1 mdc1 5 pos HAR Hin) as (_ & _ & Hfb & Hsh).
rewrite EF in Hfb, Hsh. change (fs_frame_bytes 5) with 2048 in Hfb. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
assert (R : forall r val, In (r, val) (PB4_RA v pos n) -> getr rX1 (Z_to_bv 5 r) = w64 val)
  by (intros r val H; exact (pb4_rg rX1 _ r val HRG H)).
set (E := Eimg (Ereg rX1 [w64 (pf_F v pos)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX1 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (pf_F v pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX1 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (R 9 _ ltac:(unfold PB4_RA; pb4_in)); unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), (R 21 _ ltac:(unfold PB4_RA; pb4_in)); unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pb4_ssB
  (restrict (w_H Wc) (mkst rX1 (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x12f4))) memc1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pb4_ssB. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x88 8 (SOff 32 0) (pf_F v pos)).
        -- rewrite pb4_den_atom0. exact E32.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc1 _ _ W88).
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x98 8 (SOff 32 0) (pf_F v pos)).
        -- rewrite pb4_den_atom0. exact E32.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc1 _ _ W98).
    + rewrite U21. unfold SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hsh o ltac:(lia))).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hfb (pf_F v pos + o) ltac:(lia))).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U21, U32. unfold SHADOW_OFF in *.
    repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite U9, U32. change (2 ^ 5) with 32. repeat split; lia. }
revert HS HEI EE E32 U9 U21 U32. generalize E as E0. clear E. intros E0 HS HEI EE E32 U9 U21 U32.
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x12f4)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x12f4))).
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold pb4_ssB in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    rewrite U21 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5) with 2048. rewrite U32 in Ha. lia. }
pb4_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (pf_SH v pos + 4 <= a < pf_SH v pos + 6 \/ pf_F v pos <= a < pf_F v pos + 8) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc1 a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc1 (ms_mem ms)
    (fun a => pf_SH v pos + 4 <= a < pf_SH v pos + 6 \/ pf_F v pos <= a < pf_F v pos + 8) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin'];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U21, ?U32 in Hrr; lia |]).
  destruct Hin'. }
(* the registers at the call *)
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + 17332)) by (pb4_rreg HS; apply (codeptr_val _ 17332 HEI)).
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos)) by (pb4_rreg HS; rewrite pb4_den_atom0; exact E32).
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 1152) by (pb4_rreg HS; reflexivity).
assert (QA : forall r val, In (r, val) (PB4_RA v pos n) -> getr (ms_regs ms) (Z_to_bv 5 r) = w64 val).
{ intros r val Hr. pose proof (R r val Hr) as Rr. unfold PB4_RA in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr];
    [injection Hr as <- <-; pb4_rreg HS; rewrite pb4_den_atom0;
     lazymatch goal with |- ew _ ?k = _ => rewrite (EE k (Z_to_bv 5 (Z.of_nat k)) eq_refl) end; exact Rr |]).
  destruct Hr. }
pmkst HS.
pose proof HJ as (HARc & _).
assert (ML : model_laws (as_universe B))
  by exact (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG05.model_laws_ok (as_universe B)
              (am_universe _ _ _ _ (proj1 HARc))).
assert (Hflag : rdword (rdW Wc (ms_mem ms)) (frame_addr lyc 5 pos + fs_frame_bytes 5 - 8) = Some (flag_addr lyc 5 pos)).
{ rewrite EF, EL. rewrite (rdword_ext (rdW Wc memc1) (rdW Wc (ms_mem ms))); [exact HFL|].
  intros k Hk. change (fs_frame_bytes 5) with 2048. apply K1; [lia|]. unfold SHADOW_OFF in *. lia. }
eapply SRr_bind.
{ apply (aj_stack_free_cls_atS SEGS B LAWS pa_segs_low ML (pa_sigma SS___asan_stack_free_5) 5 (ASF5 fx) ltac:(lia)
    Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [] lyc Sc _ 0 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 17332)) pos 1152 HJ).
  - unfold spZ. match goal with |- context [getr (ms_regs ms) ?r] =>
      rewrite (pb4_bvr (ms_regs ms) r 2 _ eq_refl (QA 2 _ ltac:(unfold PB4_RA; pb4_in))) end.
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (pb4_m16 _ _ S6 S3).
  - lia.
  - rewrite ESTK. unfold ESTACK. lia.
  - apply (pb4_bvr _ _ 3); [reflexivity | exact (QA 3 _ ltac:(unfold PB4_RA; pb4_in))].
  - apply (pb4_bvr _ _ 4); [reflexivity | exact (QA 4 _ ltac:(unfold PB4_RA; pb4_in))].
  - apply (pb4_bvr _ _ 1); [reflexivity | exact Q1].
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite EF. apply (pb4_bvr _ _ 10); [reflexivity | exact Q10].
  - apply (pb4_bvr _ _ 11); [reflexivity | exact Q11].
  - exact Hflag. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & K2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in K2 by lia.
rewrite EF, EL in K2. change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in K2.
change (fs_frame_bytes 5 / 8) with 256 in K2.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 17332)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x133c)) regs2 mem2 md2).
apply (Kc regs2 mem2 md2 HJ2).
- intros a Ha Hn. unfold pb4_Wr in Hn.
  rewrite (K2 a Ha);
    [ apply K1; [exact Ha | intros H; apply Hn; lia]
    | intros H; apply Hn; lia | intros H; apply Hn; lia | intros H; apply Hn; unfold ESTACK in *; lia ].
- unfold pf_rg, PB4_RB. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    rewrite (pb4_preg _ _ _ HP2) by (unfold acallee_saved; lia); apply QA; unfold PB4_RA; pb4_in.
Qed.

(* ---------- run C: 0x89174 .. ret 0x891c4, and the post ---------- *)
Lemma pb4_getr_bv : forall rr (r : bv 5) k, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = getr rr r.
Proof. intros rr r k <-. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma pb4_sC : forall v pos lyc Sc Wc rX memc mdc cf rX2 memc2 mdc2,
  INV_DONE B v pos lyc Sc Wc rX memc mdc cf ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [] lyc (stack_free_state 5 pos Sc) Wc memc2 mdc2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb4_Wr v pos a -> rdW Wc memc2 a = rdW Wc memc a) ->
  pf_rg rX2 (PB4_RB v (Z.of_nat (length (rc_seg cf)))) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x133c)) rX2 memc2 mdc2) (PF_POSTr B v cf).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf rX2 memc2 mdc2 HI HJ K HRG.
pose proof HI as (HCX & HFI & HOBJ & HRC & _ & _ & _).
destruct (pb4_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & EL & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & L1).
pose proof HFI as (_ & Hly & HSc & HPm & HSAV & _).
pose proof HOBJ as (_ & _ & _ & _ & HCH & _).
destruct (pb4_cblk v pos lyc Sc Wc memc mdc HG HAR Hin EF EL HCH) as (Cb1 & Cb2 & Cb3).
pose proof HCX as (HPRE & _). pose proof HPRE as (_ & Hra & _ & Hgp & Htp & _).
set (n := Z.of_nat (length (rc_seg cf))) in *.
pose proof asan_consts as (C1 & _).
assert (R : forall r val, In (r, val) (PB4_RB v n) -> getr rX2 (Z_to_bv 5 r) = w64 val)
  by (intros r val H; exact (pb4_rg rX2 _ r val HRG H)).
(* the saved registers, kept at memc2 *)
assert (HSAV2 : pf_saved (rdW Wc memc2) (pf_sp0 v) (p_regs v)).
{ intros j r Hj. rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc2)); [exact (HSAV j r Hj)|].
  assert (Hj13 : (j < 13)%nat)
    by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
  intros k Hk. destruct (pb4_saved_nw v pos HG (pf_sp0 v - 8 - 8 * Z.of_nat j + k) ltac:(lia)) as (H0 & H1).
  exact (K _ H0 H1). }
set (E := Eimg (Ereg rX2 (map (fun r => getr (p_regs v) (Z_to_bv 5 r)) PF_SAVED))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX2 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (ES : forall j r, nth_error PF_SAVED j = Some r -> ew E (32 + j) = getr (p_regs v) (Z_to_bv 5 r)).
{ intros j r Hj.
  assert (Hj13 : (j < 13)%nat)
    by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  rewrite (nth_indep _ _ (getr (p_regs v) (Z_to_bv 5 0)))
    by (rewrite length_map; change (length PF_SAVED) with 13%nat; exact Hj13).
  rewrite (map_nth (fun r0 => getr (p_regs v) (Z_to_bv 5 r0))).
  rewrite (nth_error_nth PF_SAVED j 0 Hj). reflexivity. }
assert (U8 : bv_unsigned (ew E 8) = pf_sp0 v)
  by (rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), (R 8 _ ltac:(unfold PB4_RB; pb4_in)); unfold w64;
      apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pb4_ssC
  (restrict (w_H Wc) (mkst rX2 (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x133c))) memc2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pb4_ssC. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pb4_stkC.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros ck Hck. apply in_map_iff in Hck as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error PF_SAVED j) as [r|] eqn:Er;
      [|apply nth_error_None in Er; change (length PF_SAVED) with 13%nat in Er; lia].
    pose proof (bv_unsigned_in_range 64 (getr (p_regs v) (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
    apply (chunk_ok_val SEGS E _ (pf_sp0 v) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
      (bv_unsigned (getr (p_regs v) (Z_to_bv 5 r)))).
    + rewrite pb4_den_atom0, (ES j r Er), Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn; lia.
    + replace (pf_sp0 v + (-8 - 8 * Z.of_nat j)) with (pf_sp0 v - 8 - 8 * Z.of_nat j) by lia.
      exact (val_mem_of_rdword SEGS (w_H Wc) memc2 _ _ (HSAV2 j r Er)).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8. change (2 ^ 4) with 16. repeat split; lia. }
revert HS HEI EE ES U8. generalize E as E0. clear E. intros E0 HS HEI EE ES U8.
assert (SHOK : sh_ok SEGS pb4_BxA [] E0 (mrestrict (w_H Wc) memc2)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x133c)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x133c))).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
pb4_clear_md.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc2 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc2 (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
(* the registers at the ret: ra, s0, s1, s2 .. s11 the saved ones, sp = s0, gp / tp kept, a0 = s2 = n *)
assert (QS : forall j r, nth_error PF_SAVED j = Some r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr (p_regs v) (Z_to_bv 5 r)).
{ intros j r Hj. rewrite <- (ES j r Hj).
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]; cbn [nth_error PF_SAVED] in Hj;
    [injection Hj as <-; pb4_rreg HS; rewrite pb4_den_atom0; reflexivity .. | destruct j; discriminate]. }
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
unfold PF_POSTr. apply (apost_baseF_of_base SEGS). unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists lyc, (stack_free_state 5 pos Sc), r, m, d end.
split.
{ rewrite <- (pb4_getr_bv (ms_regs ms) 1%bv 1 eq_refl), (QS 0%nat 1 eq_refl), (pb4_getr_bv (p_regs v) 1%bv 1 eq_refl).
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr. repeat match type of Hc with _ \/ _ => destruct Hc as [-> | Hc] | ?x = _ => subst x end.
  - pb4_rreg HS. rewrite pb4_den_atom0, (EE 8%nat (Z_to_bv 5 8) eq_refl), (R 8 _ ltac:(unfold PB4_RB; pb4_in)).
    rewrite (pb4_getr_bv (p_regs v) 2%bv 2 eq_refl). unfold pf_sp0, spZ, w64. apply Z_to_bv_bv_unsigned.
  - pb4_rreg HS. rewrite pb4_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl), (R 3 _ ltac:(unfold PB4_RB; pb4_in)).
    rewrite (pb4_getr_bv (p_regs v) 3%bv 3 eq_refl). symmetry. exact Hgp.
  - pb4_rreg HS. rewrite pb4_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl), (R 4 _ ltac:(unfold PB4_RB; pb4_in)).
    rewrite (pb4_getr_bv (p_regs v) 4%bv 4 eq_refl). symmetry. exact Htp.
  - exact (QS 1%nat 8 eq_refl).
  - exact (QS 2%nat 9 eq_refl).
  - exact (QS 3%nat 18 eq_refl).
  - exact (QS 4%nat 19 eq_refl).
  - exact (QS 5%nat 20 eq_refl).
  - exact (QS 6%nat 21 eq_refl).
  - exact (QS 7%nat 22 eq_refl).
  - exact (QS 8%nat 23 eq_refl).
  - exact (QS 9%nat 24 eq_refl).
  - exact (QS 10%nat 25 eq_refl).
  - exact (QS 11%nat 26 eq_refl).
  - exact (QS 12%nat 27 eq_refl). }
split.
{ rewrite <- (pb4_getr_bv (ms_regs ms) 10%bv 10 eq_refl). pb4_rreg HS.
  rewrite pb4_den_atom0, (EE 18%nat (Z_to_bv 5 18) eq_refl). exact (R 18 _ ltac:(unfold PB4_RB; pb4_in)). }
split.
{ destruct HRC as (bs & Hb & Henc). exists bs. split; [|exact Henc].
  intros i Hi. destruct Henc as (Hlen & _). unfold seg_spec.SEG_C_SIZE in Hlen.
  destruct (Cb3 (p_c v + Z.of_nat i) ltac:(lia)) as (_ & H0 & H1).
  rewrite (K3 _ H0), (K _ H0 H1). exact (Hb i Hi). }
split.
{ unfold ablocks. rewrite blocks_stack_free_state. exact HPm. }
split; [exact Hly|].
destruct HSc as (f0 & EF0). rewrite EF0.
exists (mkFS (fs_hint (st_fs (set_fs f0 (p_S v)))) (del_pos (fs_live (st_fs (set_fs f0 (p_S v)))) 5 pos)).
unfold stack_free_state. destruct (p_S v); reflexivity.
Qed.

(* ---------- the segment ---------- *)
Lemma pb4_main : H_DONE B.
Proof.
intros v pos lyc Sc Wc rX memc mdc cf HI.
pose proof HI as (HCX & HFI & _ & _ & HSL & _ & _).
destruct (pb4_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & EL & _).
pose proof HFI as (_ & _ & _ & _ & _ & HFL & _).
assert (W88 : rdword (rdW Wc memc) (pf_s1 v + 0x88) = Some (pf_F v pos)) by (apply (pb4_sl _ _ _ _ _ HSL); pb4_in).
assert (W98 : rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_F v pos)) by (apply (pb4_sl _ _ _ _ _ HSL); pb4_in).
apply (pb4_sA v pos lyc Sc Wc rX memc mdc cf _ HI).
intros rX1 memc1 mdc1 HJ1 K1 HR1.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & L1). pose proof asan_consts as (C1 & _).
apply (pb4_sB v pos lyc Sc Wc rX1 memc1 mdc1 (Z.of_nat (length (rc_seg cf))) _ HG Hin EF EL HJ1);
  [ rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc1)); [exact W88 | intros k Hk; apply K1; lia]
  | rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc1)); [exact W98 | intros k Hk; apply K1; lia]
  | rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc1));
      [exact HFL | intros k Hk; apply K1; try change (fs_frame_bytes 5) with 2048; lia]
  | exact HR1 | ].
intros rX2 memc2 mdc2 HJ2 K2 HR2.
apply (pb4_sC v pos lyc Sc Wc rX memc mdc cf rX2 memc2 mdc2 HI HJ2); [|exact HR2].
intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha).
Qed.
End x.

(* the segment statement of pf_pieces.v at every FP state *)
Theorem pf_seg_B4_holds : S_B4 B.
Proof. intros f0. exact (pb4_main (fx := f0)). Qed.
End d.
