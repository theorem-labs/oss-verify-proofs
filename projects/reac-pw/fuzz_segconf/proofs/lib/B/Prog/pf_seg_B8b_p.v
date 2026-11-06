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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 552 of its 667 lines of code are new or changed and 4938 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a1.v, with its module paths and module names changed; 120 of its 159 lines of code are new or changed and 628 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the PROV2 piece of
   segment B8b of reac_segconf_parse_file's walk, pb8b_prov2_holds : forall n, HA_TAIL B n -> H_PROV2 B n
   (lib/B/Prog/pf_pieces.v's INV_PROV2 / H_PROV2 at 0x88e4c). A B8b sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8b, piece PROV2 -> TAIL; reuse search and CONFIRM:
   the rule-24 lookup record, verdict none).
   ADAPTED from a working branch (an image-A segment lane: pf_a8b_m.v's pfa8b_rconf_prov2, ported as
   pf_seg_B8b_m.v's pb8b_rconf_prov2) and a working branch's pf_a3_k.v (the snprintf site), re-derived on
   image B's code.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 2 instructions, no check, no UBSan trap:
     0x88e4c jal wrapper_snprintf     snprintf(&c->seg[gi].ignore_file, 0x60, "%s", c->reading)
                                      (B12 set a0 at 0x88e38, a1 0x88e3c, a2 0x88e40 = 0x21340, a3 0x88e48)
     0x88e50 j 0x88600                TAIL
   Both are the shared step pf_seg_B8b_s.v's pb8b_snp_tail with the destination inside the block c's first
   footprint range ([c, c + RC_N + 4); gi < 32 by sa_rconf's bound, pb8b_seg_in) and the source c->reading
   (pb8b_reading_str; 95 bytes at most, its span inside the block, apart from the destination). The model edit
   is pf_prov_mid (PIgn b) -> pf_prov_fin (PIgn b) (pb8b_rconf_prov2); TAIL at the next line's offset
   o' = pf_next s o and ln' = ln + 1 (PF_RM's s9 / s6), the counters' room already the room after the line
   (INV_PROV2's pf_st), the rest shorter than n (pfA_facts.pf_next_skipn_lt).
   Section hypothesis: SNP (RtFormat.asnprintf_realizes at SS___interceptor_trampoline_snprintf, gotwA, guardA,
   every FP state), the only call. Instructions walked: 2 of 2; checks 0 / 0; UBSan traps 0 / 0. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces pf_seg_B8b_d pf_seg_B8b_s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B8b_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the record's fields r_upd does not touch *)
Lemma pb8bp_upd_fields : forall (cf : rconf) i f,
  length (rc_seg (r_upd cf i f)) = length (rc_seg cf) /\ rc_refused (r_upd cf i f) = rc_refused cf /\
  rc_overflow (r_upd cf i f) = rc_overflow cf.
Proof. intros cf i f. unfold r_upd, r_set_segs. cbn [rc_seg rc_refused rc_overflow]. rewrite upd_nth_len. auto. Qed.
(* a reader that agrees with rd' on the block [c, c + SEG_C_SIZE) shows the same record there *)
Lemma pb8bp_rconf_ext : forall (rd rd' : reader) c cf,
  (forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rd' x = rd x) -> sa_rconf rd c cf -> sa_rconf rd' c cf.
Proof.
intros rd rd' c cf K (bs & Hb & Henc). exists bs. split; [|exact Henc].
destruct Henc as [Hl _]. intros i Hi. rewrite K by lia. exact (Hb i Hi).
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Theorem pb8b_prov2_holds : forall n, HA_TAIL B n -> H_PROV2 B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cf nm o ln d b gi HI.
destruct HI as (HB & HMID & HST & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL0 & HFSH).
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4096 & Hcceil & HcA & HcH & Hcap).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HMID as (Ho & Hn & HCTX).
destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
set (cm := pf_prov_mid (PIgn b) cf gi) in *.
cbn [pf_cur_ok] in HCUR.
assert (Hgi : (gi < length (rc_seg cf))%nat).
{ unfold cm, pf_prov_mid in HCUR. rewrite (proj1 (pb8bp_upd_fields cf gi _)) in HCUR. exact HCUR. }
destruct (pf_seg_B8b_m.pb8b_prov_mid_fields b cf gi Hgi) as (Er & _ & Ll & _).
fold cm in Er, Ll.
pose proof HRC as (bs & Hbs & Henc).
pose proof Henc as (Lbs & L32 & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
destruct Hrd as (_ & Hrdl & _ & _).
rewrite Er in Hrdl.
assert (Hgi32 : (gi < 32)%nat) by (rewrite Ll in L32; lia).
pose proof (pb8b_seg_in (p_c v) gi seg_spec.RS_IGNORE_FILE 96 Hgi32 ltac:(unfold seg_spec.RS_IGNORE_FILE; lia)
  ltac:(lia) ltac:(unfold seg_spec.RS_IGNORE_FILE; lia)) as (Hd1 & Hd2).
pose proof pb8b_rc_vals as (ERN & EGN & ERR & ESG & EIF & ERS & ESZ).
destruct HcH as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrqc].
set (str := rc_reading cf) in *.
assert (HSTR : sa_str (rdW Wc memc) (p_c v + seg_spec.RC_READING) str)
  by (rewrite <- Er; exact (pf_seg_B8b_m.pb8b_reading_str _ (p_c v) cm HRC ltac:(lia))).
assert (Hl96 : Z.of_nat (length str) < 96) by lia.
pose proof (Z.mod_pos_bound (- (p_c v + seg_spec.RC_READING + Z.of_nat (length str) + 1)) 8 ltac:(lia)) as Hspm.
unfold pf_postm.
apply (pb8b_snp_tail B SNP n v pos lyc Sc Wc rX memc mdc (pf_prov_fin (PIgn b) cf gi) (Some gi) nm
  (pf_next (p_s v) o) (ln + 1) d (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE) 0x60
  (p_c v + seg_spec.RC_READING) str TAIL HB HCTX).
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
- apply (pb8b_rg_sub _ _ _ HRG). intros x Hx. unfold PF_RM. cbn [In app] in Hx |- *. unfold PF_RL in Hx |- *.
  cbn [In app] in Hx |- *. tauto.
- apply (pb8b_rg_sub _ _ _ HRG). intros x Hx. unfold PF_RM, PF_RL. cbn [In app] in Hx |- *. tauto.
- left. split; lia.
- lia.
- exact HSTR.
- (* c->reading's bytes and NUL: inside the block *)
  split; [lia|]. split; [lia|].
  split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memc mdc bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length str) + 1) HAR Hbc ltac:(lia) ltac:(lia))|].
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length str) + 1) HAR Hbc ltac:(lia) ltac:(lia))|].
  intros Hp. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length str) + 1) HAR Hbc ltac:(lia) ltac:(lia) Hp).
- apply Nat2Z.inj_le. assert (E : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity). rewrite E. lia.
- lia.
- exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memc mdc bc mc (p_c v + seg_spec.RC_READING)
    (Z.of_nat (length str) + 8) HAR Hbc ltac:(lia) ltac:(lia)).
- unfold seg_spec.cstr_span. lia.
- unfold sa_disj, seg_spec.cstr_span. lia.
- (* pf_st once the string and its NUL are at &seg[gi].ignore_file *)
  intros rd' Hw Hk.
  assert (Hsn : (length (snprintf_s 0x60 F_s [AS str]) < 96)%nat) by exact (pf_seg_B8b_m.pb8b_sn96_len str).
  (* the block's bytes: rd' outside the written range is rd *)
  assert (KB : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE ->
      ~ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE <= x <
         seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE + Z.of_nat (S (length (snprintf_s 0x60 F_s [AS str])))) ->
      rd' x = rdW Wc memc x).
  { intros x Hx Hnd. apply Hk; [lia | exact Hnd | lia]. }
  set (rdp := fun x => if (p_c v <=? x) && (x <? p_c v + seg_spec.SEG_C_SIZE) then rd' x else rdW Wc memc x).
  assert (Hrdp_in : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> rdp x = rd' x).
  { intros x Hx. unfold rdp. replace ((p_c v <=? x) && (x <? p_c v + seg_spec.SEG_C_SIZE)) with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (HRCp : sa_rconf rdp (p_c v) (pf_prov_fin (PIgn b) cf gi)).
  { apply (pf_seg_B8b_m.pb8b_rconf_prov2 (rdW Wc memc) rdp (p_c v) cf gi b HRC Hgi ltac:(lia)).
    - intros x Hx Hnd. unfold rdp.
      destruct ((p_c v <=? x) && (x <? p_c v + seg_spec.SEG_C_SIZE)) eqn:Eb; [|reflexivity].
      apply andb_prop in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.ltb_lt in Eb2.
      exact (KB x ltac:(lia) Hnd).
    - intros k0 Hk0.
      assert (Hsn' : (length (snprintf_s 96 F_s [AS (rc_reading cf)]) < 96)%nat)
        by exact (pf_seg_B8b_m.pb8b_sn96_len (rc_reading cf)).
      rewrite Hrdp_in; [exact (Hw k0 Hk0)|]. lia. }
  split; [exact (pb8bp_rconf_ext rdp rd' (p_c v) _ (fun x Hx => eq_sym (Hrdp_in x Hx)) HRCp)|].
  split; [cbn [pf_cur_ok]; unfold pf_prov_fin; rewrite (proj1 (pb8bp_upd_fields cf gi _)); exact Hgi|].
  split.
  { destruct HNM as (f & Hfb & Hfe). exists f. split; [|exact Hfe].
    pose proof Hfe as [Hfl _]. intros i Hi. rewrite Hfl in Hi.
    rewrite Hk; [exact (Hfb i ltac:(rewrite Hfl; exact Hi)) | unfold PF_O_CN; lia | | unfold PF_O_CN; lia].
    unfold PF_O_CN. intros Hq. destruct Hcap as [Hcap | Hcap]; lia. }
  split.
  { unfold pf_cnt in *. unfold pf_prov_fin. rewrite (proj1 (proj2 (pb8bp_upd_fields cf gi _))),
      (proj2 (proj2 (pb8bp_upd_fields cf gi _))).
    unfold cm, pf_prov_mid in HCNT. rewrite (proj1 (proj2 (pb8bp_upd_fields cf gi _))),
      (proj2 (proj2 (pb8bp_upd_fields cf gi _))) in HCNT. exact HCNT. }
  rewrite (rdword_ext (rdW Wc memc) rd'); [exact HC0|].
  intros k0 Hk0. apply Hk; [lia | lia | lia].
Qed.
End x.
End e.
End f.
End d.
