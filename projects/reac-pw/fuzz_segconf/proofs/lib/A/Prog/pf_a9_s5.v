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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 309 of its 363 lines of code are new or changed and 4999 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): stretch E of segment A9 of reac_segconf_parse_file's walk,
   the theorem a9_sE : SA9_E B of lib/A/Prog/pf_a9_d.v (K9 0x88510 -> TAIL 0x88068). Part of
   segment A9's proof, by the G3 walk owner, 2026-10-30.

   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk, one stretch of segment A9;
   the whole function's rule-24 line, its pasted released-proof index output and the G3 walk owner's CONFIRM of
   2026-10-30T15:42:08Z are in the unit's internal record, commit dfb49d6ad789,
   path records/segp/g3-lookup.md, reuse verdict none:
   written new)

   THE CODE (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s in records/segp/dis/ at that commit,
   lines 680-681):
     0x88510 jal 0x88da4 refuse     a0 = s8 = c, a1 = s10 = lineno, a2 = F_knock / F_nokey (0x21980 / 0x21a40),
                                    a3 = slot 0x50 = cur_name = F + 0x20, a4 = the value / the key in buf
     0x88514 j   0x88068            TAIL (BASE + PF_TAIL)

   THE PROOF.
   - refuse_site_ok_88510 (VERIFY rule 1j-bis): INV_K9 at the jal gives every premise of refuse_contract besides
     afn_pre (which PaFx.cl_callSF builds from the journal): arodata_okP, the three argument registers with their
    ranges, refuse_pre (cur_name's C string from pf_a9_f.v's a9_nm_str, with its two shadow cells 0 under
    PF_SC_LINE, a9e_shb_cn; each string argument by pf_a6_k.v's a6_obj_arg: cur_name at [0x20, 0x30), the buf
    string at buf through a6_buf_arg), sa_room and the event bound. The
     stack-protector cells at the site are pf_obj's last conjunct: no hypothesis is taken there.
     a9e_stk is the window arithmetic: refuse's window at sp = s1 fits parse_file's (12464 + 336 <= 12800).
   - The run: a seed with no memory region (a9e_seed; the two instructions read and write no memory), one run of
     the plain executor to the call (PaCallRun.v paj_run_shc), refuse by PaFx.cl_callSF (its post is
     apost_baseF: it returns at another FP state fx1, and the segment's post is lifted back by
     PaFx.srr_apost_baseF_lift), a fresh seed at the return 0x88514 at fx1 and one run to TAIL
     (PaLibF.v paj_run_to_sh), then H_TAIL at fx1.
   - The TAIL cut after a call whose post has no keep clause: pf_base by segment A6's pf_a6_k.v (a6_keeps_refuse:
     refuse's footprint lies in the block c; a6_base_move: the heap facts re-derived from AR at the exit state,
     the frame and its shadow by the journal's frames clause), cur_name by a6_nm_move, the counters by
     pfA_facts.v's pf_cnt_refuse, the registers by aregs_preserved (every register of the cut is callee-saved).
   SECTION HYPOTHESES: SIGP (refuse's call target), REFUSE (refuse_contract at every FP state), and VRO and SSPX,
   which are FORCED by pf_a6_k.a6_base_move after the refuse call: refuse's post gives only its journal, the
   journal keeps an image byte only when it is not in as_owned_static B (YCbq.v:479), and whether the GOT word
   0xa36d8 and the guard 0x5ff078 are owned statics is a record fact of listing stage 2
   (SegRecCells.seg_rec_cells, after AF0m); arodata_okP after refuse needs pa_relro_img, which is VRO. Both are
   discharged from listing stage 2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a9_d pf_a9_f pf_a5_k pf_a6_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
Lemma a9e_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma a9e_rg_tr : forall (r1 r2 : bvmap 5 word) L, pf_rg r1 L ->
  (forall rv, In rv L -> getr r2 (Z_to_bv 5 (fst rv)) = getr r1 (Z_to_bv 5 (fst rv))) -> pf_rg r2 L.
Proof.
intros r1 r2 L H K. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (K rv Hin). exact (H rv Hin).
Qed.
(* reading a register of a symbolic state (lib/A/Prog/pf_a2.v's pa2_rreg, segment A2's proof) *)
Ltac a9e_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac a9e_in := cbn [In app]; repeat (first [left; reflexivity | right]).

(* the window arithmetic of the call: refuse at sp = s1, o = s1 - sp0 is -320 or -336 *)
Lemma a9e_stk : forall sp0 s1, sp0 mod 16 = 0 -> s1 = a6_s1v sp0 ->
  (s1 - sp0) mod 16 = 0 /\ s1 - sp0 <= 0 /\ 0 <= STK_refuse /\
  STK_refuse - (s1 - sp0) <= STK_reac_segconf_parse_file.
Proof.
intros sp0 s1 H16 ->. pose proof (a6_s1 sp0 H16) as (S1a & S1b & S1c & S1d).
pose proof STK_values as (_ & SR & _ & SPF & _). rewrite SR, SPF.
pose proof (Z.div_mod (a6_s1v sp0 - sp0) 16 ltac:(lia)) as D. rewrite S1d in D.
split; [exact S1d|]. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* cur_name's two shadow cells (4, 5) are 0 while it is in scope: the cur_name analogue of pf_a9_f.v's
   a9_shb_buf *)
Lemma a9e_shb_cn : forall i, 4 <= i < 6 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb.
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a symbolic state with every register its own atom and no memory region, at listing offset pc *)
Definition a9e_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma a9e_seed : forall (W : world SEGS) (rX : bvmap 5 word) memc pc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (a9e_ss pc)
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros W rX memc pc. rewrite restrict_mkst_fx. unfold a9e_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.
End f.
End d.

(* the seed above is closed over the FP state: the walk takes it at fx before refuse and at fx1 after *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* refuse's call target (SegObj.v; the pinned instance gives it by computation) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
(* the listing's read-only range: forced by pf_a6_k.a6_base_move after the refuse call (arodata_okP after refuse
   needs pa_relro_img); discharged from listing stage 2 *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the callee: refuse_contract at image A's numbers (lib/A/Prog/refuse_c.v, SegInstA.v), at every FP state *)
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the contract writer's route A (2026-10-30), lib/A/Prog/reac_segconf_parse.v:137's shape: the stack-protector cells at
   every AR state. Forced by pf_a6_k.a6_base_move after the refuse call: refuse's post has no keep clause and its
   journal does not keep the GOT word 0xa36d8 (an owned static); discharged from SegRecCells.seg_rec_cells when
   listing stage 2 compiles. *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* pf_base at the same state with another model whose journal it carries (the plain run to the call changes the
   model only by materialisation) *)
Lemma a9e_base_md : forall v pos lyc Sc Wc rX memc mdc mdc' sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  pf_base B v pos lyc Sc Wc rX memc mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc mdc' sc (CX & (_ & FI) & OBJ & SL & FSH) HJ.
exact (conj CX (conj (conj HJ FI) (conj OBJ (conj SL FSH)))).
Qed.

(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> refuse at 0x88510 (refuse(c, lineno, F_knock / F_nokey,
   cur_name, the value / the key)): INV_K9 at the jal gives refuse_contract's premises over the call's registers
   regsc (the cut's, ra the return 0x88514) *)
Lemma refuse_site_ok_88510 : forall n x ei gi f fa wp w lyc Sc Wc rX memc mdc (regsc : bvmap 5 word),
  INV_K9 B n x ei gi f fa wp w lyc Sc Wc rX memc mdc ->
  (forall r, In r [2; 10; 11; 12; 13; 14] -> getr regsc (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regsc 10 = w64 (p_c (y_v x)) /\ 0 <= p_c (y_v x) < 2 ^ 64 /\
  getr regsc 11 = w64 (y_ln x + 1) /\ 0 <= y_ln x + 1 < 2 ^ 64 /\
  getr regsc 12 = w64 fa /\ 0 <= fa < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c (y_v x)) (y_ln x + 1) fa
    [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17] (y_cf x) (y_ln x + 1) f
    [AS (y_nm x); AS w] /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
Proof.
intros n x ei gi f fa wp w lyc Sc Wc rX memc mdc regsc
  ((HB & HMID & HST & HSL & HLT & HD0 & HDL) & HCUR & HSCH & HARG & (HWS & HWB) & HRK & RG) KR.
pose proof HB as (CX & FI & OBJ & SL & FSH).
destruct (a6_cx B (y_v x) CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 (y_v x)) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof FI as (HJ & Hly & _ & _ & _ & _ & HFRM & HRG).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof CX as (_ & _ & _ & Hc64 & _ & _ & _ & _ & _ & Hroom & Hev).
destruct OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
destruct HST as (RC & COK & NM & CNT).
destruct HMID as (Ho & Hn & (Hno & Hlines & Hln & Hle)).
pose proof (pf_next_le (p_s (y_v x)) (y_o x) Ho) as HNL.
pose proof asan_consts as (C1 & _).
(* the call registers *)
assert (RK : forall r val, In (r, val) (PF_RL (y_v x) (y_pos x) ++ PF_RM (y_v x) (y_o x) (y_ln x) ++
    [(20, a9_cp x); (10, p_c (y_v x)); (11, y_ln x + 1); (12, fa);
     (13, pf_F (y_v x) (y_pos x) + PF_O_CN); (14, wp)]) -> In r [2; 10; 11; 12; 13; 14] ->
    getr regsc (Z_to_bv 5 r) = w64 val).
{ intros r val Hin Hr. rewrite (KR r Hr). exact (a5_rg_get rX _ r val RG Hin). }
assert (R2 : getr regsc 2 = w64 (pf_s1 (y_v x))).
{ change (getr regsc 2) with (getr regsc (Z_to_bv 5 2)). rewrite (KR 2) by a9e_in.
  exact (a5_rg_get rX _ 2 (pf_s1 (y_v x)) HRG ltac:(a9e_in)). }
assert (R10 : getr regsc 10 = w64 (p_c (y_v x))).
{ change (getr regsc 10) with (getr regsc (Z_to_bv 5 10)). apply RK; [unfold PF_RL, PF_RM|]; a9e_in. }
assert (R11 : getr regsc 11 = w64 (y_ln x + 1)).
{ change (getr regsc 11) with (getr regsc (Z_to_bv 5 11)). apply RK; [unfold PF_RL, PF_RM|]; a9e_in. }
assert (R12 : getr regsc 12 = w64 fa).
{ change (getr regsc 12) with (getr regsc (Z_to_bv 5 12)). apply RK; [unfold PF_RL, PF_RM|]; a9e_in. }
assert (R13 : getr regsc 13 = w64 (pf_F (y_v x) (y_pos x) + PF_O_CN)).
{ change (getr regsc 13) with (getr regsc (Z_to_bv 5 13)). apply RK; [unfold PF_RL, PF_RM|]; a9e_in. }
assert (R14 : getr regsc 14 = w64 wp).
{ change (getr regsc 14) with (getr regsc (Z_to_bv 5 14)). apply RK; [unfold PF_RL, PF_RM|]; a9e_in. }
assert (Hsp : spZ regsc = pf_s1 (y_v x)) by (unfold spZ; rewrite R2; apply a6_w64_u; lia).
(* the format: F_knock or F_nokey, a literal of PARSE_FILE_LITS at seg_litA_rc f *)
assert (HF : (f = F_knock \/ f = F_nokey) /\ fa = seg_litA_rc f).
{ destruct HARG as [(-> & -> & _) | (-> & -> & _)]; [split; [left|] | split; [right|]]; reflexivity. }
destruct HF as [HF Hfa].
assert (HL : In f PARSE_FILE_LITS).
{ unfold PARSE_FILE_LITS. apply in_or_app. left. destruct HF as [-> | ->]; a9e_in. }
pose proof (LITS f HL) as HLL.
pose proof HLL as (Hfp & _ & Hpin & _).
pose proof (Hpin lyc Sc Wc memc mdc HAR) as (_ & Hfp63 & _).
split; [exact ROD|].
split; [exact R10|]. split; [lia|].
split; [exact R11|]. split; [lia|].
split; [exact R12|]. split; [rewrite Hfa; lia|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [destruct CNT as [CN1 _]; lia|].
  split; [lia|]. split; [reflexivity|].
  (* the forbidden ranges of sa_va_args: the stack below sp, the refusal slot and c->refused *)
  assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
      (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
      [(ly_stk_lo lyc, spZ regsc);
       (seg_spec.refusal_addr (p_c (y_v x)) (length (rc_refusal (y_cf x))),
        seg_spec.refusal_addr (p_c (y_v x)) (length (rc_refusal (y_cf x))) + seg_spec.RC_REFUSAL_LEN);
       (p_c (y_v x) + seg_spec.RC_REFUSED, p_c (y_v x) + seg_spec.RC_REFUSED + 4)]).
  { destruct (a6_heap_bounds B _ _ _ _ _ (p_c (y_v x)) seg_spec.SEG_C_SIZE HAR HC
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
    destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
    constructor; [left; cbn [fst]; rewrite Hly; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
    constructor. }
  (* cur_name: its C string from pf_nm (pf_a9_f.v a9_nm_str), F + 0x20 8-aligned *)
  assert (HCN8 : (pf_F (y_v x) (y_pos x) + PF_O_CN) mod 8 = 0).
  { unfold PF_O_CN. pose proof (Z.div_mod (pf_F (y_v x) (y_pos x)) 32 ltac:(lia)) as D.
    replace (pf_F (y_v x) (y_pos x) + 32) with ((4 * (pf_F (y_v x) (y_pos x) / 32) + 4) * 8) by lia.
    apply Z_mod_mult. }
  destruct (a9_nm_str (rdW Wc memc) (pf_F (y_v x) (y_pos x) + PF_O_CN) (y_nm x) HCN8 NM) as [HNS HN16].
  destruct (a6_obj_arg B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE 0x20 0x30
    (pf_F (y_v x) (y_pos x) + PF_O_CN) (y_nm x) _ HB ltac:(lia) eq_refl eq_refl ltac:(lia)
    ltac:(intros i Hi; apply a9e_shb_cn; change (0x20 / 8) with 4 in Hi; change (0x30 / 8) with 6 in Hi; exact Hi)
    HNS ltac:(unfold PF_O_CN; lia) ltac:(unfold PF_O_CN; lia) HWl) as [HVA1 HLOC1].
  (* the value / the key: a C string in buf (segment A6's a6_buf_arg) *)
  destruct (a6_buf_arg B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE wp w _ HB eq_refl eq_refl HWS HWB HWl)
    as [HVA2 HLOC2].
  split; [unfold seg_spec.REFUSE_FORMATS; destruct HF as [-> | ->]; a9e_in|].
  split; [destruct HF as [-> | ->]; vm_compute; reflexivity|].
  split; [rewrite Hfa; lia|]. split; [exact Hfa|]. split; [rewrite Hfa; exact HLL|].
  split; [cbn [sa_va_args]; rewrite R13, R14; exact (conj HVA1 (conj HVA2 I))|].
  split; [cbn [refuse_va_locs]; rewrite R13, R14; exact (conj HLOC1 (conj HLOC2 I))|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- split.
  + unfold sa_room. unfold sa_room_n in Hroom. rewrite Hfrs. cbn [app length]. lia.
  + unfold EV_refuse. unfold EV_reac_segconf_parse_file in Hev. lia.
Qed.

(* ---------- the stretch: K9 -> TAIL ---------- *)
Lemma a9_sE : SA9_E B.
Proof.
intros n HT x ei gi f fa wp w lyc Sc Wc rX memc mdc HI.
pose proof HI as ((HB & HMID & HST & HSL & HLT & HD0 & HDL) & HCUR & HSCH & HARG & HINB & HRK & HRG).
pose proof HB as (CX & FI & OBJ & SLb & FSH).
destruct (a6_cx B (y_v x) CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a9e_stk (pf_sp0 (y_v x)) (pf_s1 (y_v x)) Hsp16 (a6_s1_eq (y_v x))) as (Ho16 & Hoz & HS0 & HSTK).
pose proof (a6_s1 (pf_sp0 (y_v x)) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof FI as (HJ & Hly & _ & _ & HSV & _ & HFRM & HRG0).
pose proof (proj1 HJ) as HAR.
destruct (a5_chain B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH].
destruct HST as (HRC & HCOK & HNM & HCNT).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
(* the post: r_key's knock / no-key step is the refusal *)
unfold a9_goal. rewrite HRK. unfold pf_postm, PF_POSTr.
(* 0x88510: the seed, the run to the call *)
pose proof (a9e_seed (fx := fx) Wc rX memc A9_K9) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
unfold cfg_at. change (w64 (BASE + A9_K9)) with (Z_to_bv 64 (BASE + A9_K9)).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?y ?m] =>
  set (mdv1 := with_vm_backing (m_vm_lazy m) y m) in *; clearbody mdv1 end.
rename ms into ms1.
(* the run wrote nothing; only ra changed *)
assert (Hmem1 : ms_mem ms1 = memc).
{ apply functional_extensionality. intros y. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
assert (QK1 : forall r, In r [2; 3; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 24; 26; 27] ->
    getr (ms_regs ms1) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [a9e_rreg HS; rewrite a9e_den_atom0; apply EE; reflexivity |]).
  destruct Hr. }
prreg HS (1%bv : bv 5) Q1.
pmkst HS.
rewrite Hmem1. rewrite Hmem1 in HJ.
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
(* refuse's premises at the call (rule 1j-bis) *)
destruct (refuse_site_ok_88510 n x ei gi f fa wp w lyc Sc Wc rX memc mdc (ms_regs ms1) HI
  ltac:(intros r Hr; apply QK1; revert Hr; cbn [In]; tauto))
  as (HROD1 & H10 & Hc64 & H11 & Hl64 & H12 & Hf64 & HPRE & HROOM & HEV).
assert (HB1 : pf_base B (y_v x) (y_pos x) lyc Sc Wc rX memc mdv1 PF_SC_LINE)
  by exact (a9e_base_md (y_v x) (y_pos x) lyc Sc Wc rX memc mdc mdv1 PF_SC_LINE HB HJ).
assert (QS0 : s0Z (ms_regs ms1) = pf_sp0 (y_v x)).
{ unfold s0Z. change (getr (ms_regs ms1) 8) with (getr (ms_regs ms1) (Z_to_bv 5 8)).
  rewrite (QK1 8) by a9e_in. rewrite (a5_rg_get rX _ 8 (pf_sp0 (y_v x)) HRG0) by a9e_in. apply a6_w64_u. lia. }
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms1) memc _ STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x))
    [(5, y_pos x)] lyc Sc _ 0 STK_refuse (refuse_W (p_c (y_v x)) (y_cf x)) EV_refuse
    (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + 14304)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c (y_v x)) (refuse (y_cf x) (y_ln x + 1) f [AS (y_nm x); AS w]) /\
       sa_noalloc B lyc Sc ly2 S2) HJ).
  - unfold spZ. change (getr (ms_regs ms1) 2) with (getr (ms_regs ms1) (Z_to_bv 5 2)).
    rewrite (QK1 2) by a9e_in. rewrite (a5_rg_get rX _ 2 (pf_s1 (y_v x)) HRG0) by a9e_in.
    rewrite a6_w64_u by lia. lia.
  - exact Ho16.
  - exact Hoz.
  - exact HS0.
  - exact HSTK.
  - change (getr (ms_regs ms1) 3) with (getr (ms_regs ms1) (Z_to_bv 5 3)).
    rewrite (QK1 3) by a9e_in. exact (a5_rg_get rX _ 3 (as_gp B) HRG0 ltac:(a9e_in)).
  - change (getr (ms_regs ms1) 4) with (getr (ms_regs ms1) (Z_to_bv 5 4)).
    rewrite (QK1 4) by a9e_in. exact (a5_rg_get rX _ 4 (as_tp B) HRG0 ltac:(a9e_in)).
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite QS0. replace (pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) with (pf_s1 (y_v x)) by lia.
    exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { apply (REFUSE fx lyc Sc Wc (ms_regs ms1) memc mdv1 ch1 (p_c (y_v x)) (y_ln x + 1) fa (y_ln x + 1) (y_cf x) f
        [AS (y_nm x); AS w] HPRE1 HROD1 H10 Hc64 H11 Hl64 H12 Hf64 HPRE HROOM HEV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
    destruct OBJ as (_ & _ & _ & _ & HC & _).
    destruct (a6_heap_bounds B _ _ _ _ _ (p_c (y_v x)) seg_spec.SEG_C_SIZE HAR HC
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
    apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
cbv beta. intros W2 c2 HLE (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
destruct HNA2 as (HPERM2 & Hly2 & HS2e).
replace (pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) with (pf_s1 (y_v x)) in HJc2 by lia.
(* what refuse kept: the stack from s1 up, the text, the unowned image bytes, the frame and its shadow *)
pose proof (a6_keeps_refuse B (y_v x) (y_pos x) lyc Sc Wc rX memc mdv1 PF_SC_LINE (y_cf x) ly2 S2 W2 mem2 md2
  EV_refuse HB1 HJc2 HPERM2) as HKP.
(* 0x88514 at fx1: a fresh seed, the run to TAIL *)
pose proof (a9e_seed (fx := fx1) W2 regs2 mem2 14304) as HS2.
set (E2 := Eimg (Ereg regs2 [])) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = getr regs2 r)
  by (intros k r Hk; subst E2; apply ew_Eimg_Ereg_nat; exact Hk).
clear HS HF HFr HG.
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_TAIL.
{ intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
cbn [ms_mem mkst] in HFr, HG, HF.
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?y ?m] =>
  set (mdv2 := with_vm_backing (m_vm_lazy m) y m) in *; clearbody mdv2 end.
assert (Hmem2 : ms_mem ms = mem2).
{ apply functional_extensionality. intros y. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
assert (QK2 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [a9e_rreg HS2; rewrite a9e_den_atom0; apply EE2; reflexivity |]).
  destruct Hr. }
(* every register the TAIL cut names is callee-saved: the cut's value *)
assert (KF : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. pose proof Hr as Hr'. cbn [In] in Hr'.
  assert (Hcs : acallee_saved r) by (unfold acallee_saved; lia).
  rewrite (QK2 r Hr), (HP2 r Hcs). apply QK1. revert Hr. cbn [In]. tauto. }
pmkst HS2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
    with (cfg_at (fx := fx1) SEGS (BASE + PF_TAIL) rg mm mdx) end.
rewrite Hmem2. rewrite Hmem2 in HJ2.
pose proof (HT fx1) as HT1. unfold H_TAIL, PF_POSTr in HT1.
apply (HT1 (y_v x) (y_pos x) ly2 S2 W2 (ms_regs ms) mem2 mdv2
  (refuse (y_cf x) (y_ln x + 1) f [AS (y_nm x); AS w]) (y_cur x) (y_nm x)
  (pf_next (p_s (y_v x)) (y_o x)) (y_ln x + 1) (y_d x)).
destruct HMID as (Ho & Hn & HCTX).
pose proof (pf_next_skipn_lt (p_s (y_v x)) (y_o x) Ho) as HNX.
unfold INV_TAIL.
split; [|split; [exact HCTX|split; [lia|split]]].
- (* pf_base at TAIL: segment A6's rebuild after refuse *)
  apply (a6_base_move B VRO SSPX fx1 (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE ly2 S2 W2 (ms_regs ms)
    mem2 mdv2 HB Hfx1 HJ2 Hly2 HS2e HPERM2 HKP).
  intros r Hr. apply KF. revert Hr. cbn [In]. tauto.
- (* pf_st: c holds the refusal's state, cur and cur_name unchanged, the counters *)
  split; [exact HRC2|].
  split.
  { unfold pf_cur_ok in *. destruct (refuse_proj (y_cf x) (y_ln x + 1) f [AS (y_nm x); AS w]) as (Hseg & _).
    destruct (y_cur x); [rewrite Hseg; exact HCOK | exact I]. }
  split.
  { apply (a6_nm_move (y_v x) (y_pos x) (rdW Wc memc) (rdW W2 mem2) (y_nm x) HNM).
    intros a Ha. destruct HKP as (_ & _ & _ & K4). apply K4. left. exact Ha. }
  exact (pf_cnt_refuse (y_cf x) (y_ln x + 1) f [AS (y_nm x); AS w] (a9_k x) _ HNX HCNT).
- (* the registers: PF_RL, s5 = the next line, s10 = lineno, s4 = cur *)
  apply (a9e_rg_tr rX (ms_regs ms)).
  + refine (a5_rg_incl rX _ _ _ HRG).
    intros rv Hrv. unfold PF_RL, PF_RM, a9_cp in *. revert Hrv. cbn [app In]. tauto.
  + intros rv Hrv. apply KF. unfold PF_RL in Hrv. cbn [app In] in Hrv.
    repeat (destruct Hrv as [<- | Hrv]; [cbn [fst]; a9e_in |]). destruct Hrv.
Qed.

End e.
End f.
End d.
