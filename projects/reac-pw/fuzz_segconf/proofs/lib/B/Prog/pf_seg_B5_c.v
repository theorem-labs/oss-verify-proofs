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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 326 of its 384 lines of code are new or changed and 4995 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece C -> R5 (a B5 sub-lane of the image-B G3 walk owner, 2026-10-30): b5_c_ok : H_R5 B n -> H_C B n.
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk: segment B5's C piece; the
   function's rule-24 record is the rule-24 lookup record).
   ADAPTED from the image-A G3 walk owner's image-A lane, on a working branch (lib/A/Prog/pf_a7_w3_c.v w3_trim_step and
   pf_a7_w2.v w2_A / w2_body_str: trim through PaNoChain.cl_callS_wide, trim's post as a C string) and a
   B5 sub-lane of image B (pf_seg_B5_r3.v: the slot-0xd0 seed), re-derived on image B's code over B's kit
   lib/B/Prog/pf_seg_B5_k.v.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), call C11 of the plan:
     C  0x88388 `ld a0,208(s1)`   a0 = slot 0xd0 = buf (pf_pieces.v PF_SL, set at 0x881d4)
        0x8838c `jal trim`        the listing's pa_sigma SS_trim = BASE + AF_trim (Section hypothesis SIGP); trim's
                                  contract (TRIM, lib/B/Prog/trim_c.v) for the C string s' = r_strip_comment line in
                                  buf (INV_C); return 0x88390 = R5 with a0 = lp = buf + trim_lead s' and the C string
                                  pf_tline s o = r_trim s' at lp (pfA_facts.L_trim_holds).
   The proof: a seed at C (every register its own atom; the extra atom 32 = buf; slot 0xd0 read on s1's atom 9, no
   byte written), one run of the plain executor to the call (PaCallRun.paj_run_shc), trim's premises at the call
   (trim_pre: the string's bytes and NUL from INV_C, its tail and its range in the live class-5 frame by AR_laws'
   al_frames, buf addressable by the kit's b5_addr_buf, the destination by b5_fframe_buf), the call by
   PaNoChain.cl_callS_wide (trim writes one byte of buf, its NUL at trim_end_addr: the callee's footprint is an own
   frame byte, so cl_callS's RC_PARSE_W footprint premise does not hold; the frame chain at s1 by the kit's b5_chain),
   and INV_R5 at trim's return state, in trim's new world: pf_base by b5c_move (the kit's b5_move with the world
   free: the keep lemmas are reader-generic), pf_st by b5_keep_st, the trimmed line by b5c_body_str. 2 of B5's 116
   instructions walked (0x88388, 0x8838c), no check, no trap, one call (C11).
   Section hypotheses: SIGP (seg_sig_prog: the listing's program call targets), TRIM (trim_contract at image B's
   entry BASE + AF_trim and STK_trim). No SSPX, no VRO. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun PaSB PaArt PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c trim_c reac_segconf_parse_file_c
  SegInstB pf_pieces pf_seg_B5_d pf_seg_B5_k pf_seg_B5_hd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= pure facts ======================= *)
Lemma b5c_bv8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 8) with 256. lia.
Qed.
(* trim's post (the kept prefix and the NUL it stored) is the C string r_trim s at p + trim_lead s
   (pf_a7_w2.v w2_body_str) *)
Lemma b5c_body_str : forall (rd : reader) p s,
  ~ In 0 s -> (forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256) ->
  sa_bytes rd p (seg_spec.zb (firstn (seg_spec.trim_lead s + length (r_trim s)) s) ++ [seg_spec.ZERO]) ->
  sa_tail rd (p + Z.of_nat (seg_spec.trim_lead s) + Z.of_nat (length (r_trim s))) ->
  sa_str rd (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s).
Proof.
  intros rd p s Hn HR HB HT.
  destruct (L_trim_holds s Hn) as (Hle & Heq & Hnf).
  set (k := seg_spec.trim_lead s) in *. set (m := length (r_trim s)) in *.
  assert (HLF : length (seg_spec.zb (firstn (k + m) s)) = (k + m)%nat)
    by (unfold seg_spec.zb; rewrite length_map, length_firstn; lia).
  split; [split|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i m) as [Him|Him].
    + rewrite app_nth1 by lia.
      assert (Hidx : nth i (r_trim s) 0 = nth (k + i) s 0).
      { rewrite Heq at 1. rewrite nth_firstn.
        destruct (Nat.ltb_spec i m) as [_|Hc]; [|lia]. apply PaArt.nth_skipn_add. }
      rewrite Hidx.
      replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
      rewrite (HB (k + i)%nat ltac:(rewrite length_app, HLF; cbn [length]; lia)).
      rewrite app_nth1 by (rewrite HLF; lia).
      unfold seg_spec.zb, ZB0. rewrite (map_nth (Z_to_bv 8) (firstn (k + m) s) 0 (k + i)).
      rewrite nth_firstn. destruct (Nat.ltb_spec (k + i) (k + m)) as [_|Hc]; [|lia].
      rewrite b5c_bv8 by (apply HR; lia). reflexivity.
    + assert (i = m) as -> by lia.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      replace (p + Z.of_nat k + Z.of_nat m) with (p + Z.of_nat (k + m)) by lia.
      rewrite (HB (k + m)%nat ltac:(rewrite length_app, HLF; cbn [length]; lia)).
      rewrite app_nth2 by (rewrite HLF; lia). rewrite HLF, Nat.sub_diag. cbn [nth].
      reflexivity.
  - exact Hnf.
  - replace (p + Z.of_nat k + Z.of_nat m) with (p + Z.of_nat k + Z.of_nat (length (r_trim s))) by reflexivity.
    exact HT.
Qed.

(* the seed at C: every register its own atom; the extra atom 32 = buf, slot 0xd0 read on s1's atom 9 (no byte of
   that region written; pf_seg_B5_r3.v's seed) *)
Definition b5c_ss : sstate := mkSS B5_C sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xd0 0xd8 0xd0 0xd0 [YP09.mkChunk 0xd0 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []).

(* a register of the state after a run, as the executor wrote it (st_ok_pi after a plain run, st_ok after a run to a
   call) *)
Ltac b5c_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b5c_atoms := repeat (apply Forall_cons; [split; [cbn [fst]; lia | cbn [fst]; vm_compute; reflexivity] |]); apply Forall_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the listing's program call targets: pa_sigma SS_trim = BASE + AF_trim *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
(* trim's contract at image B's entry, at every FP state *)
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.

(* the registers a run left as their own atoms keep the values they had (pf_seg_B5_r3.v b5r3_rg_keep) *)
Lemma b5c_rg_keep : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok SEGS E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_restrict_reg SEGS H E ss ms _ HS), Hs, b5_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

(* every byte of the class-5 frame is mapped at a cut state (AR_laws' al_frames: a live frame's bytes are present) *)
Lemma b5c_frame_some : forall v pos lyc Sc Wc rX memc mdc sc a, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc a <> None.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc a HB Ha.
pose proof HB as (HCX & HFI & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (_ & Hin & EF & _ & HAR).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & Hpres & _).
apply (aview_some_of_apresent SEGS). apply Hpres. rewrite EF. change (fs_frame_bytes 5) with 2048. exact Ha.
Qed.
(* the bytes after a NUL inside buf up to the next 8-byte boundary (buf is 8-aligned and ends 8-aligned) *)
Lemma b5c_tail_buf : forall v pos lyc Sc Wc rX memc mdc sc e, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  b5_buf v pos <= e < b5_buf v pos + 512 -> sa_tail (rdW Wc memc) e.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc e HB He x Hx.
pose proof HB as (HCX & HFI & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & _).
pose proof G as (_ & _ & _ & _ & _ & _ & G7 & G8 & G9 & _).
unfold b5_buf, PF_O_BUF in He.
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
apply (b5c_frame_some v pos lyc Sc Wc rX memc mdc sc x HB). lia.
Qed.
(* the cut's events: trim spends none (the journal's events clause and pf_cx's bound) *)
Lemma b5c_ev : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  st_nev Sc + EV_trim <= EV_MAX.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof HB as (HCX & (HJ & _) & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
unfold EV_reac_segconf_parse_file in HEV. unfold EV_trim. lia.
Qed.

(* pf_base after a step that kept every byte off b5_Wr (and every visible byte visible), in the step's own world:
   the kit's b5_move with the world free (its keep lemmas are stated over any two readers) *)
Lemma b5c_move : forall v pos lyc Sc Wc rX memc mdc sc Sc' (W' : world SEGS) rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' W' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  b5_kept v pos (rdW Wc memc) (rdW W' memc') ->
  pf_rg rX' (b5_FI B v) ->
  pf_fsh (rdW W' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' W' rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc Sc' W' rX' memc' mdc' sc' HB HJ' [f HSf] HPerm K HRG HFSH.
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
destruct HFI as (_ & Hly & (f0 & HS0) & HP0 & HSV & HFL & HFRM & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply b5_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (b5_k_saved v pos HG _ _ K _ HSV)|].
  split; [exact (b5_k_flag v pos HG _ _ K _ HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [apply (b5_k_sl v pos HG _ _ K); [repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia | exact HC8]|].
  exact HRG. }
split.
{ pose proof (b5_keep_obj B v pos lyc Sc Wc memc mdc _ _ HG HAR Hin EF K HOBJ) as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (b5_k_sl v pos HG _ _ K _ (b5_PF_SL_rng v pos) HSL) | exact HFSH].
Qed.

(* ======================= C 0x88388 -> R5 0x88390 (trim, C11) ======================= *)
Lemma b5_c_ok : forall n, H_R5 B n -> H_C B n.
Proof.
intros n HR5 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HL512 & HZS & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & LS & HSTR & HADDR & HTH & HCH).
pose proof HLN as (HCTX & Ho & Hk & HST).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
destruct (b5_SHv v pos G) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (STT & _ & _ & ESTK & _).
assert (ES : ESTACK = 4096) by reflexivity.
pose proof alloc_ceiling_lt as Hac.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PI := PI)) as HBLO.
assert (Ebf : b5_buf v pos = pf_F v pos + 64) by reflexivity.
(* the string strip_comment left in buf: s' = r_strip_comment line, a prefix of the line, NUL-free *)
destruct (L_line_bytes_holds (p_s v) o NUL) as (_ & HLNZ & _).
destruct (L_strip_holds (pf_line (p_s v) o) HLNZ) as (kc & Hkc & Hsc & _ & _).
assert (HSL' : (length (r_strip_comment (pf_line (p_s v) o)) <= b5_len v o)%nat)
  by (rewrite Hsc, length_firstn; unfold b5_len; lia).
assert (HNZ' : ~ In 0 (r_strip_comment (pf_line (p_s v) o)))
  by (rewrite Hsc; apply nulfree_firstn; exact HLNZ).
destruct (L_trim_holds _ HNZ') as (HTle & HTeq & HTnf).
set (s' := r_strip_comment (pf_line (p_s v) o)) in *.
clear Hsc.
assert (HL' : Z.of_nat (length s') < 512) by lia.
(* the registers at C *)
rewrite b5_rg_app in HRG. destruct HRG as (HRL & HRM).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b5_rg rX _ 9 _ HRG0); b5_in).
(* slot 0xd0 = buf *)
assert (SD0 : rdword (rdW Wc memc) (pf_s1 v + 0xd0) = Some (b5_buf v pos)).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xd0, pf_F v pos + PF_O_BUF) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
(* the seed *)
set (E := Eimg (Ereg rX [w64 (b5_buf v pos)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (b5_buf v pos))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E b5c_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_C)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b5c_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xd0 8 (SOff 32 0) (b5_buf v pos)).
    + rewrite b5_den_atom0. exact E32.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + change (Z.of_N 8) with 8. lia.
    + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ SD0).
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + B5_C)) with (Z_to_bv 64 (BASE + B5_C)).
(* 0x88388 ld a0,208(s1); 0x8838c jal trim *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). vm_compute in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. lia. }
clear HFr HF HG.
(* the registers at the call *)
assert (QFI : pf_rg (ms_regs ms) (b5_FI B v)).
{ apply (b5c_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold b5_FI; b5c_atoms | exact HRG0]. }
assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln)).
{ apply (b5c_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold PF_RL, PF_RM; cbn [app]; b5c_atoms|].
  rewrite b5_rg_app. split; [exact HRL | exact HRM]. }
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B5_R5)).
{ b5c_rreg HS. rewrite (codeptr_val _ _ HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (b5_buf v pos)) by (b5c_rreg HS; rewrite b5_den_atom0; exact E32).
assert (Q2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b5_rg _ _ 2 _ QFI); unfold b5_FI; b5_in).
assert (Q3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (b5_rg _ _ 3 _ QFI); unfold b5_FI; b5_in).
assert (Q4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (b5_rg _ _ 4 _ QFI); unfold b5_FI; b5_in).
assert (Q8 : getr (ms_regs ms) (Z_to_bv 5 8) = w64 (pf_sp0 v)) by (apply (b5_rg _ _ 8 _ QFI); unfold b5_FI; b5_in).
assert (R1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + B5_R5)) by exact (b5hd_bvr _ 1%bv 1 _ eq_refl Q1).
assert (R3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (b5hd_bvr _ 3%bv 3 _ eq_refl Q3).
assert (R4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (b5hd_bvr _ 4%bv 4 _ eq_refl Q4).
assert (R8' : getr (ms_regs ms) 8 = w64 (pf_sp0 v)) by exact (b5hd_bvr _ 8%bv 8 _ eq_refl Q8).
assert (R10' : getr (ms_regs ms) 10 = w64 (b5_buf v pos)) by exact (b5hd_bvr _ 10%bv 10 _ eq_refl Q10).
assert (Qsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ rewrite (b5hd_spZ (ms_regs ms) (pf_s1 v) Q2) by lia. lia. }
assert (Hal16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by exact (b5_m16 _ _ G6 G3).
(* the cut state at the call (the run wrote nothing) *)
destruct (b5hd_step B v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdq 0 HB HJ
  ltac:(rewrite ES; lia) ltac:(intros a Ha _; exact (KM1 a Ha)) QFI) as (HB1 & _).
pose proof HB1 as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & HROD1 & _) & _).
(* trim's string: s' and its NUL in buf (INV_C), its tail and range in the live frame *)
assert (HZS1 : sa_zs (rdW Wc (ms_mem ms)) (b5_buf v pos) (s' ++ [0])).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite KM1; [exact (HZS i ltac:(rewrite length_app; cbn [length]; lia))|]. lia. }
assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) (b5_buf v pos) s').
{ split; [split; [exact HZS1 | exact HNZ'] |].
  apply (b5c_tail_buf v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE _ HB1). lia. }
assert (HA1 : sa_addr (rdW Wc (ms_mem ms)) (b5_buf v pos) (Z.of_nat (length s') + 1))
  by exact (b5_addr_buf B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq (b5_buf v pos) (Z.of_nat (length s') + 1) HB1
    ltac:(lia) ltac:(lia) ltac:(lia)).
assert (HFF1 : sa_fframe lyc Sc (b5_buf v pos) (Z.of_nat (length s') + 1))
  by exact (b5_fframe_buf B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE (b5_buf v pos)
    (Z.of_nat (length s') + 1) HB1 ltac:(lia) ltac:(lia) ltac:(lia)).
pose proof (b5c_ev v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HEV.
(* the frame chain at s1 *)
destruct (b5_chain B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE HB1) as [ch1 HCH1].
(* where trim writes its NUL *)
set (e := trim_end_addr (b5_buf v pos) s') in *.
assert (HeB : b5_buf v pos <= e < b5_buf v pos + 512) by (unfold e, trim_end_addr; lia).
pmkst HS.
rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_trim))
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0 STK_trim [(e, e + 1)] EV_trim
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B5_R5)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (b5_buf v pos + Z.of_nat (seg_spec.trim_lead s')) /\
       sa_bytes (rdW W2 mem2) (b5_buf v pos)
         (seg_spec.zb (firstn (seg_spec.trim_lead s' + length (r_trim s')) s') ++ [seg_spec.ZERO]) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) STK_trim (fun a => a = e) /\
       sa_noalloc B lyc Sc ly2 S2) HJ Qsp Hal16).
  - lia.
  - rewrite STT. lia.
  - rewrite STT, ESTK. lia.
  - exact R3'.
  - exact R4'.
  - exact R1'.
  - apply ret_ok_codeptr_v; [unfold B5_R5, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold B5_R5, AF_reac_segconf_parse_file; lia).
    unfold B5_R5, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite R8'. unfold w64. rewrite unsigned_lit_small by lia. exact HCH1.
  - intros HPRE1. eapply SRr_mono.
    { apply (TRIM fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq ch1 (b5_buf v pos) s' HPRE1).
      - exact HROD1.
      - exact R10'.
      - lia.
      - unfold trim_pre. split; [lia|]. split; [exact HSTR1|]. split; [exact HA1|]. split; [|lia].
        left. split; [exact HFF1 | exact (proj1 (proj2 (proj2 (proj2 HA1))))].
      - exact HEV. }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ').
    exists ly', S', regs', mem', md'. split; [rewrite R1'; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HQ'].
  - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite Hly. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos).
    change (fs_frame_bytes 5) with 2048. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. destruct Hr as [<- | []].
    cbn [fst snd] in Ha. exfalso. rewrite ESTK in Hw. lia. }
(* back at 0x88390, in trim's world W2 *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP & (H10' & HBY & HKP & HNA)).
destruct HNA as (HPerm & -> & HSf).
change (0 + EV_trim) with 0 in HJo.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B5_R5)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B5_R5) regs2 mem2 md2).
(* what trim kept: every byte off its window [s1 - STK_trim, s1) and off its NUL e *)
assert (HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - STK_trim <= a < pf_s1 v) -> a <> e ->
  rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hw Hne. rewrite (HKP a Ha); [exact (KM1 a Ha) | rewrite Qsp; lia | exact Hne]. }
assert (K : b5_kept v pos (rdW Wc memc) (rdW W2 mem2)).
{ split.
  - intros a Ha Hn. apply HK0; [exact Ha | |].
    + intros Hw. apply Hn. unfold b5_Wr. left. rewrite STT in Hw. rewrite ESTK. lia.
    + intros ->. apply Hn. unfold b5_Wr. right. left. exact HeB.
  - intros a Ha Hv.
    destruct (Z_lt_le_dec a (pf_s1 v - STK_trim)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
    + destruct (Z.eq_dec a e) as [-> | Hne].
      * assert (Hix : (seg_spec.trim_lead s' + length (r_trim s') <
            length (seg_spec.zb (firstn (seg_spec.trim_lead s' + length (r_trim s')) s') ++ [seg_spec.ZERO]))%nat).
        { unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
        pose proof (HBY _ Hix) as Ee. unfold e, trim_end_addr. rewrite Ee. discriminate.
      * rewrite (HK0 a Ha ltac:(lia) Hne). exact Hv.
    + pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
      apply (aview_some_of_apresent SEGS). apply Hpres. lia.
    + rewrite (HK0 a Ha ltac:(lia) ltac:(rewrite STT in Hlo; lia)). exact Hv. }
assert (HFSH2 : pf_fsh (rdW W2 mem2) (pf_SH v pos) PF_SC_LINE).
{ apply (b5_keep_fsh_same v pos _ _ PF_SC_LINE G K); [|exact HFSH].
  intros i Hi. apply HK0; [lia | rewrite STT; lia | lia]. }
assert (HRG2 : pf_rg regs2 (b5_FI B v)) by exact (b5_rg_pres _ _ _ HP (b5_FI_cs B v) QFI).
pose proof (b5c_move v pos lyc Sc Wc rX memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 PF_SC_LINE HB HJo HSf HPerm K
  HRG2 HFSH2) as HB2.
(* the trimmed line: trim's kept prefix and its NUL, the tail in the live frame *)
assert (HT2 : sa_tail (rdW W2 mem2) e) by exact (b5c_tail_buf v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE e HB2 HeB).
assert (HR' : forall i, (i < length s')%nat -> 0 <= nth i s' 0 < 256).
{ intros i Hi. assert (Hi' : (i < length (s' ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (HZS i Hi') as Ez. rewrite app_nth1 in Ez by lia. exact (sa_aview_rng SEGS (w_H Wc) memc _ _ Ez). }
assert (HBODY : sa_str (rdW W2 mem2) (b5_buf v pos + Z.of_nat (seg_spec.trim_lead s')) (r_trim s')).
{ apply (b5c_body_str (rdW W2 mem2) (b5_buf v pos) s' HNZ' HR' HBY).
  replace (b5_buf v pos + Z.of_nat (seg_spec.trim_lead s') + Z.of_nat (length (r_trim s'))) with e
    by (unfold e, trim_end_addr; lia).
  exact HT2. }
apply (HR5 v pos lyc S2 W2 regs2 mem2 md2 cf cur nm o ln d (b5_buf v pos + Z.of_nat (seg_spec.trim_lead s'))).
split; [exact HB2|].
split.
{ split; [exact HCTX|]. split; [exact Ho|]. split; [exact Hk|].
  exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm _ G HAR Hin EF K HCH HST). }
split; [exact HL512|].
change (pf_tline (p_s v) o) with (r_trim s').
split; [exact HBODY|].
split.
{ unfold pf_inb. split; lia. }
rewrite app_assoc. apply b5_rg_app. split.
- apply (b5_rg_pres (ms_regs ms) regs2 _ HP); [|exact QL].
  unfold PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
- unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  eapply b5hd_bvr2; [exact H10' | reflexivity].
Qed.
End e.
End f.
End d.
