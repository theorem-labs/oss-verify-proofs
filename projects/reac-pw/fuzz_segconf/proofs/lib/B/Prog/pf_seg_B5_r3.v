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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 333 of its 380 lines of code are new or changed and 5006 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece R3 -> LONG / R4 (the B5 segment lane of the image-B G3 walk owner, piece prover: a sub-lane, 2026-10-30):
   b5_r3_ok : H_LONG B n -> H_R4 B n -> H_R3 B n.
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk; the function's rule-24 record
   is the rule-24 lookup record).
   ADAPTED from the image-A G3 walk owner's image-A piece lib/A/Prog/pf_a5_r3.v (commit 003b9dc874eb, a5_r3_ok),
   re-derived on image B's code with the B5 kit (pf_seg_B5_k.v) and the template piece pf_seg_B5_r2.v (the
   B5 segment lane, 2305ce2c2c85). B differs from A here: buf comes from slot 0xd0 (A: 0xb8 through s4), the text pointer
   is s11 (A: s9), and B stores no cur slot before the call (A: `sd s4,0xb0(s1)`).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), reached from Q3 after meta_fill_00 put buf in
   scope (s11 = p = t + o, s7 = LEN):
     0x88250 `li a0,512`
     0x88254 `bltu s7,a0,0x882bc`  LEN >= 512 falls to LONG 0x88258 (INV_LONG: a0 = 512 is scratch);
     0x882bc `ld a0,208(s1)`       a0 = slot 0xd0 = buf (PF_SL)
     0x882c0 `mv a1,s11`           a1 = t + o
     0x882c4 `mv a2,s7`            a2 = LEN
     0x882c8 `jal checked_memcpy`  call C10, __asan_memcpy (pa_sigma SS___asan_memcpy), stepped by PaCall.aj_intrin_atS
                                   OCpy under AMEMCPY: destination buf[0 .. LEN) in the owned class-5 frame (awr_byte's
                                   in_frames clause), addressable (b5_addr_buf: buf's shadow cells are 0 under
                                   PF_SC_LINE); source the line's LEN bytes at t + o inside the text's live block
                                   (range_addressable_of_block, shadow_hull_vis_of_block), apart from buf (the block and
                                   the frame are disjoint, sep_block_frame); LEN < 512 < 2 ^ 32
   then R4 0x882cc: buf[0 .. LEN) = the text's bytes [o, o + LEN) = pf_line s o (pfA_facts.L_line_bytes_holds).
   6 of B5's 116 instructions walked (0x88250, 0x88254, 0x882bc .. 0x882c8), no inline check, no UBSan trap, one call
   (C10). Section hypothesis: AMEMCPY only. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B5_d pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of the state after a run, as the executor wrote it (st_ok_pi after a plain run, st_ok after a run to a
   call) *)
Ltac b5r3_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b5r3_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma b5r3_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b5r3_dec : forall x lo hi, (lo <= x < hi) \/ ~ (lo <= x < hi).
Proof.
intros x lo hi. destruct (Z_lt_le_dec x lo) as [H1 | H1]; [right; lia|].
destruct (Z_lt_le_dec x hi) as [H2 | H2]; [left; lia | right; lia].
Qed.
(* b5_text's 65535%nat is an abstract numeral that zify cannot read: its Z form *)
Lemma b5r3_le65535 : forall k : nat, (k <= 65535)%nat -> Z.of_nat k <= 65535.
Proof. intros k H. apply Nat2Z.inj_le in H. exact H. Qed.
Lemma b5r3_nth_skipn : forall {A} (l : list A) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
intros A l k. revert l. induction k as [|k IH]; intros [|x l] i d; cbn; try reflexivity; [destruct i; reflexivity | apply IH].
Qed.

(* the seed at R3: every register its own atom; the extra atom 32 = buf, slot 0xd0 read on s1's atom 9 (no byte of
   that region written) *)
Definition b5r3_ss : sstate := mkSS B5_R3 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xd0 0xd8 0xd0 0xd0 [YP09.mkChunk 0xd0 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []).

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
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* the registers a run left as their own atoms keep the values they had (pf_a5_r3.v r3_rg_keep / r3_rg_keep_pi) *)
Lemma b5r3_rg_keep : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
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
Lemma b5r3_rg_keep_pi : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hs, b5_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Ltac b5r3_atoms := repeat (apply Forall_cons; [split; [cbn [fst]; lia | cbn [fst]; vm_compute; reflexivity] |]); apply Forall_nil.

(* pf_base at the same frame state after a run that kept every byte (pf_seg_B5_r2.v b5r2_base_same) *)
Lemma b5r3_base_same : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (b5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' HB HJ' KM HRG.
pose proof HB as (HCX & HFI & _ & _ & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & _).
pose proof HFI as (_ & _ & (f0 & HS0) & _).
assert (K : b5_kept v pos (rdW Wc memc) (rdW Wc memc')).
{ split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
apply (b5_move B v pos lyc Sc Wc rX memc mdc sc Sc rX' memc' mdc' sc HB HJ').
- exists f0. rewrite HS0. rewrite b5_set_fs2. reflexivity.
- apply Permutation_refl.
- exact K.
- exact HRG.
- destruct (b5_SHv v pos HG) as (_ & SH1 & SH2 & _).
  intros i Hi. rewrite (KM (pf_SH v pos + i)) by lia. exact (HFSH i Hi).
Qed.

Lemma b5_r3_ok : forall n, H_LONG B n -> H_R4 B n -> H_R3 B n.
Proof.
intros n HLONG HR4 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & LS & HSTR & HADDR & HTH & HCH).
pose proof (b5r3_le65535 _ LS) as HLSZ.
pose proof HLN as (HCTX & Ho & Hk & HST).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
assert (ES : ESTACK = 4096) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite ESTK in Hpres.
destruct (b5_SHv v pos G) as (ESH & SH1 & SH2 & F8).
pose proof (pf_line_len_le (p_s v) o) as HLL. rewrite pfa_len_skipn in HLL.
assert (HLEN : (b5_len v o <= length (p_s v))%nat) by (unfold b5_len; lia).
pose proof (proj1 (Nat2Z.inj_le _ _) HLEN) as HLZ.
pose proof HADDR as (Ht0 & Ht63 & Htam & _).
unfold pf_len in Ht63, Htam.
assert (Ebf : b5_buf v pos = pf_F v pos + 64) by reflexivity.
(* slot 0xd0 = buf *)
assert (SD0 : rdword (rdW Wc memc) (pf_s1 v + 0xd0) = Some (b5_buf v pos)).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xd0, pf_F v pos + PF_O_BUF) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
(* the text: its bytes, its block, the block apart from the frame *)
pose proof HSTR as ((HZS & _) & _).
pose proof HTH as (bt & mt & Hbt & Ht1 & Ht2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & _ & _ & _ & _ & _ & Hmt).
pose proof (req_size_pos mt (proj1 Hmt)) as [_ Hmtr].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bt mt 5 pos HAR Hbt Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
assert (TXT : forall a, p_t v <= a < p_t v + pf_len v -> b5_out v pos a)
  by (intros a Ha; exact (b5_out_sa_heap B v pos lyc Sc Wc memc mdc _ _ a G HAR Hin EF HTH Ha)).
assert (TXV0 : forall j, (j < b5_len v o)%nat ->
    rdW Wc memc (p_t v + Z.of_nat o + Z.of_nat j) = Some (nth j (pf_line (p_s v) o) 0)).
{ intros j Hj. unfold b5_len in Hj.
  replace (p_t v + Z.of_nat o + Z.of_nat j) with (p_t v + Z.of_nat (o + j)) by lia.
  rewrite (HZS (o + j)%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia.
  destruct (L_line_bytes_holds (p_s v) o NUL) as (LB1 & _ & _).
  rewrite LB1. rewrite nth_firstn. destruct (Nat.ltb_spec j (length (pf_line (p_s v) o))) as [_ | Hc0]; [|lia].
  rewrite b5r3_nth_skipn. reflexivity. }
(* the registers at R3 *)
rewrite b5_rg_app in HRG. destruct HRG as (HRL & HRR). rewrite b5_rg_app in HRR. destruct HRR as (HRM & HRT).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b5_rg rX _ 9 _ HRG0); b5_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (Z.of_nat (b5_len v o))) by (apply (b5_rg rX _ 23 _ HRT); b5_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (p_t v + Z.of_nat o)) by (apply (b5_rg rX _ 27 _ HRT); b5_in).
(* the seed *)
set (E := Eimg (Ereg rX [w64 (b5_buf v pos)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (b5_buf v pos))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat (b5_len v o))) by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (E27 : ew E 27 = Z_to_bv 64 (p_t v + Z.of_nat o)) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); exact R27).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E b5r3_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_R3)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b5r3_ss. apply pa_entry_st_ok_full.
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
unfold cfg_at. change (w64 (BASE + B5_R3)) with (Z_to_bv 64 (BASE + B5_R3)).
(* 0x88250 `li a0,512`, up to the length test 0x88254 *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr & Ha). unfold b5r3_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b5r3_clear_md.
rename ms into ms1, HG into HG1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem b5r3_ss) (w_H Wc) memc (ms_mem ms1) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. lia. }
clear HFr HF.
(* 0x88254 `bltu s7,a0` *)
psrr_branch_pi RUNP BR HS.
- (* LEN < 512: 0x882bc .. the memcpy call 0x882c8 *)
  assert (HL512 : (b5_len v o < 512)%nat).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom E 23 (Z.of_nat (b5_len v o)) E23) in Hc by lia.
    rewrite U_lit in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { intros a (r & Hr & Ha). vm_compute in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. lia. }
  b5r3_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms1) (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  clear HFr HF HG HG1.
  pose proof HJ as (HART & _).
  (* the registers at the call *)
  assert (QFI : pf_rg (ms_regs ms) (b5_FI B v)).
  { apply (b5r3_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold b5_FI; b5r3_atoms | exact HRG0]. }
  assert (Q2 : getr (ms_regs ms) (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b5_rg _ _ 2 _ QFI); unfold b5_FI; b5_in).
  assert (Q3 : getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (b5_rg _ _ 3 _ QFI); unfold b5_FI; b5_in).
  assert (Q4 : getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (b5_rg _ _ 4 _ QFI); unfold b5_FI; b5_in).
  assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B5_R4)).
  { b5r3_rreg HS. rewrite (codeptr_val _ _ HEI). reflexivity. }
  assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (b5_buf v pos)) by (b5r3_rreg HS; rewrite b5_den_atom0; exact E32).
  assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (p_t v + Z.of_nat o)) by (b5r3_rreg HS; rewrite b5_den_atom0; exact E27).
  assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (Z.of_nat (b5_len v o))) by (b5r3_rreg HS; rewrite b5_den_atom0; exact E23).
  assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln ++ [(23, Z.of_nat (b5_len v o))])).
  { apply (b5r3_rg_keep E _ ms (w_H Wc) rX _ HS EE); [unfold PF_RL, PF_RM; cbn [app]; b5r3_atoms|].
    rewrite !b5_rg_app. split; [exact HRL | split; [exact HRM|]].
    unfold pf_rg. apply Forall_cons; [cbn [fst snd]; exact R23 | apply Forall_nil]. }
  assert (Qsp : spZ (ms_regs ms) = pf_s1 v).
  { unfold spZ. rewrite (b5r3_bvr (ms_regs ms) 2%bv 2 _ eq_refl Q2). unfold w64. rewrite unsigned_lit_small by lia.
    reflexivity. }
  (* the state at the call is the cut's: buf is addressable there *)
  assert (HB1 : pf_base B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv0 PF_SC_LINE)
    by exact (b5r3_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdv0 HB HJ KM QFI).
  destruct (b5_addr_buf B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv0 (b5_buf v pos) (Z.of_nat (b5_len v o)) HB1
    ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & BA1 & BA2 & BA3).
  (* the text's bytes at the call *)
  assert (TXV : forall j, (j < b5_len v o)%nat ->
      rdW Wc (ms_mem ms) (p_t v + Z.of_nat o + Z.of_nat j) = Some (nth j (pf_line (p_s v) o) 0)).
  { intros j Hj. rewrite KM; [exact (TXV0 j Hj)|]. unfold b5_len in Hj. lia. }
  pmkst HS.
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx) Wc (ms_regs ms)
      (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
      (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0 (b5_buf v pos) (p_t v + Z.of_nat o) (Z.of_nat (b5_len v o))
      (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B5_R4)) HJ).
    - apply (b5r3_bvr _ _ 10); [reflexivity | exact Q10].
    - apply (b5r3_bvr _ _ 11); [reflexivity | exact Q11].
    - apply (b5r3_bvr _ _ 12); [reflexivity | exact Q12].
    - lia.
    - lia.
    - lia.
    - rewrite Qsp. lia.
    - apply b5_m16; [exact G6 | exact G3].
    - lia.
    - rewrite ESTK, ES. lia.
    - apply (b5r3_bvr _ _ 3); [reflexivity | exact Q3].
    - apply (b5r3_bvr _ _ 4); [reflexivity | exact Q4].
    - apply (b5r3_bvr _ _ 1); [reflexivity | exact Q1].
    - apply ret_ok_codeptr_v; [unfold B5_R4, AF_reac_segconf_parse_file; lia | reflexivity].
    - intros a Ha. split.
      + right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
        rewrite EF. change (fs_frame_bytes 5) with 2048. lia.
      + rewrite ES. lia.
    - intros a Ha Hfp _. exfalso. apply b5_rcw_in in Hfp.
      destruct (b5_out_sa_heap B v pos lyc Sc Wc memc mdc _ _ a G HAR Hin EF HCH Hfp) as (_ & _ & Hno).
      apply Hno. lia.
    - exact BA1.
    - exact BA2.
    - exact BA3.
    - cbv iota. split; [lia|]. split; [unfold pf_len, b5_len in *; lia|]. split.
      { intros a Ha. split.
        - replace a with (p_t v + Z.of_nat o + Z.of_nat (Z.to_nat (a - (p_t v + Z.of_nat o)))) by lia.
          rewrite TXV by (unfold b5_len in *; lia). discriminate.
        - rewrite Qsp, ES. destruct (TXT a ltac:(unfold pf_len, b5_len in *; lia)) as (Ha1 & _). lia. }
      split; [unfold pf_len, b5_len in *; lia|].
      split; [unfold amem_range in *; unfold b5_len in *; lia|].
      split.
      + eapply (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) _ bt mt);
          [exact HART | exact Hbt | lia | unfold pf_len, b5_len in *; lia].
      + intros H0. eapply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) _ bt mt);
          [exact HART | exact Hbt | lia | unfold pf_len, b5_len in *; lia | exact H0]. }
  cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HCPY & HKEEP & _ & _).
  cbv beta iota in HCPY.
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B5_R4)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + B5_R4) regs2 mem2 md2).
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HKEEP by lia.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  rewrite ESTK in Hpres2.
  (* what the call kept: every byte off buf[0 .. LEN) and its own stack window below s1 *)
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ (b5_buf v pos <= a < b5_buf v pos + Z.of_nat (b5_len v o)) ->
      ~ (pf_s1 v - ESTACK <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha H1 H2. rewrite (HKEEP a Ha H1 H2). exact (KM a Ha). }
  assert (KP : b5_kept v pos (rdW Wc memc) (rdW Wc mem2)).
  { split.
    - intros a Ha Hn. apply KX; [exact Ha | |]; intros Hq; apply Hn; unfold b5_Wr.
      + right; left. lia.
      + left. rewrite ES in Hq. rewrite ESTK. lia.
    - intros a Ha Hv.
      destruct (b5r3_dec a (pf_sp0 v - 12832) (pf_sp0 v)) as [Dw | Dw].
      { apply (aview_some_of_apresent SEGS). apply Hpres2. exact Dw. }
      destruct (b5r3_dec a (b5_buf v pos) (b5_buf v pos + Z.of_nat (b5_len v o))) as [Db | Db].
      { replace a with (b5_buf v pos + (a - b5_buf v pos)) by lia. rewrite HCPY by lia.
        replace (p_t v + Z.of_nat o + (a - b5_buf v pos))
          with (p_t v + Z.of_nat o + Z.of_nat (Z.to_nat (a - b5_buf v pos))) by lia.
        rewrite TXV by lia. discriminate. }
      rewrite KX; [exact Hv | exact Ha | exact Db | rewrite ES; lia]. }
  apply (HR4 v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d).
  split; [|split; [|split; [|split]]].
  + apply (b5_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc regs2 mem2 md2 PF_SC_LINE HB HJ2).
    * destruct HSc as (f0 & HS0). exists f0. rewrite HS0. rewrite b5_set_fs2. reflexivity.
    * apply Permutation_refl.
    * exact KP.
    * exact (b5_rg_pres (ms_regs ms) regs2 _ HP2 (b5_FI_cs B v) QFI).
    * apply (b5_keep_fsh_same v pos _ _ PF_SC_LINE G KP); [|exact HFSH].
      intros i Hi. apply KX; [lia | rewrite Ebf; lia | rewrite ES; lia].
  + split; [exact HCTX|]. split; [exact Ho|]. split; [exact Hk|].
    exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm _ G HAR Hin EF KP HCH HST).
  + exact HL512.
  + intros i Hi. rewrite HCPY by (unfold b5_len in *; lia). exact (TXV i Hi).
  + apply (b5_rg_pres (ms_regs ms) regs2 _ HP2); [|exact QL].
    unfold PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
- (* LEN >= 512: LONG 0x88258 *)
  assert (HL512 : (512 <= b5_len v o)%nat).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom E 23 (Z.of_nat (b5_len v o)) E23) in Hc by lia.
    rewrite U_lit in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_sh RUNTO HS HJ PF_LONG.
  { intros a (r & Hr & Ha). vm_compute in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. lia. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b5r3_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms1) (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  clear HFr HF HG HG1.
  assert (QFI : pf_rg (ms_regs ms) (b5_FI B v)).
  { apply (b5r3_rg_keep_pi E _ ms (w_H Wc) rX _ HS EE); [unfold b5_FI; b5r3_atoms | exact HRG0]. }
  assert (QL : pf_rg (ms_regs ms) (PF_RL v pos ++ PF_RM v o ln ++
      [(27, p_t v + Z.of_nat o); (23, Z.of_nat (b5_len v o))])).
  { apply (b5r3_rg_keep_pi E _ ms (w_H Wc) rX _ HS EE); [unfold PF_RL, PF_RM; cbn [app]; b5r3_atoms|].
    rewrite !b5_rg_app. split; [exact HRL | split; [exact HRM | exact HRT]]. }
  assert (KP : b5_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_LONG) rg mm mdx) end.
  rewrite (b5_post_step B v cf cur nm o ln Ho).
  apply (HLONG v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ cf cur nm o ln (d ++ [pf_line (p_s v) o])).
  split; [|split; [|split; [|split]]].
  + exact (b5r3_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) _ HB HJ KM QFI).
  + exact (b5_mid n v pos (rdW Wc memc) cf cur nm o ln d NUL HLN).
  + exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm _ G HAR Hin EF KP HCH HST).
  + exact HL512.
  + exact QL.
Qed.
End e.
End f.
End d.
