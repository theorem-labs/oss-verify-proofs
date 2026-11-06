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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 583 of its 656 lines of code are new or changed and 4980 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B11b_a.v, with its module paths and module names changed; 483 of its 554 lines of code are new or changed and 585 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the RBT cut of segment B11a of
   reac_segconf_parse_file's walk, b11_rbt_ok : (RS1 at every FP state) -> HA_MISS n -> B11_RBT_stmt n
   (lib/B/Prog/pf_seg_B11a_k.v, lib/B/Prog/pf_pieces.v); the B11a segment lane of the image-B G3 walk owner (a piece sub-lane), 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, B11a's RBT cut: miss branch and first snprintf)

   WHAT IT PROVES. From RBT (0x889dc, reac_box_catalogue_by_token's return, a0 = cat_ptr catA (by_token low)):
   - the MISS branch (by_token = None, a0 = 0): `beqz a0` taken to MISS 0x88a50, nothing written, INV_MISS rebuilt
     from b11_cx (b11_cx_move) and the registers the run keeps; the post is H_MISS's (b11_step's None branch);
   - the HIT branch (by_token = Some i, a0 = catA + 0x128 i <> 0): the token run 0x889dc .. 0x88a04
       0x889dc beqz a0 (not taken: a0's fact [1, 2^64 - 1]); 0x889e0 ld a0,192(s1) (slot 0xc0 = cur);
       0x889e4 andi a0,a0,3; 0x889e8 bnez a0 -> 0x891c8 (UBSan trap T22, not taken: cur's fact al2 = 2, from
       pf_tf's c mod 16 = 0 and cur = c + 356 gi, 356 = 4 * 89); 0x889ec ld s3,192(s1); 0x889f0 a0 = cur + 36;
       0x889f4 / 0x889f8 a2 = 0x21340 "%s" (A_OBJ 35 by VO); 0x889fc a1 = 24; 0x88a00 ld a3,144(s1) (slot 0x90 =
       model low F + 0x2e0); 0x88a04 jal snprintf
     then snprintf(cur->model, 24, "%s", low) (row 4, ASNPRINTF, through pf_seg_B11a_h_t.v's b11ht_aj_snprintf_atSF:
     the destination [cur + 36, cur + 60) in c's table, the footprint RC_PARSE_W c's first range; the format by
     pf_obj's sa_lit; the argument low by INV_RBT's sa_str and b11_ra_frame), and at the return 0x88a08 (FP state fx1,
     fxrel fx fx1) INV_RS1: c holds b11_cf1 cf gi val (pf_seg_B11a_h_t.v's b11ht_rconf_model1: T = r_low val 0 24,
     |T| <= 23, snprintf_s 24 F_s [AS T] = T by b11f_snprintf_low, the bytes T ++ [0] at cur + 36, every other byte
     of c kept), pf_base at fx1 (b11_move with cw = b11_cw v gi, then the rounding mode of fx1), the rest of b11_cx
     by the keep lemmas, s3 = cur by aregs_preserved; RS1 at fx1, lifted to fx by srr_apost_baseF_lift.
   The instruction pcs walked: 0x889dc (both branches), 0x889e0, 0x889e4, 0x889e8, 0x889ec, 0x889f0, 0x889f4,
   0x889f8, 0x889fc, 0x88a00, 0x88a04 (the call). No inline ASan check lies on these pcs. The one UBSan trap, T22
   0x889e8, is decided not taken by the token executor from the seed's alignment fact on cur. The ASan premises of
   the snprintf call: the destination's shadow and amem by pf_obj's sa_addr c SEG_C_SIZE (sub-ranges), its
   footprint by RC_PARSE_W c and c's live block, off the image by b11_G's off_img c; the argument's shadow by
   b11_ra_frame (model low's cells 0x5c .. 0x5e in scope at PF_SC_L146) and shadow_hull_vis_of_frame, its amem by
   b11_G's frame range; the format's by sa_lit's pinned view; the read-only view by pf_obj's arodata_okP, the guard
   cells by pf_obj's sa_ssp, the rounding mode by pf_fi's sa_frm0; every window apart by b11_G's numbers.
   Section hypotheses: ASNPRINTF (snprintf's contract at every FP state) and VO : seg_val_objs (the literal "%s" at
   A_OBJ 35).

   ADAPTED from a working branch + U piece walks; templates lib/B/Prog/pf_seg_B3_p1.v (the B3 segment lane,
   a lane branch f5fd160e1686: the seed with slot chunks on s1, paj_run_tok to a snprintf call, the call through
   the journal and the state after it), lib/B/Prog/pf_seg_B11a_m.v (the B11a segment lane, a lane branch db5280e50cc6:
   the registers kept by a run, b11_move with the keep lemmas, the next cut rebuilt), the released fuzz_command
   check_reply_s4.v (origin/ossv/recipes 501c0d516c69: the snprintf call and the FP-state lift). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11a_k pf_seg_B11a_g
  pf_seg_B11a_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B11a_h_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B3_p1.v's, pf_seg_B11a_m.v's) ---------- *)
Lemma b11h_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b11h_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b11h_set_fs_id : forall s, set_fs (st_fs s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
(* the shadow hull of a sub-range lies in the hull of the range (lib/B/Prog/trim_s.v tr_hull_sub) *)
Lemma b11h_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 Hn s Hs. apply H.
pose proof (Z.div_le_mono (shadow_addr x) (shadow_addr x') 8 ltac:(lia) (shadow_mono x x' H1)) as D1.
pose proof (Z.div_le_mono (shadow_addr (x' + n' - 1)) (shadow_addr (x + n - 1)) 8 ltac:(lia)
  (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia))) as D2.
lia.
Qed.
(* a reader that agrees on every address keeps a C string and an addressable range *)
Lemma b11h_same_str : forall (rd rd' : reader) p s, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  0 <= p -> p + Z.of_nat (length s) + 8 <= 2 ^ 64 -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s HK H0 H1 [[Hz Hn] Ht]. split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HK by lia. exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). rewrite HK by lia. exact (Ht x Hx).
Qed.
Lemma b11h_same_addr : forall (rd rd' : reader) q n, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HK (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split.
- intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HK; [exact Hs|].
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 63) ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF. lia.
- intros Hn s Hs. rewrite HK; [exact (H4 Hn s Hs)|].
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  lia.
Qed.
Lemma b11h_cspan : forall w (T : list Z), Z.of_nat (length T) + 1 <= seg_spec.cstr_span w T <= Z.of_nat (length T) + 8.
Proof.
intros w T. unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length T) + 1)) 8 ltac:(lia)). lia.
Qed.
(* model low's three cells are 0x00 in PF_SC_L146 *)
Lemma b11h_shb_l146 : forall i, 0x5c <= i < 0x5f -> pf_shb PF_SC_L146 i = 0.
Proof.
intros i Hi. assert (i = 0x5c \/ i = 0x5d \/ i = 0x5e) as [-> | [-> | ->]] by lia; vm_compute; reflexivity.
Qed.
Ltac b11h_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b11h_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac b11h_ro_awr := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac b11h_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b11h_getq QR k := apply (b11h_bvr _ _ k); [reflexivity | apply (b11_rg_get _ _ _ _ QR); solve [b11h_in]].

(* ---------- the seeds at RBT (0x889dc) ---------- *)
(* MISS: every register its own atom, a0 pinned to 0 *)
Definition b11h_ss0 : sstate := mkSS B11_RBT (sr_set sr_atoms (Z_to_bv 5 10) (SLit 0)) [] None (mkFacts [] [] []).
(* HIT: every register its own atom, atom 32 = model low (slot 0x90), atom 33 = cur (slot 0xc0, 4-aligned), a0 in
   [1, 2^64 - 1]; the region: slots 0x90 .. 0xc8 of s1, read-only *)
Definition b11h_r1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0xc8 0x90 0x90
  [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0))].
Definition b11h_ss1 : sstate := mkSS B11_RBT sr_atoms [b11h_r1] None
  (mkFacts [(10%nat, mkAF 1 (2 ^ 64 - 1) 0); (33%nat, PTR 2)] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* pf_pieces.v's hypotheses for B11a's first snprintf, and the listing's object atoms (B's SegObj) *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis VO : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma b11h_obj35 : forall E, img_env VAL A_LIM E -> ew E 276%nat = w64 (seg_litA_rc F_s).
Proof.
intros E HE. rewrite (img_env_atomP E 276%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 276%nat with (A_OBJ 35). rewrite (VO 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* pf_base at another FP state: its only FP conjunct is pf_fi's rounding mode *)
Lemma b11h_base_fx : forall (fa fb : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc,
  pf_base (fx := fa) B v pos lyc Sc Wc rX memc mdc sc -> sa_frm0 (fx := fb) ->
  pf_base (fx := fb) B v pos lyc Sc Wc rX memc mdc sc.
Proof.
intros fa fb v pos lyc Sc Wc rX memc mdc sc (HCX & (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8 & H9 & H10) & HO & HS & HF) Hf.
exact (conj HCX (conj (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj Hf (conj H8 (conj H9 H10)))))))))
  (conj HO (conj HS HF)))).
Qed.

Section x. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Lemma b11h_seed0 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc,
  getr rX (Z_to_bv 5 10) = w64 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b11h_ss0
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B11_RBT)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc R10. rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (mkSS B11_RBT sr_atoms [] None (mkFacts [] [] []))
  (mkst rX (Z_to_bv 64 (BASE + B11_RBT)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) 0 HS0 R10 eq_refl).
Qed.

Lemma b11h_seed1 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 low cur a0,
  getr rX (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 0xc8 <= 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0x90) = Some low -> 0 <= low < 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0xc0) = Some cur -> 4096 <= cur <= 140737479966720 -> cur mod 4 = 0 ->
  getr rX (Z_to_bv 5 10) = w64 a0 -> 1 <= a0 < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 low; w64 cur])) b11h_ss1
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B11_RBT)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 low cur a0 R9 H0 H1 Hl Hl0 Hc Hc1 Hc4 R10 Ha0.
set (E := Eimg (Ereg rX [w64 low; w64 cur])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = a0)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 low) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 cur) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U33 : bv_unsigned (ew E 33) = cur) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (RG : region_ok SEGS E (mrestrict (w_H Wc) memc) b11h_r1).
{ unfold region_ok, b11h_r1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|constructor]].
  - apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x90 8 (SOff 32 0) low).
    + rewrite b11h_den_atom0, E32. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact Hl.
  - apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0xc0 8 (SOff 33 0) cur).
    + rewrite b11h_den_atom0, E33. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact Hc. }
rewrite restrict_mkst_fx. unfold b11h_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [exact RG | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10, Z.pow_0_r, Z.mod_1_r; lia|].
  split; [|exact I].
  unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite U33. change (2 ^ 2) with 4. lia.
Qed.

(* ---------- the MISS branch: RBT -> MISS (0x88a50) ---------- *)
Lemma b11h_miss : forall n, HA_MISS B n ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_RBT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  by_token (r_low val 0 24) = None ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_RBT) rX memc mdc) (b11_post B v cf gi nm val o ln).
Proof.
intros n HMISS v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI Hbt.
destruct HI as (HCX & _ & HRG).
pose proof HCX as (HB & _).
pose proof HB as (_ & HFI & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
unfold b11_post, b11_step. rewrite Hbt.
rewrite Hbt in HRG. cbn [seg_spec.cat_ptr] in HRG. unfold PF_RL, PF_RM in HRG.
assert (R10 : getr rX (Z_to_bv 5 10) = w64 0) by (apply (b11_rg_get rX _ 10 _ HRG); b11h_in).
pose proof (b11h_seed0 Wc rX memc R10) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B11_RBT)) with (Z_to_bv 64 (BASE + B11_RBT)).
(* 0x889dc beqz a0 (a0 = 0): taken, to MISS *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_MISS.
{ b11h_ro_awr. }
b11h_clear_md.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
assert (KP : b11_kept v pos false None (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b11h_rreg HS; rewrite b11h_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (QFI : pf_rg (ms_regs ms) (b11_FI B v)).
{ unfold pf_rg, b11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b11_rg_get rX _ _ _ HRG0); b11h_in | b11h_in]). }
pose proof (b11_cx_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc Wc (ms_regs ms) (ms_mem ms) mdv
  HCX HJ ltac:(exists (st_fs Sc); symmetry; apply b11h_set_fs_id) (Permutation_refl _) KP QFI)
  as (HB2 & HMID2 & HST2 & HSTR2 & HINB2 & HSL2).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_MISS) rg mm mdx) end.
apply (HMISS fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val).
split; [exact HB2|]. split; [exact HMID2|]. split; [exact HST2|]. split; [exact HSTR2|]. split; [exact HINB2|].
split; [exact Hbt|]. split; [exact HSL2|].
unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  (rewrite QK; [apply (b11_rg_get rX _ _ _ HRG); b11h_in | b11h_in]).
Qed.

(* ---------- the HIT branch, the run: RBT -> the snprintf call at 0x88a04 ---------- *)
Ltac b11h_regq HS EE E32 E33 HEI RG1 RG2 :=
  lazymatch goal with |- getr (ms_regs ?ms) (Z_to_bv 5 ?k) = _ =>
    let Rk := fresh "Rk" in prreg HS (Z_to_bv 5 k) Rk; rewrite Rk; clear Rk end;
  first
  [ exact (b11h_obj35 _ HEI)
  | exact E32
  | exact E33
  | reflexivity
  | rewrite E33; unfold w64; rewrite unsigned_lit_small by lia; f_equal; unfold seg_spec.RS_MODEL; lia
  | lazymatch goal with |- ew _ ?n = _ => let z := eval cbv in (Z.of_nat n) in rewrite (EE n (Z_to_bv 5 z) eq_refl) end;
    first [apply (b11_rg_get _ _ _ _ RG1); solve [b11h_in] | apply (b11_rg_get _ _ _ _ RG2); solve [b11h_in]] ].

Definition b11h_QL (v : pfv) (pos : Z) (o : nat) (ln : Z) (gi : nat) : list (Z * Z) :=
  [(10, seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL); (11, 24); (12, seg_litA_rc F_s);
   (13, pf_F v pos + PF_O_L146); (19, seg_spec.rseg_addr (p_c v) gi)] ++
  b11_FI B v ++ PF_RL v pos ++ PF_RM v o ln.

Lemma b11h_run1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i (Q : world SEGS -> config -> Prop),
  INV_RBT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  by_token (r_low val 0 24) = Some i ->
  (forall regsT memT mdT,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
     pf_rg regsT (b11h_QL v pos o ln gi) ->
     getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B11_RET_SN1) ->
     SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B11_RBT) rX memc mdc) Q.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i Q HI Hbt Kc.
destruct HI as (HCX & _ & HRG).
pose proof HCX as (HB & _ & HST & _).
pose proof HB as (_ & HFI & _ & HSL & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & _ & HRG0).
pose proof (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (GG & _).
pose proof GG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _ & C16 & C4 & Cc & _).
pose proof asan_consts as (A1 & _).
pose proof HST as (HRC & HCUR & _ & _ & HC0).
assert (Hgi : (gi < length (rc_seg cf))%nat) by exact HCUR.
assert (Hgi32 : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & Hn32 & _)); lia).
pose proof (b11f_by_token_lt _ _ Hbt) as Hi11.
pose proof pf_B_values as (_ & _ & EcatA & _).
assert (ESZ : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ECUR : seg_spec.rseg_addr (p_c v) gi = p_c v + 356 * Z.of_nat gi) by reflexivity.
assert (Hcurb : 4096 <= seg_spec.rseg_addr (p_c v) gi <= 140737479966720) by lia.
assert (Hc4 : seg_spec.rseg_addr (p_c v) gi mod 4 = 0).
{ rewrite ECUR. apply Z.mod_divide in C16 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 16 + 356 * Z.of_nat gi) with ((4 * q + 89 * Z.of_nat gi) * 4) by lia. apply Z_mod_mult. }
rewrite Hbt in HRG. unfold PF_RL, PF_RM in HRG.
assert (Ha0 : 1 <= seg_spec.cat_ptr catA (Some i) < 2 ^ 64)
  by (unfold seg_spec.cat_ptr, pin_spec.CAT_ROW; rewrite EcatA; lia).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b11_rg_get rX _ 9 _ HRG0); b11h_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (seg_spec.cat_ptr catA (Some i))) by (apply (b11_rg_get rX _ 10 _ HRG); b11h_in).
assert (Hlow : rdword (rdW Wc memc) (pf_s1 v + 0x90) = Some (pf_F v pos + PF_O_L146))
  by (apply (b11_slot_get _ _ _ 0x90 _ HSL); unfold PF_SL; b11h_in).
pose proof (b11h_seed1 Wc rX memc (pf_s1 v) (pf_F v pos + PF_O_L146) (seg_spec.rseg_addr (p_c v) gi)
  (seg_spec.cat_ptr catA (Some i)) R9 ltac:(lia) ltac:(lia) Hlow ltac:(unfold PF_O_L146; lia) HC0 Hcurb Hc4 R10 Ha0)
  as HS.
set (E0 := Eimg (Ereg rX [w64 (pf_F v pos + PF_O_L146); w64 (seg_spec.rseg_addr (p_c v) gi)])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr rX r)
  by (intros n0 r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = w64 (pf_F v pos + PF_O_L146))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E0 33 = w64 (seg_spec.rseg_addr (p_c v) gi))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
clearbody E0.
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B11_RBT)) with (Z_to_bv 64 (BASE + B11_RBT)).
(* 0x889dc .. 0x88a04: beqz (not taken), cur's T22 test (not taken), the snprintf arguments, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b11h_ro_awr. }
b11h_clear_md.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B11_RET_SN1))
  by (prreg HS (Z_to_bv 5 1) R1; rewrite R1; reflexivity).
assert (QR : pf_rg (ms_regs ms) (b11h_QL v pos o ln gi)).
{ unfold pf_rg, b11h_QL, b11_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    b11h_regq HS EE E32 E33 HEI HRG0 HRG. }
pmkst HS.
exact (Kc _ _ _ HJ KM QR Q1).
Qed.

(* ---------- the HIT branch, the call: snprintf(cur->model, 24, "%s", low) at 0x88a04, then RS1 (0x88a08) ---------- *)
Lemma b11h_call1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i regsT memT mdT,
  (forall fx1 : YK11.FPState, B11_RS1_stmt (fx := fx1) B n) ->
  INV_RBT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  by_token (r_low val 0 24) = Some i ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
  pf_rg regsT (b11h_QL v pos o ln gi) ->
  getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B11_RET_SN1) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT)
    (b11_post B v cf gi nm val o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i regsT memT mdT RS1 HI Hbt HJT KMT QR Q1.
destruct HI as (HCX & HLOW & HRG).
pose proof HCX as (HB & HMID & HST & HSTR & HINB & HSL70).
pose proof HB as (HCXv & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & HTF & _ & HRG0).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (GG & Hin & EF & Hfrs & HAR & Hly & HFP & HSHP).
pose proof GG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5 & C16 & C4 & Cc & Capp & Cdj & Ctx & Coff).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof pf_B_values as (_ & _ & _ & Egw & Egd & _ & _ & _ & _ & _ & EFs).
pose proof HJT as (HART & _).
pose proof HST as (HRC & HCUR & HNM & HCNT & HC0).
assert (Hgi : (gi < length (rc_seg cf))%nat) by exact HCUR.
assert (Hgi32 : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & Hn32 & _)); lia).
assert (ESZ : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ERN : seg_spec.RC_N = 0x2c80) by reflexivity.
assert (ERM : seg_spec.RS_MODEL = 0x24) by reflexivity.
assert (ECUR : seg_spec.rseg_addr (p_c v) gi = p_c v + 356 * Z.of_nat gi) by reflexivity.
assert (EK : CMD_SNP_K = 8192) by reflexivity.
assert (EES : ESTACK = 4096) by reflexivity.
assert (ELOW : PF_O_L146 = 0x2e0) by reflexivity.
assert (EIE : kImgEnd = 0x602000) by reflexivity.
assert (EIH : CMD_IMG_HI = 0x602000) by reflexivity.
assert (EIL : CMD_IMG_LO = 0x10000) by reflexivity.
assert (EGW : CMD_GOTW = 0xa3e98) by reflexivity.
unfold zdisjoint in Cdj. cbn [fst snd] in Cdj. unfold off_img in Coff.
(* the registers at the call *)
pose proof QR as QRu. unfold b11h_QL, b11_FI, PF_RL, PF_RM in QRu.
unfold b11h_QL in QR.
apply (proj1 (b11_rg_app _ _ _)) in QR as [QR0 QR1].
apply (proj1 (b11_rg_app _ _ _)) in QR1 as [QFI QR2].
apply (proj1 (b11_rg_app _ _ _)) in QR2 as [QRL QRM].
assert (Q10 : getr regsT 10 = w64 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL)) by b11h_getq QRu 10.
assert (Q11 : getr regsT 11 = w64 24) by b11h_getq QRu 11.
assert (Q12 : getr regsT 12 = w64 (seg_litA_rc F_s)) by b11h_getq QRu 12.
assert (Q2 : getr regsT 2 = w64 (pf_s1 v)) by b11h_getq QRu 2.
assert (Q3 : getr regsT 3 = w64 (as_gp B)) by b11h_getq QRu 3.
assert (Q4 : getr regsT 4 = w64 (as_tp B)) by b11h_getq QRu 4.
assert (Q1' : getr regsT 1 = Z_to_bv 64 (BASE + B11_RET_SN1)) by (apply (b11h_bvr _ _ 1); [reflexivity | exact Q1]).
assert (Hsp : spZ regsT = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* the cut's objects at the call's reader: the run wrote nothing *)
assert (KT : b11_kept v pos false None (rdW Wc memc) (rdW Wc memT)).
{ split; [intros a Ha _; exact (KMT a Ha) | intros a Ha Hv; rewrite (KMT a Ha); exact Hv]. }
assert (HOBJT : pf_obj B v lyc Sc (rdW Wc memT))
  by exact (b11_keep_obj B v pos lyc Sc Wc memc mdc false None _ _ GG HAR Hin EF I KT HOBJ).
pose proof HOBJT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
pose proof T5 as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrq].
(* the value: T = r_low val 0 24, at most 23 bytes, NUL-free, its bytes 1 .. 255 *)
pose proof HSTR as ((_ & Hval0) & _).
pose proof (b11f_low_len val 24 Hval0) as HTlen.
assert (HTl : (length (r_low val 0 24) < 24)%nat) by lia.
pose proof (b11f_low_nulfree val 24 Hval0) as HT0.
pose proof (b11ht_bytes_range_aview SEGS (w_H Wc) memc _ _ HLOW) as HTb1.
assert (HTb : Forall (fun x => 0 <= x < 256) (r_low val 0 24))
  by (apply Forall_forall; intros x Hx; rewrite Forall_forall in HTb1; pose proof (HTb1 x Hx); lia).
assert (Hsn : sn_bytes (24 - 1) (r_low val 0 24) = r_low val 0 24 ++ [0]).
{ unfold sn_bytes. rewrite firstn_all2; [reflexivity | lia]. }
assert (Hsl : sn_len (24 - 1) (r_low val 0 24) = Z.of_nat (length (r_low val 0 24)) + 1).
{ unfold sn_len. rewrite Hsn, length_app. cbn [length]. lia. }
pose proof (b11h_cspan (pf_F v pos + PF_O_L146) (r_low val 0 24)) as CSP.
(* model low as snprintf's argument: its bytes, NUL, slack, amem and shadow *)
assert (LstrT : sa_str (rdW Wc memT) (pf_F v pos + PF_O_L146) (r_low val 0 24))
  by (apply (b11h_same_str _ _ _ _ KMT); [lia | lia | exact HLOW]).
assert (LaddrC : sa_addr (rdW Wc memc) (pf_F v pos + PF_O_L146) (Z.of_nat (length (r_low val 0 24)) + 1)).
{ split; [lia|]. split; [lia|].
  split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
  split.
  - apply (range_addressable_sub _ _ (pf_F v pos + 0x2e0) 24).
    + apply (b11_ra_frame B v pos lyc Sc Wc rX memc mdc PF_SC_L146 0x2e0 24 HB); try reflexivity; try lia.
      intros i0 Hi0. apply b11h_shb_l146.
      assert (E1 : 0x2e0 / 8 = 92) by reflexivity. assert (E2 : (0x2e0 + 24) / 8 = 95) by reflexivity.
      rewrite E1, E2 in Hi0. lia.
    + lia.
    + lia.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memc mdc 5 pos);
      [exact HAR | exact Hin | rewrite EF; lia | rewrite EF; change (fs_frame_bytes 5) with 2048; lia | lia]. }
assert (LaddrT : sa_addr (rdW Wc memT) (pf_F v pos + PF_O_L146) (Z.of_nat (length (r_low val 0 24)) + 1))
  by exact (b11h_same_addr _ _ _ _ KMT LaddrC).
assert (FMT : sa_lit SEGS B (rdW Wc memT) (seg_litA_rc F_s) F_s)
  by (apply T7; unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity).
eapply SRr_bind.
{ apply (b11ht_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (pa_sigma SS___interceptor_trampoline_snprintf)
    (ASNPRINTF fx) Wc regsT memT STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v)
    (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdT 0 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL) 24
    (seg_litA_rc F_s) (r_low val 0 24) (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B11_RET_SN1)) HJT Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - exact (b11_m16 _ _ S6 S3).
  - lia.
  - rewrite ESTK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [unfold B11_RET_SN1, AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split.
    + right; left. split.
      * exists (p_c v, p_c v + seg_spec.RC_N + 4).
        split; [unfold seg_spec.RC_PARSE_W; left; reflexivity|]. cbn [fst snd]. lia.
      * exists bc, mc. split; [exact Hbc|]. lia.
    + lia.
  - intros a Ha _ [[_ Hi] | Hs]; exfalso.
    + pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr. lia.
    + lia.
  - pose proof T4 as (_ & _ & Hcam & _). unfold amem_range in *. lia.
  - pose proof T4 as (_ & _ & _ & HRA & _).
    apply (range_addressable_sub _ _ _ _ _ _ HRA); lia.
  - pose proof T4 as (_ & _ & _ & _ & HHV).
    apply (b11h_hull_sub _ _ _ _ _ (HHV ltac:(lia))); lia.
  - rewrite Hsl. unfold off_img. lia.
  - rewrite EIH, EK. lia.
  - exact T9.
  - rewrite Egw. lia.
  - rewrite Egw, EIH. lia.
  - rewrite Egd. lia.
  - rewrite Egd, EIH. lia.
  - rewrite Egw, EIL. lia.
  - rewrite Egd, EIL. lia.
  - apply (b11ht_FR_s_regs (rdW Wc memT) _ (seg_litA_rc F_s) (pf_F v pos + PF_O_L146) (r_low val 0 24) regsT).
    + unfold argZ. change (10 + 3) with 13. rewrite (b11_rg_get _ _ 13 _ QRu ltac:(b11h_in)). unfold w64.
      apply unsigned_lit_small. lia.
    + rewrite EFs. lia.
    + rewrite EFs, EIL. lia.
    + rewrite EFs, EGW. lia.
    + exact (proj1 (proj2 FMT)).
    + pose proof FMT as (_ & _ & Hp & _). pose proof (Hp lyc Sc Wc memT mdT HART) as Hpa.
      rewrite b11ht_F_s_len in Hpa. exact Hpa.
    + rewrite Hsp, Hsl, EFs. unfold snp_out.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint; cbn [fst snd]. lia.
    + lia.
    + exact (b11ht_bytes_range_aview SEGS (w_H Wc) memT _ _ LstrT).
    + lia.
    + exact LstrT.
    + exact LaddrT.
    + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
    + rewrite Hsp, Hsl. unfold snp_out.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint; cbn [fst snd]. lia.
  - lia.
  - intros a (sg & Hsg & Hw & Hr) Ho He. exact (T8 a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
  - exact HFRM. }
(* back at 0x88a08 at the FP state fx1 the wrapper returns *)
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & _ & Hby & Hkp & Hpr & _).
rewrite Hsl in Hby, Hkp. rewrite Hsn in Hby.
(* every byte outside the model prefix and the call's window is the cut's *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL <= a
         < seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL + (Z.of_nat (length (r_low val 0 24)) + 1)) ->
    ~ (pf_s1 v - CMD_SNP_K <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha H1 H2. rewrite (Hkp a Ha H1) by (intros H3; apply H2; lia). exact (KMT a Ha). }
assert (Hcw : b11_cw_ok v (b11_cw v gi)) by exact (b11_cw_ok_gi v gi Hgi32).
assert (KP : b11_kept v pos false (b11_cw v gi) (rdW Wc memc) (rdW Wc mem2)).
{ split.
  - intros a Ha Hn. apply K2; [exact Ha | |]; intros Hq; apply Hn; unfold b11_Wr, b11_cw.
    + right; right; right. cbv beta iota. lia.
    + left. rewrite ESTK. lia.
  - intros a Ha Hv.
    assert (Hd : seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL <= a
        < seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL + (Z.of_nat (length (r_low val 0 24)) + 1) \/
      ~ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL <= a
        < seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL + (Z.of_nat (length (r_low val 0 24)) + 1))) by lia.
    destruct Hd as [Hd | Hd].
    { replace a with (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL + (a - (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL)))
        by lia.
      rewrite Hby by lia. discriminate. }
    assert (Hw : pf_s1 v - CMD_SNP_K <= a < pf_s1 v \/ ~ (pf_s1 v - CMD_SNP_K <= a < pf_s1 v)) by lia.
    destruct Hw as [Hw | Hw].
    { apply (aview_some_of_apresent SEGS). apply Hpr. apply (apresent_of_aview SEGS); [exact Ha | | rewrite KMT by exact Ha; exact Hv].
      intros Himg. pose proof (pa_img_range a Himg) as Hr. unfold kImgEnd in Hr. lia. }
    rewrite K2 by assumption. exact Hv. }
(* the cut at 0x88a08: pf_base at fx1, the record b11_cf1, the rest kept *)
assert (QFI2 : pf_rg regs2 (b11_FI B v)) by exact (b11_rg_pres _ _ _ HP2 (b11_FI_cs B v) QFI).
assert (HB1 : pf_base (fx := fx) B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_L146).
{ apply (b11_move B fx v pos lyc Sc Wc rX memc mdc PF_SC_L146 Sc Wc regs2 mem2 md2 PF_SC_L146 false (b11_cw v gi)
    HB Hcw HJ2 ltac:(exists (st_fs Sc); symmetry; apply b11h_set_fs_id) (Permutation_refl _) KP QFI2 HFRM).
  exact (b11_keep_fsh v pos (b11_cw v gi) _ _ _ GG Hcw KP HFSH). }
assert (HB2 : pf_base (fx := fx1) B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_L146)
  by exact (b11h_base_fx fx fx1 v pos lyc Sc Wc regs2 mem2 md2 PF_SC_L146 HB1 (fxrel_frm0 fx fx1 HFRM Hfx)).
assert (HRC2 : sa_rconf (rdW Wc mem2) (p_c v) (b11_cf1 cf gi val)).
{ unfold b11_cf1. rewrite (b11f_snprintf_low val Hval0).
  apply (b11ht_rconf_model1 (rdW Wc memc) (rdW Wc mem2) (p_c v) cf gi (r_low val 0 24) HRC Hgi HTl HT0 HTb).
  - intros i0 Hi0. pose proof (Hby (Z.of_nat i0) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. exact Hb.
  - intros a Ha Hn. apply K2; lia. }
assert (HINV : INV_RS1 (fx := fx1) B n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val).
{ split; [|split; [exists i; exact Hbt|]].
  - split; [exact HB2|]. split; [exact HMID|].
    split.
    + split; [exact HRC2|].
      split; [exact (b11f_cur_ok_upd cf gi _ gi HCUR)|].
      split; [exact (b11_keep_nm v pos false (b11_cw v gi) _ _ nm GG Hcw KP HNM)|].
      split; [exact (b11f_cnt_upd cf gi _ _ HCNT)|].
      exact (b11_keep_slot v pos false (b11_cw v gi) _ _ 0xc0 _ GG Hcw KP ltac:(lia) HC0).
    + split; [exact (b11_keep_buf_str v pos false (b11_cw v gi) _ _ vp val GG Hcw KP HINB HSTR)|].
      split; [exact HINB|].
      apply (b11_keep_sl v pos false (b11_cw v gi) _ _ _ GG Hcw KP); [|exact HSL70].
      intros ov [<- | []]. cbn [fst]. lia.
  - apply (proj2 (b11_rg_app _ _ _)). split; [exact (b11_rg_pres _ _ _ HP2 (b11_RL_cs v pos) QRL)|].
    apply (proj2 (b11_rg_app _ _ _)). split; [exact (b11_rg_pres _ _ _ HP2 (b11_RM_cs v o ln) QRM)|].
    unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    rewrite (HP2 19 ltac:(unfold acallee_saved; lia)). apply (b11_rg_get _ _ 19 _ QR0). b11h_in. }
(* RS1 at fx1, lifted to the post at fx *)
unfold b11_post, pf_postm, PF_POSTr.
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
change (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + B11_RET_SN1)) mem2 (seg_rom SEGS)) md2)
  with (@cfg_at fx1 SEGS (BASE + B11_RET_SN1) regs2 mem2 md2).
exact (RS1 fx1 v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val HINV).
Qed.

(* ---------- the cut ---------- *)
Lemma b11h_rbt : forall n, (forall fx1 : YK11.FPState, B11_RS1_stmt (fx := fx1) B n) -> HA_MISS B n ->
  B11_RBT_stmt (fx := fx) B n.
Proof.
intros n RS1 HMISS v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct (by_token (r_low val 0 24)) as [i|] eqn:Hbt.
- apply (b11h_run1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i _ HI Hbt).
  intros regsT memT mdT HJT KMT QR Q1.
  exact (b11h_call1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i regsT memT mdT RS1 HI Hbt HJT KMT QR Q1).
- exact (b11h_miss n HMISS v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI Hbt).
Qed.
End x.

(* the cut at every ambient FP state *)
Theorem b11_rbt_ok : forall (fx : YK11.FPState) (n : nat),
  (forall fx1 : YK11.FPState, B11_RS1_stmt (fx := fx1) B n) -> HA_MISS B n -> B11_RBT_stmt (fx := fx) B n.
Proof. intros fx n RS1 HM. exact (b11h_rbt (fx := fx) n RS1 HM). Qed.
End d.
