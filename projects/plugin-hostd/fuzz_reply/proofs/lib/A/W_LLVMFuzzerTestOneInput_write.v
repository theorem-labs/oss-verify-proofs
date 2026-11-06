(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_write of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the jump
   table's arm 1 (fuzz_reply.c:704-708), from the arm's entry 0x843bc to the latch 0x84490, in the form of
   lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt (entry state from the cut's facts, paj_run_tok,
   psrr_branch_tok, the next cut re-established) and of lib/A/W_source_reset.v's internal call (the callee's spec at
   its own G, lifted to the caller's journal by W_journal's ajournal_gx_sub).
   The arm: fuzz_u16(&in) (two shadow-checked byte reads of the input block, 0x843bc-0x8445c), fuzz_take(&in, u16, &p)
   (n = min(u16, in.n), 0x84460-0x84474, with in.n stored at F+144), then `if (s && n) list_push(&s->pending, p, n)`
   (0x84478-0x84488), then li s4,10 and the fall into the latch 0x84490.  The arm is also entered with s5 = 0 from
   the no-source path at 0x843b8 (INV_A 1's lregs_D allows it).
   The callee is W2's pb_list_push_g (lib/A/W_list_push.v), taken at list_push's own G (the 16 bytes of
   g_s[si].pending) with MMAX = cf_malloc_max = 2^30 - 2^20, and its journal lifted with ajournal_gx_G_mono and
   composed with W_journal's ajournal_gx_sub.
   What this file takes, and from whom (all Section hypotheses):
     the contract parameters, LAWS, HG, LS, RINV - _cut's Section w, verbatim;
     TL / MLAW / ARE / AMA / AMEMCPY - pb_list_push_g's allocator instance and site rules, verbatim;
     GWR / ERR - _cut's glob_wr_law / errno_law;
     HGs / HZS - the G-coverage and zero-shadow facts of g_s (no gx_rt of G_fr: G_fr holds errno, see _exit.v);
     HGW / HERRS / ROM_ERR - G_fr / errno facts, proved for G_fr_c in W_LLVMFuzzerTestOneInput_G.v (c_HGW, c_HERRS,
                 c_ROM_ERR);
     ROM_PIN - rom_out's pinning conjunct (W_journal.v:397), the start-up instance's debt;
     RI_write_* and LS_write_* - the arm's open model obligations. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_list_push.
(* list_push's trace peak within the sum (lp_tr_peak_le), for its byte premise *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyGuard.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
Import ListNotations.
(* ReplyGuard removed every sink instance from resolution; the one this walk is about is the ASan image's
   (AE2k.tfib_sink_head, ofl_head 0x5f9b68), the instance _cut's journal names, so it is the only one restored *)
#[local] Existing Instance AE2k.tfib_sink_head.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the arm's addresses (offsets from fr_B0) *)
Definition A_wr_arm : Z := AF_arm_write.                                 (* 0x843bc the arm's entry *)
Definition A_wr_zero : Z := AF_fr_LLVMFuzzerTestOneInput + 0x380.        (* 0x84430 no byte left *)
Definition A_wr_two : Z := AF_fr_LLVMFuzzerTestOneInput + 0x390.         (* 0x84440 a second byte *)
Definition A_wr_take : Z := AF_fr_LLVMFuzzerTestOneInput + 0x3b0.        (* 0x84460 fuzz_take *)
Definition A_wr_call : Z := AF_fr_LLVMFuzzerTestOneInput + 0x3d8.        (* 0x84488 jal list_push *)
Definition A_wr_li : Z := AF_fr_LLVMFuzzerTestOneInput + 0x3dc.          (* 0x8448c li s4,10 *)
Definition A_wr_store : Z := AF_fr_LLVMFuzzerTestOneInput + 0x3bc.       (* 0x8446c add s6,t3,a2 *)
Definition WR_N : Z := 144.                                              (* the frame cell holding in.n *)

(* ------------------------------------------------------------------ one bit of arithmetic *)
(* the u16: `slli a2,a2,8; or a2,a2,a1` over two bytes *)
Lemma land_shl8 : forall a b, 0 <= a < 256 -> 0 <= b -> Z.land (Z.shiftl b 8) a = 0.
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 a i); [apply Bool.andb_false_r | lia |].
    destruct (Z.eq_dec a 0) as [->|Hne]; [cbn; lia|].
    assert (Z.log2 a < 8) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma lor_shl8 : forall a b, 0 <= a < 256 -> 0 <= b -> Z.lor (Z.shiftl b 8) a = 256 * b + a.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (Z.shiftl b 8) a = 0) by (apply land_shl8; lia).
  assert (Hx : Z.lor (Z.shiftl b 8) a = Z.lxor (Z.shiftl b 8) a).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.lxor_spec.
    pose proof (f_equal (fun z => Z.testbit z i) Hl) as Hb0. cbn beta in Hb0.
    rewrite Z.land_spec, Z.bits_0 in Hb0.
    destruct (Z.testbit (Z.shiftl b 8) i), (Z.testbit a i); cbn in Hb0 |- *; congruence. }
  rewrite Hx, <- Z.add_nocarry_lxor by exact Hl. rewrite Z.shiftl_mul_pow2 by lia. cbn. lia.
Qed.
(* the u16 the engine builds: `slli a2,a2,8; or a2,a2,a1` *)
Lemma wr_u16 : forall Ev b0 b1,
  ew Ev 32 = Z_to_bv 64 b0 -> ew Ev 33 = Z_to_bv 64 b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  U Ev (SAlu ALU_OR (SAlu ALU_SLL (SOff 33 0) (SLit 8)) (SOff 32 0)) = b0 + 256 * b1.
Proof.
  intros Ev b0 b1 H32 H33 Hb0 Hb1.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom Ev 33 b1 H33 ltac:(lia)), (U_atom Ev 32 b0 H32 ltac:(lia)), U_SLit.
  change (zcanon 8) with 8. change (Z.land 8 63) with 8.
  rewrite (zcanon_id (Z.shiftl b1 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
  rewrite lor_shl8 by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Section wr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- _cut's Section w, verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
(* the laws at the instance's ARi0, which W2's re-derived pb_list_push_g takes (W_journal_x.AR_laws_x_ARi0) *)
Hypothesis LX0 : AR_laws_x segs B (ARi0 segs B) 0.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ---- what the other lanes owe ---- *)
(* list_push's request bound: the instance's cf_malloc_max BY DEFINITION (ATopKeeper's CfParamsReply.fr_MMAX), so the
   two cannot drift if cf_malloc_max changes (a Theorem Labs lane 21:16Z); wr_HMMAX is checked by computation at its value *)
Definition WR_MMAX : Z := CfParamsReply.fr_MMAX.
Lemma wr_HMMAX : 2 ^ 29 < WR_MMAX <= 2 ^ 30.
Proof. unfold WR_MMAX. split; [apply Z.ltb_lt | apply Z.leb_le]; vm_compute; reflexivity. Qed.
(* pb_list_push_g's other arguments (lib/A/W_list_push.v Section g): the allocator instance and the three
   site rules list_push calls, verbatim *)
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
(* the allocator rules in the caller-context form, each at ITS OWN K0 table (a Theorem Labs lane 20:04Z: one CTX per entry) *)
Hypothesis ARE : arealloc_cf_rule_c segs B MT WR_MMAX CTX_AREALLOC (SIGMA WS_realloc).
Hypothesis AMA : amalloc_cf_rule_c segs B MT WR_MMAX CTX_AMALLOC.
Hypothesis AMEMCPY : aintrin_realizes segs B OCpy (SIGMA WS_asan_memcpy).
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis ERR : errno_law B.
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).

(* ---- G_fr / errno facts this arm adds; each is proved for G_fr_c in lib/A/W_LLVMFuzzerTestOneInput_G.v ---- *)
(* the globals the model reads, other than g_s and errno *)
Definition wr_G : list (Z * Z) :=
  [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8);
   (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4); (rg_client_broken fr_RG, 1);
   (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_gone fr_RG, 1); (rg_lock fr_RG, 12);
   (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
(* the model's globals are in G_fr (c_HGW) *)
Hypothesis HGW : forall a, inG wr_G a -> inG G_fr a.
(* errno is apart from g_s and from the model's globals (c_HERRS): gx_rt of list_push's G and the model's carry *)
Hypothesis HERRS : forall a, inG ((rg_s fr_RG, 4 * ASRC) :: wr_G) a -> ~ (as_errno B <= a < as_errno B + 4).
(* errno is no read-only byte (c_ROM_ERR): rom_out's errno conjunct (W_journal.v:398) *)
Hypothesis ROM_ERR : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
(* ---- the start-up instance's debt (not a G_fr / errno fact) ---- *)
(* rom_out's pinning conjunct (W_journal.v:397, comment :372-375), verbatim: an allocator-owned read-only byte is a
   byte of one of AR's const cells.  With ROM_ERR and two vm_computes it gives rom_out at list_push's G, so the
   journal carries rom_view across the call (W_journal.v ajournal_gx_rom_view) *)
Hypothesis ROM_PIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.

(* ------------------------------------------------------------------ the arm's model side (plain records only) *)
(* the input cursor at the arm's entry (lregs_D's k') and what is left of the input there *)
Definition wr_k1 (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1.
Definition wr_rem (cx : lfcx) (m : lmod) : Z := c_n cx - wr_k1 cx m.
(* fuzz_u16: the two bytes it reads, little-endian; a short input reads zeros *)
Definition wr_u (cx : lfcx) (m : lmod) : Z :=
  if 2 <=? wr_rem cx m then in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1)
  else if wr_rem cx m =? 1 then in_byte cx (wr_k1 cx m) else 0.
(* the bytes fuzz_u16 consumed, and fuzz_take's n = min(u16, in.n) *)
Definition wr_c (cx : lfcx) (m : lmod) : Z := Z.min 2 (wr_rem cx m).
Definition wr_n (cx : lfcx) (m : lmod) : Z := Z.min (wr_u cx m) (wr_rem cx m - wr_c cx m).
Definition wr_k2 (cx : lfcx) (m : lmod) : Z := wr_k1 cx m + wr_c cx m + wr_n cx m.
Definition wr_src (cx : lfcx) (m : lmod) : Z := c_p cx + wr_k1 cx m + wr_c cx m.
Definition wr_x (cx : lfcx) (m : lmod) : list byte :=
  firstn (Z.to_nat (wr_n cx m)) (skipn (Z.to_nat (wr_k1 cx m + wr_c cx m)) (c_pl cx)).
(* the source the dispatch picked, when it picked one *)
Definition wr_kb (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0.
Definition wr_pick (cx : lfcx) (m : lmod) (si : nat) (h : hsrc) : Prop :=
  pick (lm_hs m) (wr_kb cx m) = Some si /\ (si < 4)%nat /\ nth si (lm_hs m) None = Some h.
(* the model after the operation *)
Definition wr_skip (m : lmod) (k : Z) : lmod :=
  LM k (lm_hs m) (lm_G m) (lm_es m) (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition set_pending (h : hsrc) (l : hlist) : hsrc :=
  HS (hs_fd h) (hs_open h) (hs_closed h) (hs_eintr h) l (hs_off h) (hs_partial h) (hs_pjunk h)
     (hs_npartial h) (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).
Definition set_ev (c : ctl) (v : Z) : ctl := CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) v.
Fixpoint set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | S n', y :: l' => y :: set_nth n' x l'
  | _, [] => []
  end.
Definition wr_push (m : lmod) (k : Z) (si : nat) (h' : hsrc) (ev : Z) : lmod :=
  LM k (set_nth si (Some h') (lm_hs m)) (lm_G m) (lm_es m) (set_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).

Lemma set_nth_length : forall (A : Type) n (x : A) l, length (set_nth n x l) = length l.
Proof.
  intros A n x l. revert n. induction l as [|y l IH]; intros [|n]; cbn [set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma set_nth_same : forall (A : Type) n (x : A) l d, (n < length l)%nat -> nth n (set_nth n x l) d = x.
Proof.
  intros A n x l d. revert n. induction l as [|y l IH]; intros [|n] Hn; cbn [set_nth length nth] in *;
    try lia; [reflexivity | apply IH; lia].
Qed.
Lemma set_nth_other : forall (A : Type) n p (x : A) l d, n <> p -> nth p (set_nth n x l) d = nth p l d.
Proof.
  intros A n. induction n as [|n IH]; intros [|p] x l d Hnp; destruct l as [|y l];
    cbn [set_nth nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

(* ------------------------------------------------------------------ the arm's open model obligations *)
Hypothesis RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
Hypothesis LS_write_skip : forall cx t m ly S,
  LS cx t m ly S -> LS cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Hypothesis RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).
Hypothesis LS_write_room : forall cx t m si h ly S,
  LS cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (lp_cost MT (hs_pending h) (wr_n cx m)).
(* the push rule at W8Add's PROPOSED text (lib/A/ReplyLS.v atop_LS_write_push_prop, a working branch
   f57b3e2d0ca), in this Section's form (B, MT): list_push's post facts about the pushed list l' (lp_post, W_contract.v:
   the record, the capacity, the address kept when it does not grow, and the blocks' change) in place of the published
   `mo_le MT S S' cost` alone, which left l' and S' free *)
Hypothesis LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LS cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  LS cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.

(* ------------------------------------------------------------------ the arm's entry state *)
Definition wr_Bx : sv := SOff 26 0.
Definition wr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition wr_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
            (26%nat, mkAF SB SB 0); (28%nat, mkAF 4096 140737479966720 0);
            (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] [].
Definition wr_ss2 : sstate :=
  mkSS A_wr_arm sr_atoms
    [ YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
      YP09.mkRegion (Some 28%nat) 0 2 0 0
        [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0))] ]
    None wr_facts.
Definition wr_ss1 : sstate :=
  mkSS A_wr_arm sr_atoms
    [ YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
      YP09.mkRegion (Some 28%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ]
    None wr_facts.
Definition wr_ss0 : sstate :=
  mkSS A_wr_arm sr_atoms [ YP09.mkRegion (Some 9%nat) 144 152 144 152 [] ] None wr_facts.
Definition wr_SH (nb : Z) : list shent := [ mkSHE 28 0 nb ].
Definition wr_extra (b0 b1 : Z) : list word := map (Z_to_bv 64) [b0; b1].

(* the frame's address, and the window the arm writes *)
Lemma mod32_mod16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
  intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
  destruct H as [k ->]. exists (2 * k). lia.
Qed.
Lemma wr_F_mod32 : forall cx, lf_F cx mod 32 = 0.
Proof.
  intros cx. unfold lf_F. pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HD.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HB.
  replace (spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) with (32 * ((spZ (c_regs cx) - 320) / 32)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma wr_F_range : forall cx, spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320.
Proof.
  intros cx. unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia.
Qed.

(* an input byte, as the program reads it *)
Lemma wr_byte : forall (cx : lfcx) (W : world segs) mem i,
  garr8 segs (arm W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  0 <= i < Z.of_nat (length (c_pl cx)) ->
  val_mem segs (arm W mem) (c_p cx + i) 1 (in_byte cx i).
Proof.
  intros cx W mem i Hg Hi.
  assert (Hj : (Z.to_nat i < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
    by (rewrite length_map; lia).
  destruct (Hg (Z.to_nat i) Hj) as [Hv _]. rewrite Z2Nat.id in Hv by lia.
  unfold in_byte. rewrite <- (map_nth (fun b : byte => bv_unsigned b) (c_pl cx) (Z_to_bv 8 0)).
  change (bv_unsigned (Z_to_bv 8 0)) with 0. exact Hv.
Qed.

(* the entry state at the arm, with two bytes of input left *)
Lemma wr_entry2 : forall (cx : lfcx) (m : lmod) ly S (W : world segs) regs mem md,
  AR segs B ly S W mem md ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) ->
  astk_ok LLVMF_STK (c_ly cx) (spZ (c_regs cx)) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 (c_p cx + wr_k1 cx m) ->
  In (c_p cx, c_n cx) (ablocks B ly S) ->
  garr8 segs (arm W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  c_n cx = Z.of_nat (length (c_pl cx)) -> 0 < c_n cx < 2 ^ 26 ->
  0 <= wr_k1 cx m -> wr_k1 cx m + 2 <= c_n cx ->
  st_ok_pi segs VAL (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1))))) wr_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs wr_Bx (wr_SH 2)
       (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1)))))
       (mrestrict (w_H W) mem).
Proof.
  intros cx m ly S W regs mem md HAR Hpres Hstk R2 R9 R26 R28 Hin Hg Hlen Hcn Hk0 Hk2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (al_blocks _ _ LAWS ly S W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hnmax).
  pose proof (wr_F_mod32 cx) as HFm. pose proof (wr_F_range cx) as HFr.
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil, Hpapp.
  set (b0 := in_byte cx (wr_k1 cx m)). set (b1 := in_byte cx (wr_k1 cx m + 1)).
  assert (Hb0 : 0 <= b0 < 256) by (unfold b0, in_byte; apply u8_range).
  assert (Hb1 : 0 <= b1 < 256) by (unfold b1, in_byte; apply u8_range).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (wr_extra b0 b1))). pose proof pa_B_ok as HBASE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
  assert (E32 : ew E 32 = Z_to_bv 64 b0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 b1)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
    by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
  assert (HF46 : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (Hp2 : c_p cx + wr_k1 cx m + 2 <= c_p cx + c_n cx) by lia.
  split.
  - unfold wr_ss2, A_wr_arm. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 9%nat (lf_F cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. unfold LLVMF_STK in *. lia.
      * rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val segs E _ (c_p cx + wr_k1 cx m) 0 1 (SOff 32 0) b0);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat.
           replace (c_p cx + wr_k1 cx m) with (c_p cx + wr_k1 cx m) by reflexivity.
           exact (wr_byte cx W mem (wr_k1 cx m) Hg ltac:(lia)).
        -- apply (chunk_ok_val segs E _ (c_p cx + wr_k1 cx m) 1 1 (SOff 33 0) b1);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           change (N.to_nat 1) with 1%nat.
           replace (c_p cx + wr_k1 cx m + 1) with (c_p cx + (wr_k1 cx m + 1)) by lia.
           exact (wr_byte cx W mem (wr_k1 cx m + 1) Hg ltac:(lia)).
    + apply pairwise_disjoint_of_extents.
      unfold extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 9%nat (lf_F cx) E9) by lia. rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LLVMF_STK in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E26, E28, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
      unfold SB, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try (apply mod32_mod16; exact HFm).
  - unfold sh_ok, wr_SH. constructor; [|constructor].
    destruct (al_shadow _ _ LAWS ly S W mem md (c_p cx) (c_n cx) HAR Hin) as [Hbs _].
    eapply (shent_ok_of_range segs (w_H W) mem E wr_Bx 28 (c_p cx) (c_n cx) (c_p cx + wr_k1 cx m) 0 2).
    + eapply block_shadow_range; [exact Hbs | lia | rewrite Hreq; lia].
    + unfold U, wr_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      cbn [Z.min Z.max] in Hx. lia.
Qed.

(* the entry state at the arm, with one byte of input left *)
Lemma wr_entry1 : forall (cx : lfcx) (m : lmod) ly S (W : world segs) regs mem md,
  AR segs B ly S W mem md ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) ->
  astk_ok LLVMF_STK (c_ly cx) (spZ (c_regs cx)) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 (c_p cx + wr_k1 cx m) ->
  In (c_p cx, c_n cx) (ablocks B ly S) ->
  garr8 segs (arm W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  c_n cx = Z.of_nat (length (c_pl cx)) -> 0 < c_n cx < 2 ^ 26 ->
  0 <= wr_k1 cx m -> wr_k1 cx m + 1 <= c_n cx ->
  st_ok_pi segs VAL (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) wr_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs wr_Bx (wr_SH 1) (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) (mrestrict (w_H W) mem).
Proof.
  intros cx m ly S W regs mem md HAR Hpres Hstk R2 R9 R26 R28 Hin Hg Hlen Hcn Hk0 Hk2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (al_blocks _ _ LAWS ly S W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hnmax).
  pose proof (wr_F_mod32 cx) as HFm. pose proof (wr_F_range cx) as HFr.
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil, Hpapp.
  set (b0 := in_byte cx (wr_k1 cx m)).
  assert (Hb0 : 0 <= b0 < 256) by (unfold b0, in_byte; apply u8_range).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (wr_extra b0 0))). pose proof pa_B_ok as HBASE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
  assert (E32 : ew E 32 = Z_to_bv 64 b0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
    by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
  assert (HF46 : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  split.
  - unfold wr_ss1, A_wr_arm. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 9%nat (lf_F cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. unfold LLVMF_STK in *. lia.
      * rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        apply (chunk_ok_val segs E _ (c_p cx + wr_k1 cx m) 0 1 (SOff 32 0) b0);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat.
        exact (wr_byte cx W mem (wr_k1 cx m) Hg ltac:(lia)).
    + apply pairwise_disjoint_of_extents.
      unfold extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 9%nat (lf_F cx) E9) by lia. rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LLVMF_STK in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E26, E28, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
      unfold SB, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try (apply mod32_mod16; exact HFm).
  - unfold sh_ok, wr_SH. constructor; [|constructor].
    destruct (al_shadow _ _ LAWS ly S W mem md (c_p cx) (c_n cx) HAR Hin) as [Hbs _].
    eapply (shent_ok_of_range segs (w_H W) mem E wr_Bx 28 (c_p cx) (c_n cx) (c_p cx + wr_k1 cx m) 0 1).
    + eapply block_shadow_range; [exact Hbs | lia | rewrite Hreq; lia].
    + unfold U, wr_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      cbn [Z.min Z.max] in Hx. lia.
Qed.

(* the entry state at the arm, with no input left: no region of the input, no shadow check *)
Lemma wr_entry0 : forall (cx : lfcx) (m : lmod) ly S (W : world segs) regs mem md,
  AR segs B ly S W mem md ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) ->
  astk_ok LLVMF_STK (c_ly cx) (spZ (c_regs cx)) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 (c_p cx + wr_k1 cx m) ->
  In (c_p cx, c_n cx) (ablocks B ly S) -> 0 < c_n cx < 2 ^ 26 ->
  0 <= wr_k1 cx m <= c_n cx ->
  st_ok_pi segs VAL (Eimg (Ereg regs (wr_extra 0 0))) wr_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs wr_Bx [] (Eimg (Ereg regs (wr_extra 0 0))) (mrestrict (w_H W) mem).
Proof.
  intros cx m ly S W regs mem md HAR Hpres Hstk R2 R9 R26 R28 Hin Hcn Hk0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (al_blocks _ _ LAWS ly S W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hnmax).
  pose proof (wr_F_mod32 cx) as HFm. pose proof (wr_F_range cx) as HFr.
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil, Hpapp.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (wr_extra 0 0))). pose proof pa_B_ok as HBASE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
  assert (E32 : ew E 32 = Z_to_bv 64 0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
    by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
  assert (HF46 : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  split.
  - unfold wr_ss0, A_wr_arm. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 9%nat (lf_F cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. unfold LLVMF_STK in *. lia.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E26, E28, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
      unfold SB, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try (apply mod32_mod16; exact HFm).
  - unfold sh_ok. constructor.
Qed.

Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* a run's write obligation: the in.n cell [F+144, F+152) is in the function's own stack window, every other
   region is read-only *)
Ltac wr_awr U9 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
       first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ] |] ].
(* the bytes a run writes lie in the in.n cell *)
Ltac wr_wr U9 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia;
     rewrite ?U9 in Hr; unfold WR_N; lia |]);
  destruct Hin.
Lemma wr_frame_win : forall E rs (m m' : word -> option byte) lo hi,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Proof. intros E rs m m' lo hi HF Hw x Hx. apply HF. intros Hin. apply Hx. apply Hw. exact Hin. Qed.
Lemma wr_mg_trans : forall m1 m2 m3 : word -> option byte, mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
(* after a run: the memory agrees with the arm's entry memory outside the in.n cell, and only grew *)
Ltac wr_upd U9 MEQ MG :=
  lazymatch goal with HFx : frame_of ?Ev ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
  lazymatch goal with HGx : mem_grows (mrestrict H m0) (mrestrict H m1) |- _ =>
    let MEQn := fresh "MEQn" in let MGn := fresh "MGn" in
    lazymatch type of MEQ with forall x, ~ (?lo <= _ < ?hi) -> mrestrict _ _ x = mrestrict _ ?mo x =>
    assert (MEQn : forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m1 x = mrestrict H mo x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          rewrite (wr_frame_win Ev rs _ _ lo hi HFx ltac:(wr_wr U9) x Hx); exact (MEQ x Hx)) end;
    pose proof (wr_mg_trans _ _ _ MG HGx) as MGn;
    clear MEQ MG HFx HGx; rename MEQn into MEQ; rename MGn into MG end end;
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
Ltac wr_pin Hnew Hold n v :=
  lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ev _ _ |- _ =>
      assert (Hnew : ew Ev n = Z_to_bv 64 v) by (rewrite ?ew_ewset_other by lia; exact Hold)
  end.

(* the journal's stack window is present *)
Lemma wr_pres : forall cx own ly3 S3 (W : world segs) mem md k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a.
Proof.
  intros cx own ly3 S3 W mem md k HJ a Ha.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact (Hp a Ha).
Qed.

(* ------------------------------------------------------------------ the cut point inside the arm, 0x84478
   fuzz_u16 and fuzz_take done: a2 = n, t3 = the pushed bytes' address, s6 = in.p after the operation, F+144 =
   in.n after it, s5 = the picked source or 0 *)
Definition A_wr_tst : Z := AF_fr_LLVMFuzzerTestOneInput + 0x3c8.          (* 0x84478 beqz s5 *)
Definition lregs_T (cx : lfcx) (t : Z) (m : lmod) (FF : Z) (regs : bvmap 5 word) (W : world segs)
    (mem : word -> option byte) : Prop :=
  lregs_common B cx FF regs /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  0 <= lm_k m < c_n cx /\ lm_O m = [] /\ in_byte cx (lm_k m) mod 10 = 1 /\
  ((exists si, pick (lm_hs m) (wr_kb cx m) = Some si /\ getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si)) \/
   (pick (lm_hs m) (wr_kb cx m) = None /\ getr regs 21 = w64 0)) /\
  getr regs 12 = w64 (wr_n cx m) /\ getr regs 28 = w64 (wr_src cx m) /\
  getr regs 22 = w64 (c_p cx + wr_k2 cx m) /\ sv8 W mem (lf_F cx + WR_N) (c_n cx - wr_k2 cx m).
Definition WST (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + A_wr_tst) regs mem md /\ jt_rom W mem /\
    lcut B G_fr fr_FP LS RINV cx t true (lregs_T cx t) regs mem md W.

(* ---- the cut facts across the arm's store to in.n (the shape of W_LLVMFuzzerTestOneInput_drain.v de_carry, whose
   only store is the same cell; the model and frame lemmas are _latch.v's) ---- *)
Lemma wr_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
(* the frame across a run whose only store is the in.n cell (_drain.v de_aframe_kept) *)
Lemma wr_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + WR_N <= a < lf_F cx + WR_N + 8) -> abyte_kept W mem W' mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  CEIL8 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= CEIL8 ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof lt_ceil_lo as HCL. unfold WR_N, CEIL8 in *.
  assert (KW : forall a n, awr W mem a n -> awr W' mem' a n) by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lf_F cx + 144 \/ lf_F cx + 152 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (lt_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply HK; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 9 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | assumption]. }
  do 3 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split; [exact (KW _ _ A16)|].
  split; [|exact (KW _ _ (proj2 A17))].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HK; lia.
Qed.
(* everything lcut says of the memory, carried across a run whose only store is the in.n cell (_drain.v
   de_carry) *)
Lemma wr_store_kept : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + WR_N <= a < lf_F cx + WR_N + 8) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem' /\
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hfin Hlen Hsp HFR HFL HMOD HIN HRV HJT KEEP WK.
  pose proof lt_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320) by (pose proof (wr_F_range cx); lia).
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold WR_N, CEIL8 in *; lia. }
  split.
  { apply (wr_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold CEIL8, SB in *; lia. }
  split; [exact (lt_amodel_kept B LAWS ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (lt_ainput_kept B LAWS cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (lt_rom_kept W W mem mem' HRV KL)|].
  split; [exact (lt_jt_kept W W mem mem' HJT KL)|].
  (* the fake frame's flag word (lcut's conjunct after aframe_at): below CEIL8, so kept *)
  unfold sv8 in *. apply (akept_vm W mem); [|exact HFL].
  intros x Hx. apply KL. cbn in Hx. unfold CEIL8, SB in *. lia.
Qed.
(* the facts of the cut point 0x84478, at the memory the walk ends in *)
Lemma wr_mid_facts : forall cx t (W : world segs) mem md mem' md' ly3 S3 k m fpos regs',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  (forall x : word, ~ (lf_F cx + WR_N <= bv_unsigned x < lf_F cx + WR_N + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> jt_rom W mem ->
  lregs_T cx t m (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut B G_fr fr_FP LS RINV cx t true (lregs_T cx t) regs' mem' md' W.
Proof.
  intros cx t W mem md mem' md' ly3 S3 k m fpos regs' HB HJ HJ' MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HRI HJT HR.
  pose proof (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ ly3 S3 W mem md k HJ) as HAR.
  assert (Hfp : In (1, fpos) (frames S3)).
  { destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ ly3 S3 W mem md k HJ) as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  pose proof HB as (_ & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + WR_N <= a < lf_F cx + WR_N + 8) ->
      abyte_kept W mem W mem' a).
  { intros a Ha Hna. split.
    - apply aview_eq_of. apply MEQ. rewrite unsigned_lit_small by lia. exact Hna.
    - intros Hw. apply (writable_kept (w_H W) mem mem' a); [|exact Hw].
      intros Hp. exact (wr_pres_grows W mem mem' a MG Hp). }
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a).
  { intros a Hw. apply (writable_kept (w_H W) mem mem' a); [|exact Hw].
    intros Hp. exact (wr_pres_grows W mem mem' a MG Hp). }
  destruct (wr_store_kept cx W mem mem' md ly3 S3 fpos m HAR Hfp (eq_sym Hnlen) ltac:(unfold LLVMF_STK in *; lia)
              HFR HFL HMOD HIN HRV HJT KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2 & HFL2).
  split; [exact HJT2|].
  exists [(1, fpos)], ly3, S3, k, m, fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
  split; [exact HIN2|].
  split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|]. exact HR.
Qed.
(* a symbolic value read as a number *)
Lemma wr_sv_of_U : forall E v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H Hz. apply bv_eq. rewrite unsigned_lit_small by exact Hz. exact H. Qed.
(* the registers the walk to 0x84478 leaves alone *)
Definition WR_KEPT : list (bv 5) := [2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 29]%bv.
Ltac wr_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.

(* the registers of the cut point 0x84478, from the dispatch's and the walk's *)
Lemma wr_regs_T : forall cx t m FF (regs regsD regs' : bvmap 5 word) (W : world segs) mem',
  lregs_common B cx FF regsD -> getr regsD 27 = w64 t -> 0 <= t < OPS_MAX ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 1 ->
  ((exists i, pick (lm_hs m) (wr_kb cx m) = Some i /\ getr regsD 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat i)) \/
   (1 = 1 /\ pick (lm_hs m) (wr_kb cx m) = None /\ getr regsD 21 = w64 0)) ->
  (forall r, In r jt_kept -> getr regs r = getr regsD r) ->
  (forall r, In r WR_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 12 = w64 (wr_n cx m) -> getr regs' 28 = w64 (wr_src cx m) ->
  getr regs' 22 = w64 (c_p cx + wr_k2 cx m) -> sv8 W mem' (lf_F cx + WR_N) (c_n cx - wr_k2 cx m) ->
  lregs_T cx t m FF regs' W mem'.
Proof.
  intros cx t m FF regs regsD regs' W mem' (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4)
    R27 Ht Hk HO Hop HSRC KR0 KR Q12 Q28 Q22 SVN.
  assert (KK : forall r, In r WR_KEPT -> getr regs' r = getr regsD r).
  { intros r Hr. rewrite (KR r Hr). apply KR0. cbv [WR_KEPT In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbv; tauto|]). destruct Hr. }
  split.
  { split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(cbv; tauto)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
    split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
    split; [rewrite (KK 23%bv ltac:(cbv; tauto)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
    split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
    split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
    split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
    rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
  split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|]. split; [exact Hop|].
  split.
  { rewrite (KK 21%bv ltac:(cbv; tauto)).
    destruct HSRC as [(i & Hpk & R21) | (_ & Hpk & R21)]; [left; exists i; split; assumption | right; split; assumption]. }
  split; [exact Q12|]. split; [exact Q28|]. split; [exact Q22|]. exact SVN.
Qed.
(* the registers the walk kept, read off the final symbolic state *)
Ltac wr_kept HS HAE KR2 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    lazymatch type of HAE with env_agree 32 ?er _ =>
      let HAE2 := fresh "HAE2" in
      assert (HAE2 : env_agree 32 er Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]);
      pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ WR_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR2;
      cbn [ms_regs restrict] in KR2; clear HAE2
    end
  end.

(* fuzz_u16 and fuzz_take, 0x843bc-0x84474 *)
Lemma wr_head : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 1 cx t W c -> SRr segs W c (WST cx t).
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  subst own. clear HJOUR.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R6 & R7 & R27 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2' & C3' & C4' & C5).
  (* the operation is 1 *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 1).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 1) with true in HPK.
  destruct HPK as (R28 & R29 & HSRC).
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (wr_k1 cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (wr_kb cx m) in HSRC.
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  (* the arm's registers are the dispatch's *)
  assert (KR : forall r, In r jt_kept -> getr regs r = getr regsD r) by exact KR0.
  assert (R2 : getr regs 2 = w64 (lf_F cx)) by (rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2).
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26).
  assert (R28' : getr regs 28 = w64 (c_p cx + wr_k1 cx m)) by (rewrite (KR 28%bv ltac:(cbv; tauto)); exact R28).
  assert (R29' : getr regs 29 = w64 (wr_rem cx m)) by (rewrite (KR 29%bv ltac:(cbv; tauto)); exact R29).
  assert (R7' : getr regs 7 = w64 1) by (rewrite (KR 7%bv ltac:(cbv; tauto)); exact R7).
  (* the contract's facts *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ ly3 S3 W mem md k HJ) as HAR.
  pose proof (wr_pres cx _ ly3 S3 W mem md k HJ) as Hpres.
  pose proof HJ as HJ0.
  pose proof HIN as (Hblk & Hg).
  destruct Hblk as [(Hn0 & _) | (Hcn & Hin)]; [lia|].
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hin) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil.
  pose proof (wr_F_range cx) as HFr. pose proof (wr_F_mod32 cx) as HFm.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  assert (MEQ : forall x : word, ~ (lf_F cx + WR_N <= bv_unsigned x < lf_F cx + WR_N + 8) ->
    mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by reflexivity.
  assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by apply mem_grows_refl.
  assert (Hrem : 0 <= wr_rem cx m < 2 ^ 26) by (unfold wr_rem; lia).
  assert (Hb0 : 0 <= in_byte cx (wr_k1 cx m) < 256) by (unfold in_byte; apply u8_range).
  assert (Hb1 : 0 <= in_byte cx (wr_k1 cx m + 1) < 256) by (unfold in_byte; apply u8_range).
  destruct (Z_lt_le_dec (wr_rem cx m) 2) as [Hr2 | Hr2].
  1: destruct (Z.eq_dec (wr_rem cx m) 0) as [Hr0 | Hr1].
  - (* ---- no byte left ---- *)
    destruct (wr_entry0 cx m ly3 S3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hcn ltac:(unfold wr_rem in *; lia))
      as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra 0 0))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra 0 0)) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: taken, no byte left *)
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + clear Hc.
      paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      assert (Mu : wr_u cx m = 0) by (unfold wr_u; rewrite Hr0; reflexivity).
      assert (Mc : wr_c cx m = 0) by (unfold wr_c; rewrite Hr0; reflexivity).
      assert (Mn : wr_n cx m = 0) by (unfold wr_n; rewrite Mu, Mc, Hr0; reflexivity).
      assert (Mk2 : wr_k2 cx m = wr_k1 cx m) by (unfold wr_k2; rewrite Mc, Mn; lia).
      assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m) by (unfold wr_src; rewrite Mc; lia).
      wr_kept HS HAE KR2.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
      wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
        assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
        [ unfold sv8, WR_N;
          eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
          [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
          | apply wr_sv_of_U; [rewrite U_lit by lia; unfold wr_rem in Hr0; lia | unfold wr_rem in Hr0; lia]
          | unfold wr_rem in Hr0; lia | zside ]
        | ];
        assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
          by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [apply U_lit; lia | lia]);
        assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
          by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia]);
        assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
          by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia])
      end.
      pmkst HS. apply SRr_ret.
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|].
      apply (wr_mid_facts cx t W mem md _ _ ly3 S3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
      exact (wr_regs_T cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
  - (* ---- one byte left ---- *)
    destruct (wr_entry1 cx m ly3 S3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hg Hnlen Hcn
      ltac:(lia) ltac:(unfold wr_rem in *; lia)) as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0)) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (E7 : ew E 7 = Z_to_bv 64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7').
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: not taken *)
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      (* the shadow-checked byte read, to 0x843d8 bne t4,t2 *)
      paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      wr_pin A29 E29 29%nat (wr_rem cx m). wr_pin A7 E7 7%nat 1.
      psrr_branch_tok RUN BR HS SHOK wr_Bspan.
      * exfalso. rewrite branch_ne_U, (U_atom _ 29 (wr_rem cx m) A29), (U_atom _ 7 1 A7) in Hc by lia.
        apply Bool.negb_true_iff, Z.eqb_neq in Hc. lia.
      * clear Hc. paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
        wr_upd U9 MEQ MG.
        assert (Hr1' : wr_rem cx m = 1) by lia.
        assert (Mc : wr_c cx m = 1) by (unfold wr_c; rewrite Hr1'; reflexivity).
        assert (Mn : wr_n cx m = 0).
        { unfold wr_n. rewrite Mc, Hr1'. apply Z.min_r. unfold wr_u. rewrite Hr1'.
          destruct (Z.leb_spec 2 1); [lia|]. destruct (Z.eqb_spec 1 1); lia. }
        assert (Mk2 : wr_k2 cx m = wr_k1 cx m + 1) by (unfold wr_k2; rewrite Mc, Mn; lia).
        assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m + 1) by (unfold wr_src; rewrite Mc; lia).
        wr_kept HS HAE KR2.
        pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
        wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
        wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
          assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
          [ unfold sv8, WR_N;
            eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
            [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
            | apply wr_sv_of_U; [rewrite U_lit by lia; unfold wr_rem in Hr1'; lia | unfold wr_rem in Hr1'; lia]
            | unfold wr_rem in Hr1'; lia | zside ]
          | ];
          assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
            by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [apply U_lit; lia | lia]);
          assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
            by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 1 A28) by lia; lia | lia]);
          assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
            by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 1 A28) by lia; lia | lia])
        end.
        pmkst HS. apply SRr_ret.
        lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
        split; [reflexivity|].
        apply (wr_mid_facts cx t W mem md _ _ ly3 S3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
        exact (wr_regs_T cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
  - (* ---- two bytes or more left ---- *)
    destruct (wr_entry2 cx m ly3 S3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hg Hnlen Hcn
      ltac:(lia) ltac:(unfold wr_rem in *; lia)) as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1))))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1)))) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (E7 : ew E 7 = Z_to_bv 64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7').
    assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (wr_k1 cx m)))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (E33 : ew E 33 = Z_to_bv 64 (in_byte cx (wr_k1 cx m + 1)))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: not taken *)
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      (* the first shadow-checked byte read, to 0x843d8 bne t4,t2 *)
      paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      wr_pin A29 E29 29%nat (wr_rem cx m). wr_pin A7 E7 7%nat 1.
      psrr_branch_tok RUN BR HS SHOK wr_Bspan.
      * clear Hc.
        (* the second shadow-checked byte read, the u16, to 0x84464 bltu a2,a3 *)
        paj_run_tok RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
        wr_upd U9 MEQ MG.
        wr_pin A32 E32 32%nat (in_byte cx (wr_k1 cx m)).
        wr_pin A33 E33 33%nat (in_byte cx (wr_k1 cx m + 1)).
        wr_pin A29b E29 29%nat (wr_rem cx m).
        assert (Mu : wr_u cx m = in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1))
          by (unfold wr_u; rewrite (proj2 (Z.leb_le 2 (wr_rem cx m)) ltac:(lia)); reflexivity).
        assert (Mc : wr_c cx m = 2) by (unfold wr_c; lia).
        assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m + 2) by (unfold wr_src; rewrite Mc; lia).
        psrr_branch_tok RUN BR HS SHOK wr_Bspan.
        -- (* u16 < in.n: n = u16 *)
           rewrite branch_ltu_U, (wr_u16 _ _ _ A32 A33 Hb0 Hb1) in Hc.
           rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29b) in Hc by lia.
           apply Z.ltb_lt in Hc.
           paj_run_to_tok RUNTO HS HJ SHOK wr_Bspan A_wr_tst. { wr_awr U9. }
           wr_upd U9 MEQ MG.
           assert (Mn : wr_n cx m = in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1))
             by (unfold wr_n; rewrite Mu, Mc; lia).
           assert (Mk2 : wr_k2 cx m = wr_k1 cx m + 2 + wr_n cx m) by (unfold wr_k2; rewrite Mc; lia).
           wr_kept HS HAE KR2.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
           wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
           wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
           wr_pin A32b E32 32%nat (in_byte cx (wr_k1 cx m)).
           wr_pin A33b E33 33%nat (in_byte cx (wr_k1 cx m + 1)).
           wr_pin A29c E29 29%nat (wr_rem cx m).
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
             assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
             [ unfold sv8, WR_N;
               eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
               [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
               | apply wr_sv_of_U;
                 [ rewrite U_SAlu, (U_atom_off _ 29 (wr_rem cx m) (-2) A29c), (wr_u16 _ _ _ A32b A33b Hb0 Hb1) by lia;
                   cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; lia); rewrite Mk2, Mn; unfold wr_rem; lia
                 | rewrite Mk2, Mn; unfold wr_rem in *; lia ]
               | rewrite Mk2, Mn; unfold wr_rem in *; lia | zside ]
             | ];
             assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
               by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [exact (wr_u16 _ _ _ A32b A33b Hb0 Hb1) | lia]);
             assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
               by (rewrite Q22, Mk2, Mn; unfold w64; apply wr_sv_of_U;
                   [ rewrite U_SAlu, (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28), (wr_u16 _ _ _ A32b A33b Hb0 Hb1)
                       by lia;
                     cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; unfold wr_rem in *; lia); lia
                   | unfold wr_rem in *; lia ]);
             assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
               by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28) by lia; lia | lia])
           end.
           pmkst HS. apply SRr_ret.
           lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
           split; [reflexivity|].
           apply (wr_mid_facts cx t W mem md _ _ ly3 S3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
           exact (wr_regs_T cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
        -- (* u16 >= in.n: n = in.n *)
           rewrite branch_ltu_U, (wr_u16 _ _ _ A32 A33 Hb0 Hb1) in Hc.
           rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29b) in Hc by lia.
           apply Z.ltb_ge in Hc.
           paj_run_to_tok RUNTO HS HJ SHOK wr_Bspan A_wr_tst. { wr_awr U9. }
           wr_upd U9 MEQ MG.
           assert (Mn : wr_n cx m = wr_rem cx m - 2) by (unfold wr_n; rewrite Mu, Mc; lia).
           assert (Mk2 : wr_k2 cx m = c_n cx) by (unfold wr_k2; rewrite Mc, Mn; unfold wr_rem; lia).
           wr_kept HS HAE KR2.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
           wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
           wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
           wr_pin A29c E29 29%nat (wr_rem cx m).
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
             assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
             [ unfold sv8, WR_N;
               eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
               [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
               | apply wr_sv_of_U; [rewrite U_lit by lia; lia | lia]
               | lia | zside ]
             | ];
             assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
               by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29c) by lia; lia | lia]);
             assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
               by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U;
                   [ rewrite U_SAlu, (U_atom _ 28 (c_p cx + wr_k1 cx m) A28), (U_atom _ 29 (wr_rem cx m) A29c) by lia;
                     cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; unfold wr_rem in *; lia); unfold wr_rem; lia
                   | lia ]);
             assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
               by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28) by lia; lia | lia])
           end.
           pmkst HS. apply SRr_ret.
           lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
           split; [reflexivity|].
           apply (wr_mid_facts cx t W mem md _ _ ly3 S3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
           exact (wr_regs_T cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
      * exfalso. rewrite branch_ne_U, (U_atom _ 29 (wr_rem cx m) A29), (U_atom _ 7 1 A7) in Hc by lia.
        apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.

(* pick() returns an open slot (_drain.v de_pick_from / de_pick_some) *)
Lemma wr_pick_from : forall hs j k i, pick_from hs j k = Some i ->
  (j <= i < j + length hs)%nat /\ exists h, nth (i - j) hs None = Some h.
Proof.
  induction hs as [|o hs IH]; intros j k i Hp; [discriminate Hp|].
  cbn [pick_from] in Hp. destruct o as [h|].
  - destruct (k =? 0).
    + injection Hp as <-. cbn [length]. split; [lia|]. exists h. rewrite Nat.sub_diag. reflexivity.
    + destruct (IH (S j) (k - 1) i Hp) as [Hr [h' Hh']]. cbn [length]. split; [lia|].
      exists h'. replace (i - j)%nat with (S (i - S j)) by lia. exact Hh'.
  - destruct (IH (S j) k i Hp) as [Hr [h' Hh']]. cbn [length]. split; [lia|].
    exists h'. replace (i - j)%nat with (S (i - S j)) by lia. exact Hh'.
Qed.
Lemma wr_pick_some : forall hs kb i, pick hs kb = Some i ->
  (i < length hs)%nat /\ exists h, nth i hs None = Some h.
Proof.
  intros hs kb i Hp. unfold pick in Hp. destruct (nopen hs =? 0); [discriminate Hp|].
  destruct (wr_pick_from hs 0 (kb mod nopen hs) i Hp) as [Hr [h Hh]].
  rewrite Nat.sub_0_r in Hh. split; [lia | exists h; exact Hh].
Qed.

(* ------------------------------------------------------------------ 0x8448c li s4,10, to the latch *)
(* the arm's join: operation t done, the model the one after it, the registers the latch's (x20 is 10 on every
   path: lregs_D keeps it and list_push preserves it); li s4,10 stores it again *)
Definition JST (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + A_wr_li) regs mem md /\ jt_rom W mem /\
    lcut B G_fr fr_FP LS RINV cx (t + 1) true (lregs_K B cx t) regs mem md W.
Definition wj_facts : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition wj_extra : list word := map (Z_to_bv 64) [SB].
Definition WBx : sv := SOff 32 0.
(* every register but s4 *)
Definition WJ_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma wj_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs wj_extra)) (mkSS A_wr_li sr_atoms [] None wj_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_li)) mem (seg_rom segs)))
  /\ sh_ok segs WBx [] (Eimg (Ereg regs wj_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs wj_extra)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [wj_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Lemma wt_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs wj_extra)) (mkSS A_wr_tst sr_atoms [] None wj_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_tst)) mem (seg_rom segs)))
  /\ sh_ok segs WBx [] (Eimg (Ereg regs wj_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs wj_extra)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [wj_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* a run over read-only regions leaves the memory as it was (_cut's jt_mem) *)
Ltac wr_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

Lemma wr_join : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  JST cx t W c -> SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (wj_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs wj_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs wj_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_wr_li)) with (Z_to_bv 64 (BASE + A_wr_li)).
  paj_run_to_tok RUNTO HS HJ SHOK wr_Bspan AF_LLVM_latch. { apply awr_ok_x_nil. }
  wr_mem HF Em. clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (20%bv : bv 5) Q20.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht & R22 & SVN & Hk).
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite Q20; reflexivity|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [exact SVN | exact Hk].
Qed.

Lemma in_byte_range : forall cx i, 0 <= in_byte cx i < 256.
Proof. intros cx i. unfold in_byte. apply u8_range. Qed.
Lemma wr_n_range : forall cx m, wr_k1 cx m <= c_n cx ->
  0 <= wr_n cx m < 65536 /\ wr_k1 cx m <= wr_k1 cx m + wr_c cx m /\ wr_k1 cx m + wr_c cx m <= wr_k2 cx m <= c_n cx.
Proof.
  intros cx m H.
  assert (Hu : 0 <= wr_u cx m < 65536).
  { unfold wr_u. pose proof (in_byte_range cx (wr_k1 cx m)). pose proof (in_byte_range cx (wr_k1 cx m + 1)).
    destruct (2 <=? wr_rem cx m); [|destruct (wr_rem cx m =? 1)]; lia. }
  unfold wr_k2, wr_n, wr_c in *. unfold wr_rem in *. lia.
Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps
   (lib/A/W_op_add.v oa_call_keep / oa_call_keep_blk / oa_call_keep_hi and lib/A/W_source_reset.v gx_keep_*, at
   any callee G1: the donor journal's clauses read through ajournal_g's overlay) *)
Lemma wr_ck_img : forall G1 STK sp1 FP1 ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  ajournal_gx segs B G1 0 [] STK sp1 FP1 ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP1 ->
  forall a, in_img segs a -> ~ inG G1 a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma wr_ck_blk : forall G1 STK sp1 FP1 ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 ->
  ajournal_gx segs B G1 0 [] STK sp1 FP1 ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP1 (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G1 STK sp1 FP1 ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G1 (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img segs B LAWS ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
Lemma wr_ck_hi : forall G1 STK sp1 FP1 ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 ->
  ajournal_gx segs B G1 0 [] STK sp1 FP1 ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK <= a < sp1) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* the caller's fake frame and its shadow, outside the callee's FP *)
Lemma wr_ck_frm : forall G1 STK sp1 FP1 ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 -> AR segs B ly0 S0 W0 m0 md0 ->
  ajournal_gx segs B G1 0 [] STK sp1 FP1 ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall cid pos a, In (cid, pos) (frames S0) ->
  (frame_addr ly0 cid pos <= a < frame_addr ly0 cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly0 cid pos) <= a < shadow_addr (frame_addr ly0 cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP FP1 a -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HAR0 HJx cid pos a Hf Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds segs B LAWS ly0 S0 W0 m0 md0 cid pos HAR0 Hf) as (HF1 & HF2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as HFB.
  assert (HSA : SHADOW_OFF <= shadow_addr (frame_addr ly0 cid pos) /\
                shadow_addr (frame_addr ly0 cid pos) + fs_frame_bytes cid / 8 <= SHADOW_OFF + alloc_ceiling).
  { unfold shadow_addr.
    assert (H1 : 0 <= frame_addr ly0 cid pos / 8 <= frame_addr ly0 cid pos)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (H2 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    lia. }
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hf ltac:(unfold frame_rng, in_zr; cbn [fst snd]; exact Ha) Hno).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  unfold SHADOW_OFF in HSA.
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  destruct Ha as [Ha | Ha].
  - destruct (al_client_img _ _ LAWS ly0 S0 W0 m0 md0 a HAR0
      ltac:(right; left; exists cid, pos; split; [exact Hf | lia])) as [_ Hni].
    exact (Hni (proj1 (HGok a Hin))).
  - pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* ------------------------------------------------------------------ the bytes a representation reads: a range of
   globals, or a byte of one of its blocks (the footprints of lib/A/W_rep.v's frame lemmas; the shape of _latch.v's
   lt_alist .. lt_aout, with "below CEIL8" replaced by "a global or inside a block of the predicate") *)
Definition blk_cov (bl : list (Z * Z)) (a : Z) : Prop := exists b n, In (b, n) bl /\ b <= a < b + req_size n.
Lemma wr_akept_cov : forall (W W' : world segs) mem mem' fp (P : Z -> Prop) bl,
  (forall r, In r fp -> forall a, fst r <= a < snd r -> P a \/ blk_cov bl a) ->
  (forall a, P a -> abyte_kept W mem W' mem' a) ->
  (forall b n, In (b, n) bl -> forall j, 0 <= j < req_size n -> abyte_kept W mem W' mem' (b + j)) ->
  akept W mem W' mem' fp.
Proof.
  intros W W' mem mem' fp P bl HC HP HB r Hr a Ha.
  destruct (HC r Hr a Ha) as [Hp | (b & n & Hin & Hba)]; [exact (HP a Hp)|].
  replace a with (b + (a - b)) by lia. apply (HB b n Hin). lia.
Qed.
Lemma blk_cov_incl : forall bl bl' a, incl bl bl' -> blk_cov bl a -> blk_cov bl' a.
Proof. intros bl bl' a Hi (b & n & Hb & Ha). exists b, n. split; [exact (Hi _ Hb) | exact Ha]. Qed.
Lemma wr_cov_alist : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ blk_cov (alist_blks l) a.
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) r Hr a Ha.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn in Ha; lia|].
  apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
    destruct Hr as [<- | []]. right. exists (hl_v l), (AREC * hl_cap l).
    split; [unfold alist_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); apply in_or_app; left; left; reflexivity|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    cbn [gfp fst snd] in Ha. rewrite lt_bzs_len, length_app, lt_concat_len in Ha.
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq].
    unfold hl_n, AREC in *. lia.
  - apply in_map_iff in Hr. destruct Hr as (x & <- & Hx). right.
    exists (fst x), (Z.of_nat (length (snd x)) + 1).
    split; [unfold alist_blks; apply in_or_app; right;
            apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hx|].
    cbn [gfp fst snd] in Ha. rewrite lt_bzs_len, length_app in Ha. cbn [length] in Ha.
    pose proof (req_size_pos (Z.of_nat (length (snd x)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma wr_cov_asrc : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
  (HA <= a < HA + ASRC) \/ blk_cov (asrc_blks h) a.
Proof.
  intros ly S W mem HA h HS r Hr a Ha.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - left. cbn in Ha. lia.
  - right. exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
    cbn [gfp fst snd] in Ha. rewrite lt_bzs_len, Hpj in Ha. unfold req_size, APARTIAL in *. cbn. lia.
  - apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    { destruct (wr_cov_alist ly S W mem _ _ _ Hpend r Hr a Ha) as [Hh | Hb]; [left; unfold ASRC; lia|].
      right. apply (blk_cov_incl (alist_blks (hs_pending h))); [|exact Hb].
      intros x Hx. unfold asrc_blks. right. apply in_or_app. left. exact Hx. }
    apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    { destruct (wr_cov_alist ly S W mem _ _ _ Hexp r Hr a Ha) as [Hh | Hb]; [left; unfold ASRC; lia|].
      right. apply (blk_cov_incl (alist_blks (hs_expected h))); [|exact Hb].
      intros x Hx. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hx. }
    { destruct (wr_cov_alist ly S W mem _ _ _ Hheld r Hr a Ha) as [Hh | Hb]; [left; unfold ASRC; lia|].
      right. apply (blk_cov_incl (alist_blks (hs_held h))); [|exact Hb].
      intros x Hx. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hx. }
Qed.
Lemma wr_cov_aentry : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> blk_cov (aentry_blks e) a.
Proof.
  intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) r Hr a Ha.
  unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
    destruct Hr as [<- | []].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
    exists (re_buf e), (re_cap e).
    split; [unfold aentry_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); apply in_or_app; left; left; reflexivity|].
    cbn [gfp fst snd] in Ha. rewrite lt_bzs_len, length_app in Ha.
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + cbn [gfp fst snd] in Ha. rewrite lt_bzs_len, lt_key_ptrs_len in Ha.
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      { rewrite Hz, Hks in Ha. cbn [length] in Ha. lia. }
      exists (re_hp e), (re_kh e).
      split; [unfold aentry_blks; apply in_or_app; right; rewrite (proj2 (Z.eqb_neq _ _) Hz);
              apply in_or_app; left; left; reflexivity|].
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq].
      unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr. destruct Hr as (kk & <- & Hk).
      exists (key_addr kk), (Z.of_nat (length (key_text kk)) + 1).
      split; [unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
              apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
      cbn [gfp fst snd] in Ha. rewrite lt_bzs_len, length_app in Ha. cbn [length] in Ha.
      pose proof (req_size_pos (Z.of_nat (length (key_text kk)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma wr_cov_arelay : forall ly S (W : world segs) mem G es, arelay_at B fr_RG ly S W mem G es ->
  forall r, In r (arelay_fp fr_RG G es) -> forall a, fst r <= a < snd r ->
  inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4)] a \/ blk_cov (arelay_blks G es) a.
Proof.
  intros ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) r Hr a Ha.
  unfold arelay_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | Hr]]]].
  - left. apply inG_cons. left. unfold in_zr. cbn in Ha |- *. lia.
  - left. apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn in Ha |- *. lia.
  - left. apply inG_cons. right. apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn in Ha |- *. lia.
  - right. exists G, ATABLE. split; [left; reflexivity|]. cbn [fst snd] in Ha.
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - right. apply in_concat in Hr. destruct Hr as (f & Hf & Hr). apply in_map_iff in Hf. destruct Hf as (e & <- & He).
    rewrite Forall_forall in R10.
    apply (blk_cov_incl (aentry_blks e)); [|exact (wr_cov_aentry ly S W mem e (R10 e He) r Hr a Ha)].
    intros x Hx. unfold arelay_blks. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map; exact He | exact Hx].
Qed.
Definition wr_out_G : list (Z * Z) :=
  [(rg_send_max fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4);
   (rg_client_broken fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1)].
Lemma wr_cov_aout : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  forall r, In r (aout_fp B fr_RG cap out) -> forall a, fst r <= a < snd r ->
  inG wr_out_G a \/ (as_errno B <= a < as_errno B + 4) \/ blk_cov (aout_blks cap out) a.
Proof.
  intros ly S W mem c O mx no cap out HO r Hr a Ha.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp in Hr. unfold wr_out_G.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
    try (left; unfold inG; repeat (first [apply Exists_cons_hd; unfold in_zr; cbn in Ha |- *; lia
                                         | apply Exists_cons_tl]); fail).
  - right. left. cbn in Ha. lia.
  - right. right. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hr|].
    destruct Hr as [<- | []]. destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|].
    exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); left; reflexivity|].
    cbn [fst snd] in Ha. pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Ltac wr_inG := unfold wr_G, inG;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd fr_RG fr_globals rg_src rg_nsrc rg_capsrc
    rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr rg_gone rg_lock
    rg_wake] in *; unfold AG_NFD, AG_THREAD_UP, AG_LISTEN in *; lia | apply Exists_cons_tl]).
(* the bytes the model at slot si keeps across list_push: the other globals, and g_s but the pending list head *)
Definition wr_glob (HA a : Z) : Prop :=
  inG wr_G a \/ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC /\ ~ (HA + 16 <= a < HA + 32)).
Lemma wr_inG_rel : forall HA a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4)] a -> wr_glob HA a.
Proof.
  intros HA a Ha. left. unfold inG in Ha. rewrite !Exists_cons, Exists_nil in Ha. unfold in_zr in Ha.
  cbn [fst snd] in Ha. destruct Ha as [Ha | [Ha | [Ha | []]]]; wr_inG.
Qed.
Lemma wr_inG_out : forall HA a, inG wr_out_G a -> wr_glob HA a.
Proof.
  intros HA a Ha. left. unfold wr_out_G, inG in Ha. rewrite !Exists_cons, Exists_nil in Ha. unfold in_zr in Ha.
  cbn [fst snd] in Ha. repeat (destruct Ha as [Ha | Ha]; [wr_inG|]). destruct Ha.
Qed.
(* a slot of the model, at the same position of a list split around slot si *)
Lemma wr_slot_split : forall (hs1 hs2 : list (option hsrc)) o i b,
  i <> length hs1 -> In b (slot_blks (nth i (hs1 ++ o :: hs2) None)) ->
  In b (concat (map slot_blks hs1)) \/ In b (concat (map slot_blks hs2)).
Proof.
  intros hs1 hs2 o i b Hi Hb.
  destruct (Nat.lt_ge_cases i (length hs1)) as [Hlt | Hge].
  - left. rewrite app_nth1 in Hb by exact Hlt. apply in_concat. exists (slot_blks (nth i hs1 None)).
    split; [apply in_map; apply nth_In; exact Hlt | exact Hb].
  - right. rewrite app_nth2 in Hb by exact Hge. destruct (i - length hs1)%nat as [|j] eqn:Ej; [lia|].
    cbn [nth] in Hb. destruct (Nat.lt_ge_cases j (length hs2)) as [Hj | Hj].
    + apply in_concat. exists (slot_blks (nth j hs2 None)). split; [apply in_map; apply nth_In; exact Hj | exact Hb].
    + rewrite nth_overflow in Hb by exact Hj. cbn in Hb. destruct Hb.
Qed.
(* the model across list_push: slot si is the pushed source h', every other part is carried (the content of the
   donor's a1c_relay / a1c_out / a1_globals, over the representation of lib/A/W_rep.v) *)
Lemma wr_amodel_tr : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' m (si : nat) h h' OTH
    hs1 hs2 k',
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  lm_hs m = hs1 ++ Some h :: hs2 -> length hs1 = si -> (si < 4)%nat ->
  (forall a, wr_glob (rg_s fr_RG + ASRC * Z.of_nat si) a -> abyte_kept W mem W' mem' a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W' mem' a) ->
  (forall b n, In (b, n) OTH -> In (b, n) (ablocks B ly' S') /\
     forall j, 0 <= j < req_size n -> abyte_kept W mem W' mem' (b + j)) ->
  incl ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1) ++
        concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)) OTH ->
  asrc_at B ly' S' W' mem' (rg_s fr_RG + ASRC * Z.of_nat si) h' ->
  amodel_at B ly' S' W' mem' (wr_push m k' si (h') (ct_ev (lm_c m))).
Proof.
  intros ly S W mem md ly' S' W' mem' m si h h' OTH hs1 hs2 k' HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10)
    Ehs Hl1 Hsi KG KE KB Hincl HSRC.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (AK : forall fp (P : Z -> Prop) bl, (forall r, In r fp -> forall a, fst r <= a < snd r -> P a \/ blk_cov bl a) ->
      (forall a, P a -> wr_glob HA a) -> incl bl OTH -> akept W mem W' mem' fp).
  { intros fp P bl HC HP Hbl. apply (wr_akept_cov W W' mem mem' fp P bl HC).
    - intros a Ha. apply KG, HP, Ha.
    - intros b n Hb j Hj. exact (proj2 (KB b n (Hbl _ Hb)) j Hj). }
  assert (KL : forall b, In b OTH -> In b (ablocks B ly' S')) by (intros [b n] Hb; exact (proj1 (KB b n Hb))).
  assert (KGg : forall a, inG wr_G a -> abyte_kept W mem W' mem' a) by (intros a Ha; apply KG; left; exact Ha).
  unfold amodel_at, wr_push. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite set_nth_length; exact M1|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite set_nth_same by (rewrite M1; exact Hi). exact HSRC.
    - rewrite set_nth_other by (intros E; apply Hne; symmetry; exact E).
      specialize (M2 i Hi). unfold aslot in *.
      assert (Hne' : Z.of_nat i <> Z.of_nat si) by lia.
      assert (HGi : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
          wr_glob HA a).
      { intros a Ha. right. unfold HA. unfold fr_RG, ASRC in *. cbn [rg_s fr_globals] in *.
        clear - Ha Hi Hsi Hne'. split; lia. }
      destruct (nth i (lm_hs m) None) as [hj|] eqn:Ehj.
      + apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ hj M2).
        * apply (AK (asrc_fp _ hj) (fun a => rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC)
                    (asrc_blks hj) (wr_cov_asrc ly S W mem _ hj M2) HGi).
          intros b Hb. apply Hincl.
          assert (Hb' : In b (slot_blks (nth i (hs1 ++ Some h :: hs2) None))) by (rewrite <- Ehs, Ehj; exact Hb).
          destruct (wr_slot_split hs1 hs2 (Some h) i b ltac:(lia) Hb') as [H1 | H2];
            [right; apply in_or_app; right; apply in_or_app; left; exact H1
            | right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact H2].
        * intros b Hb. apply KL. apply Hincl.
          assert (Hb' : In b (slot_blks (nth i (hs1 ++ Some h :: hs2) None))) by (rewrite <- Ehs, Ehj; exact Hb).
          destruct (wr_slot_split hs1 hs2 (Some h) i b ltac:(lia) Hb') as [H1 | H2];
            [right; apply in_or_app; right; apply in_or_app; left; exact H1
            | right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact H2].
      + destruct M2 as [G1 G2]. split.
        * apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
          apply KG, HGi. unfold ASRC in *. lia.
        * apply (akept_awr W mem); [|exact G2]. intros x Hx. apply KG, HGi. lia. }
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ M3).
    - apply (AK _ _ _ (wr_cov_arelay ly S W mem _ _ M3)); [intros a Ha; apply wr_inG_rel; exact Ha|].
      intros b Hb. apply Hincl. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb.
    - intros b Hb. apply KL. apply Hincl. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb. }
  split.
  { destruct (lm_c m) as [cl br dd ei ev]. cbn [set_ev ct_ev].
    apply (aout_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ M4).
    - apply (wr_akept_cov W W' mem mem' _ (fun a => inG wr_out_G a \/ (as_errno B <= a < as_errno B + 4))
               (aout_blks (lm_cap m) (lm_out m))).
      + intros r Hr a Ha. destruct (wr_cov_aout ly S W mem _ _ _ _ _ _ M4 r Hr a Ha) as [H1 | [H1 | H1]];
          [left; left; exact H1 | left; right; exact H1 | right; exact H1].
      + intros a [Ha | Ha]; [apply KG, wr_inG_out, Ha | apply KE, Ha].
      + intros b n Hb j Hj. apply (proj2 (KB b n (Hincl _ ltac:(right; apply in_or_app; right; apply in_or_app;
          right; apply in_or_app; right; exact Hb)))). exact Hj.
    - intros b Hb. apply KL. apply Hincl. right. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hb. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r Hr a Ha. destruct Hr as [<- | []].
    apply KGg. cbn [fst snd] in Ha. wr_inG. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []].
    apply KGg. cbn [fst snd] in Ha. wr_inG. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r Hr a Ha. destruct Hr as [<- | []].
    apply KGg. cbn [fst snd] in Ha. wr_inG. }
  split; [apply (akept_vm W mem); [intros x Hx; apply KGg; cbn in Hx; wr_inG | exact M8]|].
  destruct M10 as (M11 & M12 & M13 & M14).
  split; [apply (akept_awr W mem); [intros x Hx; apply KGg; wr_inG | exact M9]|].
  split; [exact M11|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KGg; cbn in Hx; wr_inG | exact M12]|].
  split; [destruct M13 as [lst M13]; exists lst;
          apply (akept_vm W mem); [intros x Hx; apply KGg; cbn in Hx; wr_inG | exact M13]|].
  apply (akept_awr W mem); [intros x Hx; apply KGg; wr_inG | exact M14].
Qed.

(* ------------------------------------------------------------------ the live blocks: distinct, one per address *)
(* lib/A/W_gesture_end.v ablocks_nodup *)
Lemma wr_ablocks_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* two live blocks at one address are one block (the donor's a1_uniq) *)
Lemma wr_uniq : forall ly S (W : world segs) mem md p n n', AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (p, n') (ablocks B ly S) -> n = n'.
Proof.
  intros ly S W mem md p n n' HAR H1 H2. destruct (Z.eq_dec n n') as [E|Hne]; [exact E|]. exfalso.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
  destruct (al_blocks _ _ LAWS ly S W mem md p n' HAR H2) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos n' ltac:(lia)).
  pose proof (sep_blocks segs B LAWS ly S W mem md p n p n' HAR H1 H2 ltac:(intros E; injection E; lia)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a live block other than the vector is apart from list_push's FP *)
Lemma wr_nohit : forall ly S (W : world segs) mem md p n v c, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (v, AREC * c) (ablocks B ly S) -> 0 < c -> (p, n) <> (v, AREC * c) ->
  forall j, 0 <= j < req_size n -> ~ inFP [(v, v + AREC * c)] (p + j).
Proof.
  intros ly S W mem md p n v c HAR H1 H2 Hc Hne j Hj (r & Hr & Hra). destruct Hr as [<- | []].
  cbn [fst snd] in Hra.
  pose proof (sep_blocks segs B LAWS ly S W mem md p n v (AREC * c) HAR H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hrq : req_size (AREC * c) = AREC * c) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * c) 0); lia).
  rewrite Hrq in Hd. lia.
Qed.
Lemma wr_map_fst_alist_blks : forall l, map fst (alist_blks l) = list_blocks l.
Proof.
  intros l. unfold alist_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
  destruct (hl_cap l =? 0); reflexivity.
Qed.

(* ------------------------------------------------------------------ the source list_push pushed into: its pending
   list is the callee's l', every other part carried (the donor's a1_src_push) *)
Lemma wr_asrc_push : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' HA h l' d x,
  asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> ~ (HA + 16 <= a < HA + 32) -> abyte_kept W mem W' mem' a) ->
  (forall a, HA <= a < HA + ASRC -> writable_at segs (arm W' mem') a) ->
  (forall b n, In (b, n) ((hs_partial h, APARTIAL) :: alist_blks (hs_expected h) ++ alist_blks (hs_held h)) ->
     In (b, n) (ablocks B ly' S') /\ forall j, 0 <= j < req_size n -> abyte_kept W mem W' mem' (b + j)) ->
  alist_at B ly' S' W' mem' (HA + 16) l' false ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] -> (1 <= length x)%nat ->
  NoDup (hs_blocks (set_pending h l')) ->
  asrc_at B ly' S' W' mem' HA (set_pending h l').
Proof.
  intros ly S W mem ly' S' W' mem' HA h l' d x
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) KS WS KB HL' HREC Hx1 HND.
  assert (Hvm : forall a n v, HA <= a ->
      (a + Z.of_nat n <= HA + 16 \/ (HA + 32 <= a /\ a + Z.of_nat n <= HA + 96)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v).
  { intros a n v H0 Hr Hv. apply (akept_vm W mem); [|exact Hv]. intros y Hy. apply KS; unfold ASRC; lia. }
  unfold asrc_at.
  cbn [set_pending hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong
       hs_pad hs_expected hs_held].
  split; [apply Hvm; [lia | left; cbn; lia | exact H1]|].
  split; [apply Hvm; [lia | left; cbn; lia | exact H2]|].
  split; [apply Hvm; [lia | left; cbn; lia | exact H3]|].
  split; [apply Hvm; [lia | left; cbn; lia | exact H4]|].
  split; [intros i Hi; apply WS; lia|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [exact HL'|].
  split; [apply Hvm; [lia | right; cbn; lia | exact H11]|].
  split; [apply Hvm; [lia | right; cbn; lia | exact H12]|].
  split; [apply Hvm; [lia | right; cbn; lia | exact H13]|].
  split; [apply Hvm; [lia | right; cbn; lia | exact H14]|].
  split.
  { rewrite HREC. right. destruct H15 as [(Hnil & Hoff) | (r & rs & Er & Hoff)].
    - rewrite Hnil. exists (d, x), []. split; [reflexivity|]. cbn [snd]. lia.
    - rewrite Er. exists r, (rs ++ [(d, x)]). split; [reflexivity | exact Hoff]. }
  split; [exact H16|]. split; [exact H17|].
  split; [exact (proj1 (KB _ _ (or_introl eq_refl)))|].
  split; [exact H19|].
  split.
  { apply (akept_garr8 W mem); [|exact H20]. intros y Hy. rewrite lt_bzs_len, H19 in Hy.
    replace y with (hs_partial h + (y - hs_partial h)) by lia.
    apply (proj2 (KB _ _ (or_introl eq_refl))). pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)).
    lia. }
  split; [exact H21|].
  split.
  { apply (alist_at_kept B ly S W mem ly' S' W' mem' (HA + 64) _ true H22).
    - apply (wr_akept_cov W W' mem mem' _ (fun a => HA + 64 <= a < HA + 64 + 16) (alist_blks (hs_expected h))
               (wr_cov_alist ly S W mem _ _ _ H22)).
      + intros a Ha. apply KS; unfold ASRC; lia.
      + intros b n Hb j Hj. apply (proj2 (KB b n ltac:(right; apply in_or_app; left; exact Hb))). exact Hj.
    - intros [b n] Hb. exact (proj1 (KB b n ltac:(right; apply in_or_app; left; exact Hb))). }
  split.
  { apply (alist_at_kept B ly S W mem ly' S' W' mem' (HA + 80) _ true H23).
    - apply (wr_akept_cov W W' mem mem' _ (fun a => HA + 80 <= a < HA + 80 + 16) (alist_blks (hs_held h))
               (wr_cov_alist ly S W mem _ _ _ H23)).
      + intros a Ha. apply KS; unfold ASRC; lia.
      + intros b n Hb j Hj. apply (proj2 (KB b n ltac:(right; apply in_or_app; right; exact Hb))). exact Hj.
    - intros [b n] Hb. exact (proj1 (KB b n ltac:(right; apply in_or_app; right; exact Hb))). }
  exact HND.
Qed.

(* ------------------------------------------------------------------ the frame and the fake frame across the call
   (the frame cells lie in [F, sp0), the fake frame and its shadow are a frame of the cut) *)
Lemma wr_aframe_call : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> apresent (w_H W') mem' a) ->
  (forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    KV KP KF.
  pose proof (wr_F_range cx) as HFr.
  assert (SV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 Hv. unfold sv8, arm in *. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact Hv].
    intros q Hq. apply KV. cbn in Hq. lia. }
  assert (FV : forall a v, FF <= a -> a + 8 <= FF + 128 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 Hv. apply (akept_vm W mem); [|exact Hv]. intros q Hq. apply KF. cbn in Hq. lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply SV; [lia | lia | exact (A1 o r Hin)]. }
  split; [intros i Hi; apply (apresent_writable segs); apply KP; lia|].
  do 9 (split; [apply SV; [lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply SV; [lia | lia | assumption]|]).
    apply SV; [lia | lia | assumption]. }
  split; [apply FV; [lia | lia | exact A13]|].
  split; [apply FV; [lia | lia | exact A14]|].
  split; [apply FV; [lia | lia | exact A15]|].
  split; [apply (akept_awr W mem); [intros q Hq; apply KF; lia | exact A16]|].
  split.
  - apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros q Hq.
    unfold fake_shadow in Hq. cbn [length] in Hq. apply KF. lia.
  - apply (akept_awr W mem); [intros q Hq; apply KF; lia | exact (proj2 A17)].
Qed.

(* ------------------------------------------------------------------ the read-only image *)
(* no read-only segment meets a range of G (W_LLVMFuzzerTestOneInput_G.v rom_apart, here so as not to import it) *)
Definition wr_rom_apart (G : list (Z * Z)) : bool :=
  forallb (fun sg => seg_writable sg || forallb (fun r =>
    (fst r + snd r <=? Z.of_N (seg_base sg)) || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) G) segs.
Lemma wr_rom_apart_ok : forall G a, wr_rom_apart G = true -> in_rom segs a -> ~ inG G a.
Proof.
  intros G a H (sg & Hs & Hw & Hr) Ha. unfold wr_rom_apart in H. rewrite forallb_forall in H.
  specialize (H sg Hs). rewrite Hw in H. cbn [orb] in H. rewrite forallb_forall in H.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr' & Hz). specialize (H r Hr').
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; unfold in_zr in Hz; lia.
Qed.
Definition wr_romb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma wr_romb_ok : forall a, wr_romb a = true -> in_rom segs a.
Proof.
  intros a H. unfold wr_romb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hw H1].
  apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hs|]. split; [exact Hw | lia].
Qed.
(* the jump table is read-only, so a ROM-view state keeps it *)
Lemma wr_jt_rom_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJT HR HR' i Hi.
  assert (HB : forallb wr_romb (map (fun j => fr_jtab + Z.of_nat j) (seq 0 36)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in HB.
  apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
  intros q Hq. cbn in Hq.
  assert (Hrom : in_rom segs (fr_jtab + 4 * i + q)).
  { apply wr_romb_ok. replace (fr_jtab + 4 * i + q) with (fr_jtab + Z.of_nat (Z.to_nat (4 * i + q))) by lia.
    apply HB. apply in_map_iff. exists (Z.to_nat (4 * i + q)). split; [reflexivity | apply in_seq; lia]. }
  rewrite (HR' _ Hrom), (HR _ Hrom). reflexivity.
Qed.

(* errno's place below CEIL8, the premise _latch.v's lt_afn_pre_at (the call site's afn_pre) takes: the allocator
   instance's api_env (pal_env) *)
Lemma wr_errno_low : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8.
Proof. pose proof (pal_env B TL) as ((HE0 & HE1) & _). pose proof lt_ceil_lo. unfold CEIL8, kLowMemEnd in *. lia. Qed.

(* ------------------------------------------------------------------ list_push's own G: the 16 bytes of the
   pending list's head of slot si (W_contract.v lp_spec_g at G = wr_G1 si, lifted with ajournal_gx_G_mono) *)
Definition wr_LA (si : nat) : Z := rg_s fr_RG + ASRC * Z.of_nat si + 16.
Definition wr_G1 (si : nat) : list (Z * Z) := [(wr_LA si, 16)].
Lemma wr_G1_gs : forall si a, (si < 4)%nat -> inG (wr_G1 si) a ->
  wr_LA si <= a < wr_LA si + 16 /\ rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC.
Proof.
  intros si a Hsi Ha. unfold wr_G1 in Ha. apply inG_cons in Ha as [Ha | Ha]; [|destruct (inG_nil a Ha)].
  unfold in_zr in Ha. cbn [fst snd] in Ha. unfold wr_LA, ASRC in *.
  assert (Z.of_nat si <= 3) by lia. split; lia.
Qed.
Lemma wr_G1_fr : forall si, (si < 4)%nat -> forall a, inG (wr_G1 si) a -> inG G_fr a.
Proof. intros si Hsi a Ha. apply HGs. exact (proj2 (wr_G1_gs si a Hsi Ha)). Qed.
Lemma wr_gx_ok1 : forall si, (si < 4)%nat -> gx_ok segs B (wr_G1 si).
Proof. intros si Hsi. exact (gx_ok_sub segs B (wr_G1 si) G_fr (wr_G1_fr si Hsi) HG). Qed.
(* the runtime's two static cells gx_rt names are apart from g_s (vm_compute at PB_fr; _G.v c_HAP) *)
Lemma wr_HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
               (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rg_s fr_RG).
Proof.
  assert (H0 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  assert (H1 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 32)) || (VAL (A_OBJ 32) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in H0, H1. split.
  - destruct H0 as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
  - destruct H1 as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
Qed.
Lemma wr_gx_rt1 : forall si, (si < 4)%nat -> gx_rt B (wr_G1 si).
Proof.
  intros si Hsi a Ha. destruct (wr_G1_gs si a Hsi Ha) as [_ Hs].
  split; [apply HERRS; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia|].
  destruct wr_HAP as [[H0|H0] [H1|H1]]; split; lia.
Qed.
Lemma wr_azs1 : forall si, (si < 4)%nat -> azs B (wr_LA si) 16.
Proof.
  intros si Hsi. destruct HZS as (r & Hr & H8 & H1 & H2). exists r. split; [exact Hr|]. split; [exact H8|].
  unfold wr_LA, ASRC in *. assert (Z.of_nat si <= 3) by lia. split; lia.
Qed.
(* the pending list's head is 8-aligned (lp_spec's LA mod 8 = 0): g_s = 0x5d88e0, slots of 96 bytes, offset 16 *)
Lemma wr_LA8 : forall si, wr_LA si mod 8 = 0.
Proof.
  intros si. unfold wr_LA, ASRC. change (rg_s fr_RG) with 6129888.
  replace (6129888 + 96 * Z.of_nat si + 16) with ((766238 + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult.
Qed.
(* rom_out at list_push's G (W_journal.v:396): g_s and the sink's head are no ROM (vm_compute), ROM_PIN, ROM_ERR *)
Lemma wr_rom_out1 : forall si, (si < 4)%nat -> rom_out segs B (wr_G1 si).
Proof.
  intros si Hsi a Ha.
  split.
  { intros HG1. destruct (wr_G1_gs si a Hsi HG1) as [_ Hs].
    assert (Hb : wr_rom_apart [(rg_s fr_RG, 4 * ASRC)] = true) by (vm_compute; reflexivity).
    apply (wr_rom_apart_ok _ a Hb Ha).
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
  split; [exact (ROM_PIN a Ha)|]. split; [exact (ROM_ERR a Ha)|].
  intros Hh. assert (Hb : wr_rom_apart [(AOFL_HEAD, 8)] = true) by (vm_compute; reflexivity).
  apply (wr_rom_apart_ok _ a Hb Ha).
  apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* errno-style apartness of a list of ranges, as a boolean *)
Lemma wr_apart_b : forall L lo n, forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) L = true ->
  forall a, inG L a -> ~ (lo <= a < lo + n).
Proof.
  intros L lo n H a Ha Hlo. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Hz.
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma wr_G_gs : forall a, inG wr_G a -> ~ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
Proof. apply wr_apart_b. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ the bytes list_push copies *)
Lemma wr_nth_firstn : forall {A} (L : list A) N j d, (j < N)%nat -> nth j (firstn N L) d = nth j L d.
Proof.
  intros A L. induction L as [|x L IH]; intros [|N] [|j] d H; cbn [firstn nth]; try lia; try reflexivity.
  apply IH. lia.
Qed.
Lemma wr_nth_skipn : forall {A} (L : list A) K j d, nth j (skipn K L) d = nth (K + j) L d.
Proof.
  intros A L. induction L as [|x L IH]; intros [|K] j d; cbn [skipn nth Nat.add]; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.
Lemma wr_garr8_x : forall m b (pl : list byte) K N,
  garr8 segs m b (map (fun x : byte => bv_unsigned x) pl) -> (K + N <= length pl)%nat ->
  garr8 segs m (b + Z.of_nat K) (bzs (firstn N (skipn K pl))).
Proof.
  intros m b pl K N Hg HK j Hj. unfold bzs in Hj |- *. rewrite length_map, length_firstn, length_skipn in Hj.
  destruct (Hg (K + j)%nat ltac:(rewrite length_map; lia)) as [H1 H2].
  assert (E : nth j (map bz (firstn N (skipn K pl))) 0 = nth (K + j) (map (fun x : byte => bv_unsigned x) pl) 0).
  { rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_firstn, length_skipn; lia).
    rewrite map_nth.
    rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
    rewrite map_nth. unfold bz. rewrite wr_nth_firstn by lia. rewrite wr_nth_skipn. reflexivity. }
  rewrite E. replace (b + Z.of_nat K + Z.of_nat j) with (b + Z.of_nat (K + j)) by lia. split; assumption.
Qed.
Lemma wr_x_len : forall cx m, 0 <= wr_k1 cx m -> wr_k2 cx m <= c_n cx -> c_n cx = Z.of_nat (length (c_pl cx)) ->
  0 <= wr_n cx m -> 0 <= wr_c cx m -> Z.of_nat (length (wr_x cx m)) = wr_n cx m.
Proof.
  intros cx m H0 H2 Hl Hn Hc. unfold wr_x. rewrite length_firstn, length_skipn. unfold wr_k2 in H2. lia.
Qed.

(* ------------------------------------------------------------------ the model's blocks around slot si's pending
   list (the donor's pass bookkeeping, a1_pass_of, over model_blks) *)
Definition wr_A0 (m : lmod) (hs1 : list (option hsrc)) (h : hsrc) : list (Z * Z) :=
  (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1) ++ [(hs_partial h, APARTIAL)].
Definition wr_B0 (m : lmod) (hs2 : list (option hsrc)) (h : hsrc) : list (Z * Z) :=
  alist_blks (hs_expected h) ++ alist_blks (hs_held h) ++ concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m).
Ltac wr_app_norm := repeat (rewrite <- app_assoc || rewrite <- app_comm_cons || rewrite app_nil_l).
Lemma wr_model_split : forall m hs1 h hs2, lm_hs m = hs1 ++ Some h :: hs2 ->
  model_blks m = wr_A0 m hs1 h ++ alist_blks (hs_pending h) ++ wr_B0 m hs2 h.
Proof.
  intros m hs1 h hs2 Ehs. unfold model_blks, wr_A0, wr_B0. rewrite Ehs, map_app, concat_app.
  cbn [map concat slot_blks]. unfold asrc_blks. wr_app_norm. reflexivity.
Qed.
Lemma wr_set_nth_app : forall {A} (l1 l2 : list A) x y, set_nth (length l1) x (l1 ++ y :: l2) = l1 ++ x :: l2.
Proof. intros A l1. induction l1 as [|z l1 IH]; intros l2 x y; cbn [set_nth length app]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma wr_model_split' : forall m hs1 h hs2 k si l' ev, lm_hs m = hs1 ++ Some h :: hs2 -> length hs1 = si ->
  model_blks (wr_push m k si (set_pending h l') ev) = wr_A0 m hs1 h ++ alist_blks l' ++ wr_B0 m hs2 h.
Proof.
  intros m hs1 h hs2 k si l' ev Ehs Hl. subst si. unfold model_blks, wr_push, wr_A0, wr_B0.
  cbn [lm_hs lm_G lm_es lm_cap lm_out]. rewrite Ehs, wr_set_nth_app, map_app, concat_app.
  cbn [map concat slot_blks]. unfold asrc_blks. cbn [set_pending hs_partial hs_pending hs_expected hs_held].
  wr_app_norm. reflexivity.
Qed.
Definition zz_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma wr_perm : forall l1 l2 : list (Z * Z), (forall y, count_occ zz_dec l1 y = count_occ zz_dec l2 y) ->
  Permutation l1 l2.
Proof. intros l1 l2 H. exact (proj2 (Permutation_count_occ zz_dec l1 l2) H). Qed.
Lemma wr_perm_pre : forall IB A0 V R Bl r0 : list (Z * Z),
  Permutation (IB ++ (A0 ++ (V ++ R) ++ Bl) ++ r0) (V ++ (IB ++ A0 ++ R ++ Bl ++ r0)).
Proof. intros. apply wr_perm. intros y. rewrite !count_occ_app. lia. Qed.
Lemma wr_perm_post : forall (x : Z * Z) IB A0 V' R Bl r0,
  Permutation ([x] ++ V' ++ (IB ++ A0 ++ R ++ Bl ++ r0)) (IB ++ (A0 ++ (V' ++ R ++ [x]) ++ Bl) ++ r0).
Proof. intros. apply wr_perm. intros y. rewrite !count_occ_app. lia. Qed.
Lemma wr_perm_src : forall (x pp : Z * Z) V' IB A1 R E Hd S2 r0,
  Permutation ([x] ++ V' ++ (IB ++ (A1 ++ [pp]) ++ R ++ (E ++ Hd ++ S2) ++ r0))
              (((V' ++ R ++ [x]) ++ [pp] ++ E ++ Hd) ++ (IB ++ A1 ++ S2 ++ r0)).
Proof. intros. apply wr_perm. intros y. rewrite !count_occ_app. lia. Qed.
Lemma wr_nodup_disj : forall (L1 L2 : list (Z * Z)) b, List.NoDup (L1 ++ L2) -> In b L1 -> In b L2 -> False.
Proof.
  induction L1 as [|x L1 IH]; intros L2 b HN H1 H2; [destruct H1|].
  inversion HN as [|y l Hy HN']; subst. destruct H1 as [<- | H1].
  - apply Hy. apply in_or_app. right. exact H2.
  - exact (IH L2 b HN' H1 H2).
Qed.
Lemma wr_nodup_app_l : forall (L1 L2 : list (Z * Z)), List.NoDup (L1 ++ L2) -> List.NoDup L1.
Proof.
  induction L1 as [|x L1 IH]; intros L2 HN; [constructor|].
  inversion HN as [|y l Hy HN']; subst. constructor; [|exact (IH L2 HN')].
  intros Hx. apply Hy. apply in_or_app. left. exact Hx.
Qed.

(* a concrete register is callee-saved (_latch.v lt_cs, whose Ltac is local to its Section) *)
Ltac wr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* ------------------------------------------------------------------ 0x84478-0x84488, the list_push call *)
(* the call: list_push(&g_s[si].pending, in.p + k1 + c, n) at 0x85090, back at 0x8448c *)
Lemma wr_call : forall cx t (W : world segs) (regs : bvmap 5 word) mem md ly3 S3 k m fpos si h,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> jt_rom W mem ->
  lregs_common B cx (frame_addr ly3 1 fpos) regs -> getr regs 27 = w64 t -> 0 <= t < OPS_MAX ->
  getr regs 22 = w64 (c_p cx + wr_k2 cx m) -> sv8 W mem (lf_F cx + WR_N) (c_n cx - wr_k2 cx m) ->
  getr regs 1 = w64 (BASE + A_wr_li) ->
  getr regs 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat si + 16) -> getr regs 11 = w64 (wr_src cx m) ->
  getr regs 12 = w64 (wr_n cx m) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  SRr segs W (cfg_at segs (BASE + AF_fr_list_push) regs mem md) (JST cx t).
Proof.
  intros cx t W regs mem md ly3 S3 k m fpos si h HB HJ HFR HFL HMOD HIN HRV HSEP HLS HRI HROM HCOM R27 Ht R22 SVN R1 R10
    R11 R12 Hk HO Hop HPK Hn.
  pose proof HPK as (Hpk & Hsi & Hh).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof HB as (_ & HPRE0).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
  pose proof HPREE as (HAR0 & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (wr_F_range cx) as HFr.
  assert (HFb : (spZ (c_regs cx)) - 352 < lf_F cx <= (spZ (c_regs cx)) - 320) by lia.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (Hsp1 : spZ regs = lf_F cx) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
  (* the journal from the entry to the call *)
  pose proof (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ ly3 S3 W mem md k HJ) as HAR.
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ ly3 S3 W mem md k HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & HGONE & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* slot si and its pending list *)
  pose proof HMOD as (M1 & M2 & _ & M4 & _).
  pose proof (M2 si Hsi) as HS0. unfold aslot in HS0. rewrite Hh in HS0.
  pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
  destruct (@nth_split _ si (lm_hs m) None ltac:(rewrite M1; exact Hsi)) as (hs1 & hs2 & Ehs & Hl1).
  rewrite Hh in Ehs.
  (* the input and fuzz_take's numbers *)
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (wr_n_range cx m ltac:(lia)) as (Hnr & Hc1 & Hc2).
  assert (Hwc0 : 0 <= wr_c cx m) by (unfold wr_c, wr_rem; lia).
  assert (Hlenx : Z.of_nat (length (wr_x cx m)) = wr_n cx m) by (apply wr_x_len; lia).
  pose proof HIN as (Hblk & Hgin).
  destruct Hblk as [(Hz & _) | (Hcn & Hinb)]; [lia|].
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hinb) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  destruct (LS_write_room cx t m si h ly3 S3 HLS HPK Hn) as (Hroom1 & Hroom2 & Hroom3).
  (* the live blocks: the input, the model with slot si's pending list apart, the rest *)
  destruct HSEP as ((rest0 & Hperm0) & HSEP2).
  assert (EIB : input_blks cx = [(c_p cx, c_n cx)])
    by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | reflexivity]).
  set (l := hs_pending h) in *.
  set (V := if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]).
  set (R := map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)).
  assert (EAL : alist_blks l = V ++ R) by reflexivity.
  set (A0 := wr_A0 m hs1 h). set (B0 := wr_B0 m hs2 h).
  set (P := [(c_p cx, c_n cx)] ++ A0 ++ R ++ B0 ++ rest0).
  assert (HP3 : Permutation (ablocks B ly3 S3) (V ++ P)).
  { eapply Permutation_trans; [exact Hperm0|]. rewrite EIB, (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
    exact (wr_perm_pre [(c_p cx, c_n cx)] A0 V R B0 rest0). }
  pose proof (Permutation_NoDup HP3 (wr_ablocks_nodup ly3 S3 W mem md HAR)) as HNDVP.
  (* the input block is not the vector *)
  assert (Hqv : c_p cx <> hl_v l).
  { intros E. pose proof HL as (_ & _ & _ & _ & _ & [(_ & Hv0) | (Hcap & Hvin & _)] & _); [lia|].
    pose proof (wr_uniq ly3 S3 W mem md (c_p cx) (c_n cx) (AREC * hl_cap l) HAR Hinb
      ltac:(rewrite E; exact Hvin)) as En.
    apply (wr_nodup_disj V P (c_p cx, c_n cx) HNDVP).
    - unfold V. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0'|Hc0']; [lia|]. left. rewrite E, En. reflexivity.
    - unfold P. apply in_or_app. left. left. reflexivity. }
  (* the bytes list_push copies, read off the input *)
  assert (Hgx : garr8 segs (mrestrict (w_H W) mem) (wr_src cx m) (bzs (wr_x cx m))).
  { unfold wr_src, wr_x.
    replace (c_p cx + wr_k1 cx m + wr_c cx m) with (c_p cx + Z.of_nat (Z.to_nat (wr_k1 cx m + wr_c cx m))) by lia.
    apply wr_garr8_x; [exact Hgin | unfold wr_k2 in Hc2; lia]. }
  (* list_push's afn_pre (_latch.v lt_afn_pre_at) *)
  destruct (lt_afn_pre_at B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv G_fr fr_FP HG LS RINV
      wr_errno_low cx true ly3 S3 fpos k W mem md regs LP_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite R1. apply ret_ok_codeptr_v; [unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite R1. unfold w64.
    rewrite unsigned_lit_small by (unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput in *; lia).
    unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput in *. lia. }
  { exact C3. } { exact C4. } { exact C8. }
  { unfold LP_STK, ASTACK. lia. } { unfold LP_STK, ASTACK, LLVMF_STK. lia. }
  (* the call: lp_spec_g at list_push's own G *)
  eapply SRr_bind.
  { refine (pb_list_push_g B LX0 TL MT MLAW WR_MMAX wr_HMMAX CTX_AREALLOC ARE
      ltac:(assert (E : [BASE + AF_fr_list_push + 0xac] = [0x8513c]) by (vm_compute; reflexivity); rewrite E;
            unfold CTX_AREALLOC; vm_compute; repeat (first [left; reflexivity | right]))
      CTX_AMALLOC AMA AMEMCPY
      ltac:(assert (E : [BASE + AF_fr_list_push + 0xd0] = [0x85160]) by (vm_compute; reflexivity); rewrite E;
            unfold CTX_AMALLOC; vm_compute; repeat (first [left; reflexivity | right]))
      (wr_G1 si) (wr_gx_ok1 si Hsi)
      (wr_gx_rt1 si Hsi) W ly3 S3 regs mem md ch (wr_LA si) (wr_src cx m) l false (wr_x cx m) (c_p cx) (c_n cx)
      HPREc R10 R11 _ (wr_LA8 si) HL _ (wr_azs1 si Hsi) Hroom1 _ _ Hinb Hqv _ _ Hgx _ _ _).
    - rewrite Hlenx. exact R12.
    - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    - rewrite Hlenx. lia.
    - (* the room round's C3 text: list_push's byte premise at its trace's peak, within LS_write_room's sum
         (W_tr_peak.v lp_tr_peak_le) *)
      rewrite Hlenx.
      assert (Hc0 : 0 <= hl_cap l) by (pose proof HL as (_ & _ & _ & _ & _ & [(Hc & _) | (Hc & _)] & _); lia).
      pose proof (W_tr_peak.lp_tr_peak_le l (wr_n cx m) Hc0 ltac:(lia)) as Htrpk. lia.
    - unfold wr_src. lia.
    - rewrite Hlenx, Hreq. unfold wr_src, wr_k2 in *. lia.
    - discriminate.
    - intros _. lia.
    - rewrite Hlenx. exact Hroom3. }
  intros W2 c2 Hwle (ly' & S' & regs' & mem' & md' & kk & l' & d & -> & HJc & HPRS & HL' & HREC & HCAP & HVV & HPERM
    & HPRES & HERRV & HFRS & HMO).
  rewrite Hsp1 in HJc.
  apply SRr_ret.
  set (n1 := Z.of_nat (length (wr_x cx m)) + 1) in *.
  (* list_push's journal *)
  pose proof (ajournal_gx_AR segs B (wr_G1 si) 0 [] LP_STK _ _ _ _ _ _ _ _ ly' S' W2 mem' md' kk HJc) as HAR'.
  destruct (ajournal_gx_inner segs B (wr_G1 si) 0 [] LP_STK _ _ _ _ _ _ _ _ ly' S' W2 mem' md' kk HJc)
    as (memS1 & HJci & _).
  pose proof HJci as (_ & HLY & _).
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. pose proof HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames S')) by (rewrite HFRS; exact Hin1).
  (* the callee's footprint: the vector, a model block, so a temporary block or inside the entry's FP *)
  assert (HFP1 : forall a, inFP (lp_FP l) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    assert (Hvm : In (hl_v l, AREC * hl_cap l) (model_blks m)).
    { rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL. apply in_or_app. right. apply in_or_app. left.
      apply in_or_app. left. unfold V. try rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity. }
    assert (Hrq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
      by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    destruct (HSEP2 _ Hvm) as [Hne | Hall].
    - right. exists (hl_v l), (AREC * hl_cap l). split; [exact Hvin|]. split; [exact Hne|]. rewrite Hrq. lia.
    - left. split; [apply Hall; cbn [fst snd]; lia|].
      exists (hl_v l), (AREC * hl_cap l). split; [exact Hvin | rewrite Hrq; lia]. }
  pose proof (ajournal_gx_G_mono segs B (wr_G1 si) G_fr 0 [] LP_STK (lf_F cx) (lp_FP l) ly3 S3 W mem md [] ly' S'
    W2 mem' md' kk (wr_G1_fr si Hsi) HJc) as HJcG.
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k
     LP_STK (lf_F cx) 0 [] (lp_FP l) [] ly' S' W2 mem' md' kk HJ HJcG
     ltac:(unfold LP_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a (r & [] & _)) HG HFP1) as HJ2.
  cbn [app] in HJ2.
  (* ROM and the jump table *)
  pose proof (ajournal_gx_rom_view segs B pa_segs_low (wr_G1 si) 0 [] LP_STK (lf_F cx) (lp_FP l) ly3 S3 W mem md []
    ly' S' W2 mem' md' kk HJc (wr_rom_out1 si Hsi) HRV) as HRV2.
  pose proof (wr_jt_rom_kept W W2 mem mem' HROM HRV HRV2) as HROM2.
  (* the frame window [F, (spZ (c_regs cx))) and the fake frame *)
  assert (KST : forall a, lf_F cx <= a < (spZ (c_regs cx)) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (wr_ck_hi (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 W mem md ly' S' W2 mem' md' kk
      (wr_gx_ok1 si Hsi) HJc a); unfold LP_STK, ASTACK, LLVMF_STK in *; lia. }
  pose proof (wr_pres cx [(1, fpos)] ly' S' W2 mem' md' (k + kk) HJ2) as KPR.
  assert (KSTb : forall a, lf_F cx <= a < (spZ (c_regs cx)) -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split; [exact (KST a Ha)|]. intros _. apply (apresent_writable segs). apply KPR.
    unfold LLVMF_STK. lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & HFFapp).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFapp.
  assert (HFF8 : 8 * ((frame_addr ly3 1 fpos) / 8) <= (frame_addr ly3 1 fpos) < 8 * ((frame_addr ly3 1 fpos) / 8) + 8)
    by (pose proof (Z.div_mod (frame_addr ly3 1 fpos) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (frame_addr ly3 1 fpos) 8 ltac:(lia)); lia).
  assert (NFF : forall a, (frame_addr ly3 1 fpos) <= a < (frame_addr ly3 1 fpos) + 128 \/ SB + (frame_addr ly3 1 fpos) / 8 <= a < SB + (frame_addr ly3 1 fpos) / 8 + 16 -> ~ inFP (lp_FP l) a).
  { intros a Ha (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    assert (Hrq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
      by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    destruct (al_blocks _ _ LAWS ly3 S3 W mem md _ _ HAR Hvin) as (_ & _ & _ & Hvapp & _).
    rewrite Hrq in Hvapp.
    destruct Ha as [Ha | Ha].
    - pose proof (sep_block_frame segs B LAWS ly3 S3 W mem md _ _ 1 fpos HAR Hvin Hin1) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      clear - Ha Hra Hd. lia.
    - clear - Ha Hra Hvapp HFFapp HFF8 HFF1 CA1. unfold in_app, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  assert (KFF : forall a, (frame_addr ly3 1 fpos) <= a < (frame_addr ly3 1 fpos) + 128 \/ SB + (frame_addr ly3 1 fpos) / 8 <= a < SB + (frame_addr ly3 1 fpos) / 8 + 16 -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split.
    - apply (wr_ck_frm (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 W mem md ly' S' W2 mem' md' kk (wr_gx_ok1 si Hsi)
        HAR HJc 1 fpos a Hin1); [| exact (NFF a Ha)].
      change (fs_frame_bytes 1) with 128. destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact Ha].
    - intros _. apply (apresent_writable segs).
      destruct (al_frames _ _ LAWS ly' S' W2 mem' md' 1 fpos HAR' Hin1') as (_ & _ & HP1 & HP2).
      rewrite HFA in HP1, HP2. change (fs_frame_bytes 1) with 128 in HP1, HP2.
      destruct Ha as [Ha | Ha]; [exact (proj1 (HP1 a Ha))|].
      replace a with (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) by ring.
      apply HP2. clear - Ha. unfold shadow_addr, SHADOW_OFF, SB in *. change (128 / 8) with 16. lia. }
  assert (HFR2 : aframe_at cx true (frame_addr ly3 1 fpos) W2 mem').
  { apply (wr_aframe_call cx true (frame_addr ly3 1 fpos) W W2 mem mem' HFR).
    - intros a Ha. apply KST. lia.
    - intros a Ha. apply KPR. unfold LLVMF_STK. lia.
    - exact KFF. }
  (* the fake frame's flag word across list_push: inside KFF's 128 bytes, and ly' keeps ly_F *)
  assert (HFL2 : sv8 W2 mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
    { unfold flag_addr. pose proof HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    rewrite EFL. unfold sv8 in *. apply (akept_vm W mem); [|exact HFL].
    intros x Hx. apply KFF. left. cbn in Hx. lia. }
  (* the callee's journal keeps the image bytes the model reads *)
  assert (HSK : ~ YI16.sink_open_fp (lp_FP l)).
  { intros (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    destruct (al_blocks _ _ LAWS ly3 S3 W mem md _ _ HAR Hvin) as (_ & Hv4096 & _). lia. }
  assert (KG : forall a, wr_glob (rg_s fr_RG + ASRC * Z.of_nat si) a -> abyte_kept W mem W2 mem' a).
  { intros a Ha.
    assert (HaG : inG G_fr a) by (destruct Ha as [Ha | [Ha _]]; [exact (HGW a Ha) | exact (HGs a Ha)]).
    assert (HaE : ~ (as_errno B <= a < as_errno B + 4)).
    { apply HERRS. apply inG_cons.
      destruct Ha as [Ha | [Ha _]]; [right; exact Ha | left; unfold in_zr; cbn [fst snd]; lia]. }
    assert (HaN : ~ inG (wr_G1 si) a).
    { intros H1. destruct (wr_G1_gs si a Hsi H1) as [H1a H1b]. destruct Ha as [Ha | [_ Ha]].
      - exact (wr_G_gs a Ha H1b).
      - apply Ha. unfold wr_LA, ASRC in *. lia. }
    split.
    - exact (wr_ck_img (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 W mem md ly' S' W2 mem' md' kk HJc HSK a
        (proj1 (HG a HaG)) HaN (proj1 (proj2 (HG a HaG))) HaE).
    - intros _. exact (GWR (w_H W2) mem' a HaG). }
  assert (KE : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split.
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HERRV. lia.
    - intros _. destruct (ERR ly' S' W2 mem' md' HAR') as [_ Hw].
      replace a with (as_errno B + (a - as_errno B)) by lia. apply Hw. lia. }
  (* the live blocks after the call *)
  set (V' := if hl_cap l' =? 0 then [] else [(hl_v l', AREC * hl_cap l')]).
  assert (HP' : Permutation (ablocks B ly' S') ([(d, n1)] ++ V' ++ P)).
  { unfold V'. clear HJc HJcG HJ2 HJci.
    destruct (lp_grow l) eqn:Eg.
    - assert (Hc' : hl_cap l' <> 0).
      { rewrite HCAP. unfold grow_cap. unfold lp_grow in Eg. rewrite Eg. destruct (Z.eqb_spec (hl_cap l) 0); lia. }
      rewrite (proj2 (Z.eqb_neq _ _) Hc'). try rewrite Eg in HPERM.
      destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
      + try rewrite (proj2 (Z.eqb_eq _ _) Hc0) in HPERM. cbn [andb negb] in HPERM.
        apply (HPERM P). unfold V in HP3. try rewrite (proj2 (Z.eqb_eq _ _) Hc0) in HP3. exact HP3.
      + try rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HPERM. cbn [andb negb] in HPERM.
        apply (HPERM P). unfold V in HP3. try rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HP3. exact HP3.
    - assert (Hc' : hl_cap l' = hl_cap l).
      { rewrite HCAP. unfold grow_cap. unfold lp_grow in Eg. rewrite Eg. reflexivity. }
      assert (Hv' : hl_v l' = hl_v l) by (apply HVV; first [exact Eg | reflexivity]).
      rewrite Hc', Hv'. fold V. try rewrite Eg in HPERM. cbn [andb] in HPERM.
      apply (HPERM (V ++ P)). exact HP3. }
  pose proof (Permutation_NoDup HP' (wr_ablocks_nodup ly' S' W2 mem' md' HAR')) as HNDP'.
  assert (EAL' : alist_blks l' = V' ++ R ++ [(d, n1)]).
  { unfold alist_blks, V', R, n1. rewrite HREC, map_app. reflexivity. }
  (* a block live at and after the call, not the vector, is kept *)
  assert (KBLK : forall b n, In (b, n) (ablocks B ly3 S3) -> In (b, n) (ablocks B ly' S') -> ~ In (b, n) V ->
     forall j, 0 <= j < req_size n -> abyte_kept W mem W2 mem' (b + j)).
  { intros b n H3 H' HnV j Hj. split.
    - apply (wr_ck_blk (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 W mem md ly' S' W2 mem' md' kk
        (wr_gx_ok1 si Hsi) HJc b n j H3 H' Hj).
      intros (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
      refine (wr_nohit ly3 S3 W mem md b n (hl_v l) (hl_cap l) HAR H3 Hvin Hcp _ j Hj _).
      + intros E. apply HnV. unfold V. try rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. symmetry. exact E.
      + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity | exact Hra].
    - intros _. apply (apresent_writable segs).
      destruct (al_blocks _ _ LAWS ly' S' W2 mem' md' b n HAR' H') as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr (b + j) ltac:(lia))). }
  assert (HXP : forall b, In b (A0 ++ B0) -> In b P).
  { intros b Hb. unfold P. apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; right; apply in_or_app;
      [left; exact Hb | right; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
  assert (KBX : forall b n, In (b, n) (A0 ++ B0) -> In (b, n) (ablocks B ly' S') /\
     forall j, 0 <= j < req_size n -> abyte_kept W mem W2 mem' (b + j)).
  { intros b n Hb. pose proof (HXP _ Hb) as HbP.
    assert (H3 : In (b, n) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HP3)); apply in_or_app; right; exact HbP).
    assert (H' : In (b, n) (ablocks B ly' S'))
      by (apply (Permutation_in _ (Permutation_sym HP')); apply in_or_app; right; apply in_or_app; right; exact HbP).
    split; [exact H'|]. apply KBLK; [exact H3 | exact H' |]. intros HV. exact (wr_nodup_disj V P (b, n) HNDVP HV HbP). }
  (* the input after the call *)
  assert (Hinb' : In (c_p cx, c_n cx) (ablocks B ly' S')).
  { apply (Permutation_in _ (Permutation_sym HP')). apply in_or_app. right. apply in_or_app. right.
    unfold P. apply in_or_app. left. left. reflexivity. }
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { split; [right; split; [exact Hcn | exact Hinb'] |].
    apply (akept_garr8 W mem); [| exact Hgin]. intros a Ha. rewrite length_map, <- HlenP in Ha.
    replace a with (c_p cx + (a - c_p cx)) by lia.
    eapply KBLK; [exact Hinb | exact Hinb' | | rewrite Hreq; lia].
    intros HV. apply (wr_nodup_disj V P (c_p cx, c_n cx) HNDVP HV). unfold P. apply in_or_app. left. left. reflexivity. }
  (* slot si after the call: list_push's l' as its pending list *)
  set (A1 := (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1)).
  set (S2 := concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)).
  set (L' := alist_blks l' ++ [(hs_partial h, APARTIAL)] ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  assert (HPL : Permutation ([(d, n1)] ++ V' ++ P) (L' ++ ([(c_p cx, c_n cx)] ++ A1 ++ S2 ++ rest0))).
  { assert (EA0 : A0 = A1 ++ [(hs_partial h, APARTIAL)]) by (unfold A0, A1, wr_A0; wr_app_norm; reflexivity).
    assert (EB0 : B0 = alist_blks (hs_expected h) ++ alist_blks (hs_held h) ++ S2) by reflexivity.
    unfold P, L'. rewrite EA0, EB0, EAL'.
    exact (wr_perm_src (d, n1) (hs_partial h, APARTIAL) V' [(c_p cx, c_n cx)] A1 R
      (alist_blks (hs_expected h)) (alist_blks (hs_held h)) S2 rest0). }
  assert (HL'in : forall b, In b L' -> In b (ablocks B ly' S')).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP')). apply (Permutation_in _ (Permutation_sym HPL)).
    apply in_or_app. left. exact Hb. }
  assert (HNDH : NoDup (hs_blocks (set_pending h l'))).
  { assert (EL : hs_blocks (set_pending h l') = map fst L').
    { unfold hs_blocks, L'. cbn [set_pending hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !wr_map_fst_alist_blks. reflexivity. }
    rewrite EL. apply NoDup_ListNoDup. apply NoDup_map_NoDup_ForallPairs.
    - intros [b1 n1'] [b2 n2'] Hb1 Hb2 Eb. cbn [fst] in Eb. subst b2.
      f_equal. exact (wr_uniq ly' S' W2 mem' md' b1 n1' n2' HAR' (HL'in _ Hb1) (HL'in _ Hb2)).
    - exact (wr_nodup_app_l L' _ (Permutation_NoDup HPL HNDP')). }
  assert (HSRC' : asrc_at B ly' S' W2 mem' (rg_s fr_RG + ASRC * Z.of_nat si) (set_pending h l')).
  { apply (wr_asrc_push ly3 S3 W mem ly' S' W2 mem' (rg_s fr_RG + ASRC * Z.of_nat si) h l' d (wr_x cx m) HS0).
    - intros a Ha1 Ha2. apply KG. right. split; [|exact Ha2].
      unfold ASRC in *. assert (Z.of_nat si <= 3) by lia. lia.
    - intros a Ha1. apply (GWR (w_H W2) mem' a). apply HGs.
      unfold ASRC in *. assert (Z.of_nat si <= 3) by lia. lia.
    - intros b n Hb. apply KBX. apply in_app_iff. unfold A0, B0, wr_A0, wr_B0.
      destruct Hb as [Hb | Hb].
      + left. right. apply in_app_iff. right. apply in_app_iff. right. left. exact Hb.
      + right. apply in_app_iff in Hb as [Hb | Hb]; apply in_app_iff;
          [left; exact Hb | right; apply in_app_iff; left; exact Hb].
    - exact HL'.
    - exact HREC.
    - lia.
    - exact HNDH. }
  (* the model after the call *)
  assert (Hincl : incl ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1) ++
        concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)) (A0 ++ B0)).
  { intros b Hb. unfold A0, B0, wr_A0, wr_B0. destruct Hb as [<- | Hb]; [left; reflexivity|].
    right.
    apply in_app_iff in Hb as [Hb | Hb];
      [apply in_app_iff; left; apply in_app_iff; left; exact Hb|].
    apply in_app_iff in Hb as [Hb | Hb];
      [apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hb|].
    apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hb.
    - apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Hb. }
  pose proof (wr_amodel_tr ly3 S3 W mem md ly' S' W2 mem' m si h (set_pending h l') (A0 ++ B0) hs1 hs2 (wr_k2 cx m)
    HAR HMOD Ehs Hl1 Hsi KG KE KBX Hincl HSRC') as HMOD2.
  (* the separation after the call *)
  assert (NB : forall b, In b ([(d, n1)] ++ V') -> ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
      (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)).
  { intros [b n] Hb.
    destruct (in_dec zz_dec (b, n) (ablocks B (c_ly cx) (c_S cx))) as [Hen | Hen]; [|left; exact Hen].
    destruct (in_dec zz_dec (b, n) (ablocks B ly3 S3)) as [H3 | H3].
    - apply (Permutation_in _ HP3) in H3. apply in_app_iff in H3 as [HV | HPb].
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
        apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact HV.
      + exfalso. apply (wr_nodup_disj ([(d, n1)] ++ V') P (b, n)); [rewrite <- app_assoc; exact HNDP' | exact Hb | exact HPb].
    - right. intros a Ha. cbn [fst snd] in Ha.
      destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) b n HAR0 Hen)
        as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (b + (a - b)) by lia. apply (HGONE b n (a - b) Hen H3). lia. }
  assert (HSEP' : ablocks_sep B fr_FP cx (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))) ly' S').
  { split.
    - exists rest0. rewrite EIB, (wr_model_split' m hs1 h hs2 (wr_k2 cx m) si l' (ct_ev (lm_c m)) Ehs Hl1), EAL'.
      eapply Permutation_trans; [exact HP'|]. exact (wr_perm_post (d, n1) [(c_p cx, c_n cx)] A0 V' R B0 rest0).
    - intros b Hb. rewrite (wr_model_split' m hs1 h hs2 (wr_k2 cx m) si l' (ct_ev (lm_c m)) Ehs Hl1), EAL' in Hb.
      rewrite !in_app_iff in Hb.
      destruct Hb as [Hb | [[Hb | [Hb | Hb]] | Hb]].
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). apply in_or_app. left. exact Hb.
      + apply NB. apply in_or_app. right. exact Hb.
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
        apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb.
      + apply NB. apply in_or_app. left. exact Hb.
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). apply in_or_app. right. apply in_or_app. right.
        exact Hb. }
  (* LS and the relational invariant *)
  assert (HMO' : mo_le MT S3 S' (lp_cost MT l (wr_n cx m))) by (rewrite <- Hlenx; exact HMO).
  pose proof (LS_write_push cx t m si h l' d (ct_ev (lm_c m)) ly3 S3 ly' S' HLS HPK Hn HREC HCAP HVV HPERM HMO') as HLS'.
  pose proof (RI_write_push cx t m si h l' d (ct_ev (lm_c m)) HRI Hk Hop HPK Hn HREC HCAP Hev) as HRI'.
  (* the registers list_push preserves *)
  assert (RP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r)
    by (intros r Hr; exact (lt_pres regs regs' r HPRS Hr)).
  assert (HRK : lregs_K B cx t (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))) (frame_addr ly3 1 fpos) regs' W2 mem').
  { split.
    { split; [rewrite (RP 2%bv ltac:(wr_cs)); exact C2|].
      split; [rewrite (RP 8%bv ltac:(wr_cs)); exact C8|].
      split; [rewrite (RP 9%bv ltac:(wr_cs)); exact C9|].
      split; [rewrite (RP 18%bv ltac:(wr_cs)); exact C18|].
      split; [rewrite (RP 19%bv ltac:(wr_cs)); exact C19|].
      split; [rewrite (RP 20%bv ltac:(wr_cs)); exact C20|].
      split; [rewrite (RP 23%bv ltac:(wr_cs)); exact C23|].
      split; [rewrite (RP 24%bv ltac:(wr_cs)); exact C24|].
      split; [rewrite (RP 25%bv ltac:(wr_cs)); exact C25|].
      split; [rewrite (RP 26%bv ltac:(wr_cs)); exact C26|].
      split; [rewrite (RP 3%bv ltac:(wr_cs)); exact C3|].
      rewrite (RP 4%bv ltac:(wr_cs)); exact C4. }
    split; [rewrite (RP 27%bv ltac:(wr_cs)); exact R27|].
    split; [exact Ht|].
    cbn [lm_k wr_push].
    split; [rewrite (RP 22%bv ltac:(wr_cs)); exact R22|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KSTb; unfold WR_N in *; lia | exact SVN]|].
    lia. }
  (* INV_K's facts at 0x8448c *)
  exists regs', mem', md'.
  split; [unfold cfg_at; rewrite R1; reflexivity|].
  split; [exact HROM2|].
  exists [(1, fpos)], ly', S', (k + kk), (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))), fpos.
  rewrite HFA.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HRI'|].
  exact HRK.
Qed.

(* 0x84478 beqz s5; 0x8447c beqz a2; addi a0,s5,16; mv a1,t3; jal list_push *)
Lemma wr_tst : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  WST cx t W c -> SRr segs W c (JST cx t).
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  destruct HR as (HCOM & R27 & Ht & Hk & HO & Hop & HSRC & R12 & R28 & R22 & SVN).
  pose proof HJ as HJ0.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (wr_n_range cx m ltac:(lia)) as (Hn & Hc1 & Hc2).
  destruct (wt_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs wj_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs wj_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn0; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn0).
  assert (E12 : ew E 12 = Z_to_bv 64 (wr_n cx m)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  clear HE.
  (* the skip: the model after the operation, the cut facts unchanged (no store) *)
  assert (SKIP : forall regs' md', (forall r, In r WJ_KEPT -> getr regs' r = getr regs r) ->
      getr regs' 20 = getr regs 20 ->
      ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md' k ->
      (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
      SRr segs W (cfg_at segs (fr_B0 + A_wr_li) regs' mem md') (JST cx t)).
  { intros regs' md' KR R20 HJ' Hsk. apply SRr_ret.
    exists regs', mem, md'. split; [reflexivity|]. split; [exact HROM|].
    exists [(1, fpos)], ly3, S3, k, (wr_skip m (wr_k2 cx m)), fpos.
    split; [exact HJ'|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
    split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
    split; [exact (LS_write_skip cx t m ly3 S3 HLS)|].
    split; [exact (RI_write_skip cx t m HRI Hk Hop Hsk)|].
    pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
    split.
    { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite R20; exact C20|].
      split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KR 4%bv ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    split; [exact SVN|]. cbn [wr_skip lm_k]. lia. }
  unfold cfg_at. change (w64 (fr_B0 + A_wr_tst)) with (Z_to_bv 64 (BASE + A_wr_tst)).
  paj_run_tok RUN HS HJ SHOK wr_Bspan. { apply awr_ok_x_nil. }
  wr_mem HF Em. clear HF HFr HG0.
  (* 0x84478 beqz s5 *)
  destruct HSRC as [(si & Hpk & R21) | (Hpk & R21)].
  - assert (E21 : ew E 21 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat si))
      by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
    destruct (wr_pick_some (lm_hs m) (wr_kb cx m) si Hpk) as [Hsi [h Hh]].
    pose proof HMOD as (Hlen4 & _). rewrite Hlen4 in Hsi.
    assert (Hs0 : 0 < rg_s fr_RG + ASRC * Z.of_nat si < 2 ^ 64)
      by (unfold fr_RG, ASRC; cbn [rg_s fr_globals]; lia).
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom _ 21 _ E21), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      paj_run_tok RUN HS HJ SHOK wr_Bspan. { apply awr_ok_x_nil. }
      wr_mem HF Em2. clear HF HFr HG0.
      wr_pin A12 E12 12%nat (wr_n cx m).
      (* 0x8447c beqz a2 *)
      psrr_branch_tok RUN BR HS SHOK wr_Bspan.
      * rewrite branch_eq_U, (U_atom _ 12 _ A12), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK wr_Bspan A_wr_li. { apply awr_ok_x_nil. }
        wr_mem HF Em3. clear HF HFr HG0.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
            by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                       | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE2
          ltac:(vm_compute; reflexivity)) as KR.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra [20%bv] HS HAE2
          ltac:(vm_compute; reflexivity) 20%bv ltac:(left; reflexivity)) as K20.
        cbn [ms_regs restrict] in KR, K20.
        pmkst HS. rewrite Em3, Em2, Em in *.
        apply (SKIP _ _ KR K20 HJ). right. exact Hc.
      * rewrite branch_eq_U, (U_atom _ 12 _ A12), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK wr_Bspan AF_fr_list_push. { apply awr_ok_x_nil. }
        wr_mem HF Em3. clear HF HFr HG0.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
            by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                       | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra
          [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (1%bv : bv 5) Q1.
        wr_prreg_raw HS (10%bv : bv 5) Q10. wr_prreg_raw HS (11%bv : bv 5) Q11. wr_prreg_raw HS (12%bv : bv 5) Q12.
        assert (E28 : ew E 28 = Z_to_bv 64 (wr_src cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
        wr_pin A21 E21 21%nat (rg_s fr_RG + ASRC * Z.of_nat si).
        wr_pin A28 E28 28%nat (wr_src cx m).
        wr_pin A12b E12 12%nat (wr_n cx m).
        assert (Hsrc : 0 <= wr_src cx m < 2 ^ 64)
          by (pose proof HIN as ([(Hz & _) | (_ & Hin)] & _); [lia|];
              destruct (al_blocks _ _ LAWS ly3 S3 W mem md _ _ (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _
                ly3 S3 W mem md k HJ0) Hin) as (_ & H4096 & Hce & _);
              pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq];
              pose proof asan_consts as (C1 & _); unfold wr_src; lia).
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
          assert (R10 : getr (ms_regs msx) 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat si + 16))
            by (rewrite Q10; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 21 _ 16 A21) by (unfold fr_RG, ASRC; cbn [rg_s fr_globals]; lia); lia
                | unfold fr_RG, ASRC in *; cbn [rg_s fr_globals] in *; lia]);
          assert (R11 : getr (ms_regs msx) 11 = w64 (wr_src cx m))
            by (rewrite Q11; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia]);
          assert (R12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
            by (rewrite Q12; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A12b | lia] | lia])
        end.
        pmkst HS. rewrite Em3, Em2, Em in *.
        pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
        eapply (wr_call cx t W _ mem _ ly3 S3 k m fpos si h HB HJ HFR HFL HMOD HIN HRV HSEP HLS HRI HROM).
        -- split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2|].
           split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact C8|].
           split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9|].
           split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact C18|].
           split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact C19|].
           split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact C20|].
           split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact C23|].
           split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact C24|].
           split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact C25|].
           split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26|].
           split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact C3|].
           rewrite (KR 4%bv ltac:(cbv; tauto)); exact C4.
        -- rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27.
        -- exact Ht.
        -- rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22.
        -- exact SVN.
        -- exact Q1.
        -- exact R10.
        -- exact R11.
        -- exact R12'.
        -- exact Hk.
        -- exact HO.
        -- exact Hop.
        -- split; [exact Hpk | split; [exact Hsi | exact Hh]].
        -- lia.
  - psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK wr_Bspan A_wr_li. { apply awr_ok_x_nil. }
      wr_mem HF Em2. clear HF HFr HG0.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE2
        ltac:(vm_compute; reflexivity)) as KR.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra [20%bv] HS HAE2
        ltac:(vm_compute; reflexivity) 20%bv ltac:(left; reflexivity)) as K20.
      cbn [ms_regs restrict] in KR, K20.
      pmkst HS. rewrite Em2, Em in *.
      apply (SKIP _ _ KR K20 HJ). left. exact Hpk.
    + exfalso. assert (E21 : ew E 21 = Z_to_bv 64 0) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
      rewrite branch_eq_U, (U_atom _ 21 _ E21), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.

(* ------------------------------------------------------------------ the arm *)
Theorem lf_arm_write : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 1 cx t W c -> SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  eapply SRr_bind; [exact (wr_head cx t W c HB HA)|].
  intros W1 c1 _ HT. eapply SRr_bind; [exact (wr_tst cx t W1 c1 HB HT)|].
  intros W2 c2 _ HJ. exact (wr_join cx t W2 c2 HB HJ).
Qed.
End wr.
