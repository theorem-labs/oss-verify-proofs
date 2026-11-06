(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 746 of its 805 lines of code are new or changed and 467 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A' (ASan build), row TPA-FIT:
   the FIT segment, TP_PC_FIT (+248, A' 0x84de4) -> TP_PC_END (+332, A' 0x84e38).
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   WHAT IT PROVES: tp_seg_FIT_holds : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_FIT B SK CTX0 P
   (TxPut102A_Base.v), for an abstract memory invariant P; the continuation tp_k_END is applied at +332 to
   tp_at_END, whose tp_Q is the DONE arm (f1 = 0, own kept, pre = src, cap1 = tp_cap1 D from tp_fitarm).
   THE INPUTS (on the row's base, the interface TxPut102A_Base.v (sha256 62ed8c667f58; internal record), Required, none
   changed): TxPut102A_Base.v (tp_at_FIT, tp_at_END, tp_seg_FIT, tp_img, PL_txp_A over the A' listing
   lib/A/Listing_prog.v 1ab147923c5d), TxPutKeep102.v (tpk_ra_keep / tpk_hull_keep / tpk_shadow_lo / tpk_hull_lo /
   tpk_aview_of_m), S1Ledger.v (prh_ledger_kept_aview, prh_ledger_hblock), the text lib/A/PRH_FnTx.v b6f264e13647
   through Base, the engine set (YC80x / YC1fPx runners, YGcallMxmn.aj_intrin_at_xm,
   YCbqGcallW.cj_kept). Pin sha256 1be0f53d96cb9d6c; listing tx_put.asan.new.s sha256 bbe8e5e79238.
   THE CODE (DERIVED byte offsets from the entry, A' addresses as reading aids only):
     +248 add s10, s10, s6; lbu a0, 0(s10); bnez         8-byte load check of t (token; report +488 not andi)
     +260 lbu a0, 0(s7); bnez                             8-byte load check of t + 8 (report +496)
     +268 ld a0, 0(s0); ld a1, 8(s0); add a0, a0, a1; mv a1, s2; mv a2, s1
     +288 jal __asan_memcpy (b1 + len0, s, n)             YGcallMxmn.aj_intrin_at_xm OCpy, text AI below
     +292 ld a0, 8(s0); ld a1, 0(s0); add a0, a0, s1; sd a0, 8(s0)    t->n := len0 + n (no check: S0's t + 8 check)
     +308 add a0, a1, a0; srli; add a1, a1, s6; lb a1, 0(a1); bnez +440 (andi / blt slow path) 1-byte check of the NUL
     +328 sb zero, 0(a0)                                  the NUL
   REFUTED SITES (every report path of the segment): +488 / +496 (load8 of t / t + 8) by the engine's obligations,
   proved from the stack-shadow law alx_zshadow_byte (the record lies in the real stack, tpf_stk_ra); +440 / +444
   (store1 of b1 + len0 + n) by the shadow entry TPF_SH2, proved from tp_blk's range_addressable (len0 + n < cap1)
   kept across __asan_memcpy (a shadow byte is no application byte, tpk_shadow_lo).
   ACROSS THE CALL: the journal by aj_intrin_at_xmR at the cut's relation wle' segs RZ_cf (the cut follows the GROW's
   realloc; the call keeps the world, so its SRr rule is lifted into SRrG at that relation); P by srr_inv_call from the
   text's memnorm keep; the record, the saved slots and the source by the text's view frame; tp_KR by tpf_kept_step
   (the fused cj_keptR step, VIEW frame, window STK_tx_put); the buffer bytes the walk writes are FP (fit arm) or a
   block the grow made (tpf_fresh).
   NAMED ARGUMENT (Section hypothesis): AI, __asan_memcpy's text YGcallMxmn.aintrin_realizes_xm at
   OCpy and at the listing's own SIGMA AS___asan_memcpy over ARcf, lifted to ARcfx by aintrin_realizes_xm_conj
   (the text TxPut102A_Base.v's header names). No other hypothesis.
   Numerals: 248 / 292 / 332 (DERIVED offsets: TP_PC_FIT, TPF_PC_RET, TP_PC_END); 112 / 4096 / 4208 / 16496 (LENGTH:
   the frame, ESTACK, their sum, STK_tx_put); 8 / 16 / 28 (LENGTH: record fields); 16 / 4096 (LENGTH: block and page
   alignment); 32..35 / 512 (DERIVED: the engine's extra atoms and token base); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64
   (bounds); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallMxmn YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger TxPutKeep102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102 TxPut102A_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the return site of the jal __asan_memcpy at +288 (DERIVED offset) ---- *)
Definition TPF_PC_RET : Z := 292.
(* the shadow base is s6 (register atom 22, value SHADOW_OFF); the shadow span of every checked address *)
Definition TPF_Bx : sv := SOff 22 0.
Definition TPF_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* +248 .. +288: the record at s0 = t (register atom 8), read only: b1 (atom 32) at t, len0 (atom 33) at t + 8 *)
Definition tpf_rec1 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
(* s10 = t >> 3 and s7 = (t + 8 >> 3) + s6, the two shadow addresses S0 leaves in registers, in the engine's shape *)
Definition tpf_regs1 : list sv :=
  sr_set (sr_set sr_atoms (26%bv : bv 5) (SAlu ALU_SRL (SOff 8 0) (SLit 3)))
    (23%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 22 0)).
Definition tpf_facts1 : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition tpf_ss1 : sstate := mkSS (TP_OFF + TP_PC_FIT) tpf_regs1 [tpf_rec1] None tpf_facts1.
(* +292 .. +332: the record with t + 8 writable; the NUL byte at b1 + len0 + n (atom 34), writable; n' = len0 + n is
   atom 35; the two sums the code forms are aliased to atoms 35 and 34 *)
Definition tpf_rec2 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 16 8 16 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition tpf_nul : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition tpf_facts2 : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (34%nat, mkAF 0 (2 ^ 47 - 8) 0)] []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 9 0), SOff 35 0); (SAlu ALU_ADD (SOff 32 0) (SOff 35 0), SOff 34 0)].
Definition tpf_ss2 : sstate := mkSS (TP_OFF + TPF_PC_RET) sr_atoms [tpf_rec2; tpf_nul] None tpf_facts2.
(* the NUL byte's shadow entry: its 1-byte store check is discharged from the start memory (sh_ok) *)
Definition TPF_SH2 : list shent := [mkSHE 34 0 1].

(* ---- pure helpers ---- *)
Lemma tpf_regs_ok_same : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e H He r'. unfold sr_set.
destruct (bv_eqb r 0) eqn:Er; [exact (H r')|].
specialize (H r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Er'; [exact H|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Ei; [|exact H].
apply Nat.eqb_eq in Ei. apply ridx_inj in Ei. subst r'. symmetry. exact He.
Qed.

Lemma tpf_pairwise_perm : forall (A : Type) (R : A -> A -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros A R Hs l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. exact (Permutation_in _ (Permutation_sym P) Hz).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
- exact (IH2 (IH1 H)).
Qed.

Lemma tpf_mod16 : forall c, c mod 4096 = 0 -> c mod 16 = 0.
Proof.
intros c H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
replace (q * 4096) with ((q * 256) * 16) by ring. apply Z.mod_mul. lia.
Qed.
(* two multiples of m, the first below the second, are m apart *)
Lemma tpf_al16 : forall m x y, 0 < m -> x mod m = 0 -> y mod m = 0 -> x < y -> x + m <= y.
Proof.
intros m x y Hm Hx Hy Hlt. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hy; [|lia].
destruct Hx as [qx ->]. destruct Hy as [qy ->].
assert (Hq : qx < qy) by (apply (Z.mul_lt_mono_pos_r m); [exact Hm | exact Hlt]).
replace (qx * m + m) with ((qx + 1) * m) by ring. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma tpf_zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

Lemma tpf_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.

Section fit. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
#[local] Instance TPF_PrhImg : PrhImg := prh_img_A.
#[local] Instance TPF_PAListing : PAListing A_prog_listing := PL_txp_A.
#[local] Instance TPF_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* NAMED ARGUMENT: __asan_memcpy's text with the memnorm keep (YGcallMxmn.v
   aintrin_realizes_xm), at the listing's own entry SIGMA AS___asan_memcpy, over ARcf (the instance's allocator) *)
Hypothesis AI : aintrin_realizes_xm segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) OCpy
  (SIGMA AS___asan_memcpy).
(* the allocator's laws at ARcf (AR_laws_ok_cf, YG0lawscf.v) and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf segs B := AR_laws_ok_cf segs B.
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B LAWS_cf.
(* the memcpy text lifted to ARcfx = ARcf /\ xs_placed_cf (YGcallMxmn.v Section cj) *)
Let AIx := aintrin_realizes_xm_conj segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md)
  (fun ly S => xs_placed_cf ly S) OCpy (SIGMA AS___asan_memcpy) AI.
(* the world relation of the cuts after the GROW's realloc: the FIT cut's journal and keep are at it (TxPut102A_Base.v
   tp_at_FIT), and the segment's runs, its keep and the memcpy call's continuation are over it *)
#[local] Notation RW := (wle' segs YGcfRehidePost.RZ_cf).

Ltac tpl := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd,
  kHighShadowEnd, SHADOW_OFF in *; lia.

Lemma tpf_ew_reg : forall regs xs n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (Eimg (Ereg regs xs)) n = getr regs x.
Proof.
intros regs xs n x Hn. pose proof (u5_range x) as Hr. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs xs n x Hn).
Qed.
Lemma tpf_ew_x : forall regs xs j, (32 + j < A_TEXT)%nat -> ew (Eimg (Ereg regs xs)) (32 + j) = nth j xs (Z_to_bv 64 0).
Proof. intros regs xs j Hj. rewrite Eimg_low by exact Hj. exact (ew_Ereg_extra regs xs j). Qed.

(* a chunk of a symbolic region gives the bytes of its value (the converse of YI04.chunk_ok_val) *)
Lemma tpf_val_mem_of_chunk : forall E mem base off (n : N) e v,
  YP09.chunk_ok segs E mem base (YP09.mkChunk off (CVal n e)) -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> val_mem segs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hv Hn k Hk.
pose proof (N_nat_Z n) as Hnn.
assert (Hv64 : 0 <= v < 2 ^ 64).
{ split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
assert (Hk' : 0 <= Z.of_nat k < YP09.c_len (YP09.mkChunk off (CVal n e))).
{ unfold YP09.c_len, YP09.cv_len. cbn [YP09.c_val]. lia. }
destruct (H (Z.of_nat k) Hk') as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb, Hm. rewrite He in Hb. injection Hb as <-.
rewrite Hm. f_equal. rewrite le_byte_small by (try rewrite Hnn; lia).
unfold byte_of_word. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma tpf_mbyte_some : forall H (m : word -> option byte) a v, aview segs H m a = Some v ->
  mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* tp_garr8_move / tp_hull_sub of the S10 tx walk (S10TxPut.v (sha256 7d5da9894878; internal record)), verbatim in shape *)
Lemma tpf_garr8_move : forall (W W' : world segs) m m' x d l, garr8 segs (mrestrict (w_H W) m) x l ->
  (forall j, (j < length l)%nat -> aview segs (w_H W') m' (d + Z.of_nat j) = aview segs (w_H W) m (x + Z.of_nat j)) ->
  garr8 segs (mrestrict (w_H W') m') d l.
Proof.
intros W W' m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte segs (mrestrict (w_H W') m') (d + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA;
  [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma tpf_hull_sub : forall (rd : reader) p m d k, shadow_hull_vis rd p m -> p <= d -> d + k <= p + m -> 0 < k ->
  shadow_hull_vis rd d k.
Proof.
intros rd p m d k Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + k - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* a range of the real stack is addressable in every ARcfx state (the stack-shadow law, alx_zshadow_byte) *)
Lemma tpf_stk_ra : forall ly S Hp (W : world segs) mem md a n, ARcfx B ly S Hp W mem md ->
  ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte segs B (ARcfx B) LAWS ly S Hp W mem md x HAR ltac:(lia)).
Qed.

(* the buffer of a granted grow is not a block of the entry state (prhtx_grow's second arm; the cut state's blocks are
   pairwise disjoint, so (b1, cap1) occurs once in its permutation of (b1, cap1) :: bl1 ++ bl2) *)
Lemma tpf_fresh : forall ly0 S0 ly3 S3 Hp3 (W3 : world segs) mem3 md3 b0 cap0 b1 cap1,
  ARcfx B ly3 S3 Hp3 W3 mem3 md3 -> In (b1, cap1) (ablocks B ly3 S3) -> cap0 < cap1 ->
  prhtx_grow B ly0 S0 ly3 S3 b0 cap0 b1 cap1 -> ~ In (b1, cap1) (ablocks B ly0 S0).
Proof.
intros ly0 S0 ly3 S3 Hp3 W3 mem3 md3 b0 cap0 b1 cap1 HAR Hin1 Hlt Hgrow Hin0.
destruct Hgrow as [(_ & Ec & _) | (_ & bl1 & bl2 & Hsplit & Hperm)]; [lia|].
pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR Hin1) as (_ & _ & _ & _ & _ & Hpw).
assert (Hin12 : In (b1, cap1) (bl1 ++ bl2)).
{ destruct Hsplit as [(_ & E0) | (_ & E0)]; rewrite E0 in Hin0; [exact Hin0|].
  apply in_app_or in Hin0 as [H|[H|H]]; [apply in_or_app; left; exact H | injection H as _ H2; lia |
    apply in_or_app; right; exact H]. }
pose proof (Permutation_map (fun b : Z * Z => (fst b, req_size (snd b))) Hperm) as Hpm.
pose proof (tpf_pairwise_perm _ zdisjoint tpf_zdisjoint_sym _ _ Hpm Hpw) as Hpw'.
cbn [map pairwise] in Hpw'. destruct Hpw' as [HF _]. rewrite Forall_forall in HF.
specialize (HF (b1, req_size cap1) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hin12)).
unfold zdisjoint in HF. cbn [fst snd] in HF. pose proof (req_size_pos cap1 ltac:(lia)). lia.
Qed.

(* THE KEEP ACROSS THE SEGMENT: cj_keptR from entry to the cut, a view frame from the cut to a later memory at the same
   allocator state whose written bytes lie in the walker's window, in OR, or in a block of that state that is in FPc
   or was not a block of the entry state (the fused form of YCbqGcallW.v's cj_kept_exec and cj_kept_trans; the
   frame is a VIEW equality because __asan_memcpy's text states its frame through aview). Over any world relation R:
   the step keeps the world, so R's conjunct passes through. *)
Lemma tpf_kept_step : forall (R : world segs -> world segs -> Prop)
  STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 mem3 md3 (Wr : Z -> Prop),
  cj_keptR (SK := SK) segs B prh_pst R STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 ->
  ARcfx B ly2 S2 Hp2 W2 mem2 md2 ->
  YM05.alloc_ceiling <= sp - STKf -> ly_stk_lo ly2 <= sp - STKf -> sp <= ly_stk_hi ly2 ->
  aos_step FPc mdc md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, Wr a -> (sp - STKf <= a < sp) \/ inFP OR a \/
     (exists b m, In (b, m) (ablocks B ly2 S2) /\ b <= a < b + req_size m /\
        (inFP FPc a \/ ~ In (b, m) (ablocks B lyc Sc)))) ->
  cj_keptR (SK := SK) segs B prh_pst R STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 W2 mem3 md3.
Proof.
intros R STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 mem3 md3 Wr
  (Hly & Hsecs & Hwle & Hio & Hfrs & F1 & F2 & Hgone & F3 & F4 & F5) HAR Hcs Hwlo Hwhi Hio3 Heqw HW.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hblk : forall b m a, In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
  4096 <= a < YM05.alloc_ceiling).
{ intros b m a Hb Ha. pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & H4096 & Hc & _).
  lia. }
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio3|]. split; [exact Hfrs|].
split.
{ intros a Ha Hw Hq. rewrite <- (F1 a Ha Hw Hq). apply Heqw; [lia|]. intros HWa.
  destruct (HW a HWa) as [Hs | [Ho | (b & m & Hb & Hr & _)]]; [exact (Hw Hs) | exact (Hq Ho) |].
  pose proof (Hblk b m a Hb Hr). lia. }
split.
{ intros p m i H1 H2 Hi Hf Hq. rewrite <- (F2 p m i H1 H2 Hi Hf Hq).
  pose proof (Hblk p m (p + i) H2 ltac:(lia)) as Hpi.
  apply Heqw; [lia|]. intros HWa.
  destruct (HW _ HWa) as [Hs | [Ho | (b & m' & Hb & Hr & Hc)]]; [lia | exact (Hq Ho) |].
  destruct (Z.eq_dec b p) as [Ebp | Nbp]; [destruct (Z.eq_dec m' m) as [Emm | Nmm]|].
  - subst b m'. destruct Hc as [Hc | Hc]; [exact (Hf Hc) | exact (Hc H1)].
  - assert (Hne : (b, m') <> (p, m)) by (intros E; injection E as _ E2; exact (Nmm E2)).
    pose proof (sep_blocks_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 b m' p m HAR Hb H2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - assert (Hne : (b, m') <> (p, m)) by (intros E; injection E as E1 _; exact (Nbp E1)).
    pose proof (sep_blocks_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 b m' p m HAR Hb H2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split; [exact Hgone|].
split.
{ intros a Hi Hn He Hpst Hsp Hq. rewrite <- (F3 a Hi Hn He Hpst Hsp Hq).
  pose proof (@pa_segs_low _ _ PA a Hi) as Hal.
  apply Heqw; [lia|]. intros HWa.
  destruct (HW a HWa) as [Hs | [Ho | (b & m & Hb & Hr & _)]]; [lia | exact (Hq Ho) |].
  exact (blk_img_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 b m a HAR Hb Hr Hi). }
split.
{ intros cid pos a Hin Hr Hf Hq. rewrite <- (F4 cid pos a Hin Hr Hf Hq).
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hin).
  assert (Efr : frame_addr ly2 cid pos = frame_addr lyc cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR Hin2) as (Hf0 & Hfc & Hfh).
  rewrite Efr in Hf0, Hfc, Hfh. pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr.
  assert (Ha : 0 <= a < YM05.alloc_ceiling) by (destruct Hr as [Hr|Hr]; zlia).
  apply Heqw; [lia|]. intros HWa.
  destruct (HW a HWa) as [Hs | [Ho | (b & m & Hb & Hrb & _)]]; [lia | exact (Hq Ho) |].
  destruct (alx_blocks segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR Hb) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 b m cid pos HAR Hb Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr in Hd.
  destruct Hr as [Hr|Hr]; zlia. }
intros a Hx He Hq. rewrite <- (F5 a Hx He Hq).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (Hx2 : Exists (in_zr a) (ly_extra ly2)) by (rewrite Eextra; exact Hx).
pose proof (alx_extra segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 a HAR Hx2) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa.
destruct (HW a HWa) as [Hs | [Ho | (b & m & Hb & Hr & _)]]; [apply Xs; lia | exact (Hq Ho) | exact (Xb b m Hb Hr)].
Qed.

(* ---- the two symbolic states ---- *)
Lemma tpf_st1 : forall (W : world segs) regs mem t b len,
  getr regs 8 = w64 t -> getr regs 22 = w64 SHADOW_OFF -> getr regs 26 = w64 (t / 8) ->
  getr regs 23 = w64 (SHADOW_OFF + (t + 8) / 8) ->
  2 ^ 46 <= t <= 2 ^ 47 - 32 -> t mod 8 = 0 -> 0 <= b < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  val_mem segs (rdW W mem) t 8 b -> val_mem segs (rdW W mem) (t + 8) 8 len ->
  st_ok_pi segs VAL (Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 len])) tpf_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (TP_OFF + TP_PC_FIT))) mem (seg_rom segs))).
Proof.
intros W regs mem t b len R8 R22 R26 R23 Ht Hta Hb Hl Mb Ml.
set (E := Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 len])).
assert (E8 : ew E 8 = w64 t) by (unfold E; rewrite (tpf_ew_reg regs _ 8 8%bv eq_refl); exact R8).
assert (E22 : ew E 22 = w64 SHADOW_OFF) by (unfold E; rewrite (tpf_ew_reg regs _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (unfold E; exact (tpf_ew_x regs _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 len) by (unfold E; exact (tpf_ew_x regs _ 1 ltac:(unfold A_TEXT; lia))).
assert (U8 : bv_unsigned (ew E 8) = t) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold tpf_ss1. apply pa_entry_st_ok_full.
- unfold tpf_regs1. apply tpf_regs_ok_same; [apply tpf_regs_ok_same; [unfold E; apply regs_ok_Eimg_Ereg|]|].
  + rewrite R26. apply bv_eq.
    change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 8 0) (SLit 3)))) with (U E (SAlu ALU_SRL (SOff 8 0) (SLit 3))).
    rewrite U_srl3, U_SOff, U8, Z.add_0_r, zcanon_id by (unfold M64; lia).
    unfold w64. rewrite unsigned_lit_small; [reflexivity|].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  + rewrite R23. apply bv_eq.
    change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 22 0))))
      with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 22 0))).
    rewrite tpf_U_add, U_srl3, !U_SOff, U8, U22, Z.add_0_r.
    rewrite (zcanon_id (t + 8)) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
    assert (Hq : 0 <= (t + 8) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    rewrite Z.mod_small by (unfold SHADOW_OFF; lia).
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). lia.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, tpf_rec1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val segs E _ t 0 8 (SOff 32 0) b); [| lia | lia | rewrite Z.add_0_r; exact Mb].
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + apply (chunk_ok_val segs E _ t 8 8 (SOff 33 0) len); [| lia | lia | exact Ml].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- unfold tpf_facts1. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U8, U22. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma tpf_st2 : forall (W : world segs) regs mem t b len n,
  getr regs 8 = w64 t -> getr regs 22 = w64 SHADOW_OFF -> getr regs 9 = w64 n ->
  2 ^ 46 <= t <= 2 ^ 47 - 32 -> t mod 8 = 0 ->
  0 <= b -> 0 <= len -> 0 <= n -> b + len + n <= 2 ^ 47 - 8 -> b + len + n + 1 <= t ->
  val_mem segs (rdW W mem) t 8 b -> val_mem segs (rdW W mem) (t + 8) 8 len ->
  (forall a, t + 8 <= a < t + 16 -> writable_at segs (rdW W mem) a) ->
  writable_at segs (rdW W mem) (b + len + n) ->
  st_ok_pi segs VAL
    (Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 (b + len + n); Z_to_bv 64 (len + n)])) tpf_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (TP_OFF + TPF_PC_RET))) mem (seg_rom segs))).
Proof.
intros W regs mem t b len n R8 R22 R9 Ht Hta Hb Hl Hn HQ HQt Mb Ml Hw8 HwQ.
set (E := Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 len; Z_to_bv 64 (b + len + n); Z_to_bv 64 (len + n)])).
assert (E8 : ew E 8 = w64 t) by (unfold E; rewrite (tpf_ew_reg regs _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 n) by (unfold E; rewrite (tpf_ew_reg regs _ 9 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = w64 SHADOW_OFF) by (unfold E; rewrite (tpf_ew_reg regs _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (unfold E; exact (tpf_ew_x regs _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 len) by (unfold E; exact (tpf_ew_x regs _ 1 ltac:(unfold A_TEXT; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (b + len + n)) by (unfold E; exact (tpf_ew_x regs _ 2 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (len + n)) by (unfold E; exact (tpf_ew_x regs _ 3 ltac:(unfold A_TEXT; lia))).
assert (U8 : bv_unsigned (ew E 8) = t) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = n) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = b) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = len) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = b + len + n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = len + n) by (rewrite E35; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold tpf_ss2. apply pa_entry_st_ok_full.
- unfold E; apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, tpf_rec2.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw8; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E _ t 0 8 (SOff 32 0) b); [| lia | lia | rewrite Z.add_0_r; exact Mb].
      cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * apply (chunk_ok_val segs E _ t 8 8 (SOff 33 0) len); [| lia | lia | exact Ml].
      cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + unfold region_ok, tpf_nul.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (b + len + n + o) with (b + len + n) by lia. exact HwQ.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [tpf_rec2 tpf_nul YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U34.
  split; [split; [right; lia | exact I] | split; [exact I | exact I]].
- unfold tpf_facts2. split; [|split; [exact I|]]; cbn [f_atoms f_alias atoms_ok alias_ok].
  + unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U22, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
  + split; [|split; [|exact I]]; apply U_inj; rewrite tpf_U_add, !U_SOff, ?U9, ?U32, ?U33, ?U34, ?U35, !Z.add_0_r;
      rewrite !zcanon_id by (unfold M64; lia); rewrite Z.mod_small by lia; lia.
Qed.

(* a symbolic state at listing offset TP_OFF + o is the cut configuration tp_cfg o (Caw102A_WA4.v's wa4_leaf), over any
   world relation R *)
Lemma tpf_leaf : forall (R : world segs -> world segs -> Prop) (W : world segs) E ss ms md o
  (G : world segs -> config -> Prop),
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = TP_OFF + o ->
  SRrG segs R W (tp_cfg o (ms_regs ms) (ms_mem ms) md) G -> SRrG segs R W (mkCfg ms md) G.
Proof.
intros R W E ss ms md o G HS Hrv Hpc H.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv), Hpc.
unfold tp_cfg, tp_pc in H. rewrite Z.add_assoc. exact H.
Qed.

(* the buffer bytes the segment writes are the entry's FP (the fit arm: the old buffer) or a block the grow made *)
Lemma tpf_buf : forall D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1,
  tp_at_FIT B SK CTX0 D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 ->
  forall a, b1 <= a < b1 + cap1 -> inFP (tp_FP D) a \/ ~ In (b1, cap1) (ablocks B (tp_ly D) (tp_S D)).
Proof.
intros D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT a Ha.
pose proof HAT as (WS & HBUD & HCAR & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _ & HNEED & _ & _ & HARM & _ & _).
pose proof HCAR as (_ & HJ & _). unfold tp_JR in HJ. pose proof HJ as (HAR3 & _).
pose proof HBLK as (_ & Hin1 & _).
destruct HARM as [(Hnc & Eb & Ec & _ & _) | (Hlt & Ec & Hgrow & _)].
- left. unfold tp_FP, prhtx_fp. apply inFP_cons. right. unfold tp_need in Hnc.
  destruct (Z.eqb_spec (tp_cap0 D) 0) as [E0|E0]; [exfalso; lia|].
  cbn [ablocks_fp map]. apply inFP_cons. left. cbn [fst snd]. subst b1 cap1.
  pose proof (req_size_pos (tp_cap0 D) ltac:(lia)). lia.
- right. apply (tpf_fresh _ _ ly3 S3 Hp3 W3 mem3 md3 (tp_b0 D) (tp_cap0 D) b1 cap1 HAR3 Hin1); [|exact Hgrow].
  unfold tp_req, tp_need in *. lia.
Qed.

(* ---- THE END STATE: tp_at_END from the cut and what the segment did to memory. The segment wrote the bytes
   [b1 + len0, b1 + len0 + n] (the copy and the NUL), __asan_memcpy's scratch below sp = sp0 - 112, and t->n at
   [t + 8, t + 16); the copy holds src, the NUL 0, t->n len0 + n. ---- *)
Lemma tpf_end : forall D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 regsE memE mdE kE WSE,
  tp_at_FIT B SK CTX0 D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 -> tp_img B ->
  tp_budget D WSE -> tp_JR B SK RW D ly3 S3 Hp3 W3 memE mdE kE WSE ->
  (forall r : bv 5, In r [2; 3; 4]%bv -> getr regsE r = getr regs3 r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (b1 + tp_len0 D <= a <= b1 + tp_len0 D + tp_n D) ->
     ~ (tp_sp0 D - TP_FRAME - ESTACK <= a < tp_sp0 D - TP_FRAME) -> ~ (tp_t D + 8 <= a < tp_t D + 16) ->
     aview segs (w_H W3) memE a = aview segs (w_H W3) mem3 a) ->
  (forall i, 0 <= i < tp_n D ->
     aview segs (w_H W3) memE (b1 + tp_len0 D + i) = aview segs (w_H W3) mem3 (tp_s D + i)) ->
  aview segs (w_H W3) memE (b1 + tp_len0 D + tp_n D) = Some 0 ->
  val_mem segs (rdW W3 memE) (tp_t D + 8) 8 (tp_len0 D + tp_n D) ->
  tp_at_END B SK CTX0 D ly3 S3 Hp3 W3 regsE memE mdE kE.
Proof.
intros D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 regsE memE mdE kE WSE HAT IMG HBE HJE HKRE HFRM HCPY HNUL HV8.
pose proof HAT as (WS & HBUD & HCAR & HSH & Hf0 & R19 & R21 & R23 & R25 & R26 & HREC & HBLK & HTXT & HNEED & HSDJ & HKEPT3 &
  HARM & HSIDE & HPOS).
pose proof HCAR as (HPRE & HJ & HK & HKR & HSP & HSV & EHp & HROD).
pose proof HPRE as (HFP & HCLO & HRL0 & HRP0 & HLIVE & H10 & H11 & H12 & HFW & HPL & HTR & HREC0 & HINV0 & HSRC0 &
  HSLEN & HKEPT0 & HDISJ0 & HNEED0 & HLG0 & HEV0 & HLB & HREQ & HLEN).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPL as (Hta & Ht1 & Ht2 & Hwrit0 & Hra28).
pose proof HREC as (Rb1 & Rl0 & Rc1 & Rf & Mb & Ml & Mc & Mf).
pose proof HBLK as (Hcap1 & Hin1 & Hb4096 & Hbceil & Hbamr & Hbwr & Hbra & Hbhull & Hblam).
pose proof HSIDE as (HLG3 & HSRC3 & HRL3).
pose proof HSRC3 as (Hsby & Hs4096 & Hsceil & Hsamr & Hsra & Hshull).
rewrite HSLEN in Hsceil, Hsamr, Hsra, Hshull.
pose proof HINV0 as (Hltxt & _).
unfold tp_JR in HJ, HJE.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkJ & _).
pose proof HJE as (HARE & _ & _ & _ & HioE & _ & _ & _ & _ & _ & _ & _ & _ & HpresE & _ & _).
pose proof HstkJ as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (_ & HC4096). unfold ASAN_CEIL in HC4096.
unfold TxPut102A_Base.TP_PrhImg in *.
assert (FTP : @STK_tx_put prh_img_A = 16496) by (vm_compute; reflexivity).
unfold tp_need in HNEED, HNEED0. unfold tp_sp0 in *. unfold TP_FRAME, ESTACK in HFRM.
assert (Hn0 : 0 <= tp_n D) by lia.
pose proof (req_size_pos cap1 ltac:(lia)) as (Hrq1 & Hrq2).
pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR3 Hin1) as (Hb16 & _ & Hbc & _ & _ & _).
(* the bytes the segment wrote, and where everything else lies *)
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (b1 <= a < b1 + cap1) ->
  aview segs (w_H W3) memE a = aview segs (w_H W3) mem3 a) by (intros a Ha Hb; apply HFRM; lia).
assert (Hhi : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ (tp_regs D) - 4208 <= a < spZ (tp_regs D) - 112) ->
  ~ (tp_t D + 8 <= a < tp_t D + 16) -> aview segs (w_H W3) memE a = aview segs (w_H W3) mem3 a)
  by (intros a Ha H1 H2; apply HFRM; lia).
assert (Hshb : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ (b1 <= a < b1 + cap1)) by (intros a Ha Hb; tpl).
assert (Hsh : forall x, b1 <= x < b1 + cap1 ->
  aview segs (w_H W3) memE (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W3) mem3 (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (TxPutKeep102.tpk_shadow_lo x ltac:(lia)) as Hs.
  apply Hlow; [lia|]. apply Hshb. unfold shadow_of_addr. split; [pose proof (Z.div_pos x 8); lia|].
  assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). tpl. }
assert (Hhl : forall s0, shadow_addr b1 / 8 * 8 <= s0 < shadow_addr (b1 + cap1 - 1) / 8 * 8 + 8 ->
  aview segs (w_H W3) memE s0 = aview segs (w_H W3) mem3 s0).
{ intros s0 Hs0. pose proof (TxPutKeep102.tpk_hull_lo b1 cap1 s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs0) as Hs.
  apply Hlow; [lia|]. apply Hshb. unfold shadow_addr, SHADOW_OFF in Hs0. Z.div_mod_to_equations. tpl. }
assert (Hheads : forall a kk i, In (a, kk) (tp_Lam D) -> 0 <= i < 8 ->
  aview segs (w_H W3) memE (a - cf_head + i) = aview segs (w_H W3) mem3 (a - cf_head + i)).
{ intros a kk i Hin Hi.
  destruct (S1Ledger.prh_ledger_hblock B ly3 S3 Hp3 W3 mem3 _ _ _ _ _ a kk _ _ HLG3 Hin) as (Hk & Hab & _).
  pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR3 Hab) as (Hp16 & Hp4096 & Hpc & _).
  assert (Hne : (a - cf_head, kk + cf_head) <> (b1, cap1)) by (intros E; injection E as E1 _; exact (Hblam a kk Hin E1)).
  pose proof (sep_blocks_x segs B (ARcfx B) LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ HAR3 Hab Hin1 Hne) as Hd.
  pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hkc : 0 <= kk + cf_head) by lia.
  pose proof (req_size_pos (kk + cf_head) Hkc) as (Hrk & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (tpf_mod16 _ HC4096) as Hc16.
  assert (Hpl : a - cf_head + 16 <= YM05.alloc_ceiling) by (apply tpf_al16; [lia | exact Hp16 | exact Hc16 | lia]).
  apply Hlow; [lia|].
  destruct Hd as [Hd | Hd].
  - assert (a - cf_head + 16 <= b1) by (apply tpf_al16; [lia | exact Hp16 | exact Hb16 | lia]). lia.
  - lia. }
assert (Hpst : forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W3) memE a = aview segs (w_H W3) mem3 a).
{ intros a Ha. pose proof (tpi_pst_img B IMG a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
  apply Hlow; [tpl|]. intros Hb.
  exact (blk_img_x segs B (ARcfx B) LAWS ly3 S3 Hp3 W3 mem3 md3 b1 cap1 a HAR3 Hin1 ltac:(lia) Hi). }
(* the arm: the grow fact and the capacity the DONE arm names, and the buffer bytes the walk may write *)
assert (HGR : prhtx_grow B (tp_ly D) (tp_S D) ly3 S3 (tp_b0 D) (tp_cap0 D) b1 cap1 /\
  blocks_bytes S3 <= blocks_bytes (tp_S D) + cap1 - tp_cap0 D /\ cap1 = tp_cap1 D).
{ unfold tp_cap1, TxModel.tx_cap1.
  destruct HARM as [(Hnc & Eb & Ec & Ely & ES) | (Hlt & Ec & Hgrow & Hbb)].
  - unfold tp_need in Hnc. rewrite (proj2 (Z.leb_le _ _) Hnc). subst ly3 S3 b1 cap1.
    split; [left; split; [reflexivity | split; reflexivity]|]. split; [lia | reflexivity].
  - unfold tp_need in Hlt. rewrite (proj2 (Z.leb_gt _ _) Hlt). unfold tp_req, tp_need in Ec.
    split; [exact Hgrow|]. split; [exact Hbb | exact Ec]. }
assert (HFR : forall a, b1 <= a < b1 + cap1 -> inFP (tp_FP D) a \/ ~ In (b1, cap1) (ablocks B (tp_ly D) (tp_S D))).
{ exact (tpf_buf D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT). }
exists WSE. split; [exact HBE|].
split.
- (* tp_carry *)
  split; [exact HPRE|]. split; [unfold tp_JR; exact HJE|].
  split.
  { unfold tp_KR in HK |- *.
    apply (tpf_kept_step RW (@STK_tx_put prh_img_A) (spZ (tp_regs D)) (tp_OR D) (tp_FP D) (tp_ly D) (tp_S D) (tp_W D)
      (tp_mem D) (tp_md D) ly3 S3 Hp3 W3 mem3 md3 memE mdE
      (fun a => (b1 + tp_len0 D <= a <= b1 + tp_len0 D + tp_n D) \/
                (spZ (tp_regs D) - 4208 <= a < spZ (tp_regs D) - 112) \/ (tp_t D + 8 <= a < tp_t D + 16))
      HK HAR3).
    - lia.
    - rewrite Eslo. lia.
    - rewrite Eshi. lia.
    - exact HioE.
    - intros a Ha HnW. apply HFRM; [exact Ha | | |]; intros H; apply HnW; [left | right; left | right; right];
        first [exact H | lia].
    - intros a [Hb | [Hs | Hr]].
      + right. right. exists b1, cap1. split; [exact Hin1|]. split; [lia|]. apply HFR. lia.
      + left. lia.
      + right. left. unfold tp_OR, tp_FP, prhtx_fp. apply inFP_cons. left. lia. }
  split.
  { intros r Hr. assert (Hr' : In r [2; 3; 4]%bv)
      by (destruct Hr as [<- | [<- | []]]; [right; left | right; right; left]; reflexivity).
    rewrite (HKRE r Hr'). exact (HKR r Hr). }
  split; [unfold spZ; rewrite (HKRE 2%bv ltac:(left; reflexivity)); exact HSP|].
  split.
  { unfold tp_saved in HSV |- *. unfold tp_sp0 in HSV |- *.
    destruct HSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
    repeat split; (eapply val_mem_kept; [intros i Hi; apply Hhi; lia | eassumption]). }
  split; [exact EHp|].
  intros a Hro Hno Hne.
  assert (Hi : in_img segs a).
  { destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
  pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
  rewrite Hlow; [exact (HROD a Hro Hno Hne) | tpl |].
  intros Hb. exact (blk_img_x segs B (ARcfx B) LAWS ly3 S3 Hp3 W3 mem3 md3 b1 cap1 a HAR3 Hin1 ltac:(lia) Hi).
- (* tp_Q: the DONE arm *)
  exists b1, cap1, 0, (tp_own D), (tp_src D).
  rewrite HSLEN.
  split.
  { split.
    { (* prhtx_rec *)
      split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
      split; [eapply val_mem_kept; [intros i Hi; apply Hhi; lia | exact Mb]|].
      split; [exact HV8|].
      split; [eapply val_mem_kept; [intros i Hi; apply Hhi; lia | exact Mc]|].
      eapply val_mem_kept; [intros i Hi; apply Hhi; lia | exact Mf]. }
    split.
    { (* prhtx_inv *)
      split; [rewrite length_app, Nat2Z.inj_add, Hltxt, HSLEN; reflexivity|].
      right. split; [lia|]. split; [lia|]. split; [exact Hin1|].
      split.
      { unfold bytes_at. apply (proj2 (garr8_app segs _ _ _ _)). split.
        - apply (proj2 (garr8_app segs _ _ _ _)). split.
          + apply (tpf_garr8_move W3 W3 mem3 memE b1 b1 (tp_txt D) HTXT). intros j Hj.
            apply HFRM; lia.
          + apply (tpf_garr8_move W3 W3 mem3 memE (tp_s D) _ (tp_src D) Hsby). intros j Hj.
            rewrite Hltxt. rewrite (HCPY (Z.of_nat j)) by lia. reflexivity.
        - intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
          split; [|cbn; lia]. intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
          rewrite length_app, Nat2Z.inj_add, Hltxt, HSLEN. cbn [Z.of_nat nth]. rewrite !Z.add_0_r.
          match goal with |- mbyte _ _ ?x = _ => replace x with (b1 + tp_len0 D + tp_n D) by lia end.
          rewrite (tpf_mbyte_some _ _ _ 0 HNUL). reflexivity. }
      split; [lia|]. split; [lia|]. split; [exact Hbamr|].
      split.
      { intros a Ha.
        pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HARE Hin1) as (_ & _ & _ & _ & Hprs & _).
        apply (apresent_writable segs). apply (proj1 (Hprs a ltac:(lia))). }
      split; [apply (TxPutKeep102.tpk_ra_keep (aview segs (w_H W3) mem3)); [exact Hsh | exact Hbra]|].
      split; [apply (TxPutKeep102.tpk_hull_keep (aview segs (w_H W3) mem3)); [exact Hhl | exact Hbhull]|].
      exact Hblam. }
    split.
    { (* prhtx_place *)
      split; [exact Hta|]. split; [exact Ht1|]. split; [exact Ht2|].
      split; [intros a Ha; apply (apresent_writable segs); apply HpresE; lia|].
      apply (tpf_stk_ra ly3 S3 Hp3 W3 memE mdE); [exact HARE | rewrite Eslo; lia | rewrite Eshi; lia]. }
    split; [exact EHp|].
    destruct HGR as (Hg & Hbb & _). split; [exact Hg | exact Hbb]. }
  split; [left; split; [exact Hf0|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    exact (proj2 (proj2 HGR))|].
  split; [intros _; reflexivity|].
  split.
  { unfold bytes_at in *. apply (tpf_garr8_move W3 W3 mem3 memE (tp_s D) (tp_s D) (tp_src D) Hsby). intros j Hj.
    apply Hlow; [lia|]. apply HSDJ. lia. }
  split; [exact HRL3|].
  split; [exact (proj1 HPOS)|]. split; [exact (proj2 HPOS)|].
  apply (S1Ledger.prh_ledger_kept_aview B ly3 S3 Hp3 W3 mem3 ly3 S3 Hp3 W3 memE _ _ _ _ _ _ _ HLG3).
  + exact Hpst.
  + exact Hheads.
  + intros a kk _ H. exact H.
  + apply Permutation_refl.
Qed.

(* a register of the symbolic state, as its denotation *)
Ltac tpf_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* a goal `In r l` for a literal register r of a literal list *)
Ltac tpf_in := cbn; repeat (first [left; reflexivity | right]).

(* ---- THE ROW: tp_seg_FIT ---- *)
(* (the statement is Base's tp_seg_FIT, taken verbatim) *)
Theorem tp_seg_FIT_holds : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_FIT B SK CTX0 P.
Proof.
intros P PLAW PCALL Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT IMG KEND HPM.
pose proof HAT as (WS & HBUD & HCAR & HSH & Hf0 & R19 & R21 & R23 & R25 & R26 & HREC & HBLK & HTXT & HNEED & HSDJ & HKEPT3 &
  HARM & HSIDE & HPOS).
pose proof HCAR as (HPRE & HJ & HK & HKR & HSP & HSV & EHp & HROD).
pose proof HSH as (R22 & R8 & R9 & R18).
pose proof HPRE as (HFP & HCLO & HRL0 & HRP0 & HLIVE & H10 & H11 & H12 & HFW & HPL & HTR & HREC0 & HINV0 & HSRC0 &
  HSLEN & HKEPT0 & HDISJ0 & HNEED0 & HLG0 & HEV0 & HLB & HREQ & HLEN).
pose proof HFP as (HPX & _). pose proof HPX as (_ & _ & _ & Hgp & Htp & _).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPL as (Hta & Ht1 & Ht2 & Hwrit0 & Hra28).
pose proof HREC as (Rb1 & Rl0 & Rc1 & Rf & Mb & Ml & Mc & Mf).
pose proof HBLK as (Hcap1 & Hin1 & Hb4096 & Hbceil & Hbamr & Hbwr & Hbra & Hbhull & Hblam).
pose proof HSIDE as (HLG3 & HSRC3 & HRL3).
pose proof HSRC3 as (Hsby & Hs4096 & Hsceil & Hsamr & Hsra & Hshull).
rewrite HSLEN in Hsceil, Hsamr, Hsra, Hshull.
(* the cut's journal is at the budget WS (the grow's wild trace, or none) and at the relation RW; the run and
   __asan_memcpy's rule read an empty-budget journal: the cut's, rebased at the cut's depot
   (YCbqGwild.ajournal_xw_rebaseR); unbased at the end *)
pose proof HJ as HJw. unfold tp_JR in HJw.
pose proof (ajournal_xw_rebaseR (SK := SK) segs B prh_pst _ RW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ0.
pose proof HJ0 as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkJ & _).
pose proof HstkJ as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TxPut102A_Base.TP_PrhImg, TPF_PrhImg in *.
assert (FTP : @STK_tx_put prh_img_A = 16496) by (vm_compute; reflexivity).
unfold tp_need in HNEED, HNEED0. unfold tp_sp0 in *. unfold spZ in HSP. unfold TP_FRAME in HSP.
pose proof (req_size_pos cap1 ltac:(lia)) as (Hrq1 & Hrq2).
assert (Hn0 : 0 <= tp_n D) by lia.
assert (Htlo : 2 ^ 46 <= tp_t D <= 2 ^ 47 - 32).
{ assert (Hup : tp_t D + 28 <= 2 ^ 47) by (unfold spZ in *; lia).
  pose proof (tpf_al16 8 (tp_t D) (2 ^ 47 - 24) ltac:(lia) Hta ltac:(reflexivity) ltac:(lia)) as Hal.
  split; [unfold spZ in *; lia | lia]. }
assert (Hshb : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ (b1 <= a < b1 + cap1)) by (intros a Ha Hb; tpl).
(* the buffer bytes the segment writes are writable for the journal (awr_byte) *)
assert (HAWR : forall a, b1 <= a < b1 + cap1 ->
  awr_byte (@STK_tx_put prh_img_A + tp_dw D) (spZ (tp_regs D) + tp_dw D) (tp_FP D)
    (ablocks B (tp_ly D) (tp_S D)) (ablocks B ly3 S3) ly3 [] a).
{ intros a Ha. destruct (tpf_buf D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT a Ha) as [Hf | Hn].
  - right. left. split; [exact Hf|]. exists b1, cap1. split; [exact Hin1 | lia].
  - right. right. left. exists b1, cap1. split; [exact Hin1|]. split; [exact Hn | lia]. }
(* ---- +248 .. +288: the two 8-byte load checks, the loads of t->b and t->n, up to jal __asan_memcpy ---- *)
set (E1 := Eimg (Ereg regs3 [Z_to_bv 64 b1; Z_to_bv 64 (tp_len0 D)])).
assert (HEI : img_env VAL A_LIM E1) by (unfold E1; apply Eimg_env).
assert (E1_32 : ew E1 32 = Z_to_bv 64 b1) by (unfold E1; exact (tpf_ew_x regs3 _ 0 ltac:(unfold A_TEXT; lia))).
assert (E1_33 : ew E1 33 = Z_to_bv 64 (tp_len0 D))
  by (unfold E1; exact (tpf_ew_x regs3 _ 1 ltac:(unfold A_TEXT; lia))).
pose proof (tpf_st1 W3 regs3 mem3 (tp_t D) b1 (tp_len0 D) R8 R22 R26 R23 Htlo Hta ltac:(lia) ltac:(lia) Mb Ml) as HS1.
fold E1 in HS1.
assert (SHOK1 : sh_ok segs TPF_Bx [] E1 (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (UB1 : U E1 TPF_Bx = SHADOW_OFF).
{ unfold TPF_Bx. apply U_atom; [unfold E1; rewrite (tpf_ew_reg regs3 _ 22 22%bv eq_refl); exact R22 |].
  unfold SHADOW_OFF; lia. }
assert (UT1 : forall c, 0 <= c <= 16 -> U E1 (SOff 8 c) = tp_t D + c).
{ intros c Hc. rewrite U_SOff. unfold E1. rewrite (tpf_ew_reg regs3 _ 8 8%bv eq_refl), R8. unfold w64.
  rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
pose (RUN := paj_run_x_invR (fx := fx) (SK := SK) (PL := TPF_PAListing) (PI := PA) B prh_pst (ARcfx B) LAWS P PLAW
  RW (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
unfold tp_cfg, tp_pc. rewrite <- Z.add_assoc.
(* the FIT cut is after the GROW's realloc: the segment is over RW (SRr' segs RZ_cf is SRrG segs RW) *)
unfold SRr'.
paj_run_tok_x_inv RUN HS1 HJ0 SHOK1 HPM TPF_Bspan.
1,2: (match goal with |- range_addressable ?rd _ _ _ => change rd with (aview segs (w_H W3) mem3) end;
      rewrite UB1, UT1 by lia; apply (tpf_stk_ra ly3 S3 Hp3 W3 mem3 md3); [exact HAR3 | rewrite Eslo | rewrite Eshi];
      unfold spZ in *; lia).
1: (apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]).
(* at the jal: the record and the memory are unchanged *)
lazymatch goal with H : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
lazymatch type of HS1 with st_ok _ ?Ex _ _ => set (E1' := Ex) in * end.
assert (AG1 : forall i, (i < 512)%nat -> ew E1' i = ew E1 i)
  by (intros i Hi; unfold E1'; rewrite !ew_ewset_other by lia; reflexivity).
assert (AGR1 : env_agree 32 (Ereg regs3 [Z_to_bv 64 b1; Z_to_bv 64 (tp_len0 D)]) E1').
{ split; [intros i Hi; rewrite (AG1 i ltac:(lia)); unfold E1; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (KR1 : forall r, In r [2; 3; 4; 8; 9; 18; 22]%bv -> getr (ms_regs msc) r = getr regs3 r)
  by exact (regs_kept_of_st_ok segs _ _ (restrict (w_H W3) msc) regs3 _ [2; 3; 4; 8; 9; 18; 22]%bv HS1 AGR1
    ltac:(vm_compute; reflexivity)).
assert (Q10 : getr (ms_regs msc) 10 = w64 (b1 + tp_len0 D)).
{ tpf_reg HS1 (10%bv : bv 5) Hr. rewrite Hr. apply bv_eq.
  change (bv_unsigned (sv_denot E1' (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))))
    with (U E1' (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))).
  rewrite tpf_U_add, !U_SOff, !AG1 by lia. rewrite E1_32, E1_33, !Z.add_0_r, !unsigned_lit_small by lia.
  rewrite !zcanon_id by (unfold M64; lia). rewrite Z.mod_small by lia.
  unfold w64. rewrite ?unsigned_lit_small by lia. reflexivity. }
assert (Q11 : getr (ms_regs msc) 11 = getr regs3 18).
{ tpf_reg HS1 (11%bv : bv 5) Hr. rewrite Hr. cbn [sv_denot]. rewrite AG1 by lia. unfold E1.
  rewrite (tpf_ew_reg regs3 _ 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q12 : getr (ms_regs msc) 12 = getr regs3 9).
{ tpf_reg HS1 (12%bv : bv 5) Hr. rewrite Hr. cbn [sv_denot]. rewrite AG1 by lia. unfold E1.
  rewrite (tpf_ew_reg regs3 _ 9 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q1 : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + (TP_OFF + TPF_PC_RET))).
{ tpf_reg HS1 (1%bv : bv 5) Hr. rewrite Hr.
  lazymatch goal with H : img_env _ _ E1' |- _ => exact (codeptr_val (PI := PA) E1' 14384 H) end. }
rewrite (st_ok_restrict_mkst segs _ _ _ _ HS1 eq_refl). cbn [ss_pc setpc].
rewrite EM1. rewrite EM1 in HJ0, HPM.
(* ---- +288: __asan_memcpy (b1 + len0, s, n) through its text (YGcallMxmn.aj_intrin_at_xmR over RW: the call keeps
   the world, so its SRr rule is lifted into RW by YA0nH.SRr_SRrG and bound at RW) ---- *)
eapply (SRrG_bind segs RW (wle'_trans segs YGcfRehidePost.RZ_cf)).
{ apply (SRr_SRrG segs RW (wle_wle' segs YGcfRehidePost.RZ_cf)).
  eapply (aj_intrin_at_xmR (SK := SK) segs B prh_pst (ARcfx B) LAWS (@pa_segs_low _ _ PA) RW OCpy
    (SIGMA AS___asan_memcpy) AIx W3 (ms_regs msc) mem3 (@STK_tx_put prh_img_A + tp_dw D) (spZ (tp_regs D) + tp_dw D)
    (tp_FP D) (tp_ly D) (set_depot (st_depot S3) (tp_S D)) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 _ k
    (b1 + tp_len0 D) (tp_s D) (tp_n D) (-112 - tp_dw D) (Z_to_bv 64 (BASE + (TP_OFF + TPF_PC_RET))) HJ0).
  - exact Q10.
  - rewrite Q11. exact R18.
  - rewrite Q12. exact R9.
  - lia.
  - lia.
  - lia.
  - unfold spZ in *. rewrite (KR1 2%bv ltac:(tpf_in)). lia.
  - pose proof Hd16 as Hq. apply Z.mod_divide in Hq; [|lia]. destruct Hq as [q Hq]. rewrite Hq.
    replace (-112 - q * 16) with ((-7 - q) * 16) by ring. apply Z.mod_mul. lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (KR1 3%bv ltac:(tpf_in)), (HKR 3%bv ltac:(tpf_in)). exact Hgp.
  - rewrite (KR1 4%bv ltac:(tpf_in)), (HKR 4%bv ltac:(tpf_in)). exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [rewrite TP_OFF_val; unfold TPF_PC_RET; lia | vm_compute; reflexivity].
  - intros a Ha. split; [apply HAWR; lia | unfold ESTACK; lia].
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ b1 cap1 _ _ Hbra); lia.
  - intros Hn. apply (tpf_hull_sub _ b1 cap1); [exact Hbhull | lia | lia | exact Hn].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - replace a with (tp_s D + Z.of_nat (Z.to_nat (a - tp_s D))) by lia. unfold aview.
        rewrite (garr8_mbyte segs _ (tp_s D) (tp_src D) (Z.to_nat (a - tp_s D)) Hsby) by lia. discriminate.
      - unfold spZ in *. rewrite (KR1 2%bv ltac:(tpf_in)). unfold ESTACK. lia. }
    split.
    { destruct (Z_le_gt_dec (b1 + tp_len0 D + tp_n D) (tp_s D)) as [h|h]; [left; exact h|].
      destruct (Z_le_gt_dec (tp_s D + tp_n D) (b1 + tp_len0 D)) as [h'|h']; [right; exact h'|].
      exfalso. destruct (Z_le_gt_dec (b1 + tp_len0 D) (tp_s D)) as [hc|hc].
      - exact (HSDJ (tp_s D) ltac:(lia) ltac:(lia)).
      - exact (HSDJ (b1 + tp_len0 D) ltac:(lia) ltac:(lia)). }
    split; [exact Hsamr|]. split; [exact Hsra | exact Hshull]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & R10' & HCPY & HFR2 & HPRS2 & HMN2).
assert (HPM2 : P mem2) by exact (PCALL _ mem2 HMN2 HPM).
(* ---- +292 .. +332: t->n := len0 + n, the 1-byte store check and the NUL store ---- *)
assert (KR2 : forall r, In r [2; 3; 4; 8; 9; 18; 22]%bv -> getr regs2 r = getr regs3 r).
{ intros r Hr. rewrite <- (KR1 r Hr). cbn in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ first [ exact (HPR 2 ltac:(unfold acallee_saved; lia)) | exact (HPR 3 ltac:(unfold acallee_saved; lia))
            | exact (HPR 4 ltac:(unfold acallee_saved; lia)) | exact (HPR 8 ltac:(unfold acallee_saved; lia))
            | exact (HPR 9 ltac:(unfold acallee_saved; lia)) | exact (HPR 18 ltac:(unfold acallee_saved; lia))
            | exact (HPR 22 ltac:(unfold acallee_saved; lia)) ] | ]).
  destruct Hr. }
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ2 & _ & _).
pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR2 Hin1) as (_ & _ & _ & _ & Hprs2 & _).
assert (HFR2' : forall a, 0 <= a < 2 ^ 64 -> ~ (b1 + tp_len0 D <= a < b1 + tp_len0 D + tp_n D) ->
  ~ (spZ (tp_regs D) - 4208 <= a < spZ (tp_regs D) - 112) -> aview segs (w_H W3) mem2 a = aview segs (w_H W3) mem3 a).
{ intros a Ha H1 H2. apply HFR2; [exact Ha | exact H1 | unfold ESTACK; lia]. }
assert (M2b : val_mem segs (rdW W3 mem2) (tp_t D) 8 b1)
  by (eapply val_mem_kept; [intros i Hi; apply HFR2'; unfold spZ in *; lia | exact Mb]).
assert (M2l : val_mem segs (rdW W3 mem2) (tp_t D + 8) 8 (tp_len0 D))
  by (eapply val_mem_kept; [intros i Hi; apply HFR2'; unfold spZ in *; lia | exact Ml]).
assert (W28 : forall a, tp_t D + 8 <= a < tp_t D + 16 -> writable_at segs (rdW W3 mem2) a)
  by (intros a Ha; apply (apresent_writable segs); apply HpresJ2; unfold spZ in *; lia).
assert (WQ : writable_at segs (rdW W3 mem2) (b1 + tp_len0 D + tp_n D))
  by (apply (apresent_writable segs); apply (proj1 (Hprs2 (b1 + tp_len0 D + tp_n D) ltac:(lia)))).
assert (R8' : getr regs2 8 = w64 (tp_t D)) by (rewrite (KR2 8%bv ltac:(tpf_in)); exact R8).
assert (R22' : getr regs2 22 = w64 SHADOW_OFF) by (rewrite (KR2 22%bv ltac:(tpf_in)); exact R22).
assert (R9' : getr regs2 9 = w64 (tp_n D)) by (rewrite (KR2 9%bv ltac:(tpf_in)); exact R9).
assert (HQb : b1 + tp_len0 D + tp_n D <= 2 ^ 47 - 8) by lia.
assert (HQt : b1 + tp_len0 D + tp_n D + 1 <= tp_t D) by (unfold spZ in *; lia).
pose proof (tpf_st2 W3 regs2 mem2 (tp_t D) b1 (tp_len0 D) (tp_n D) R8' R22' R9' Htlo Hta ltac:(lia) ltac:(lia) Hn0
  HQb HQt M2b M2l W28 WQ) as HS2.
set (E2 := Eimg (Ereg regs2 [Z_to_bv 64 b1; Z_to_bv 64 (tp_len0 D); Z_to_bv 64 (b1 + tp_len0 D + tp_n D);
  Z_to_bv 64 (tp_len0 D + tp_n D)])) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
assert (U2_8 : bv_unsigned (ew E2 8) = tp_t D).
{ unfold E2. rewrite (tpf_ew_reg regs2 _ 8 8%bv eq_refl), R8'. unfold w64. apply unsigned_lit_small. lia. }
assert (E2_34 : ew E2 34 = Z_to_bv 64 (b1 + tp_len0 D + tp_n D))
  by (unfold E2; exact (tpf_ew_x regs2 _ 2 ltac:(unfold A_TEXT; lia))).
assert (E2_35 : ew E2 35 = Z_to_bv 64 (tp_len0 D + tp_n D))
  by (unfold E2; exact (tpf_ew_x regs2 _ 3 ltac:(unfold A_TEXT; lia))).
assert (U2_34 : bv_unsigned (ew E2 34) = b1 + tp_len0 D + tp_n D) by (rewrite E2_34; apply unsigned_lit_small; lia).
assert (U2B : U E2 TPF_Bx = SHADOW_OFF).
{ unfold TPF_Bx. apply U_atom; [unfold E2; rewrite (tpf_ew_reg regs2 _ 22 22%bv eq_refl); exact R22' |].
  unfold SHADOW_OFF; lia. }
assert (U2Q : U E2 (SOff 34 0) = b1 + tp_len0 D + tp_n D)
  by (rewrite U_SOff, U2_34, Z.add_0_r; apply zcanon_id; unfold M64; lia).
(* the NUL byte's 1-byte store check: its shadow is the buffer's, kept by __asan_memcpy (an application byte) *)
assert (SHOK2 : sh_ok segs TPF_Bx TPF_SH2 E2 (mrestrict (w_H W3) mem2)).
{ unfold sh_ok, TPF_SH2. constructor; [|constructor]. unfold shent_ok. cbn [she_m she_lo she_hi]. split.
  - rewrite U2B, U2Q. change (rd_of segs (mrestrict (w_H W3) mem2)) with (aview segs (w_H W3) mem2).
    apply (TxPutKeep102.tpk_ra_keep (aview segs (w_H W3) mem3)).
    + intros x Hx. pose proof (TxPutKeep102.tpk_shadow_lo x ltac:(lia)) as Hs. apply HFR2'; [lia | | unfold spZ in *; lia].
      intros Hb. apply (Hshb (shadow_of_addr SHADOW_OFF x)); [|lia]. unfold shadow_of_addr.
      split; [pose proof (Z.div_pos x 8); lia|]. assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). tpl.
    + apply (range_addressable_sub _ _ b1 cap1 _ _ Hbra); lia.
  - unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite U2B. rewrite U2Q in Ha. tpl. }
pose (RUNTO := paj_run_to_x_invR (fx := fx) (SK := SK) (PL := TPF_PAListing) (PI := PA) B prh_pst (ARcfx B) LAWS P
  PLAW RW (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
paj_run_to_tok_x_inv RUNTO HS2 HJ2 SHOK2 HPM2 TPF_Bspan (TP_OFF + TP_PC_END).
1: { intros a (r & Hr & Ha). try change (ss_mem tpf_ss2) with [tpf_rec2; tpf_nul] in Hr. cbn [In] in Hr.
     destruct Hr as [<- | [<- | []]];
       cbn [tpf_rec2 tpf_nul YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U2_8, ?U2_34 in Ha.
     - left. unfold spZ in *. lia.
     - apply HAWR. lia. }
(* at +332 *)
lazymatch goal with H : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ => set (E3 := Ex) in * end.
assert (AG3 : forall i, (i < 512)%nat -> ew E3 i = ew E2 i)
  by (intros i Hi; unfold E3; rewrite !ew_ewset_other by lia; reflexivity).
assert (FE : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D + 8 <= a < tp_t D + 16) -> a <> b1 + tp_len0 D + tp_n D ->
  aview segs (w_H W3) (ms_mem ms3) a = aview segs (w_H W3) mem2 a).
{ intros a Ha H1 H2. apply TxPutKeep102.tpk_aview_of_m. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). try change (ss_mem tpf_ss2) with [tpf_rec2; tpf_nul] in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [tpf_rec2 tpf_nul YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra;
    rewrite ?U2_8, ?U2_34 in Hra; lia. }
pose proof (st_ok_mem_ok segs _ _ _ HS2) as (_ & HROK & _).
cbn [abs_ss setpc ss_mem ms_mem restrict] in HROK.
apply Forall_cons_iff in HROK as [RG1 HROK]. apply Forall_cons_iff in HROK as [RG2 _].
unfold region_ok in RG1, RG2.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in RG1, RG2.
destruct RG1 as (_ & _ & _ & HC1). destruct RG2 as (_ & _ & _ & HC2).
apply Forall_cons_iff in HC1 as [HC8 _]. apply Forall_cons_iff in HC2 as [HCN _].
rewrite (AG3 8%nat ltac:(lia)), U2_8 in HC8. rewrite (AG3 34%nat ltac:(lia)), U2_34 in HCN.
assert (SD35 : sv_denot E3 (SOff 35 0) = Z_to_bv 64 (tp_len0 D + tp_n D)).
{ cbn [sv_denot]. rewrite (AG3 35%nat ltac:(lia)), E2_35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Hv64 : 0 <= tp_len0 D + tp_n D < 2 ^ (8 * Z.of_N 8)) by (change (8 * Z.of_N 8) with 64; lia).
pose proof (tpf_val_mem_of_chunk E3 _ (tp_t D) 8 8 (SOff 35 0) (tp_len0 D + tp_n D) HC8 SD35 Hv64
  ltac:(vm_compute; congruence)) as HV8.
pose proof (tpf_val_mem_of_chunk E3 _ (b1 + tp_len0 D + tp_n D) 0 1 (SLit 0) 0 HCN eq_refl
  ltac:(vm_compute; split; congruence) ltac:(vm_compute; congruence)) as HN1.
assert (HNUL : aview segs (w_H W3) (ms_mem ms3) (b1 + tp_len0 D + tp_n D) = Some 0).
{ specialize (HN1 0%nat ltac:(vm_compute; lia)). cbn [Z.of_nat] in HN1. rewrite !Z.add_0_r in HN1.
  unfold aview. rewrite HN1. vm_compute. reflexivity. }
assert (AGR3 : env_agree 32 (Ereg regs2 [Z_to_bv 64 b1; Z_to_bv 64 (tp_len0 D); Z_to_bv 64 (b1 + tp_len0 D + tp_n D);
  Z_to_bv 64 (tp_len0 D + tp_n D)]) E3).
{ split; [intros i Hi; rewrite (AG3 i ltac:(lia)); unfold E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (KR3 : forall r, In r [2; 3; 4]%bv -> getr (ms_regs ms3) r = getr regs2 r)
  by exact (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4]%bv HS2 AGR3 ltac:(vm_compute; reflexivity)).
apply (tpf_leaf RW W3 _ _ ms3 _ TP_PC_END _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
apply (KEND ly3 S3 Hp3 W3 (ms_regs ms3) (ms_mem ms3) _ k); [|exact HPM2].
apply (tpf_end D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 (ms_regs ms3) (ms_mem ms3) _ k WS HAT IMG HBUD).
- unfold tp_JR. eapply (ajournal_xw_unbase0R (SK := SK) segs B prh_pst _ RW); [exact HJ2 | exact (ajxR_wild HJw)].
- intros r Hr. rewrite (KR3 r Hr). apply KR2. destruct Hr as [<- | [<- | [<- | []]]]; tpf_in.
- intros a Ha H1 H2 H3. unfold tp_sp0, TP_FRAME, ESTACK in H2.
  rewrite (FE a Ha H3 ltac:(lia)). apply HFR2'; [exact Ha | lia | lia].
- intros i Hi. rewrite (FE (b1 + tp_len0 D + i) ltac:(lia) ltac:(unfold spZ in *; lia) ltac:(lia)). exact (HCPY i Hi).
- exact HNUL.
- exact HV8.
Qed.

End fit.

Print Assumptions tp_seg_FIT_holds.
