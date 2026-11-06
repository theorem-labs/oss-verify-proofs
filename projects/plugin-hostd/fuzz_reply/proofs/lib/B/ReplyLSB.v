(* proves no function (rule 24; kind: model instance + model rules): fr_LS for image B and SEG_HEAD's two LS rules *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) twin of lib/A/ReplyLS.v at f57b3e2d0ca
   (a working branch): fr_LS, the concrete live-state invariant LS of the entry walk of
   LLVMFuzzerTestOneInput (the Section variable `LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop` of
   lib/B/W_LLVMFuzzerTestOneInput_cut.v :617 and lib/B/W_LLVMFuzzerTestOneInput_head.v :241), typed over lib/B's
   records, taken as far as SEG_HEAD's two LS premises and the prologue's LS need them:
     the constants MB_K, MB_C, W_P, W_H (A :75-78); the measures hl_bytes, vsl, slot_pend, slot_held, slot_vsl,
     slot_npend, entry_held, pend_bytes, held_bytes, vslack, npend (A :83-90, :92-97), PHI and kk (A :102-103);
     bsum_app, bsum_perm, bsum_cons, bsum_nil and the count tactic perm_lia (A :117-140); fr_LS (A :221-228, the
     final text: no lm_cap conjunct); fr_LS_keep and fr_LS_k_only (A :246-265); hd_k'_ge (A :291-292);
     fr_LS_head_nout_b / fr_LS_head_skip_b (A :317-326, fr_LS_head_nout / fr_LS_head_skip); ls_pro_m and the
     satisfiability witness fr_LS_pro_b (A :563-608, ls_pro_m / fr_LS_pro: LS at the first head, at A's proposed
     LS_pro premise; ls_pro_m names ls_new_src, a verbatim copy of lib/B/W_op_add.v :148-149 oa_new_src).
   For the shape of LS (structural, not a meter: LS bounds the live blocks through the model's split and the potential
   PHI) see A's header, A :7-36; the text of fr_LS is A's, conjunct for conjunct.
   The last Section states SEG_HEAD's premises LS_head_nout (lib/B/W_LLVMFuzzerTestOneInput_head.v :275) and
   LS_head_skip (:281) word for word, at LS := fr_LS B CALL_ROOM_B, and closes each by its lemma.
   A -> B SWAPS (A at f57b3e2d0ca; B at cb5e14dbcf9):
   - ACfn_cf.CALL_ROOM (lib/A/ACfn_cf.v :47, := 2 ^ 33) -> the Section variable CALL_ROOM_B.  A's value comes from the
     cf driver: ACfn_cf.v :14-18 (a Theorem Labs lane's ruling of 2026-10-29) and lib/A/AD1r_heap_cf.v :59 H_live and :74
     H_bytes, which give fr_live_pre (blocks_bytes S + CALL_ROOM <= LIVE_MAX) at every call of the cf driver loop.
     At cb5e14dbcf9 image B has no such derivation: no lib/B/YCfn_cf.v (B's _cut.v :211 names it; the file is absent),
     no cf driver heap file, and lib/B/YCfn.v :26 LIVE_LIB = 2 ^ 33 is the room of the NON-cf contract, which
     lib/B/YD1r.v :647 discharges from the donor's `Permutation (ablocks B ly S) [(buf, cap)]` split (false for
     fuzz_reply after its first call, AD1r_heap_cf.v :1-4).  So CALL_ROOM_B stays a Section variable (a Theorem Labs lane's
     ruling of 2026-10-29 22:48Z: keep it a variable; no B kit file defines a CALL_ROOM): SEG_HEAD's two LS rules
     hold for every value (they do not read it), fr_LS_pro_b holds for every value, and the B top supplies the
     measured value when it instantiates LS;
   - lib/A AB1v -> lib/B YB1v; lib/Reusable YE01 -> lib/B YE01; lib/A AE2k -> lib/B YE2k, followed by
     `Require ReplyGuardB` as every lib/B walk file (lib/B/W_LLVMFuzzerTestOneInput_head.v :55, :57, :67);
   - lib/A ACfn (Imported) -> lib/B YCfn, Required only (lib/B/W_LLVMFuzzerTestOneInput_head.v :60);
   - lib/A W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal -> lib/B's files of the same names;
   - lib/A W_rep W_contract W_sites W_frame -> lib/B's files of the same names (AREC :57, APARTIAL :61, ATABLE :60 of
     lib/B/W_rep.v; model_blks reads asrc_blks :277, aentry_blks :325, aout_blks :408; ra_new is lib/B/W_contract.v
     :1085, A's text);
   - lib/A W_op_add -> NOT loaded: lib/B/W_op_add.v does not compile at cb5e14dbcf9 (line 1239: "Expects a
     disjunctive pattern with 1 branch or a conjunctive pattern made of 2 patterns"); the one name A reads from it,
     oa_new_src (B W_op_add.v :148-149), is copied verbatim below as ls_new_src;
   - lib/A W_LLVMFuzzerTestOneInput_cut -> lib/B W_LLVMFuzzerTestOneInput_cut (OPS_MAX :197, lfcx :320, lf_base :323,
     lmod :375, slot_blks :402, model_blks :403, input_blks :406, in_byte :447, picks :448, nopen :456, pick :458);
   - lib/A W_LLVMFuzzerTestOneInput_head -> lib/B W_LLVMFuzzerTestOneInput_head (lm_clear_O :246, lm_set_k :248,
     hd_kb :250, hd_k' :251).
   - fr_LS_pro_b: A states it at `lf_base B ameter_triv XM_LIB RLO RHI ACfn_cf.fr_live_pre G_fr cx`.  Here the meter
     MT is a universally quantified argument: the lemma holds at EVERY MT : ameter_ops of the record
     lib/Reusable/YC5d.v :17 (the one lib/B/W_LLVMFuzzerTestOneInput_cut.v :136 imports), so at the meter B's cf
     contract names, and it is not a witness at ameter_triv.  (fr_LS does not read MT, and the proof reads only
     lf_base's input-range and fr_live_pre conjuncts, never mo_ok.  At cb5e14dbcf9 that record's only instance is
     ameter_triv, lib/Reusable/YCbp.v :17-18, which lib/B/W_asm.v :64 names.  lib/B/YCbp.v :20 ameter_triv, which
     lib/B/W_asm.v :160 and lib/B/ReplyTFIBBParts.v :60, :66 pass, is an instance of a DIFFERENT record,
     lib/B/YC5d.v :18, and is not a value of this MT.)  fr_live_pre is ACfn_cf.fr_live_pre's text
     (lib/A/ACfn_cf.v :49) at CALL_ROOM_B.  The Context adds {SK : YI16.sink_head}: lib/B/ReplyGuardB.v removes the
     sink classes' hints, so lf_base's sink argument comes from the Context (as _head.v :137).
   Not loaded (the definitions here read nothing from them): A's lib/Reusable YCbp (ameter_triv: MT is quantified
   here), lib/A W_LLVMFuzzerTestOneInput_small / _write / _add (no lib/B file at cb5e14dbcf9) and ACfn_cf (absent
   for B).  Not ported: slot_open (A :91), the list and measure helpers (A :105-116, :142-217) that only the other
   rules use, fr_LS_room / fr_LS_k / ROOM_SPARE (A :79, :230-242) and fr_LS_pro_oa (A :549-561), which read
   CALL_ROOM's value, and the rules of the other arms (A :266-289, :293-314, :327-548, :611-683), which read B segment
   files that do not exist yet.
   CONSTANT-SWAP TABLE: every constant this file's text reads.  Each B value is read from image B's own binary
   (fuzz_reply.asan-ubsan, sha256 10ffb5f9202ae2bd..., through its fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record)) or
   from a file at cb5e14dbcf9; none is A's value plus an offset.
     name                       | A value  | B value   | where B's value comes from
     CALL_ROOM | A 2^33 (ACfn_cf.v:47) | B: Section variable | consumer must supply
     LIVE_MAX                   | 2 ^ 34   | 2 ^ 34    | no image value: lib/Reusable/YG01.v :332, the allocator kit both
                                |          |           | images load
     APARTIAL                   | 6000     | 6000      | B W_rep.v :63; B binary op_add 0x8525c `lui a0,0x1`, 0x85260
                                |          |           | `addiw a0,a0,1904` (0x1770), 0x85264 malloc
     ATABLE                     | 896      | 896       | B W_rep.v :62; B binary relay_add 0x82b6c `li s6,16`, 0x82b74-
                                |          |           | 0x82b7c `slli a1,s6,0x3; slli a2,s6,0x6; sub a1,a2,a1` (16 * 56),
                                |          |           | 0x82b80 realloc
     AREC                       | 16       | 16        | B W_rep.v :59; B binary list_push 0x853dc `slli a1,s9,0x4`
                                |          |           | (capacity * 16), 0x853e0 realloc
     OPS_MAX (LS_head_skip)     | 512      | 512       | B _cut.v :197; B binary 0x84818 `li a0,512`, 0x8481c `bne s9,a0`
     FIRST_FD (ls_pro_m)        | 100      | 100       | B binary op_add 0x8523c `addiw a0,a1,100`
     slots (length lm_hs = 4)   | 4        | 4         | B binary 0x84664 `li a4,4` (the open-count loop); op_add 0x851e0
                                |          |           | `li a0,384` with the stride 0x851fc `addi s2,s2,96` (384 / 96)
     op modulus (mod 10)        | 10       | 10        | B binary 0x8460c `li a2,10`, 0x84610 `mul`, 0x84614 `sub`
     input bound (c_n < 2 ^ 26) | 2 ^ 26   | 2 ^ 26    | B _cut.v :247 (fr_lib_pre_cf), :398 (ainput_at); B binary 0x8451c
                                |          |           | `srli a0,s5,0x1a`, 0x84530 `bnez a0,85014` (the size refusal)
     MB_K, MB_C, W_P, W_H       | 65, 2 ^ 26, 64, 4    | the same: no image value, the potential's own constants
                                |          |           | (A :75-78) over the model both images share *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k), as lib/B's segment files Require it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ the constants (A :75-78) *)
Definition MB_K : Z := 65.                       (* per input byte consumed: a write's n + 1 copy and 64 n credit *)
Definition MB_C : Z := 67108864.                 (* 2^26: the first head's g_src table, slack for the constants *)
Definition W_P : Z := 64.                        (* the credit a queued byte carries into the drain *)
Definition W_H : Z := 4.                         (* the credit a held key byte carries into remove / gone *)

(* ------------------------------------------------------------------ the measures of the model (A :82-97) *)
Local Notation zsum l := (fold_right Z.add 0 l).
Definition hl_bytes (l : hlist) : Z := zsum (map (fun r : Z * list byte => Z.of_nat (length (snd r))) (hl_recs l)).
Definition vsl (l : hlist) : Z := AREC * Z.max 0 (2 * hl_n l - hl_cap l).
Definition slot_pend (o : option hsrc) : Z :=
  match o with Some h => Z.max 0 (hl_bytes (hs_pending h) - hs_off h) | None => 0 end.
Definition slot_held (o : option hsrc) : Z := match o with Some h => hl_bytes (hs_held h) | None => 0 end.
Definition slot_vsl (o : option hsrc) : Z :=
  match o with Some h => vsl (hs_pending h) + vsl (hs_expected h) + vsl (hs_held h) | None => 0 end.
Definition slot_npend (o : option hsrc) : Z := match o with Some h => hl_n (hs_pending h) | None => 0 end.
Definition entry_held (e : rentry) : Z :=
  zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)).
Definition pend_bytes (m : lmod) : Z := zsum (map slot_pend (lm_hs m)).
Definition held_bytes (m : lmod) : Z := zsum (map slot_held (lm_hs m)) + zsum (map entry_held (lm_es m)).
Definition vslack (m : lmod) : Z := zsum (map slot_vsl (lm_hs m)).
Definition npend (m : lmod) : Z := zsum (map slot_npend (lm_hs m)).
Section ls.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* B's twin of A's ACfn_cf.CALL_ROOM (lib/A/ACfn_cf.v :47): a Section variable (a Theorem Labs lane's ruling, 22:48Z); the
   consumer that instantiates LS supplies the value (see the header) *)
Variable CALL_ROOM_B : Z.

Definition PHI (m : lmod) : Z := bsum (model_blks m) + W_P * pend_bytes m + W_H * held_bytes m + vslack m.
Definition kk (cx : lfcx) (m : lmod) : Z := Z.min (lm_k m) (c_n cx).

(* ------------------------------------------------------------------ list and count helpers (A :117-140) *)
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn [app bsum fold_right] in *; unfold bsum in *; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' HP. induction HP; unfold bsum in *; cbn in *; lia. Qed.
Lemma bsum_cons : forall b l, bsum (b :: l) = snd b + bsum l.
Proof. reflexivity. Qed.
Lemma bsum_nil : bsum [] = 0.
Proof. reflexivity. Qed.

Definition zzdec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition cnt1 (a x : Z * Z) : nat := count_occ zzdec [a] x.
Lemma cnt_cons : forall a l x, count_occ zzdec (a :: l) x = (cnt1 a x + count_occ zzdec l x)%nat.
Proof. intros a l x. unfold cnt1. cbn [count_occ]. destruct (zzdec a x); lia. Qed.
Lemma cnt_nil : forall x, count_occ zzdec [] x = 0%nat.
Proof. reflexivity. Qed.
Ltac cnt_norm := repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *).
(* turn every Permutation hypothesis and the goal into counts at one point, then linear arithmetic.  Each loop ends:
   the first clears the hypothesis it reads, the second replaces a hypothesis by its instance at x, which no longer
   matches the pattern; this Section has no Permutation or count hypothesis. *)
Ltac perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  cnt_norm; lia.

(* ------------------------------------------------------------------ LS (A :221-228) *)
Definition fr_LS (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  exists rest e0,
    Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) /\
    bsum rest + bsum (input_blks cx) + e0 <= blocks_bytes (c_S cx) /\
    blocks_bytes (c_S cx) + CALL_ROOM_B <= LIVE_MAX /\
    0 <= c_n cx < 2 ^ 26 /\ length (lm_hs m) = 4%nat /\
    4 * npend m <= kk cx m /\
    PHI m <= MB_K * kk cx m + APARTIAL * nopen (lm_hs m) + e0 + MB_C.

(* ------------------------------------------------------------------ the rules that keep the model's blocks (A :244-265) *)
(* a model with the same blocks and measures and no less input consumed has the same LS (t is free) *)
Lemma fr_LS_keep : forall cx t t' m m' ly S,
  model_blks m' = model_blks m -> PHI m' = PHI m -> nopen (lm_hs m') = nopen (lm_hs m) ->
  length (lm_hs m') = length (lm_hs m) -> npend m' = npend m -> kk cx m <= kk cx m' ->
  fr_LS cx t m ly S -> fr_LS cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S Hb Hp Ho Hl Hn Hk (rest & e0 & HP & HR & HE & Hc & Hl0 & Hnp & HM).
  exists rest, e0. rewrite Hb, Hp, Ho, Hl, Hn. unfold MB_K in *.
  refine (conj HP (conj HR (conj HE (conj Hc (conj Hl0 (conj _ _)))))); lia.
Qed.
(* the measures read lm_hs, lm_es, lm_G, lm_cap and lm_out only *)
Lemma fr_LS_k_only : forall cx t t' m m' ly S,
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  lm_k m <= lm_k m' \/ kk cx m <= kk cx m' -> fr_LS cx t m ly S -> fr_LS cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S E1 E2 E3 E4 E5 Hk H.
  assert (Hb : model_blks m' = model_blks m) by (unfold model_blks; rewrite E1, E2, E3, E4, E5; reflexivity).
  apply (fr_LS_keep cx t t' m m' ly S Hb); [| rewrite E1; reflexivity | rewrite E1; reflexivity
    | unfold npend; rewrite E1; reflexivity | unfold kk in *; lia | exact H].
  unfold PHI, pend_bytes, held_bytes, vslack. rewrite Hb, E1, E2. reflexivity.
Qed.

(* A :291-292 *)
Lemma hd_k'_ge : forall cx m, lm_k m <= hd_k' cx m.
Proof. intros cx m. unfold hd_k'. destruct (lm_k m + 1 <? c_n cx); lia. Qed.

(* ------------------------------------------------------------------ SEG_HEAD's two (A :317-326) *)
Lemma fr_LS_head_nout_b : forall cx t m ly S, fr_LS cx t m ly S -> fr_LS cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S H. exact H. Qed.
Lemma fr_LS_head_skip_b : forall cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_LS cx t m ly S -> fr_LS cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S _ _ _ _ _ _ H. apply (fr_LS_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (hd_k'_ge cx m).
Qed.

(* ------------------------------------------------------------------ the prologue: LS at the first head (A :562-608) *)
(* The source op_add opens: a VERBATIM COPY of lib/B/W_op_add.v :148-149 oa_new_src, which this file cannot load (that
   file does not compile at cb5e14dbcf9, see the header); replace it by W_op_add.oa_new_src when W_op_add.v builds. *)
Definition ls_new_src (fd q : Z) (pj : list byte) : hsrc :=
HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list.
(* the model at the first head (A :562-564: pro_m of lib/A/W_LLVMFuzzerTestOneInput_pro.v, a working branch
   fff279dd36e; B has no _pro.v at cb5e14dbcf9, and the prologue is the same C code, fuzz_reply.c:681-684) *)
Definition ls_pro_m (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z) : lmod :=
  LM 0 [Some (ls_new_src 100 q pj); None; None; None] T' [ra_new 100] c O 0 cap out 0 1.
(* LS at the first head, AT A'S PROPOSED TEXT (A :565-570): the premise is the entry split (the entry's input, its
   table T0 when it has one, its g_out buffer and the rest) with the prologue's two cases (T0 = 0: the table is new;
   T0 <> 0: T' = T0).  The meter MT is quantified (every meter; fr_LS does not read it); fr_live_pre is A's
   ACfn_cf.fr_live_pre text (lib/A/ACfn_cf.v :49) at CALL_ROOM_B. *)
Lemma fr_LS_pro_b : forall MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B MT XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX) G_fr cx ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_LS cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S (_ & Hpre) (T0 & rest0 & HE0 & Hcase).
  destruct Hpre as (_ & _ & _ & _ & Hd & _ & _ & _ & Hlive & _). cbv beta in Hlive.
  assert (Hc : 0 <= c_n cx < 2 ^ 26) by (destruct Hd as [(Hd & _) | (Hd & _)]; lia).
  assert (Hmb : model_blks (ls_pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (Ep : pend_bytes (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eh : held_bytes (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ev : vslack (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (En : npend (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eo : nopen (lm_hs (ls_pro_m q T' pj c O cap out)) = 1) by reflexivity.
  assert (Ek : kk cx (ls_pro_m q T' pj c O cap out) = 0) by (unfold kk; cbn [ls_pro_m lm_k]; lia).
  assert (Eb0 : blocks_bytes (c_S cx) = bsum (ablocks B (c_ly cx) (c_S cx))) by apply blocks_bytes_bsum.
  destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
  - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0.
    exists rest0, (bsum (aout_blks cap out)).
    split; [rewrite Hmb; perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, ?bsum_nil; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI. rewrite Hmb, Ep, Eh, Ev, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE. lia.
  - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0.
    exists rest0, (ATABLE + bsum (aout_blks cap out)).
    split; [rewrite Hmb; perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, bsum_cons, ?bsum_nil; cbn [snd]; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI. rewrite Hmb, Ep, Eh, Ev, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE. lia.
Qed.
End ls.

(* ------------------------------------------------------------------ the premises, as SEG_HEAD states them
   lib/B/W_LLVMFuzzerTestOneInput_head.v :275 (LS_head_nout) and :281 (LS_head_skip), word for word, at
   LS := fr_LS B CALL_ROOM_B; B and CALL_ROOM_B stay free: the consumer passes its own B and supplies CALL_ROOM_B. *)
Section seg_head.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Local Notation LS := (fr_LS B CALL_ROOM_B).
Lemma LS_head_nout_b : forall cx t m ly S, LS cx t m ly S -> LS cx t (lm_clear_O m) ly S.
Proof. exact (fr_LS_head_nout_b B CALL_ROOM_B). Qed.
Lemma LS_head_skip_b : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LS cx t m ly S -> LS cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. exact (fr_LS_head_skip_b B CALL_ROOM_B). Qed.
End seg_head.
